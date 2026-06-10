#include "scripting/plugin_manager.h"

#include "config/config_service.h"
#include "core/build_info.h"
#include "core/deferred_call.h"
#include "core/log.h"
#include "core/version.h"
#include "scripting/plugin_catalog.h"
#include "scripting/plugin_git.h"
#include "scripting/plugin_id.h"
#include "scripting/plugin_manifest.h"
#include "scripting/plugin_registry.h"
#include "scripting/plugin_source_locks.h"
#include "scripting/plugin_source_paths.h"
#include "util/file_utils.h"
#include "util/string_utils.h"

#include <optional>
#include <system_error>
#include <thread>
#include <unordered_set>
#include <utility>
#include <vector>

namespace scripting {

  namespace {
    constexpr Logger kLog("plugins");

    std::filesystem::path sourceRootFor(const PluginSourceConfig& source) { return plugin_paths::registryRoot(source); }

    void removeManagedGitSourceStorage(const PluginSourceConfig& source) {
      const std::string sourceBase = FileUtils::pluginSourcesDir();
      if (!sourceBase.empty()) {
        (void)plugin_paths::removeTreeUnder(plugin_paths::sourceStorageRoot(source), sourceBase);
      }
      const std::string materializedBase = FileUtils::pluginMaterializedDir();
      if (!materializedBase.empty()) {
        (void)plugin_paths::removeTreeUnder(plugin_paths::gitMaterializedRoot(source), materializedBase);
      }
    }

    bool sourceReplacementInvalidatesGitStorage(const PluginSourceConfig& previous, const PluginSourceConfig& next) {
      if (previous.kind == PluginSourceKind::Git && next.kind == PluginSourceKind::Git) {
        return previous.location != next.location;
      }
      return previous.kind == PluginSourceKind::Git || next.kind == PluginSourceKind::Git;
    }

    std::filesystem::path materializedPluginDir(const PluginSourceConfig& source, std::string_view pluginId) {
      const auto subdir = pluginSubdirFromId(pluginId);
      if (!subdir.has_value()) {
        return {};
      }
      const auto root = plugin_paths::gitMaterializedRoot(source);
      return root.empty() ? std::filesystem::path{} : root / *subdir;
    }

    std::filesystem::path uniqueTempRoot(const std::filesystem::path& root, std::string_view subdir) {
      for (int i = 0; i < 8; ++i) {
        std::string suffix = StringUtils::generateUuid();
        if (suffix.empty()) {
          suffix = std::to_string(i);
        }
        std::filesystem::path candidate = root / (".tmp-" + std::string(subdir) + "-" + suffix);
        std::error_code ec;
        if (!std::filesystem::exists(candidate, ec)) {
          return candidate;
        }
      }
      return {};
    }

    bool replaceDirectory(
        const std::filesystem::path& stagedDir, const std::filesystem::path& finalDir,
        const std::filesystem::path& materializedRoot, std::string* error
    ) {
      if (!plugin_paths::pathIsInside(stagedDir, materializedRoot)
          || !plugin_paths::pathIsInside(finalDir, materializedRoot)) {
        if (error != nullptr) {
          *error = "refusing to replace plugin outside materialized source root";
        }
        return false;
      }

      std::error_code ec;
      const auto backupDir =
          materializedRoot / (".old-" + finalDir.filename().string() + "-" + StringUtils::generateUuid());
      bool backedUp = false;
      if (std::filesystem::exists(finalDir, ec)) {
        std::filesystem::rename(finalDir, backupDir, ec);
        if (ec) {
          if (error != nullptr) {
            *error = "failed to move previous plugin copy: " + ec.message();
          }
          return false;
        }
        backedUp = true;
      }

      ec.clear();
      std::filesystem::rename(stagedDir, finalDir, ec);
      if (ec) {
        if (backedUp) {
          std::error_code restoreEc;
          std::filesystem::rename(backupDir, finalDir, restoreEc);
        }
        if (error != nullptr) {
          *error = "failed to install plugin copy: " + ec.message();
        }
        return false;
      }

      if (backedUp) {
        (void)plugin_paths::removeTreeUnder(backupDir, materializedRoot);
      }
      return true;
    }

    struct MaterializeResult {
      bool ok = false;
      std::string error;
      int exitCode = -1;
      bool timedOut = false;
      std::filesystem::path pluginDir;
      PluginManifest manifest;

      explicit operator bool() const { return ok; }
    };

    MaterializeResult materializeFailure(std::string error, int exitCode = -1, bool timedOut = false) {
      MaterializeResult result;
      result.error = std::move(error);
      result.exitCode = exitCode;
      result.timedOut = timedOut;
      return result;
    }

    MaterializeResult materializeGitPlugin(
        const PluginSourceConfig& source, const std::filesystem::path& repoRoot, std::string_view rev,
        std::string_view pluginId
    ) {
      const auto subdir = pluginSubdirFromId(pluginId);
      if (!subdir.has_value()) {
        return materializeFailure("invalid plugin id");
      }
      const auto materializedRoot = plugin_paths::gitMaterializedRoot(source);
      if (materializedRoot.empty()) {
        return materializeFailure("empty materialized source root");
      }

      std::error_code ec;
      std::filesystem::create_directories(materializedRoot, ec);
      if (ec) {
        return materializeFailure("failed to create materialized source root: " + ec.message());
      }

      const auto tmpRoot = uniqueTempRoot(materializedRoot, *subdir);
      if (tmpRoot.empty()) {
        return materializeFailure("failed to allocate temporary plugin export directory");
      }

      const auto cleanupTmp = [&] { (void)plugin_paths::removeTreeUnder(tmpRoot, materializedRoot); };
      const auto exported = plugin_git::exportSubdir(repoRoot, rev, *subdir, tmpRoot);
      if (!exported) {
        cleanupTmp();
        return materializeFailure("export failed: " + exported.err, exported.exitCode, exported.timedOut);
      }

      const auto stagedDir = tmpRoot / *subdir;
      std::string manifestError;
      auto manifest = parsePluginManifest(stagedDir / "plugin.toml", &manifestError);
      if (!manifest.has_value()) {
        cleanupTmp();
        return materializeFailure(manifestError);
      }
      if (manifest->id != pluginId) {
        cleanupTmp();
        return materializeFailure("manifest id '" + manifest->id + "' does not match requested id");
      }

      const auto finalDir = materializedRoot / *subdir;
      std::string replaceError;
      if (!replaceDirectory(stagedDir, finalDir, materializedRoot, &replaceError)) {
        cleanupTmp();
        return materializeFailure(replaceError);
      }
      cleanupTmp();
      MaterializeResult result;
      result.ok = true;
      result.pluginDir = finalDir;
      result.manifest = std::move(*manifest);
      return result;
    }
  } // namespace

  void applyPluginSourcesToRegistry(PluginRegistry& registry, const PluginsConfig& plugins) {
    // Scan the local dev dir + every configured source; a plugin is active only if
    // its id is in [plugins].enabled (opt-in, uniform across all sources).
    std::vector<std::filesystem::path> roots;
    std::unordered_set<std::string> enabled;
    if (auto localRoot = plugin_paths::localSourceRoot(); !localRoot.empty()) {
      roots.push_back(std::move(localRoot));
    }
    for (const auto& source : plugins.sources) {
      if (auto root = sourceRootFor(source); !root.empty()) {
        roots.push_back(std::move(root));
      }
    }
    for (const auto& id : plugins.enabled) {
      if (isValidPluginId(id)) {
        enabled.insert(id);
      }
    }
    registry.setSources(std::move(roots));
    registry.setEnabledFilter(std::move(enabled));
    registry.scan();
  }

  std::filesystem::path PluginManager::sourceRoot(const PluginSourceConfig& source) const {
    return sourceRootFor(source);
  }

  std::optional<PluginSourceConfig> PluginManager::findSourceOffering(std::string_view pluginId) const {
    for (const auto& source : m_config.config().plugins.sources) {
      const auto catalog = discoverCatalog(source);
      for (const auto& entry : catalog.entries) {
        if (entry.id == pluginId) {
          return source;
        }
      }
    }
    return std::nullopt;
  }

  std::optional<PluginSourceConfig> PluginManager::findSource(std::string_view name) const {
    for (const auto& source : m_config.config().plugins.sources) {
      if (source.name == name) {
        return source;
      }
    }
    return std::nullopt;
  }

  std::unordered_set<std::string> PluginManager::localPluginIds() const {
    std::unordered_set<std::string> ids;
    const std::string data = FileUtils::dataDir();
    if (data.empty()) {
      return ids;
    }
    PluginSourceConfig localSource{
        .kind = PluginSourceKind::Path, .name = "local", .location = (std::filesystem::path(data) / "plugins").string()
    };
    for (const auto& entry : discoverCatalog(localSource).entries) {
      ids.insert(entry.id);
    }
    return ids;
  }

  bool PluginManager::ensureEnabledMaterialized(const PluginsConfig& plugins) const {
    bool materialized = false;
    std::error_code ec;
    for (const auto& source : plugins.sources) {
      if (source.kind != PluginSourceKind::Git) {
        continue;
      }
      const std::filesystem::path repoRoot = plugin_paths::gitRepoRoot(source);
      if (repoRoot.empty()) {
        continue;
      }
      auto sourceLock = plugin_source_locks::acquire(source.name);
      if (!std::filesystem::exists(repoRoot / ".git", ec)) {
        // Source repo is gone (e.g. the state dir was wiped). Re-clone it (metadata
        // only); the per-plugin export below writes what's enabled.
        std::filesystem::create_directories(repoRoot.parent_path(), ec);
        kLog.info("re-cloning missing plugin source '{}'", source.name);
        const auto cloned = plugin_git::cloneBlobless(source.location, repoRoot);
        if (!cloned) {
          if (cloned.timedOut) {
            kLog.warn("plugin source '{}': clone timed out", source.name);
          } else {
            kLog.warn("plugin source '{}': clone failed with exit code {}", source.name, cloned.exitCode);
          }
          continue; // offline / unreachable — leave it; list/enable will retry
        }
      }
      for (const auto& id : plugins.enabled) {
        const auto sub = pluginSubdirFromId(id);
        if (!sub.has_value()) {
          kLog.warn("skipping enabled plugin with invalid id '{}'", id);
          continue;
        }
        if (std::filesystem::exists(materializedPluginDir(source, id) / "plugin.toml", ec)) {
          continue; // already materialized
        }
        if (!plugin_git::hasPath(repoRoot, *sub + "/plugin.toml")) {
          continue; // this source doesn't ship it
        }
        kLog.info("exporting enabled plugin '{}' from source '{}'", id, source.name);
        const auto materializedPlugin = materializeGitPlugin(source, repoRoot, "HEAD", id);
        if (materializedPlugin) {
          materialized = true;
        } else if (materializedPlugin.timedOut) {
          kLog.warn("plugin source '{}': exporting '{}' timed out", source.name, id);
        } else {
          kLog.warn(
              "plugin source '{}': exporting '{}' failed with exit code {}", source.name, id,
              materializedPlugin.exitCode
          );
        }
      }
    }
    return materialized;
  }

  void PluginManager::refresh() {
    const PluginsConfig& pc = m_config.config().plugins;
    if (m_applied && pc == m_lastApplied) {
      return;
    }
    // Heal wiped source storage / restored config once at startup. Source storage
    // does not change on later config reloads, so don't re-touch the network then.
    if (!m_applied) {
      ensureEnabledMaterialized(pc);
    }

    applyPluginSourcesToRegistry(PluginRegistry::instance(), pc);

    m_lastApplied = pc;
    m_applied = true;
  }

  EnableResult PluginManager::enable(std::string_view pluginId) {
    const std::string id(pluginId);
    if (!isValidPluginId(id)) {
      return {.ok = false, .error = "invalid plugin id '" + id + "' (expected author/plugin)"};
    }

    // Managed source: export the plugin directory before enabling.
    if (const auto source = findSourceOffering(id); source.has_value()) {
      const std::filesystem::path root = sourceRoot(*source);
      const auto subdir = pluginSubdirFromId(id);
      if (!subdir.has_value()) {
        return {.ok = false, .error = "invalid plugin id '" + id + "' (expected author/plugin)"};
      }
      std::filesystem::path manifestDir = root / *subdir;
      std::optional<PluginManifest> materializedManifest;
      if (source->kind == PluginSourceKind::Git) {
        auto sourceLock = plugin_source_locks::acquire(source->name);
        const std::filesystem::path repoRoot = plugin_paths::gitRepoRoot(*source);
        const auto materialized = materializeGitPlugin(*source, repoRoot, "HEAD", id);
        if (!materialized) {
          return {.ok = false, .error = "export failed: " + materialized.error};
        }
        manifestDir = materialized.pluginDir;
        materializedManifest = materialized.manifest;
      }
      std::string error;
      const auto manifest = materializedManifest.has_value() ? std::move(materializedManifest)
                                                             : parsePluginManifest(manifestDir / "plugin.toml", &error);
      if (!manifest.has_value()) {
        return {.ok = false, .error = error};
      }
      if (manifest->id != id) {
        return {.ok = false, .error = "manifest id '" + manifest->id + "' does not match requested id"};
      }
      if (!noctalia::version::atLeast(noctalia::build_info::version(), manifest->minNoctalia)) {
        return {
            .ok = false,
            .error = "plugin '"
                + manifest->id
                + "' requires noctalia >= "
                + manifest->minNoctalia
                + " (running "
                + std::string(noctalia::build_info::version())
                + ")",
        };
      }
    } else if (!localPluginIds().contains(id)) {
      // Not offered by any managed source and not present locally.
      return {.ok = false, .error = "no plugin '" + id + "' found in any source"};
    }

    kLog.info("enabling plugin '{}'", id);
    m_config.setPluginEnabled(id, true);
    refresh();
    return {.ok = true, .error = {}};
  }

  void PluginManager::disable(std::string_view pluginId) {
    kLog.info("disabling plugin '{}'", pluginId);
    m_config.setPluginEnabled(pluginId, false);
    refresh();
  }

  std::vector<PluginStatus> PluginManager::list() const {
    const auto& pc = m_config.config().plugins;
    const std::unordered_set<std::string> enabledSet(pc.enabled.begin(), pc.enabled.end());

    std::vector<PluginStatus> out;
    const auto collect = [&](const std::string& sourceName, const CatalogResult& catalog) {
      for (const auto& entry : catalog.entries) {
        out.push_back(
            PluginStatus{
                .id = entry.id,
                .version = entry.version,
                .source = sourceName,
                .compatible = entry.compatible,
                .enabled = enabledSet.contains(entry.id),
            }
        );
      }
    };

    if (const std::string data = FileUtils::dataDir(); !data.empty()) {
      PluginSourceConfig localSource{
          .kind = PluginSourceKind::Path,
          .name = "local",
          .location = (std::filesystem::path(data) / "plugins").string()
      };
      collect("local", discoverCatalog(localSource));
    }
    for (const auto& source : pc.sources) {
      collect(source.name, discoverCatalog(source));
    }
    return out;
  }

  void PluginManager::addSource(const PluginSourceConfig& source) {
    if (!isValidPluginSourceName(source.name)) {
      kLog.warn("refusing plugin source with invalid name '{}'", source.name);
      return;
    }
    kLog.info("adding plugin source '{}' ({})", source.name, source.location);
    if (const auto previous = findSource(source.name);
        previous.has_value() && sourceReplacementInvalidatesGitStorage(*previous, source)) {
      auto sourceLock = plugin_source_locks::acquire(source.name);
      kLog.info("plugin source '{}' changed; deleting app-managed git storage", source.name);
      removeManagedGitSourceStorage(source);
    }
    m_config.addPluginSource(source); // fires reload -> refresh re-injects the registry
  }

  void PluginManager::update(std::string sourceName) {
    const auto source = findSource(sourceName);
    if (!source.has_value() || source->kind != PluginSourceKind::Git) {
      return; // path / unknown sources are externally owned
    }
    const std::filesystem::path repoRoot = plugin_paths::gitRepoRoot(*source);
    if (repoRoot.empty()) {
      return;
    }
    std::error_code ec;
    if (!std::filesystem::exists(repoRoot / ".git", ec)) {
      return; // nothing cloned yet
    }
    // Snapshot the enabled set for the worker (config is read on the main thread only).
    std::unordered_set<std::string> enabled;
    for (const auto& id : m_config.config().plugins.enabled) {
      if (isValidPluginId(id)) {
        enabled.insert(id);
      }
    }

    // The whole git sequence runs off-thread; only the final registry rescan marshals
    // back to the main thread. `this` is an Application member, so it outlives the worker.
    std::thread([this, source = *source, repoRoot, sourceName = std::move(sourceName),
                 enabled = std::move(enabled)]() mutable {
      auto sourceLock = plugin_source_locks::acquire(source.name);
      const auto fetched = plugin_git::fetch(repoRoot);
      if (!fetched) {
        DeferredCall::callLater([sourceName, err = fetched.err]() {
          kLog.warn("update '{}': fetch failed: {}", sourceName, err);
        });
        return;
      }
      const std::string newRev = plugin_git::remoteHead(repoRoot).out;
      const std::string curRev = plugin_git::headRevision(repoRoot).out;
      if (newRev.empty() || newRev == curRev) {
        DeferredCall::callLater([sourceName]() { kLog.info("source '{}' already up to date", sourceName); });
        return;
      }

      // Compatibility guard BEFORE applying: read the *new* catalog at the fetched
      // revision (no working-tree change) and check every enabled plugin's
      // min_noctalia. If one would require a newer Noctalia, skip the update — nothing
      // is applied, so there is nothing to undo.
      if (const auto catalog = plugin_git::showFile(repoRoot, "catalog.toml", newRev); catalog) {
        for (const auto& entry : parseCatalogToml(catalog.out)) {
          if (enabled.contains(entry.id)
              && !entry.minNoctalia.empty()
              && !noctalia::version::atLeast(noctalia::build_info::version(), entry.minNoctalia)) {
            DeferredCall::callLater([sourceName, id = entry.id, min = entry.minNoctalia]() {
              kLog.warn(
                  "update '{}' withheld: '{}' requires noctalia >= {} (running {})", sourceName, id, min,
                  noctalia::build_info::version()
              );
            });
            return;
          }
        }
      }

      // Apply: export every enabled plugin this source ships at the new revision,
      // then advance HEAD so catalog/hasPath reads follow. A failed export leaves
      // HEAD where it is; exported runtime files are re-derivable on the next run.
      for (const auto& id : enabled) {
        const auto sub = pluginSubdirFromId(id);
        if (!sub.has_value()) {
          continue;
        }
        if (!plugin_git::hasPath(repoRoot, *sub + "/plugin.toml", newRev)) {
          continue; // not shipped by this source
        }
        if (const auto m = materializeGitPlugin(source, repoRoot, newRev, id); !m) {
          DeferredCall::callLater([sourceName, id, err = m.error]() {
            kLog.warn("update '{}': export '{}' failed: {}", sourceName, id, err);
          });
          return;
        }
      }
      const auto applied = plugin_git::setHead(repoRoot, newRev);
      DeferredCall::callLater([this, sourceName, ok = static_cast<bool>(applied), err = applied.err, newRev]() {
        if (!ok) {
          kLog.warn("update '{}': set HEAD failed: {}", sourceName, err);
          return;
        }
        kLog.info("updated source '{}' -> {}", sourceName, newRev);
        PluginRegistry::instance().scan(); // re-parse manifests; live .luau changes hot-reload via file watch
        if (m_onChanged) {
          m_onChanged(); // rebuild bar + reconcile services for the new revision
        }
      });
    }).detach();
  }

  void PluginManager::removeSource(std::string sourceName) {
    const auto source = findSource(sourceName);
    if (!source.has_value()) {
      return;
    }
    kLog.info("removing plugin source '{}'", sourceName);
    std::optional<plugin_source_locks::SourceLock> sourceLock;
    if (source->kind == PluginSourceKind::Git) {
      sourceLock.emplace(plugin_source_locks::acquire(source->name));
    }

    // Disable this source's plugins so no stale enabled ids linger.
    for (const auto& entry : discoverCatalog(*source).entries) {
      m_config.setPluginEnabled(entry.id, false);
    }
    if (source->kind == PluginSourceKind::Git) {
      removeManagedGitSourceStorage(*source);
    }
    m_config.removePluginSource(sourceName); // fires reload -> refresh re-injects
  }

} // namespace scripting
