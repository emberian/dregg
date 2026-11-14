//! Offline physical compaction; this does not prune logical history.
use std::path::Path;

pub(crate) fn compact_store(data_dir: &Path) -> Result<bool, String> {
    let path = data_dir.join("dregg.redb");
    if !path.is_file() {
        return Err(format!("existing store required: {}", path.display()));
    }
    crate::install_verified_distributed_gates();
    crate::install_verified_pq_cores();
    let trust = crate::poa_compact_ceremony::load_runtime_poa_compact_policy_from_env(data_dir)?;
    // Opening redb takes the same exclusive file lock as the running node. Keep
    // that handle for the entire operation; never probe then reopen unlocked.
    let mut store = match trust {
        Some(trust) => {
            dregg_persist::PersistentStore::open_with_poa_compact_trust_v1(&path, trust.policy())
        }
        None => dregg_persist::PersistentStore::open(&path),
    }
    .map_err(|e| format!("cannot exclusively open store (stop the node first): {e}"))?;
    store.compact().map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn compact_command_does_not_boot_executor_or_network() {
        let dir = tempfile::tempdir().unwrap();
        drop(dregg_persist::PersistentStore::open(&dir.path().join("dregg.redb")).unwrap());
        // Two invocations in one process also catch accidental one-shot network
        // provider or tracing initialization on this offline path.
        for _ in 0..2 {
            crate::run(crate::Cli {
                command: crate::Command::Compact {
                    data_dir: dir.path().to_owned(),
                },
            })
            .await;
        }
    }

    #[test]
    fn operator_flags_are_explicit_and_legacy_pruning_stays_hidden() {
        use clap::{CommandFactory, Parser};
        let cli = crate::Cli::try_parse_from([
            "dregg-node",
            "run",
            "--force-prove-all",
            "--enable-pruning",
            "--blocklace-checkpoint-interval",
            "0",
        ])
        .unwrap();
        assert!(matches!(
            cli.command,
            crate::Command::Run {
                force_prove_all: true,
                enable_pruning: true,
                blocklace_checkpoint_interval: 0,
                ..
            }
        ));
        let mut command = crate::Cli::command();
        let help = command
            .find_subcommand_mut("run")
            .unwrap()
            .render_long_help()
            .to_string();
        let help = help.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(!help.contains("--enable-pruning"));
        assert!(help.contains("never gossips a checkpoint"));
        assert!(help.contains("--force-prove-all"));
        assert!(matches!(
            crate::Cli::try_parse_from(["dregg-node", "compact", "--data-dir", "example"])
                .unwrap()
                .command,
            crate::Command::Compact { .. }
        ));
    }

    #[test]
    fn compact_requires_existing_unlocked_store_and_preserves_data() {
        let dir = tempfile::tempdir().unwrap();
        assert!(compact_store(dir.path()).is_err());
        let path = dir.path().join("dregg.redb");
        assert!(!path.exists());
        let store = dregg_persist::PersistentStore::open(&path).unwrap();
        store.set_config("compact-test", b"retained").unwrap();
        assert!(
            compact_store(dir.path()).is_err(),
            "must refuse the live store lock"
        );
        drop(store);
        compact_store(dir.path()).unwrap();
        let store = dregg_persist::PersistentStore::open(&path).unwrap();
        assert_eq!(
            store.get_config("compact-test").unwrap().unwrap(),
            b"retained"
        );
    }
}
