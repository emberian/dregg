//! Offline physical compaction; no executor, network, schema migration or pruning.
use std::path::Path;

pub(crate) fn compact_store(data_dir: &Path) -> Result<bool, String> {
    dregg_persist::PersistentStore::compact_file(&data_dir.join("dregg.redb"))
        .map_err(|e| format!("cannot compact existing store (stop the node first): {e}"))
}

#[cfg(test)]
mod tests {
    use clap::{CommandFactory, Parser};

    #[test]
    fn proving_and_maintenance_flags_are_explicit() {
        let cli = crate::Cli::try_parse_from(["dregg-node", "run", "--force-prove-all"]).unwrap();
        assert!(matches!(
            cli.command,
            crate::Command::Run {
                force_prove_all: true,
                ..
            }
        ));
        assert!(crate::Cli::try_parse_from(["dregg-node", "run", "--enable-pruning"]).is_err());
        let mut command = crate::Cli::command();
        let help = command
            .find_subcommand_mut("run")
            .unwrap()
            .render_long_help()
            .to_string();
        assert!(!help.contains("--enable-pruning"));
        assert!(help.contains("--force-prove-all"));
        assert!(matches!(
            crate::Cli::try_parse_from(["dregg-node", "compact", "--data-dir", "example"])
                .unwrap()
                .command,
            crate::Command::Compact { .. }
        ));
    }

    #[tokio::test]
    async fn compact_command_does_not_boot_executor_or_network() {
        let dir = tempfile::tempdir().unwrap();
        drop(dregg_persist::PersistentStore::open(&dir.path().join("dregg.redb")).unwrap());
        for _ in 0..2 {
            crate::run(crate::Cli {
                command: crate::Command::Compact {
                    data_dir: dir.path().to_owned(),
                },
            })
            .await;
        }
    }
}
