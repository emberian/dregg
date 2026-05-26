//! Configuration management for `~/.pyana/config.toml`.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    #[serde(default = "NodeConfig::default")]
    pub node: NodeConfig,
    #[serde(default = "OutputConfig::default")]
    pub output: OutputConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeConfig {
    #[serde(default = "default_node_url")]
    pub url: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    #[serde(default = "default_format")]
    pub format: String,
}

fn default_node_url() -> String {
    "http://localhost:8420".to_string()
}

fn default_format() -> String {
    "color".to_string()
}

impl Default for NodeConfig {
    fn default() -> Self {
        Self {
            url: default_node_url(),
        }
    }
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            format: default_format(),
        }
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            node: NodeConfig::default(),
            output: OutputConfig::default(),
        }
    }
}

/// Returns the default config path: `~/.pyana/config.toml`.
pub fn config_path() -> PathBuf {
    let base = dirs::home_dir().unwrap_or_else(|| PathBuf::from("."));
    base.join(".pyana").join("config.toml")
}

impl Config {
    /// Load config from the given path (or default). Missing file => defaults.
    ///
    /// On parse failure (corrupt or hand-edited TOML), logs a warning to stderr
    /// and falls back to safe built-in defaults rather than silently ignoring
    /// the user's settings. This closes a bad-UX gap where `pyana config set`
    /// or manual edits could be lost without any indication.
    pub fn load(path: Option<&str>) -> Self {
        let file_path = match path {
            Some(p) => PathBuf::from(p),
            None => config_path(),
        };

        if !file_path.exists() {
            return Config::default();
        }

        match std::fs::read_to_string(&file_path) {
            Ok(contents) => match toml::from_str(&contents) {
                Ok(cfg) => cfg,
                Err(e) => {
                    eprintln!(
                        "warning: failed to parse config file {}: {}. Using built-in defaults.",
                        file_path.display(),
                        e
                    );
                    Config::default()
                }
            },
            Err(e) => {
                if file_path.exists() {
                    eprintln!(
                        "warning: failed to read config file {}: {}. Using built-in defaults.",
                        file_path.display(),
                        e
                    );
                }
                Config::default()
            }
        }
    }

    /// Write the default config to the given path, creating parent dirs.
    pub fn write_default(path: &PathBuf) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let default = Config::default();
        let toml_str = toml::to_string_pretty(&default)?;
        std::fs::write(path, toml_str)?;
        Ok(())
    }

    /// Returns true if output format is JSON.
    pub fn is_json(&self) -> bool {
        self.output.format == "json"
    }
}

/// Set a dotted key in the config file. Creates the file if it doesn't exist.
pub fn set_value(key: &str, value: &str) -> Result<(), Box<dyn std::error::Error>> {
    let path = config_path();
    let mut cfg = Config::load(Some(path.to_str().unwrap_or("")));

    match key {
        "node.url" => cfg.node.url = value.to_string(),
        "output.format" => {
            if !["color", "plain", "json"].contains(&value) {
                return Err(format!("Invalid format '{}'. Use: color, plain, json", value).into());
            }
            cfg.output.format = value.to_string();
        }
        _ => {
            // Note: "cclerk.keyfile" was a legacy/dead setting (never loaded or used
            // by any CLI command; all cipherclerk ops proxy through the node). It is
            // no longer accepted to avoid user confusion.
            return Err(format!(
                "Unknown config key '{}'. Valid keys: node.url, output.format",
                key
            )
            .into());
        }
    }

    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let toml_str = toml::to_string_pretty(&cfg)?;
    std::fs::write(&path, toml_str)?;
    Ok(())
}
