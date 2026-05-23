//! Colored/formatted output helpers.
//!
//! Provides a unified `Context` that dispatches between colorized terminal
//! output, plain text, and JSON depending on user config.

use comfy_table::{Cell, CellAlignment, Color, ContentArrangement, Table};
use console::{Style, style};

use crate::config::Config;

/// Output mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Color,
    Plain,
    Json,
}

/// Output context -- knows how to format for the user's preference.
pub struct Context {
    pub mode: Mode,
}

impl Context {
    pub fn new(cfg: &Config) -> Self {
        let mode = match cfg.output.format.as_str() {
            "json" => Mode::Json,
            "plain" => Mode::Plain,
            _ => {
                if console::colors_enabled() {
                    Mode::Color
                } else {
                    Mode::Plain
                }
            }
        };
        Self { mode }
    }

    // ─── Structured messages ──────────────────────────────────────────────

    pub fn success(&self, msg: &str) {
        match self.mode {
            Mode::Color => eprintln!("{} {}", style("\u{2713}").green().bold(), msg),
            Mode::Plain => eprintln!("OK: {}", msg),
            Mode::Json => {} // JSON callers only care about stdout data
        }
    }

    pub fn error(&self, msg: &str) {
        match self.mode {
            Mode::Color => eprintln!("{} {}", style("\u{2717}").red().bold(), msg),
            Mode::Plain => eprintln!("ERROR: {}", msg),
            Mode::Json => {
                let j = serde_json::json!({"error": msg});
                println!("{}", serde_json::to_string_pretty(&j).unwrap());
            }
        }
    }

    pub fn warn(&self, msg: &str) {
        match self.mode {
            Mode::Color => eprintln!("{} {}", style("!").yellow().bold(), msg),
            Mode::Plain => eprintln!("WARN: {}", msg),
            Mode::Json => {}
        }
    }

    pub fn info(&self, msg: &str) {
        match self.mode {
            Mode::Color => eprintln!("{}", style(msg).dim()),
            Mode::Plain => eprintln!("{}", msg),
            Mode::Json => {}
        }
    }

    // ─── Headings and KV display ──────────────────────────────────────────

    pub fn header(&self, title: &str) {
        match self.mode {
            Mode::Color => {
                let bar = "\u{2500}".repeat(title.len() + 4);
                eprintln!("\u{256d}{}\u{256e}", bar);
                eprintln!("\u{2502} {} \u{2502}", style(title).bold().cyan());
                eprintln!("\u{2570}{}\u{256f}", bar);
            }
            Mode::Plain => {
                eprintln!("=== {} ===", title);
            }
            Mode::Json => {}
        }
    }

    pub fn kv(&self, key: &str, value: &str) {
        match self.mode {
            Mode::Color => {
                let label = Style::new().bold().apply_to(format!("{key}:"));
                eprintln!("  {:<16} {}", label, value);
            }
            Mode::Plain => {
                eprintln!("  {}: {}", key, value);
            }
            Mode::Json => {}
        }
    }

    pub fn kv_dim(&self, key: &str, value: &str) {
        match self.mode {
            Mode::Color => {
                let label = Style::new().dim().apply_to(format!("{key}:"));
                eprintln!("  {:<16} {}", label, style(value).dim());
            }
            Mode::Plain => {
                eprintln!("  {}: {}", key, value);
            }
            Mode::Json => {}
        }
    }

    // ─── Boxed output (cell inspect style) ────────────────────────────────

    pub fn boxed(&self, title: &str, rows: &[(&str, &str)]) {
        if self.mode == Mode::Json {
            return;
        }
        // Compute widths.
        let key_width = rows.iter().map(|(k, _)| k.len()).max().unwrap_or(10);
        let val_width = rows.iter().map(|(_, v)| v.len()).max().unwrap_or(20);
        let inner_width = (key_width + val_width + 3).max(title.len() + 2);

        let bar_top = "\u{2500}".repeat(inner_width + 2);
        let bar_mid = "\u{2500}".repeat(inner_width + 2);

        if self.mode == Mode::Color {
            eprintln!("\u{256d}{}\u{256e}", bar_top);
            eprintln!(
                "\u{2502} {:<width$} \u{2502}",
                style(title).bold().cyan(),
                width = inner_width
            );
            eprintln!("\u{251c}{}\u{2524}", bar_mid);
            for (k, v) in rows {
                eprintln!(
                    "\u{2502} {:<kw$}  {:<vw$} \u{2502}",
                    style(format!("{k}:")).bold(),
                    v,
                    kw = key_width + 1,
                    vw = inner_width - key_width - 3,
                );
            }
            eprintln!("\u{2570}{}\u{256f}", bar_top);
        } else {
            eprintln!("+{}+", "-".repeat(inner_width + 2));
            eprintln!("| {:<width$} |", title, width = inner_width);
            eprintln!("+{}+", "-".repeat(inner_width + 2));
            for (k, v) in rows {
                eprintln!(
                    "| {:<kw$}  {:<vw$} |",
                    format!("{k}:"),
                    v,
                    kw = key_width + 1,
                    vw = inner_width - key_width - 3
                );
            }
            eprintln!("+{}+", "-".repeat(inner_width + 2));
        }
    }

    // ─── Tree display (federation status style) ───────────────────────────

    pub fn tree(&self, root: &str, children: &[TreeNode]) {
        if self.mode == Mode::Json {
            return;
        }
        if self.mode == Mode::Color {
            eprintln!("{}", style(root).bold());
        } else {
            eprintln!("{}", root);
        }
        let len = children.len();
        for (i, child) in children.iter().enumerate() {
            let is_last = i == len - 1;
            let prefix = if is_last {
                "\u{2514}\u{2500}\u{2500}"
            } else {
                "\u{251c}\u{2500}\u{2500}"
            };
            let cont = if is_last { "   " } else { "\u{2502}  " };
            eprintln!("{} {}", prefix, child.label);
            for sub in &child.children {
                eprintln!("{}  \u{2514}\u{2500}\u{2500} {}", cont, sub.label);
            }
        }
    }

    // ─── Table output ─────────────────────────────────────────────────────

    pub fn table(&self, headers: &[&str], rows: &[Vec<String>]) {
        if self.mode == Mode::Json {
            return;
        }
        let mut table = Table::new();
        table.set_content_arrangement(ContentArrangement::Dynamic);

        let header_cells: Vec<Cell> = headers
            .iter()
            .map(|h| {
                Cell::new(h)
                    .set_alignment(CellAlignment::Left)
                    .fg(Color::Cyan)
            })
            .collect();
        table.set_header(header_cells);

        for row in rows {
            let cells: Vec<Cell> = row.iter().map(|c| Cell::new(c)).collect();
            table.add_row(cells);
        }

        eprintln!("{table}");
    }

    // ─── JSON output ──────────────────────────────────────────────────────

    #[allow(dead_code)]
    pub fn json(&self, value: &serde_json::Value) {
        if self.mode == Mode::Json {
            println!("{}", serde_json::to_string_pretty(value).unwrap());
        }
    }

    /// Print JSON to stdout regardless of mode (for data commands in json mode).
    pub fn json_stdout(&self, value: &serde_json::Value) {
        println!("{}", serde_json::to_string_pretty(value).unwrap());
    }

    // ─── Progress indicator ───────────────────────────────────────────────

    pub fn spinner(&self, msg: &str) -> indicatif::ProgressBar {
        if self.mode == Mode::Json || self.mode == Mode::Plain {
            return indicatif::ProgressBar::hidden();
        }
        let pb = indicatif::ProgressBar::new_spinner();
        pb.set_style(
            indicatif::ProgressStyle::with_template("{spinner:.cyan} {msg}")
                .unwrap()
                .tick_strings(&["\u{25d0}", "\u{25d1}", "\u{25d2}", "\u{25d3}", "\u{25cf}"]),
        );
        pb.set_message(msg.to_string());
        pb.enable_steady_tick(std::time::Duration::from_millis(120));
        pb
    }
}

/// A tree node for hierarchical output.
pub struct TreeNode {
    pub label: String,
    pub children: Vec<TreeNode>,
}

impl TreeNode {
    pub fn leaf(label: impl Into<String>) -> Self {
        Self {
            label: label.into(),
            children: vec![],
        }
    }

    pub fn branch(label: impl Into<String>, children: Vec<TreeNode>) -> Self {
        Self {
            label: label.into(),
            children,
        }
    }
}

/// Abbreviate a hex string: first 4 bytes...last 4 bytes.
pub fn abbrev_hex(hex: &str, prefix_len: usize, suffix_len: usize) -> String {
    if hex.len() <= prefix_len + suffix_len + 3 {
        return hex.to_string();
    }
    format!(
        "{}...{}",
        &hex[..prefix_len],
        &hex[hex.len() - suffix_len..]
    )
}

/// Format a large number with commas.
pub fn format_number(n: u64) -> String {
    let s = n.to_string();
    let mut result = String::new();
    for (i, c) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.push(',');
        }
        result.push(c);
    }
    result.chars().rev().collect()
}
