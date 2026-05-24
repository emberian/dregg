//! Rich embed builders for Discord messages.

use serenity::all::CreateEmbed;

/// Brand color for pyana embeds (a nice teal).
const PYANA_COLOR: u32 = 0x00B4D8;
/// Error color (red).
const ERROR_COLOR: u32 = 0xE63946;
/// Success color (green).
const SUCCESS_COLOR: u32 = 0x2A9D8F;
/// Warning color (amber).
const WARNING_COLOR: u32 = 0xE9C46A;

/// Create a standard pyana-branded embed.
pub fn pyana_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new().title(title).color(PYANA_COLOR).footer(
        serenity::all::CreateEmbedFooter::new("pyana devnet | fg-goose.online"),
    )
}

/// Create a success embed.
pub fn success_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new().title(title).color(SUCCESS_COLOR).footer(
        serenity::all::CreateEmbedFooter::new("pyana devnet | fg-goose.online"),
    )
}

/// Create an error embed.
pub fn error_embed(title: &str, description: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(description)
        .color(ERROR_COLOR)
}

/// Create a warning embed.
#[allow(dead_code)]
pub fn warning_embed(title: &str, description: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(description)
        .color(WARNING_COLOR)
}
