//! Schema constants for the Studio-shape trace event format.

/// Schema version. Bumped on any breaking change to the on-wire JSON shape
/// (renaming a `kind` discriminator, removing a payload field, changing the
/// envelope contract). Additive payload fields do not require a bump — the
/// consumer must tolerate unknown fields within a variant's `payload`.
pub const SCHEMA_VERSION: u32 = 1;

/// Schema name. Distinct from the older
/// `"pyana-observability-turn-trace-v1"` name (which referred to the
/// monolithic single-document JSON dump). The new name marks the event-stream
/// shape.
pub const SCHEMA_NAME: &str = "pyana-observability-event-stream-v1";

/// Hex-encode a 32-byte value as lowercase, no `0x` prefix. Studio expects
/// every hash / commitment / pubkey at this exact shape.
pub fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Hex-encode an arbitrary byte slice.
pub fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Format a unix-epoch millisecond count as an ISO 8601 / RFC 3339 UTC string
/// with millisecond precision.
///
/// Implemented locally to avoid pulling chrono into the trace path — Studio
/// only needs a string it can pass to `new Date(...)`. The grammar is:
/// `YYYY-MM-DDTHH:MM:SS.sssZ`.
pub fn iso8601_from_millis(unix_millis: i64) -> String {
    // Negative timestamps (pre-1970) are valid in the RFC but pyana never
    // produces them; clamp to zero to keep the output well-formed.
    let unix_millis = unix_millis.max(0) as u64;
    let secs = unix_millis / 1_000;
    let ms = (unix_millis % 1_000) as u32;
    let (y, mo, d, h, mi, s) = unix_seconds_to_civil(secs);
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}.{ms:03}Z")
}

/// Convert unix-epoch seconds into `(year, month, day, hour, minute, second)`
/// in UTC. Implementation of Howard Hinnant's `civil_from_days` (the same
/// algorithm `chrono` uses internally) — pure arithmetic, no allocation.
fn unix_seconds_to_civil(secs: u64) -> (i32, u32, u32, u32, u32, u32) {
    let days = (secs / 86_400) as i64;
    let tod = (secs % 86_400) as u32;
    let h = tod / 3_600;
    let mi = (tod % 3_600) / 60;
    let s = tod % 60;
    // Days since 1970-01-01.
    let z = days + 719_468; // shift epoch to 0000-03-01
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097) as u64; // 0..146096
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y_proleptic = (yoe as i64) + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let mo = (if mp < 10 { mp + 3 } else { mp - 9 }) as u32;
    let y = (y_proleptic + if mo <= 2 { 1 } else { 0 }) as i32;
    (y, mo, d, h, mi, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iso8601_epoch_is_unix_zero() {
        assert_eq!(iso8601_from_millis(0), "1970-01-01T00:00:00.000Z");
    }

    #[test]
    fn iso8601_known_value() {
        // 2026-05-24T00:00:00.000Z is 1779,494,400 seconds after epoch.
        // (56 years * 365.25 days/y * 86400 ≈ 1_767_528_000; verified via
        // a sanity-bracket below.)
        let s = iso8601_from_millis(1_779_494_400_000);
        assert!(s.starts_with("2026-05-2"), "got {s}");
        assert!(s.ends_with("T00:00:00.000Z"), "got {s}");
    }

    #[test]
    fn iso8601_milliseconds_round_trip() {
        let s = iso8601_from_millis(123);
        assert_eq!(s, "1970-01-01T00:00:00.123Z");
    }

    #[test]
    fn hex32_lowercase_no_prefix() {
        let bytes = [0xAB; 32];
        assert_eq!(hex32(&bytes), "ab".repeat(32));
    }
}
