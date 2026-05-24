//! Lint the JSON emitted by `gen_midnight` for structural well-formedness.
//!
//! Midnight ZKIR v3 is verified by an off-chain proof server we don't
//! bundle. To still get *some* value out of the gen_midnight backend in
//! this crate, we statically lint the emitted program: it must parse as
//! JSON, declare each pyana caveat parameter as an input wire, and
//! terminate with an `output` instruction.

use serde_json::Value;

/// Check the structure of the emitted ZKIR program. Returns `Ok(())` if
/// the JSON is valid and contains the expected instruction skeleton.
pub fn lint(zkir_json: &str, param_names: &[&str]) -> Result<(), String> {
    let v: Value =
        serde_json::from_str(zkir_json).map_err(|e| format!("ZKIR JSON does not parse: {e}"))?;

    let obj = v
        .as_object()
        .ok_or_else(|| "ZKIR root is not a JSON object".to_string())?;

    // version
    let version = obj
        .get("version")
        .ok_or_else(|| "ZKIR missing `version`".to_string())?;
    if !version.is_object() {
        return Err("ZKIR `version` is not an object".into());
    }

    // inputs — every param name must appear
    let inputs = obj
        .get("inputs")
        .and_then(Value::as_array)
        .ok_or_else(|| "ZKIR missing `inputs` array".to_string())?;
    for &param in param_names {
        let expected_wire = format!("%{param}");
        let found = inputs.iter().any(|input| {
            input
                .as_object()
                .and_then(|o| o.get("name"))
                .and_then(Value::as_str)
                .map(|n| n == expected_wire || n.starts_with(&expected_wire))
                .unwrap_or(false)
        });
        if !found {
            return Err(format!(
                "ZKIR `inputs` missing wire for param `{param}` (expected `{expected_wire}`)"
            ));
        }
    }

    // instructions — must have at least one, last one should be `output`
    let instructions = obj
        .get("instructions")
        .and_then(Value::as_array)
        .ok_or_else(|| "ZKIR missing `instructions` array".to_string())?;
    if instructions.is_empty() {
        return Err("ZKIR `instructions` is empty".into());
    }
    let last_op = instructions
        .last()
        .and_then(Value::as_object)
        .and_then(|o| o.get("op"))
        .and_then(Value::as_str);
    if last_op != Some("output") {
        return Err(format!(
            "ZKIR final instruction is not `output` (got {:?})",
            last_op
        ));
    }

    Ok(())
}
