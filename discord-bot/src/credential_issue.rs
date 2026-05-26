//! Canonical Starbridge identity issuance helpers.

use dregg_app_framework::CellId;
use serde_json::Value;
use starbridge_identity::{
    AttrValue, CredentialAttributes, CredentialSchema, IssuerKeys, build_issue_credential_action,
    employment_schema, gov_id_schema, issue, kyc_schema,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::devnet::SubmitSignedTurnResult;

pub struct CredentialIssueResult {
    pub credential_id: String,
    pub schema: String,
    pub turn: SubmitSignedTurnResult,
}

pub async fn issue_from_discord_input(
    state: &BotState,
    user_id: u64,
    issuer_cell_hex: &str,
    schema_name: &str,
    attributes_json: &str,
) -> Result<CredentialIssueResult, String> {
    let issuer_cell = parse_cell_id(issuer_cell_hex)?;
    let schema = parse_schema_name(schema_name)
        .ok_or_else(|| format!("unknown credential schema `{schema_name}`"))?;
    let attributes = parse_attributes(&schema, attributes_json)?;
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let public_key = cclerk.app.public_key().0;
    let holder_id = *blake3::hash(&public_key).as_bytes();
    let issuer_keys = issuer_keys(state, user_id, &public_key);
    let issued_at = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let credential = issue(
        &issuer_keys,
        &schema,
        holder_id,
        attributes,
        issued_at,
        None,
    )
    .map_err(|e| format!("credential issuance failed: {e}"))?;
    let credential_id = hex::encode(credential.id());
    let action = build_issue_credential_action(&cclerk.app, issuer_cell, &credential, 1, [0u8; 32]);
    let turn = state
        .devnet
        .submit_app_action(
            &cclerk,
            action,
            Some(format!("discord:identity:issue:{}", schema.name)),
        )
        .await
        .map_err(|e| e.to_string())?;

    if !turn.accepted {
        return Err(turn
            .error
            .clone()
            .unwrap_or_else(|| "node rejected the signed credential turn".to_string()));
    }

    Ok(CredentialIssueResult {
        credential_id,
        schema: schema.name,
        turn,
    })
}

fn parse_schema_name(name: &str) -> Option<CredentialSchema> {
    match name.to_ascii_lowercase().as_str() {
        "kyc" | "kyc-v1" => Some(kyc_schema()),
        "gov_id" | "gov-id" | "gov-id-v1" => Some(gov_id_schema()),
        "employment" | "employment-v1" => Some(employment_schema()),
        _ => None,
    }
}

fn parse_attributes(
    schema: &CredentialSchema,
    attributes_json: &str,
) -> Result<CredentialAttributes, String> {
    let value: Value = serde_json::from_str(attributes_json)
        .map_err(|e| format!("attributes must be a JSON object: {e}"))?;
    let obj = value
        .as_object()
        .ok_or_else(|| "attributes must be a JSON object".to_string())?;
    let mut attrs = CredentialAttributes::new();
    for (name, value) in obj {
        if !schema.has_attribute(name) {
            return Err(format!(
                "attribute `{name}` is not in schema `{}`",
                schema.name
            ));
        }
        let attr = if let Some(u) = value.as_u64() {
            AttrValue::Integer(u)
        } else if let Some(i) = value.as_i64() {
            if i < 0 {
                return Err(format!("attribute `{name}` integer must be non-negative"));
            }
            AttrValue::Integer(i as u64)
        } else if let Some(b) = value.as_bool() {
            AttrValue::Bool(b)
        } else if let Some(s) = value.as_str() {
            AttrValue::Text(s.to_string())
        } else {
            return Err(format!(
                "attribute `{name}` must be a string, bool, or integer"
            ));
        };
        attrs = attrs.with(name.as_str(), attr);
    }
    Ok(attrs)
}

fn issuer_keys(state: &BotState, user_id: u64, public_key: &[u8; 32]) -> IssuerKeys {
    let mut input = Vec::with_capacity(32 + 8);
    input.extend_from_slice(&state.config.bot_secret);
    input.extend_from_slice(&user_id.to_le_bytes());
    IssuerKeys::new(
        blake3::derive_key("dregg-discord-identity-issuer-root-v1", &input),
        state.federation_id_bytes,
        public_key.to_vec(),
        format!("discord-app:{}", state.config.discord_app_id),
    )
}

fn parse_cell_id(value: &str) -> Result<CellId, String> {
    let bytes = hex::decode(value).map_err(|_| "cell id must be 64 hex chars".to_string())?;
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "cell id must decode to 32 bytes".to_string())?;
    Ok(CellId(bytes))
}
