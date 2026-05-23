pub mod cap;
pub mod cell;
pub mod directory;
pub mod doctor;
pub mod federation;
pub mod namespace;
pub mod node;
pub mod proof;
pub mod route;
pub mod storage;
pub mod turn;
pub mod wallet;

use crate::config::Config;

/// Build a reqwest client configured for the node.
pub fn http_client() -> reqwest::Client {
    reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(30))
        .build()
        .expect("failed to build HTTP client")
}

/// Construct a full URL for the node API.
pub fn api_url(cfg: &Config, path: &str) -> String {
    let base = cfg.node.url.trim_end_matches('/');
    format!("{base}{path}")
}

/// Convenience: GET request to the node, returning JSON value.
pub async fn get_json(
    cfg: &Config,
    path: &str,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let client = http_client();
    let url = api_url(cfg, path);
    let resp = client.get(&url).send().await?;
    if !resp.status().is_success() {
        let status = resp.status();
        let body = resp.text().await.unwrap_or_default();
        return Err(format!("HTTP {status}: {body}").into());
    }
    let json = resp.json::<serde_json::Value>().await?;
    Ok(json)
}

/// Convenience: POST request with JSON body.
pub async fn post_json(
    cfg: &Config,
    path: &str,
    body: &serde_json::Value,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let client = http_client();
    let url = api_url(cfg, path);
    let resp = client.post(&url).json(body).send().await?;
    if !resp.status().is_success() {
        let status = resp.status();
        let text = resp.text().await.unwrap_or_default();
        return Err(format!("HTTP {status}: {text}").into());
    }
    let json = resp.json::<serde_json::Value>().await?;
    Ok(json)
}
