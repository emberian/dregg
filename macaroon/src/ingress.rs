//! Operator HTTP attenuation. These tokens grant transport access, never signing authority.
use crate::{Macaroon, WireCaveat};

const KID: &[u8] = b"dregg-api-ingress-v1";
const AGENT: u16 = 80;
const EFFECT: u16 = 81;
const TOPIC: u16 = 82;
const EXPIRES: u16 = 83;

/// Mint only behind full operator authentication. Topic is the decoded 32-byte symbol.
pub fn mint(key: &[u8; 32], agent: [u8; 32], topic: [u8; 32], expires: u64) -> Macaroon {
    let mut m = Macaroon::new(key, KID.to_vec(), String::new());
    for (kind, body) in [
        (AGENT, agent.to_vec()),
        (EFFECT, b"EmitEvent".to_vec()),
        (TOPIC, topic.to_vec()),
        (EXPIRES, expires.to_le_bytes().to_vec()),
    ] {
        m.add_first_party_wire(WireCaveat::new(kind, body));
    }
    m
}

/// Authenticate and clear every caveat with AND semantics, including added restrictions.
/// Each effect supplies its target cell and event topic; non-event effects are `None`.
pub fn authorize(
    key: &[u8; 32],
    token: &str,
    agent: &[u8; 32],
    effects: &[Option<([u8; 32], [u8; 32])>],
    now: u64,
) -> Result<(), &'static str> {
    let m = Macaroon::decode(token).map_err(|_| "macaroon-format")?;
    let caveats = m.verify(key, &[]).map_err(|_| "macaroon-signature")?;
    if m.nonce.kid != KID {
        return Err("macaroon-purpose");
    }
    let mut seen = [false; 4];
    for c in caveats.iter() {
        let (slot, name, valid) = match c.caveat_type {
            AGENT => (
                0,
                "agent",
                c.body == agent
                    && effects
                        .iter()
                        .all(|e| e.as_ref().is_none_or(|(cell, _)| cell == agent)),
            ),
            EFFECT => (
                1,
                "effect",
                c.body == b"EmitEvent"
                    && !effects.is_empty()
                    && effects.iter().all(Option::is_some),
            ),
            TOPIC => (
                2,
                "topic",
                effects
                    .iter()
                    .all(|e| e.as_ref().is_some_and(|(_, topic)| c.body == topic)),
            ),
            EXPIRES => (
                3,
                "expires",
                <[u8; 8]>::try_from(c.body.as_slice()).is_ok_and(|b| now < u64::from_le_bytes(b)),
            ),
            _ => return Err("unknown-caveat"),
        };
        if !valid {
            return Err(name);
        }
        seen[slot] = true;
    }
    if !seen.into_iter().all(|x| x) {
        return Err("missing-caveat");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ingress_caveats_have_teeth() {
        let key = [1; 32];
        let agent = [2; 32];
        let topic = [3; 32];
        let m = mint(&key, agent, topic, 100);
        let token = m.encode().unwrap();
        let effects = [Some((agent, topic))];
        assert_eq!(authorize(&key, &token, &agent, &effects, 99), Ok(()));
        assert_eq!(
            authorize(&key, &token, &[4; 32], &effects, 99),
            Err("agent")
        );
        assert_eq!(authorize(&key, &token, &agent, &[None], 99), Err("effect"));
        assert_eq!(
            authorize(&key, &token, &agent, &[Some((agent, [4; 32]))], 99),
            Err("topic")
        );
        assert_eq!(
            authorize(&key, &token, &agent, &effects, 100),
            Err("expires")
        );
        assert_eq!(
            authorize(&[9; 32], &token, &agent, &effects, 99),
            Err("macaroon-signature")
        );
        let mut widened = m.clone();
        widened.caveats = crate::CaveatSet::new();
        assert_eq!(
            authorize(&key, &widened.encode().unwrap(), &agent, &effects, 99),
            Err("macaroon-signature")
        );
        let mut narrow = m.clone();
        narrow.add_first_party_wire(WireCaveat::new(TOPIC, vec![4; 32]));
        assert_eq!(
            authorize(&key, &narrow.encode().unwrap(), &agent, &effects, 99),
            Err("topic")
        );
        let mut extended = m.clone();
        extended.add_first_party_wire(WireCaveat::new(EXPIRES, u64::MAX.to_le_bytes().to_vec()));
        assert_eq!(
            authorize(&key, &extended.encode().unwrap(), &agent, &effects, 100),
            Err("expires")
        );
        let bare = Macaroon::new(&key, KID.to_vec(), String::new())
            .encode()
            .unwrap();
        assert_eq!(
            authorize(&key, &bare, &agent, &effects, 99),
            Err("missing-caveat")
        );
        let mut unknown = m.clone();
        unknown.add_first_party_wire(WireCaveat::new(90, vec![]));
        assert_eq!(
            authorize(&key, &unknown.encode().unwrap(), &agent, &effects, 99),
            Err("unknown-caveat")
        );
        let forged = mint(&[8; 32], agent, topic, 100).encode().unwrap();
        assert_eq!(
            authorize(&key, &forged, &agent, &effects, 99),
            Err("macaroon-signature")
        );
    }
}
