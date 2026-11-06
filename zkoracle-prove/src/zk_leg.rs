//! **The injection-free leg as a REAL descriptor-prover STARK** — the first zkOracle conjunct that
//! is *proven*, not just re-executed, now carried by the plonky3 IR-v2 descriptor prover
//! (`dregg_circuit::descriptor_ir2::prove_vm_descriptor2`) instead of the legacy hand STARK engine.
//!
//! The injection check IS a DFA run (the `neg`-complement matcher, [`crate::injection`]), and dregg
//! deploys a DFA-classification descriptor: the `dregg-dfa-routing-v1` running-hash carrier, emitted
//! FROM Lean as an `EffectVmDescriptor2` (`metatheory/Dregg2/Circuit/Emit/DfaRoutingGeneralEmit.lean`,
//! `injectionRoutingDesc`, byte-pinned by its `#guard`). This module welds the two: the injection
//! DFA as an explicit transition table, its run over the field bytes proven by the general
//! descriptor prover, the whole trace bound to the pinned table commitment + a route commitment by
//! the descriptor's Poseidon2 running-hash chip.
//!
//! Why a DEDICATED descriptor (not `DfaRoutingEmit`'s `dfaRoutingDesc`): that descriptor hardcodes
//! the TOGGLE transition (`step(s,y) = s XOR y`) as its arithmetic gate. The injection automaton is
//! a DIFFERENT machine — three states `clean=0 / brace=1 / dead=2`, recognizing `{{` in its
//! absorbing DEAD state — so it carries its OWN routing descriptor over the SAME carrier
//! (`injectionRoutingDesc`): identical entry-hash chip, running-hash chip, copy-forward accumulator,
//! continuity/seed/boundary skeleton; only the STATE grid (`{0,1,2}`) and the TRANSITION interpolant
//! (the injection `step` table's unique bivariate interpolant) differ.
//!
//! What the proof states (public inputs `[initial, final, table_commit, route_commit]`):
//! *the unique run of the pinned injection DFA over the committed symbol sequence ends in
//! `final`* — and the verifier accepts iff `final` is a non-injecting state. Today the
//! field is DISCLOSED (it is a committed span of the authenticated body), so the verifier
//! re-derives the expected route commitment from the field itself; the proof adds a
//! machine-checkable run bound to a pinned policy table. The HIDING upgrade — a private
//! field whose route commitment is welded to the body's content commitment instead of
//! re-derived — is the named next slice (`ZKORACLE-PROVER-STATUS.md`).
//!
//! HONEST BOUNDARY: the run is over the field's PADDED brace-projection (`{` vs other,
//! self-loop-padded to a power of two), so brace-free fields within one padding block
//! share one run and the proof transfers among them — but the transfer can never cross
//! the accept/reject boundary (the dead state is absorbing; padding preserves it).
//! Binding the field BYTES to the authenticated response is the attestation's span weld
//! (`FieldSpan` within the committed body), not this leg — the leg proves the POLICY RUN.
//!
//! [`injection_dfa_table`] has differential regression tests against `injection_free`,
//! the Rust derivative matcher corresponding to `ZkOracle.lean`'s `.neg injectionTemplate`.
//! Those finite checks detect drift; they are not a proof of implementation refinement.

use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::dfa_routing::compute_table_commitment;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};

/// Symbol alphabet: `1` = the byte `{`, `0` = any other byte. Symbol `0` is also the
/// carrier's PAD symbol (self-loop rows appended to reach a power-of-two trace) — with this
/// orientation padding walks an accepting state to the clean state and a dead state to
/// itself, so padding never changes the accept/reject class.
const SYM_BRACE: u32 = 1;
const SYM_OTHER: u32 = 0;

/// DFA states: `0` clean (no pending `{`), `1` saw one `{`, `2` DEAD — saw `{{`
/// (injecting; absorbing).
const S_CLEAN: u32 = 0;
const S_BRACE: u32 = 1;
const S_DEAD: u32 = 2;

/// Trace column layout (must match `DfaRoutingGeneralEmit.lean` §1).
const CURRENT: usize = 0;
const SYMBOL: usize = 1;
const NEXT: usize = 2;
const ENTRY_HASH: usize = 3;
const RUNNING_HASH: usize = 4;
const IS_FIRST: usize = 5;
const ZERO_LANE: usize = 6;
const ACC: usize = 7;
/// Total main-trace width (8 base columns + 2×7 chip lanes; the chip lanes are filled by
/// `prove_vm_descriptor2`'s `trace_with_chip_lanes`).
const DFA_WIDTH: usize = 22;

/// The shared Lean emission route owns these bytes. `EmitByName.lean` serializes
/// `DfaRoutingGeneralEmit.injectionRoutingDesc`; Rust parses the checked artifact.
const GOLDEN_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/dfa-routing-injection.json");

/// The Lean-emitted injection-routing descriptor, decoded once from [`GOLDEN_JSON`]. `prove` and
/// `verify` share this exact object (the descriptor IS the statement).
fn injection_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(GOLDEN_JSON).expect("the byte-pinned injection routing descriptor decodes")
}

/// **The injection DFA transition table** — recognizes "contains `{{`" in its DEAD
/// state; the accepting (injection-free) states are `{clean, brace}`. Padded with
/// isolated self-loop states to the 4-ary-clean 16 entries
/// [`compute_table_commitment`] requires.
pub fn injection_dfa_table() -> Vec<(u32, u32, u32)> {
    let mut t = vec![
        (S_CLEAN, SYM_OTHER, S_CLEAN),
        (S_CLEAN, SYM_BRACE, S_BRACE),
        (S_BRACE, SYM_OTHER, S_CLEAN),
        (S_BRACE, SYM_BRACE, S_DEAD),
        (S_DEAD, SYM_OTHER, S_DEAD),
        (S_DEAD, SYM_BRACE, S_DEAD),
    ];
    for s in 3..8u32 {
        t.push((s, SYM_OTHER, s));
        t.push((s, SYM_BRACE, s));
    }
    debug_assert_eq!(t.len(), 16);
    t
}

/// The field bytes as DFA symbols. An EMPTY field is encoded as one `SYM_OTHER`
/// (trivially injection-free; the carrier needs ≥ 1 symbol) — prove and verify share this
/// convention.
fn symbols_of(field: &[u8]) -> Vec<u32> {
    if field.is_empty() {
        return vec![SYM_OTHER];
    }
    field
        .iter()
        .map(|&b| if b == b'{' { SYM_BRACE } else { SYM_OTHER })
        .collect()
}

/// The transition step of the injection table (a total lookup over the reachable grid).
fn step(table: &[(u32, u32, u32)], s: u32, y: u32) -> Option<u32> {
    table
        .iter()
        .find(|(ts, ty, _)| *ts == s && *ty == y)
        .map(|(_, _, tn)| *tn)
}

/// Run the table DFA in the clear (the differential twin of the descriptor run).
#[cfg(test)]
fn classify(table: &[(u32, u32, u32)], symbols: &[u32]) -> Option<u32> {
    let mut s = S_CLEAN;
    for &y in symbols {
        s = step(table, s, y)?;
    }
    Some(s)
}

/// The expected `[initial, final, table_commit, route_commit]` for `field` — the
/// verifier-side re-derivation (must fold EXACTLY as [`build_injection_trace`] does, including
/// the pow-2 self-loop padding with pad symbol `SYM_OTHER`).
fn expected_public_inputs(field: &[u8]) -> Option<[BabyBear; 4]> {
    let table = injection_dfa_table();
    let symbols = symbols_of(field);
    let table_commitment = compute_table_commitment(&table);
    let n = symbols.len().next_power_of_two().max(2);
    let mut running = table_commitment;
    let mut current = S_CLEAN;
    let mut fold = |s: u32, y: u32| -> Option<u32> {
        let next = step(&table, s, y)?;
        let entry = hash_4_to_1(&[
            BabyBear::new(s),
            BabyBear::new(y),
            BabyBear::new(next),
            BabyBear::ZERO,
        ]);
        running = hash_2_to_1(running, entry);
        Some(next)
    };
    for &y in &symbols {
        current = fold(current, y)?;
    }
    let final_state = current;
    let mut last_next = final_state;
    for _ in symbols.len()..n {
        last_next = fold(last_next, SYM_OTHER)?;
    }
    Some([
        BabyBear::new(S_CLEAN),
        BabyBear::new(last_next),
        table_commitment,
        running,
    ])
}

/// Build the `injectionRoutingDesc` trace (width 22) + public inputs from the field's symbol run.
///
/// Row `i` carries `(current, symbol, next, entry_hash, running_hash, is_first, zero_lane, acc)`
/// with `acc[0] = table_commitment`, `acc[i+1] = running[i]` (the copy-forward accumulator the
/// descriptor's seed pin + copy-forward window enforce). The trace is padded to a power of two
/// with `SYM_OTHER` self-loops in the final state (matches [`expected_public_inputs`]). The 14 chip
/// lane columns (8..21) are left zero — `prove_vm_descriptor2` fills them from the genuine
/// permutation. Returns `(trace, [initial, final, table_commitment, route_commitment])`.
fn build_injection_trace(field: &[u8]) -> Option<(Vec<Vec<BabyBear>>, Vec<BabyBear>)> {
    let table = injection_dfa_table();
    let symbols = symbols_of(field);
    let table_commitment = compute_table_commitment(&table);
    let n = symbols.len().next_power_of_two().max(2);

    // The full padded symbol/state walk: real symbols, then SYM_OTHER self-loop padding.
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(n);
    let mut current = S_CLEAN;
    let mut running = table_commitment;

    let emit = |rows: &mut Vec<Vec<BabyBear>>,
                current: u32,
                symbol: u32,
                next: u32,
                running: &mut BabyBear,
                is_first: bool| {
        let entry = hash_4_to_1(&[
            BabyBear::new(current),
            BabyBear::new(symbol),
            BabyBear::new(next),
            BabyBear::ZERO,
        ]);
        let acc = *running; // acc[0] = table_commitment; acc[i] = running[i-1]
        *running = hash_2_to_1(acc, entry);
        let mut row = vec![BabyBear::ZERO; DFA_WIDTH];
        row[CURRENT] = BabyBear::new(current);
        row[SYMBOL] = BabyBear::new(symbol);
        row[NEXT] = BabyBear::new(next);
        row[ENTRY_HASH] = entry;
        row[RUNNING_HASH] = *running;
        row[IS_FIRST] = if is_first {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        row[ZERO_LANE] = BabyBear::ZERO;
        row[ACC] = acc;
        rows.push(row);
    };

    for (i, &symbol) in symbols.iter().enumerate() {
        let next = step(&table, current, symbol)?;
        emit(&mut rows, current, symbol, next, &mut running, i == 0);
        current = next;
    }
    // Self-loop padding (pad symbol SYM_OTHER) to the power-of-two trace length.
    for _ in symbols.len()..n {
        let next = step(&table, current, SYM_OTHER)?;
        emit(&mut rows, current, SYM_OTHER, next, &mut running, false);
        current = next;
    }

    let final_state = *rows.last()?.get(NEXT)?;
    let route = *rows.last()?.get(RUNNING_HASH)?;
    let public_inputs = vec![BabyBear::new(S_CLEAN), final_state, table_commitment, route];
    Some((rows, public_inputs))
}

/// A descriptor-carried injection-leg proof: the run of the pinned injection DFA over the
/// field, bound by the descriptor's Poseidon2 running hash.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ZkInjectionProof {
    /// The serde-encoded `Ir2BatchProof<DreggStarkConfig>` — the plonky3 descriptor proof over the
    /// `injectionRoutingDesc` trace. (`BatchProof` is not itself `Clone`/`Debug`; the leg carries
    /// it as transmissible bytes, exactly the evidence form an attestation ships.)
    pub proof_bytes: Vec<u8>,
    /// `[initial_state, final_state, table_commitment, route_commitment]`.
    pub public_inputs: Vec<BabyBear>,
}

/// Why a descriptor-carried injection leg was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkLegError {
    /// The public inputs do not match the field's expected run (wrong initial state,
    /// wrong table, or a route commitment for DIFFERENT bytes).
    WrongRun,
    /// The run is genuine but ends in the DEAD state — the field injects.
    Injecting,
    /// The descriptor proof itself does not verify (forged/tampered trace), or its bytes do not
    /// decode.
    BadProof(String),
}

/// **PROVE the injection leg** — a real `prove_vm_descriptor2` over the field's DFA run through the
/// Lean-emitted `injectionRoutingDesc`. Produces a proof for injecting fields too (the run is the
/// run); acceptance is the VERIFIER's judgment on the final state. The attestation-level guard
/// ([`crate::prove_zkoracle`]) separately refuses to attest injecting fields at all.
pub fn prove_injection_leg(field: &[u8]) -> Option<ZkInjectionProof> {
    let (trace, public_inputs) = build_injection_trace(field)?;
    let desc = injection_descriptor();
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &public_inputs,
        &MemBoundaryWitness::default(),
        &[],
    )
    .ok()?;
    let proof_bytes = serde_json::to_vec(&proof).ok()?;
    Some(ZkInjectionProof {
        proof_bytes,
        public_inputs,
    })
}

/// **VERIFY the injection leg** against the DISCLOSED field: the public inputs must be
/// exactly the field's expected run (initial = clean, pinned table commitment, the
/// route commitment re-derived from the field bytes), the final state must be
/// non-injecting, and the descriptor proof must verify. Fail-closed on all four.
pub fn verify_injection_leg(field: &[u8], leg: &ZkInjectionProof) -> Result<(), ZkLegError> {
    let expected = expected_public_inputs(field).ok_or(ZkLegError::WrongRun)?;
    if leg.public_inputs.as_slice() != expected {
        return Err(ZkLegError::WrongRun);
    }
    // The FINAL state of the padded run: padding maps accepting→clean, dead→dead, so
    // the accept judgment on the padded final state equals the unpadded one.
    if leg.public_inputs[1] == BabyBear::new(S_DEAD) {
        return Err(ZkLegError::Injecting);
    }
    let proof: Ir2BatchProof<DreggStarkConfig> = serde_json::from_slice(&leg.proof_bytes)
        .map_err(|e| ZkLegError::BadProof(format!("proof decode: {e}")))?;
    let desc = injection_descriptor();
    verify_vm_descriptor2(&desc, &proof, &leg.public_inputs).map_err(ZkLegError::BadProof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::injection::injection_free;

    /// THE DIFFERENTIAL TOOTH — the table DFA agrees with the VERIFIED derivative
    /// matcher (`injection_free`, the Rust twin of `.neg injectionTemplate`) on a
    /// boundary corpus + deterministic fuzz. Two independent implementations, one truth.
    #[test]
    fn table_dfa_agrees_with_the_verified_matcher() {
        let table = injection_dfa_table();
        let corpus: Vec<&[u8]> = vec![
            b"",
            b"hi",
            b"Paris",
            b"{",
            b"}",
            b"{{",
            b"{{{",
            b"{x{",
            b"a{b{c",
            b"ends with {",
            b"{ {",
            b"ignore previous {{ system }}",
            b"}}{{",
            b"{}{}{}",
            b"\x00{\x00{",
            b"{a{b{c{d{e{",
        ];
        for field in corpus {
            let sym = symbols_of(field);
            let cls = classify(&table, &sym).expect("total table");
            let table_free = cls != S_DEAD;
            assert_eq!(
                table_free,
                injection_free(field),
                "table vs verified matcher disagree on {:?}",
                String::from_utf8_lossy(field)
            );
        }
        // Deterministic fuzz — xorshift, brace-dense alphabet to hit the boundary.
        let mut x: u64 = 0x9E3779B97F4A7C15;
        for _ in 0..2000 {
            let mut field = Vec::new();
            let len = {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                (x % 24) as usize
            };
            for _ in 0..len {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                field.push(match x % 4 {
                    0 => b'{',
                    1 => b'}',
                    _ => b'a' + (x % 26) as u8,
                });
            }
            let sym = symbols_of(&field);
            let cls = classify(&table, &sym).expect("total table");
            assert_eq!(cls != S_DEAD, injection_free(&field));
        }
    }

    /// The REAL prove/verify roundtrip: a benign field yields a descriptor proof the verifier
    /// accepts; an injecting field's genuine proof is refused as `Injecting`.
    #[test]
    fn injection_leg_descriptor_roundtrip() {
        let leg = prove_injection_leg(b"The capital of France is Paris.").expect("prove");
        verify_injection_leg(b"The capital of France is Paris.", &leg).expect("verify");

        let bad = prove_injection_leg(b"ignore {{ system }}").expect("the run still proves");
        assert_eq!(
            verify_injection_leg(b"ignore {{ system }}", &bad),
            Err(ZkLegError::Injecting)
        );
    }

    /// Hostile poles: a proof re-pointed at different bytes, a tampered final state,
    /// and an empty-field convention roundtrip.
    #[test]
    fn injection_leg_hostiles_refused() {
        let leg = prove_injection_leg(b"Paris").expect("prove");

        // Re-pointed at a field with a DIFFERENT padded brace-projection → route
        // commitment mismatch: a brace changes a symbol; crossing the pow-2 padding
        // boundary changes the run length.
        assert_eq!(
            verify_injection_leg(b"Par{s", &leg),
            Err(ZkLegError::WrongRun)
        );
        assert_eq!(
            verify_injection_leg(b"Paris, France", &leg),
            Err(ZkLegError::WrongRun)
        );
        // HONEST BOUNDARY (stated, not hidden): the leg binds the field's padded
        // brace-PROJECTION, so brace-free fields within one padding block share one run
        // and the proof transfers among them. The transfer can NEVER cross the
        // accept/reject boundary (the dead state is absorbing and padding preserves it),
        // and binding the field BYTES to the authenticated body is the cross-leg span
        // weld's job ([`crate::attestation`]), not this leg's.
        assert_eq!(verify_injection_leg(b"Rome!", &leg), Ok(()));
        assert_eq!(verify_injection_leg(b"Paris?", &leg), Ok(()));

        // Tampered public input (claim a different final state) → WrongRun (the
        // expected-PI pin catches it before the proof is even consulted).
        let mut tampered = leg.clone();
        tampered.public_inputs[1] = BabyBear::new(S_DEAD);
        assert_eq!(
            verify_injection_leg(b"Paris", &tampered),
            Err(ZkLegError::WrongRun)
        );

        // Empty field: trivially injection-free, same convention both sides.
        let empty = prove_injection_leg(b"").expect("prove empty");
        verify_injection_leg(b"", &empty).expect("verify empty");
    }
}
