//! Witness construction for `RouteChain8.lean`; this module defines no AIR constraints.
//! The one-based counter and eight-lane route agree with the emitted descriptor.
use crate::{descriptor_ir2::chip_absorb_all_lanes, field::BabyBear};

pub const FIELD_MODULUS: usize = 2_013_265_921;
pub const TABLE_ROUTE_DOMAIN: u32 = 1_414_677_048;

#[derive(Clone, Copy, Debug)]
pub struct Route8Config {
    pub base_width: usize,
    pub base_pi_count: usize,
    pub current: usize,
    pub symbol: usize,
    pub next: usize,
    pub domain: u32,
}

pub const TABLE_ROUTE_CONFIG: Route8Config = Route8Config {
    base_width: 3,
    base_pi_count: 2,
    current: 0,
    symbol: 1,
    next: 2,
    domain: TABLE_ROUTE_DOMAIN,
};

/// Admission is factored so the no-wrap boundary can be checked without allocating p rows.
pub fn admit_route8_length(rows: usize, public_length: usize) -> Result<(), String> {
    if rows == 0 || rows >= FIELD_MODULUS {
        return Err("route8 requires 0 < trace rows < BabyBear modulus".into());
    }
    if public_length != rows {
        return Err("route8 public length does not equal actual trace height".into());
    }
    Ok(())
}

/// Append predecessor8/output8/position to each row, route8/length to public inputs.
/// The caller supplies the zero seed for a public table or the authenticated root8 for a weld.
/// This initial shape has no inactive padding rows and requires a power-of-two height.
/// Validate every shape before modifying any input.
pub fn extend_route8(
    trace: &mut [Vec<BabyBear>],
    pis: &mut Vec<BabyBear>,
    cfg: Route8Config,
    seed: [BabyBear; 8],
) -> Result<(), String> {
    admit_route8_length(trace.len(), trace.len())?;
    if !trace.len().is_power_of_two() {
        return Err("route8 requires a power-of-two trace height; padding is not encoded".into());
    }
    if cfg.domain as usize >= FIELD_MODULUS
        || [cfg.current, cfg.symbol, cfg.next]
            .iter()
            .any(|&c| c >= cfg.base_width)
        || trace.iter().any(|r| r.len() != cfg.base_width)
        || pis.len() != cfg.base_pi_count
    {
        return Err("route8 base witness/configuration shape mismatch".into());
    }
    let mut previous = seed;
    for (i, row) in trace.iter_mut().enumerate() {
        let position = BabyBear::new((i + 1) as u32);
        let mut input = vec![
            BabyBear::new(cfg.domain),
            position,
            row[cfg.current],
            row[cfg.symbol],
            row[cfg.next],
        ];
        input.extend(previous);
        input.extend([BabyBear::new(0); 3]);
        let output = chip_absorb_all_lanes(16, &input);
        row.extend(previous);
        row.extend(output);
        row.push(position);
        previous = output;
    }
    pis.extend(previous);
    pis.push(BabyBear::new(trace.len() as u32));
    Ok(())
}

/// The main instance is first in the emitted IR2 assembly. Bind its proof-carried
/// height to the public counter before constructing verifier domains.
pub fn admit_route8_degree(degree_bits: usize, public_length: usize) -> Result<(), String> {
    let shift = u32::try_from(degree_bits).map_err(|_| "route8 degree does not fit u32")?;
    let rows = 1usize
        .checked_shl(shift)
        .ok_or("route8 degree overflows host height")?;
    admit_route8_length(rows, public_length)
}

/// Public-input route verifier: enforce actual proof height = public length and no
/// BabyBear counter wrap, then invoke the ordinary descriptor verifier. Policy/table
/// identity remains the caller's selected descriptor, whose bytes are verifier-bound.
pub fn verify_route8(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    proof: &p3_batch_stark::BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    pis: &[BabyBear],
    cfg: Route8Config,
) -> Result<(), String> {
    if desc.trace_width != cfg.base_width + 17
        || desc.public_input_count != cfg.base_pi_count + 9
        || pis.len() != desc.public_input_count
    {
        return Err("route8 verifier shape mismatch".into());
    }
    let degree = *proof
        .degree_bits
        .first()
        .ok_or("route8 proof has no main instance")?;
    admit_route8_degree(degree, pis[cfg.base_pi_count + 8].canonical_val() as usize)?;
    crate::descriptor_ir2::verify_vm_descriptor2(desc, proof, pis)
}

/// Compute the ordered opening of an actual external record under the selected policy.
/// The step function must use that policy's transition table; errors refuse unknown
/// symbols/states. This initial descriptor shape requires a power-of-two record length.
pub fn route8_for_record(
    cfg: Route8Config,
    seed: [BabyBear; 8],
    initial: BabyBear,
    record: &[BabyBear],
    step: impl Fn(BabyBear, BabyBear) -> Result<BabyBear, String>,
) -> Result<(BabyBear, [BabyBear; 8]), String> {
    admit_route8_length(record.len(), record.len())?;
    if !record.len().is_power_of_two() || cfg.domain as usize >= FIELD_MODULUS {
        return Err("route8 record requires a power-of-two length and canonical domain".into());
    }
    let mut state = initial;
    let mut previous = seed;
    for (i, &symbol) in record.iter().enumerate() {
        let next = step(state, symbol)?;
        let mut input = vec![
            BabyBear::new(cfg.domain),
            BabyBear::new((i + 1) as u32),
            state,
            symbol,
            next,
        ];
        input.extend(previous);
        input.extend([BabyBear::new(0); 3]);
        previous = chip_absorb_all_lanes(16, &input);
        state = next;
    }
    Ok((state, previous))
}

/// Verify this proof and these public inputs for an explicit external record.
/// Recompute the deterministic run under the caller-selected policy and compare
/// its initial/final state, all eight route lanes, and length before STARK verification.
/// A different record cannot be substituted while retaining the same proof/PIs.
pub fn verify_route8_record(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    proof: &p3_batch_stark::BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    pis: &[BabyBear],
    cfg: Route8Config,
    seed: [BabyBear; 8],
    initial: BabyBear,
    record: &[BabyBear],
    step: impl Fn(BabyBear, BabyBear) -> Result<BabyBear, String>,
) -> Result<(), String> {
    if cfg.base_pi_count < 2 || cfg.base_pi_count.checked_add(9) != Some(pis.len()) {
        return Err("route8 record public-input shape mismatch".into());
    }
    admit_route8_length(
        record.len(),
        pis[cfg.base_pi_count + 8].canonical_val() as usize,
    )?;
    if pis[0] != initial {
        return Err("route8 record initial state differs from public input".into());
    }
    let (final_state, route) = route8_for_record(cfg, seed, initial, record, step)?;
    if pis[1] != final_state || pis[cfg.base_pi_count..cfg.base_pi_count + 8] != route {
        return Err("route8 record endpoint or ordered route differs from public input".into());
    }
    verify_route8(desc, proof, pis, cfg)
}
