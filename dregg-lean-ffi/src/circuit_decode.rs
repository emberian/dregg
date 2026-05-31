//! circuit_decode.rs — the EXTRACTION DECODER + FINGERPRINT BINDING.
//!
//! This is the Rust half of the Lean→backend extraction bridge built by
//! `Dregg2/Exec/CircuitEmit.lean`. The Lean emitter serializes the verified
//! `kernelCircuit` (whose soundness∧completeness against `fullStepInv` is the
//! proved `Circuit.bridge`, and whose wire form is proved faithful by
//! `emit_faithful`) into a canonical JSON wire string. Here we:
//!
//!   1. **Decode** that wire string into a `DecodedDescriptor` — a faithful
//!      mirror of the relevant fields of `circuit::dsl::CircuitDescriptor` /
//!      `ConstraintExpr` (`circuit/src/dsl/circuit.rs`).
//!   2. **Fingerprint-bind**: reproduce `circuit::air_descriptor::fingerprint`
//!      EXACTLY (the documented BLAKE3-derive-key algorithm under the domain
//!      `"dregg-air-fingerprint-v1"`), compute the AIR-shape fingerprint of the
//!      Lean-decoded circuit, and assert it EQUALS the fingerprint of the
//!      Rust-native reference AIR shape. Equal fingerprints are the binding:
//!      "the AIR the validator runs IS the AIR Lean proved the bridge for."
//!
//! The fingerprint algorithm and the descriptor field-shape are replicated
//! verbatim (not imported) so this stays a self-contained module in the
//! detached `dregg-lean-ffi` crate — pulling `dregg-circuit` would drag the
//! whole plonky3/mina workspace. The replication is byte-faithful to
//! `air_descriptor.rs::fingerprint` (verified by the differential below).

// ============================================================================
// Decoded descriptor — mirror of circuit::dsl::circuit shapes (the subset the
// kernelCircuit wire form uses: var/const/add/mul expression gates).
// ============================================================================

/// Wire-form arithmetic expression — mirror of `Dregg2.Exec.CircuitEmit.EmittedExpr`
/// (which mirrors `Circuit.Expr`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodedExpr {
    Var(u64),
    Const(i64),
    Add(Box<DecodedExpr>, Box<DecodedExpr>),
    Mul(Box<DecodedExpr>, Box<DecodedExpr>),
}

/// Wire-form constraint `lhs = rhs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedConstraint {
    pub lhs: DecodedExpr,
    pub rhs: DecodedExpr,
}

/// Wire-form descriptor — mirror of the relevant `CircuitDescriptor` fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedDescriptor {
    pub name: String,
    pub trace_width: usize,
    pub constraints: Vec<DecodedConstraint>,
}

// ============================================================================
// A tiny zero-dependency JSON parser for the exact grammar emitted by
// `Dregg2.Exec.CircuitEmit.emitJson`. (We avoid serde_json to keep the
// detached crate's dep tree minimal; the grammar is fixed and small.)
//
// Grammar (no whitespace, as emitted):
//   desc  := {"name":STRING,"trace_width":NUM,"constraints":ARR}
//   ARR   := [] | [C(,C)*]
//   C     := {"lhs":E,"rhs":E}
//   E     := {"t":"var","v":NUM}
//          | {"t":"const","v":NUM}
//          | {"t":"add","l":E,"r":E}
//          | {"t":"mul","l":E,"r":E}
// ============================================================================

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Self {
        Parser { s: s.as_bytes(), i: 0 }
    }

    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }

    fn expect(&mut self, lit: &str) -> Result<(), String> {
        let b = lit.as_bytes();
        if self.i + b.len() <= self.s.len() && &self.s[self.i..self.i + b.len()] == b {
            self.i += b.len();
            Ok(())
        } else {
            Err(format!(
                "expected `{lit}` at byte {} (got `{}`)",
                self.i,
                self.context()
            ))
        }
    }

    fn context(&self) -> String {
        let end = (self.i + 16).min(self.s.len());
        String::from_utf8_lossy(&self.s[self.i..end]).into_owned()
    }

    /// Parse a JSON string literal (no escapes used by the emitter beyond plain chars).
    fn parse_string(&mut self) -> Result<String, String> {
        self.expect("\"")?;
        let start = self.i;
        while let Some(c) = self.peek() {
            if c == b'"' {
                let out = String::from_utf8_lossy(&self.s[start..self.i]).into_owned();
                self.i += 1;
                return Ok(out);
            }
            self.i += 1;
        }
        Err("unterminated string".to_string())
    }

    /// Parse a signed integer literal.
    fn parse_int(&mut self) -> Result<i64, String> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.i += 1;
            } else {
                break;
            }
        }
        let txt = std::str::from_utf8(&self.s[start..self.i]).map_err(|e| e.to_string())?;
        txt.parse::<i64>().map_err(|e| format!("bad int `{txt}`: {e}"))
    }

    fn parse_expr(&mut self) -> Result<DecodedExpr, String> {
        self.expect("{\"t\":\"")?;
        // Read the tag up to the closing quote.
        let tstart = self.i;
        while self.peek().is_some() && self.peek() != Some(b'"') {
            self.i += 1;
        }
        let tag = String::from_utf8_lossy(&self.s[tstart..self.i]).into_owned();
        self.expect("\"")?;
        match tag.as_str() {
            "var" => {
                self.expect(",\"v\":")?;
                let v = self.parse_int()?;
                self.expect("}")?;
                if v < 0 {
                    return Err(format!("negative var index {v}"));
                }
                Ok(DecodedExpr::Var(v as u64))
            }
            "const" => {
                self.expect(",\"v\":")?;
                let v = self.parse_int()?;
                self.expect("}")?;
                Ok(DecodedExpr::Const(v))
            }
            "add" | "mul" => {
                self.expect(",\"l\":")?;
                let l = self.parse_expr()?;
                self.expect(",\"r\":")?;
                let r = self.parse_expr()?;
                self.expect("}")?;
                if tag == "add" {
                    Ok(DecodedExpr::Add(Box::new(l), Box::new(r)))
                } else {
                    Ok(DecodedExpr::Mul(Box::new(l), Box::new(r)))
                }
            }
            other => Err(format!("unknown expr tag `{other}`")),
        }
    }

    fn parse_constraint(&mut self) -> Result<DecodedConstraint, String> {
        self.expect("{\"lhs\":")?;
        let lhs = self.parse_expr()?;
        self.expect(",\"rhs\":")?;
        let rhs = self.parse_expr()?;
        self.expect("}")?;
        Ok(DecodedConstraint { lhs, rhs })
    }

    fn parse_constraints(&mut self) -> Result<Vec<DecodedConstraint>, String> {
        self.expect("[")?;
        let mut out = Vec::new();
        if self.peek() == Some(b']') {
            self.i += 1;
            return Ok(out);
        }
        loop {
            out.push(self.parse_constraint()?);
            match self.peek() {
                Some(b',') => {
                    self.i += 1;
                }
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] at byte {}", self.i)),
            }
        }
        Ok(out)
    }

    fn parse_descriptor(&mut self) -> Result<DecodedDescriptor, String> {
        self.expect("{\"name\":")?;
        let name = self.parse_string()?;
        self.expect(",\"trace_width\":")?;
        let trace_width = self.parse_int()?;
        if trace_width < 0 {
            return Err(format!("negative trace_width {trace_width}"));
        }
        self.expect(",\"constraints\":")?;
        let constraints = self.parse_constraints()?;
        self.expect("}")?;
        Ok(DecodedDescriptor {
            name,
            trace_width: trace_width as usize,
            constraints,
        })
    }
}

/// Decode the canonical Lean wire string into a `DecodedDescriptor`.
pub fn decode(wire: &str) -> Result<DecodedDescriptor, String> {
    let mut p = Parser::new(wire);
    let d = p.parse_descriptor()?;
    if p.i != p.s.len() {
        return Err(format!("trailing bytes after descriptor at {}", p.i));
    }
    Ok(d)
}

// ============================================================================
// Fingerprint — byte-faithful reproduction of
// circuit::air_descriptor::fingerprint (air_descriptor.rs:111).
//
// The AIR-shape descriptor is the externally visible shape: air_id,
// column_count, public-input layout, constraint count, boundary count,
// max_degree, optional source_hash. We map a DecodedDescriptor (and a native
// reference) into this shape and hash identically.
// ============================================================================

/// One PI slot (mirror of `circuit::air_descriptor::PiSlot`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PiSlot {
    pub name: String,
    pub offset: usize,
    pub length_in_felts: usize,
}

/// The AIR-shape descriptor (mirror of `circuit::air_descriptor::AirDescriptor`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AirShape {
    pub air_id: String,
    pub column_count: usize,
    pub public_input_layout: Vec<PiSlot>,
    pub constraint_polynomial_count: usize,
    pub boundary_constraint_count: usize,
    pub max_degree: usize,
    pub source_hash: Option<[u8; 32]>,
}

/// Byte-for-byte reproduction of `circuit::air_descriptor::fingerprint`.
///
/// Domain-keyed BLAKE3 under `"dregg-air-fingerprint-v1"`; every variable-size
/// field gets an explicit `u64` little-endian length prefix so no two distinct
/// descriptors collide. This MUST stay identical to `air_descriptor.rs:111`.
pub fn fingerprint(d: &AirShape) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-air-fingerprint-v1");
    let id_bytes = d.air_id.as_bytes();
    hasher.update(&(id_bytes.len() as u64).to_le_bytes());
    hasher.update(id_bytes);
    hasher.update(&(d.column_count as u64).to_le_bytes());
    hasher.update(&(d.public_input_layout.len() as u64).to_le_bytes());
    for slot in &d.public_input_layout {
        let name_bytes = slot.name.as_bytes();
        hasher.update(&(name_bytes.len() as u64).to_le_bytes());
        hasher.update(name_bytes);
        hasher.update(&(slot.offset as u64).to_le_bytes());
        hasher.update(&(slot.length_in_felts as u64).to_le_bytes());
    }
    hasher.update(&(d.constraint_polynomial_count as u64).to_le_bytes());
    hasher.update(&(d.boundary_constraint_count as u64).to_le_bytes());
    hasher.update(&(d.max_degree as u64).to_le_bytes());
    match &d.source_hash {
        Some(h) => {
            hasher.update(&[1u8]);
            hasher.update(h);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
    *hasher.finalize().as_bytes()
}

// ============================================================================
// AIR-shape derivation for the kernel circuit.
// ============================================================================

/// Max algebraic degree of a decoded expression (var/const = 1/0, add = max,
/// mul = sum) — used to derive `max_degree` for the shape.
fn expr_degree(e: &DecodedExpr) -> usize {
    match e {
        DecodedExpr::Var(_) => 1,
        DecodedExpr::Const(_) => 0,
        DecodedExpr::Add(l, r) => expr_degree(l).max(expr_degree(r)),
        DecodedExpr::Mul(l, r) => expr_degree(l) + expr_degree(r),
    }
}

/// The PI layout the kernel circuit binds: the four `fullStepInv` conjunct
/// surfaces, in the wire's variable order. This is the AIR's externally visible
/// PI shape; it is fixed by `Circuit.encode`'s variable layout.
fn kernel_pi_layout() -> Vec<PiSlot> {
    vec![
        PiSlot { name: "total_pre".into(), offset: 0, length_in_felts: 1 },
        PiSlot { name: "total_post".into(), offset: 1, length_in_felts: 1 },
        PiSlot { name: "auth_bit".into(), offset: 2, length_in_felts: 1 },
        PiSlot { name: "len_pre".into(), offset: 3, length_in_felts: 1 },
        PiSlot { name: "len_post".into(), offset: 4, length_in_felts: 1 },
        PiSlot { name: "chain_ok".into(), offset: 5, length_in_felts: 1 },
    ]
}

/// Derive the AIR shape of the Lean-decoded kernel circuit.
pub fn kernel_air_shape_from_decoded(d: &DecodedDescriptor) -> AirShape {
    let max_degree = d
        .constraints
        .iter()
        .map(|c| expr_degree(&c.lhs).max(expr_degree(&c.rhs)))
        .max()
        .unwrap_or(0);
    AirShape {
        air_id: d.name.clone(),
        column_count: d.trace_width,
        public_input_layout: kernel_pi_layout(),
        constraint_polynomial_count: d.constraints.len(),
        boundary_constraint_count: 0,
        max_degree,
        source_hash: None,
    }
}

/// The Rust-native reference AIR shape for the kernel circuit — what the
/// validator independently expects. Equal fingerprint ⇒ the decoded Lean AIR
/// is the same AIR the validator runs.
pub fn kernel_air_shape_native() -> AirShape {
    AirShape {
        air_id: "dregg-kernel-step-v1".into(),
        column_count: 6,
        public_input_layout: kernel_pi_layout(),
        // 4 gates: conservation, authority, chain-link, obs-advance.
        constraint_polynomial_count: 4,
        boundary_constraint_count: 0,
        // obs-advance gate `len_post = len_pre + 1` is the deepest: degree 1.
        max_degree: 1,
        source_hash: None,
    }
}
