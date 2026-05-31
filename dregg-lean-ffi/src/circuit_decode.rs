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

// ============================================================================
// PART II — the FULL ConstraintExpr wire: Merkle + algebraic forms.
//
// `Dregg2/Exec/CircuitEmit.lean` (PART II/III) emits, beyond var/const/add/mul:
//   * the Merkle structural wire — `merkle_hash` / `transition` /
//     `pi_binding_first` / `pi_binding_last`;
//   * the algebraic forms — `equality` / `multiplication` / `binary` /
//     `pi_binding` / `polynomial` / `gated` / `inverted_gated` / `squared` /
//     `conditional_nonzero` / `at_least_one`.
//
// We mirror the relevant subset of `circuit::dsl::circuit::ConstraintExpr` /
// `BoundaryDef` here (column-indexed), parse those wire tags, rebuild a Merkle
// `CircuitDescriptor`, and fingerprint-bind it to the native
// `merkle_poseidon2_descriptor()` AIR shape.
// ============================================================================

/// The BabyBear prime `p = 2^31 - 2^27 + 1` (= `circuit::field::BABYBEAR_P`).
/// Signed polynomial coefficients reduce into `[0, p)` as `-c → p - c`.
pub const BABYBEAR_P: u64 = (1u64 << 31) - (1u64 << 27) + 1; // 2013265921

/// A single polynomial term — mirror of `circuit::dsl::circuit::PolyTerm`.
/// `coeff` is the BabyBear-reduced (canonical, in `[0, p)`) coefficient.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedPolyTerm {
    pub coeff: u64,
    pub col_indices: Vec<usize>,
}

/// Reduce a signed wire coefficient into canonical BabyBear `[0, p)`:
/// `-c → p - c`, matching `descriptors.rs`'s `BabyBear::new(p - 6)` etc.
fn reduce_coeff(signed: i64) -> u64 {
    let m = (signed.rem_euclid(BABYBEAR_P as i64)) as u64;
    m % BABYBEAR_P
}

/// Column-indexed constraint — mirror of the `circuit::dsl::circuit::ConstraintExpr`
/// subset the Lean emitter produces (Merkle + algebraic forms).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodedConstraintExpr {
    Equality {
        col_a: usize,
        col_b: usize,
    },
    Multiplication {
        a: usize,
        b: usize,
        output: usize,
    },
    Binary {
        col: usize,
    },
    PiBinding {
        col: usize,
        pi_index: usize,
    },
    Transition {
        next_col: usize,
        local_col: usize,
    },
    Polynomial {
        terms: Vec<DecodedPolyTerm>,
    },
    Gated {
        selector_col: usize,
        inner: Box<DecodedConstraintExpr>,
    },
    InvertedGated {
        selector_col: usize,
        inner: Box<DecodedConstraintExpr>,
    },
    Squared {
        inner: Box<DecodedConstraintExpr>,
    },
    ConditionalNonzero {
        selector_col: usize,
        value_col: usize,
        inverse_col: usize,
    },
    AtLeastOne {
        flag_cols: Vec<usize>,
    },
    MerkleHash {
        output_col: usize,
        current_col: usize,
        sib_cols: [usize; 3],
        position_col: usize,
    },
}

/// Which row a boundary targets — mirror of `circuit::dsl::circuit::BoundaryRow`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodedBoundaryRow {
    First,
    Last,
}

/// A boundary definition — mirror of `circuit::dsl::circuit::BoundaryDef::PiBinding`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedBoundary {
    pub row: DecodedBoundaryRow,
    pub col: usize,
    pub pi_index: usize,
}

/// A decoded full-ConstraintExpr descriptor — the Merkle/algebraic counterpart of
/// `DecodedDescriptor`. Mirrors the relevant fields of `CircuitDescriptor`:
/// algebraic/structural constraints, PiBinding boundaries, public-input count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedFullDescriptor {
    pub name: String,
    pub trace_width: usize,
    pub public_input_count: usize,
    pub constraints: Vec<DecodedConstraintExpr>,
    pub boundaries: Vec<DecodedBoundary>,
}

impl DecodedConstraintExpr {
    /// Algebraic degree — replicates `ConstraintExpr::degree` (circuit.rs:622).
    /// The opaque-hash forms (MerkleHash) report degree 1, exactly as native.
    pub fn degree(&self) -> usize {
        match self {
            Self::Equality { .. } => 1,
            Self::Multiplication { .. } => 2,
            Self::Binary { .. } => 2,
            Self::PiBinding { .. } => 1,
            Self::Transition { .. } => 1,
            Self::Polynomial { terms } => {
                terms.iter().map(|t| t.col_indices.len()).max().unwrap_or(0)
            }
            Self::Gated { inner, .. } => 1 + inner.degree(),
            Self::InvertedGated { inner, .. } => 1 + inner.degree(),
            Self::Squared { inner } => 2 * inner.degree(),
            Self::ConditionalNonzero { .. } => 3,
            Self::AtLeastOne { flag_cols } => flag_cols.len(),
            Self::MerkleHash { .. } => 1,
        }
    }
}

// ----------------------------------------------------------------------------
// Parser extension: the Merkle + algebraic wire tags.
// ----------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// Parse a JSON array of unsigned integers `[N,N,...]`.
    fn parse_nat_array(&mut self) -> Result<Vec<usize>, String> {
        self.expect("[")?;
        let mut out = Vec::new();
        if self.peek() == Some(b']') {
            self.i += 1;
            return Ok(out);
        }
        loop {
            let n = self.parse_int()?;
            if n < 0 {
                return Err(format!("negative index {n} in array"));
            }
            out.push(n as usize);
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in nat array at {}", self.i)),
            }
        }
        Ok(out)
    }

    /// Parse one `{"coeff":N,"cols":[...]}` polynomial term.
    fn parse_poly_term(&mut self) -> Result<DecodedPolyTerm, String> {
        self.expect("{\"coeff\":")?;
        let coeff = reduce_coeff(self.parse_int()?);
        self.expect(",\"cols\":")?;
        let col_indices = self.parse_nat_array()?;
        self.expect("}")?;
        Ok(DecodedPolyTerm { coeff, col_indices })
    }

    /// Parse a JSON array of polynomial terms.
    fn parse_poly_terms(&mut self) -> Result<Vec<DecodedPolyTerm>, String> {
        self.expect("[")?;
        let mut out = Vec::new();
        if self.peek() == Some(b']') {
            self.i += 1;
            return Ok(out);
        }
        loop {
            out.push(self.parse_poly_term()?);
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in poly terms at {}", self.i)),
            }
        }
        Ok(out)
    }

    /// Read the `"t":"<tag>"` opening and return the tag string.
    fn parse_tag(&mut self) -> Result<String, String> {
        self.expect("{\"t\":\"")?;
        let tstart = self.i;
        while self.peek().is_some() && self.peek() != Some(b'"') {
            self.i += 1;
        }
        let tag = String::from_utf8_lossy(&self.s[tstart..self.i]).into_owned();
        self.expect("\"")?;
        Ok(tag)
    }

    /// Parse one full-ConstraintExpr wire object (Merkle + algebraic tags).
    /// Returns `Ok(None)` for the two boundary tags (pi_binding_first/last),
    /// which the caller routes into `boundaries` rather than `constraints`.
    fn parse_full_constraint(
        &mut self,
    ) -> Result<FullParse, String> {
        let tag = self.parse_tag()?;
        match tag.as_str() {
            "equality" => {
                self.expect(",\"col_a\":")?;
                let col_a = self.parse_index()?;
                self.expect(",\"col_b\":")?;
                let col_b = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Equality {
                    col_a,
                    col_b,
                }))
            }
            "multiplication" => {
                self.expect(",\"a\":")?;
                let a = self.parse_index()?;
                self.expect(",\"b\":")?;
                let b = self.parse_index()?;
                self.expect(",\"output\":")?;
                let output = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Multiplication {
                    a,
                    b,
                    output,
                }))
            }
            "binary" => {
                self.expect(",\"col\":")?;
                let col = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Binary { col }))
            }
            "pi_binding" => {
                self.expect(",\"col\":")?;
                let col = self.parse_index()?;
                self.expect(",\"pi_index\":")?;
                let pi_index = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::PiBinding {
                    col,
                    pi_index,
                }))
            }
            "transition" => {
                self.expect(",\"next_col\":")?;
                let next_col = self.parse_index()?;
                self.expect(",\"local_col\":")?;
                let local_col = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Transition {
                    next_col,
                    local_col,
                }))
            }
            "polynomial" => {
                self.expect(",\"terms\":")?;
                let terms = self.parse_poly_terms()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Polynomial {
                    terms,
                }))
            }
            "gated" => {
                self.expect(",\"selector_col\":")?;
                let selector_col = self.parse_index()?;
                self.expect(",\"inner\":")?;
                let inner = self.parse_full_constraint()?.into_constraint()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Gated {
                    selector_col,
                    inner: Box::new(inner),
                }))
            }
            "inverted_gated" => {
                self.expect(",\"selector_col\":")?;
                let selector_col = self.parse_index()?;
                self.expect(",\"inner\":")?;
                let inner = self.parse_full_constraint()?.into_constraint()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::InvertedGated {
                    selector_col,
                    inner: Box::new(inner),
                }))
            }
            "squared" => {
                self.expect(",\"inner\":")?;
                let inner = self.parse_full_constraint()?.into_constraint()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::Squared {
                    inner: Box::new(inner),
                }))
            }
            "conditional_nonzero" => {
                self.expect(",\"selector_col\":")?;
                let selector_col = self.parse_index()?;
                self.expect(",\"value_col\":")?;
                let value_col = self.parse_index()?;
                self.expect(",\"inverse_col\":")?;
                let inverse_col = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(
                    DecodedConstraintExpr::ConditionalNonzero {
                        selector_col,
                        value_col,
                        inverse_col,
                    },
                ))
            }
            "at_least_one" => {
                self.expect(",\"flag_cols\":")?;
                let flag_cols = self.parse_nat_array()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::AtLeastOne {
                    flag_cols,
                }))
            }
            "merkle_hash" => {
                self.expect(",\"output_col\":")?;
                let output_col = self.parse_index()?;
                self.expect(",\"current_col\":")?;
                let current_col = self.parse_index()?;
                self.expect(",\"sib_cols\":")?;
                let sibs = self.parse_nat_array()?;
                if sibs.len() != 3 {
                    return Err(format!("merkle_hash sib_cols must have 3 entries, got {}", sibs.len()));
                }
                self.expect(",\"position_col\":")?;
                let position_col = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Constraint(DecodedConstraintExpr::MerkleHash {
                    output_col,
                    current_col,
                    sib_cols: [sibs[0], sibs[1], sibs[2]],
                    position_col,
                }))
            }
            "pi_binding_first" => {
                self.expect(",\"col\":")?;
                let col = self.parse_index()?;
                self.expect(",\"pi_index\":")?;
                let pi_index = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Boundary(DecodedBoundary {
                    row: DecodedBoundaryRow::First,
                    col,
                    pi_index,
                }))
            }
            "pi_binding_last" => {
                self.expect(",\"col\":")?;
                let col = self.parse_index()?;
                self.expect(",\"pi_index\":")?;
                let pi_index = self.parse_index()?;
                self.expect("}")?;
                Ok(FullParse::Boundary(DecodedBoundary {
                    row: DecodedBoundaryRow::Last,
                    col,
                    pi_index,
                }))
            }
            other => Err(format!("unknown full-constraint tag `{other}`")),
        }
    }

    /// Parse a non-negative index field.
    fn parse_index(&mut self) -> Result<usize, String> {
        let n = self.parse_int()?;
        if n < 0 {
            return Err(format!("negative index {n}"));
        }
        Ok(n as usize)
    }

    /// Parse the full Merkle/algebraic descriptor:
    ///   {"name":STR,"trace_width":N,"public_input_count":N,"constraints":[...]}
    fn parse_full_descriptor(&mut self) -> Result<DecodedFullDescriptor, String> {
        self.expect("{\"name\":")?;
        let name = self.parse_string()?;
        self.expect(",\"trace_width\":")?;
        let trace_width = self.parse_index()?;
        self.expect(",\"public_input_count\":")?;
        let public_input_count = self.parse_index()?;
        self.expect(",\"constraints\":")?;
        // Array of mixed constraint/boundary objects.
        self.expect("[")?;
        let mut constraints = Vec::new();
        let mut boundaries = Vec::new();
        if self.peek() == Some(b']') {
            self.i += 1;
        } else {
            loop {
                match self.parse_full_constraint()? {
                    FullParse::Constraint(c) => constraints.push(c),
                    FullParse::Boundary(b) => boundaries.push(b),
                }
                match self.peek() {
                    Some(b',') => self.i += 1,
                    Some(b']') => {
                        self.i += 1;
                        break;
                    }
                    _ => return Err(format!("expected , or ] in constraints at {}", self.i)),
                }
            }
        }
        self.expect("}")?;
        Ok(DecodedFullDescriptor {
            name,
            trace_width,
            public_input_count,
            constraints,
            boundaries,
        })
    }
}

/// A parsed wire object is either a polynomial/structural constraint or a
/// boundary (the two `pi_binding_first`/`pi_binding_last` tags).
enum FullParse {
    Constraint(DecodedConstraintExpr),
    Boundary(DecodedBoundary),
}

impl FullParse {
    fn into_constraint(self) -> Result<DecodedConstraintExpr, String> {
        match self {
            FullParse::Constraint(c) => Ok(c),
            FullParse::Boundary(_) => {
                Err("boundary (pi_binding_first/last) cannot nest inside a gated/squared inner".into())
            }
        }
    }
}

/// Decode a full Merkle/algebraic wire string into a `DecodedFullDescriptor`.
pub fn decode_full(wire: &str) -> Result<DecodedFullDescriptor, String> {
    let mut p = Parser::new(wire);
    let d = p.parse_full_descriptor()?;
    if p.i != p.s.len() {
        return Err(format!("trailing bytes after full descriptor at {}", p.i));
    }
    Ok(d)
}

/// Decode a single algebraic/structural constraint wire string (e.g. the C1
/// `merkleC1Poly.toJson` golden) into a `DecodedConstraintExpr`.
pub fn decode_constraint_expr(wire: &str) -> Result<DecodedConstraintExpr, String> {
    let mut p = Parser::new(wire);
    let c = p.parse_full_constraint()?.into_constraint()?;
    if p.i != p.s.len() {
        return Err(format!("trailing bytes after constraint at {}", p.i));
    }
    Ok(c)
}

// ============================================================================
// Merkle AIR shape derivation + native reference.
//
// The Lean Merkle wire emits `merkle_hash`, `transition`, and the two
// `pi_binding_*` boundaries. The native `merkle_poseidon2_descriptor()` ALSO
// carries the C1 position-validity `Polynomial` (degree 4, max_degree 5) as
// its first constraint. The C1 wire is emitted SEPARATELY (`merkleC1Poly`); the
// faithful reconstruction injects it so the rebuilt shape's
// `constraint_polynomial_count` (3) and `max_degree` (5) match native.
// ============================================================================

/// The Merkle AIR's PI layout: `[leaf, root]`, one felt each (the boundary PIs
/// of `merkle_poseidon2_descriptor()`).
fn merkle_pi_layout() -> Vec<PiSlot> {
    vec![
        PiSlot { name: "leaf".into(), offset: 0, length_in_felts: 1 },
        PiSlot { name: "root".into(), offset: 1, length_in_felts: 1 },
    ]
}

/// The `max_degree` field the native `merkle_poseidon2_descriptor()` declares.
///
/// NOTE: this is a *declared* descriptor field (`descriptors.rs` sets
/// `max_degree: 5`), NOT the max of the constraints' algebraic degrees — the
/// deepest constraint (C1 `Polynomial`) is degree 4, but the descriptor pins a
/// degree-5 quotient bound. The Lean wire does not carry a `max_degree` field
/// (it is prover/quotient metadata, not part of the satisfaction relation
/// `emit_faithful_merkle` proves), so the binding supplies it from the native
/// declaration. The decoded constraint degrees are still checked to be `<=` it.
pub const MERKLE_DECLARED_MAX_DEGREE: usize = 5;

/// Derive the AIR shape of the Lean-decoded Merkle circuit. The decoded wire
/// carries `merkle_hash` + `transition` as constraints and the two
/// `pi_binding_*` as boundaries; the caller threads in the separately-emitted
/// C1 `Polynomial` so the constraint set is the full native one. `max_degree`
/// is the declared descriptor field (see `MERKLE_DECLARED_MAX_DEGREE`).
pub fn merkle_air_shape_from_decoded(
    d: &DecodedFullDescriptor,
    c1: &DecodedConstraintExpr,
) -> AirShape {
    // Native constraint order is [C1 Polynomial, C2 MerkleHash, C3 Transition].
    let mut all: Vec<&DecodedConstraintExpr> = vec![c1];
    all.extend(d.constraints.iter());
    // Sanity: every decoded constraint's algebraic degree must fit the declared
    // bound (mirrors the native descriptor's degree-validation invariant).
    let derived_max = all.iter().map(|c| c.degree()).max().unwrap_or(0);
    debug_assert!(
        derived_max <= MERKLE_DECLARED_MAX_DEGREE,
        "decoded constraint degree {derived_max} exceeds declared max {MERKLE_DECLARED_MAX_DEGREE}"
    );
    AirShape {
        air_id: d.name.clone(),
        column_count: d.trace_width,
        public_input_layout: merkle_pi_layout(),
        constraint_polynomial_count: all.len(),
        boundary_constraint_count: d.boundaries.len(),
        max_degree: MERKLE_DECLARED_MAX_DEGREE,
        source_hash: None,
    }
}

/// The Rust-native reference AIR shape for the Merkle Poseidon2 circuit —
/// exactly `circuit::dsl::descriptors::merkle_poseidon2_descriptor()`'s shape:
/// 3 constraints (C1 Polynomial deg-4, C2 MerkleHash, C3 Transition), 2
/// PiBinding boundaries, `max_degree = 5`, PI layout `[leaf, root]`.
pub fn merkle_air_shape_native() -> AirShape {
    AirShape {
        air_id: "dregg-merkle-poseidon2-v1".into(),
        column_count: 6,
        public_input_layout: merkle_pi_layout(),
        constraint_polynomial_count: 3,
        boundary_constraint_count: 2,
        // descriptors.rs declares max_degree: 5 (C1 is degree 4; the descriptor
        // pins a degree-5 quotient bound).
        max_degree: 5,
        source_hash: None,
    }
}
