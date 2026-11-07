//! Checked finite-logic front end for the live descriptor IR-v2 relation.
//!
//! The source fragment is deliberately finite and executable.  Inputs and
//! bound variables range over `Bool` or a declared finite enumeration, terms
//! are variables/constants, and formulae contain equality, truth-table
//! predicates, Boolean connectives, and bounded quantifiers.
//!
//! # The compiler is Lean
//!
//! This module authors no constraint.  [`compile_logic_program`] serializes the
//! program to its canonical source bytes, sends them to the Lean compiler
//! `Dregg2.Logic.DirectLogicProgramIR2.compileBytes` (the `direct_logic_compile`
//! executable, root `metatheory/DirectLogicCompile.lean`), and parses the reply:
//! the descriptor is Lean's `emitVmJson2` bytes, the formula relation is Lean's
//! grounded Boolean source, and the input layout is Lean's.  Quantifier
//! expansion, one-hot enumeration gates, the width-at-least-one padding column
//! and the `dregg-direct-logic-v1-<BLAKE3 of source bytes>` name are all Lean
//! definitions; `program_sound` / `program_complete` are about exactly that
//! descriptor, and `compileBytes_spec` ties it to the bytes this module sent.
//!
//! What stays here is transport and checking: the source encoding (which Lean
//! decodes canonically and re-encodes, so a drift is a refusal), the reply
//! parser, consistency checks of the reply against the request (source hash,
//! name, width, layout), the transparent reference evaluator, and the
//! one-row witness encoder.
//!
//! # Locating the compiler
//!
//! [`LeanExeCompiler::locate`] uses `DREGG_DIRECT_LOGIC_COMPILER` (an executable
//! path) or else the in-tree build `metatheory/.lake/build/bin/direct_logic_compile`
//! (`cd metatheory && lake build direct_logic_compile`).  There is no Rust
//! fallback compiler: without the executable, compilation fails with
//! [`FrontendError::CompilerUnavailable`].  [`RecordedCompiler`] replays replies
//! the executable produced earlier (the test corpus), byte for byte.

use std::collections::BTreeMap;
use std::fmt;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use crate::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use crate::field::BabyBear;

/// Wire tag of a compile request (Lean `requestTag`).
pub const DIRECT_LOGIC_REQUEST_TAG: &str = "DIRECT-LOGIC-COMPILE-1";
/// Wire tag of a compile reply (Lean `replyTag`).
pub const DIRECT_LOGIC_REPLY_TAG: &str = "DIRECT-LOGIC-COMPILED-1";
/// Environment variable naming the compiler executable.
pub const DIRECT_LOGIC_COMPILER_ENV: &str = "DREGG_DIRECT_LOGIC_COMPILER";

/// Version of the source encoding, compiler rules, and portable artifact.
pub const DIRECT_LOGIC_FRONTEND_VERSION: u32 = 1;

/// A source type.  `UnboundedInteger` is representable so adapters can fail
/// closed instead of silently truncating an unbounded source domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicType {
    Bool,
    Finite { cardinality: usize },
    UnboundedInteger,
}

impl LogicType {
    fn cardinality(&self) -> Result<usize, FrontendError> {
        match self {
            Self::Bool => Ok(2),
            Self::Finite { cardinality: 0 } => Err(FrontendError::EmptyFiniteDomain),
            Self::Finite { cardinality } => Ok(*cardinality),
            Self::UnboundedInteger => Err(FrontendError::UnboundedDomain),
        }
    }
}

/// A named free input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputDecl {
    pub name: String,
    pub ty: LogicType,
}

/// A finite term.  Bound variables use de Bruijn indices (`0` is innermost).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Input(usize),
    Bound(usize),
    Constant { ty: LogicType, value: usize },
}

/// An explicit finite predicate table.  Entries are row-major in argument
/// order: `index = (((a0 * |A1|) + a1) * |A2| + a2) ...`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateTable {
    pub name: String,
    pub argument_types: Vec<LogicType>,
    pub values: Vec<bool>,
}

/// Checked bounded first-order formula syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    Top,
    Bottom,
    Equal(Term, Term),
    Predicate {
        table: PredicateTable,
        arguments: Vec<Term>,
    },
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    ForAll {
        binder: LogicType,
        body: Box<Formula>,
    },
    Exists {
        binder: LogicType,
        body: Box<Formula>,
    },
}

/// A complete finite-logic compilation unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogicProgram {
    pub inputs: Vec<InputDecl>,
    pub formula: Formula,
}

/// Concrete source values used by the reference evaluator and atom encoder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicValue {
    Bool(bool),
    Finite(usize),
}

/// Explicit resource limits.  No truncation, early-exit witness, or implicit
/// widening occurs when a limit is exceeded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompileLimits {
    pub maximum_source_nodes: usize,
    pub maximum_atoms: usize,
    pub maximum_predicate_entries: usize,
    pub maximum_quantifier_instances: usize,
    pub maximum_expanded_nodes: usize,
}

impl Default for CompileLimits {
    fn default() -> Self {
        Self {
            maximum_source_nodes: 2_048,
            maximum_atoms: 4_096,
            maximum_predicate_entries: 65_536,
            maximum_quantifier_instances: 65_536,
            maximum_expanded_nodes: 250_000,
        }
    }
}

/// A source input's exact trace-column encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputEncoding {
    pub name: String,
    pub ty: LogicType,
    pub first_atom: usize,
    pub atom_count: usize,
}

/// The Boolean graph retained beside the descriptor for transparent
/// differential evaluation.  Truth is represented by `true`/field one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoolExpr {
    Atom(usize),
    Constant(bool),
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
}

impl BoolExpr {
    pub fn evaluate(&self, atoms: &[bool]) -> Result<bool, FrontendError> {
        match self {
            Self::Atom(index) => {
                atoms
                    .get(*index)
                    .copied()
                    .ok_or(FrontendError::AtomVectorTooShort {
                        required: index.saturating_add(1),
                        actual: atoms.len(),
                    })
            }
            Self::Constant(value) => Ok(*value),
            Self::Not(value) => Ok(!value.evaluate(atoms)?),
            Self::And(left, right) => Ok(left.evaluate(atoms)? && right.evaluate(atoms)?),
            Self::Or(left, right) => Ok(left.evaluate(atoms)? || right.evaluate(atoms)?),
        }
    }

    /// Node count of the relation graph (Lean `sourceSize`).
    pub fn node_count(&self) -> usize {
        match self {
            Self::Atom(_) | Self::Constant(_) => 1,
            Self::Not(value) => 1 + value.node_count(),
            Self::And(left, right) | Self::Or(left, right) => {
                1 + left.node_count() + right.node_count()
            }
        }
    }
}

/// A checked portable artifact.  The wire image is canonical for compiler
/// version 1 and its digest is over those exact UTF-8 bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledLogicArtifact {
    descriptor: EffectVmDescriptor2,
    descriptor_json: String,
    descriptor_blake3: [u8; 32],
    source_blake3: [u8; 32],
    formula_relation: BoolExpr,
    inputs: Vec<InputEncoding>,
    logical_atom_count: usize,
}

impl CompiledLogicArtifact {
    pub fn descriptor(&self) -> &EffectVmDescriptor2 {
        &self.descriptor
    }

    pub fn descriptor_json(&self) -> &str {
        &self.descriptor_json
    }

    pub fn descriptor_bytes(&self) -> &[u8] {
        self.descriptor_json.as_bytes()
    }

    pub fn descriptor_blake3(&self) -> [u8; 32] {
        self.descriptor_blake3
    }

    pub fn descriptor_blake3_hex(&self) -> String {
        hex32(&self.descriptor_blake3)
    }

    pub fn source_blake3(&self) -> [u8; 32] {
        self.source_blake3
    }

    pub fn source_blake3_hex(&self) -> String {
        hex32(&self.source_blake3)
    }

    pub fn input_encodings(&self) -> &[InputEncoding] {
        &self.inputs
    }

    pub fn logical_atom_count(&self) -> usize {
        self.logical_atom_count
    }

    /// Formula polynomial before the separate input-encoding gates.  Use
    /// [`Self::relation_accepts_atoms`] to evaluate the complete relation.
    pub fn source_relation(&self) -> &BoolExpr {
        &self.formula_relation
    }

    /// Encode typed source inputs as the canonical trace row.  A descriptor
    /// with no logical atoms has one false padding column because the live AIR
    /// does not admit a zero-width main trace.
    pub fn encode_inputs(&self, values: &[LogicValue]) -> Result<Vec<bool>, FrontendError> {
        if values.len() != self.inputs.len() {
            return Err(FrontendError::InputCountMismatch {
                expected: self.inputs.len(),
                actual: values.len(),
            });
        }
        let mut atoms = vec![false; self.descriptor.trace_width];
        for (index, (encoding, value)) in self.inputs.iter().zip(values).enumerate() {
            match (&encoding.ty, value) {
                (LogicType::Bool, LogicValue::Bool(bit)) => {
                    atoms[encoding.first_atom] = *bit;
                }
                (LogicType::Finite { cardinality }, LogicValue::Finite(selected))
                    if *selected < *cardinality =>
                {
                    atoms[encoding.first_atom + selected] = true;
                }
                (LogicType::Finite { cardinality }, LogicValue::Finite(selected)) => {
                    return Err(FrontendError::InputValueOutOfRange {
                        input: index,
                        value: *selected,
                        cardinality: *cardinality,
                    });
                }
                _ => return Err(FrontendError::InputValueTypeMismatch { input: index }),
            }
        }
        Ok(atoms)
    }

    /// Canonical BabyBear row accepted directly by
    /// [`crate::descriptor_ir2::prove_vm_descriptor2`].  The returned row is
    /// the complete one-row witness for this row-local relation.
    pub fn trace_row(&self, values: &[LogicValue]) -> Result<Vec<BabyBear>, FrontendError> {
        Ok(self
            .encode_inputs(values)?
            .into_iter()
            .map(|bit| if bit { BabyBear::ONE } else { BabyBear::ZERO })
            .collect())
    }

    /// One-row trace wrapper for the live prover API.
    pub fn one_row_trace(
        &self,
        values: &[LogicValue],
    ) -> Result<Vec<Vec<BabyBear>>, FrontendError> {
        Ok(vec![self.trace_row(values)?])
    }

    /// Evaluate the complete compiled relation, including input one-hot
    /// validity.  This is a transparent oracle, not a proof verifier.
    pub fn relation_accepts_atoms(&self, atoms: &[bool]) -> Result<bool, FrontendError> {
        if atoms.len() != self.descriptor.trace_width {
            return Err(FrontendError::AtomCountMismatch {
                expected: self.descriptor.trace_width,
                actual: atoms.len(),
            });
        }
        for encoding in &self.inputs {
            if let LogicType::Finite { cardinality } = encoding.ty {
                let selected = (0..cardinality)
                    .filter(|offset| atoms[encoding.first_atom + offset])
                    .count();
                if selected != 1 {
                    return Ok(false);
                }
            }
        }
        self.formula_relation.evaluate(atoms)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendError {
    EmptyFiniteDomain,
    UnboundedDomain,
    DuplicateInputName(String),
    SourceTooLarge {
        nodes: usize,
        maximum: usize,
    },
    TooManyAtoms {
        atoms: usize,
        maximum: usize,
    },
    PredicateTooLarge {
        entries: usize,
        maximum: usize,
    },
    PredicateShapeMismatch {
        expected: usize,
        actual: usize,
    },
    PredicateArityMismatch {
        expected: usize,
        actual: usize,
    },
    QuantifierExpansionTooLarge {
        instances: usize,
        maximum: usize,
    },
    ExpandedRelationTooLarge {
        nodes: usize,
        maximum: usize,
    },
    InputOutOfRange {
        index: usize,
        available: usize,
    },
    BoundVariableOutOfRange {
        index: usize,
        depth: usize,
    },
    ConstantOutOfRange {
        value: usize,
        cardinality: usize,
    },
    TypeMismatch {
        expected: LogicType,
        actual: LogicType,
    },
    InputCountMismatch {
        expected: usize,
        actual: usize,
    },
    InputValueTypeMismatch {
        input: usize,
    },
    InputValueOutOfRange {
        input: usize,
        value: usize,
        cardinality: usize,
    },
    AtomVectorTooShort {
        required: usize,
        actual: usize,
    },
    AtomCountMismatch {
        expected: usize,
        actual: usize,
    },
    /// The reply's descriptor or relation failed to parse or contradicts the request.
    InternalWireDrift(String),
    /// No compiler executable could be run.
    CompilerUnavailable(String),
    /// The compiler's reply is not a well-formed `DIRECT-LOGIC-COMPILED-1` reply, or Lean
    /// refused the request bytes themselves.
    CompilerProtocol(String),
}

impl fmt::Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for FrontendError {}

/// A compiler backend: takes one request line, returns the reply text.
pub trait LogicCompiler {
    fn compile_request(&self, request: &str) -> Result<String, FrontendError>;
}

/// The Lean compiler executable (`lake build direct_logic_compile`), run once per request.
#[derive(Clone, Debug)]
pub struct LeanExeCompiler {
    program: PathBuf,
}

impl LeanExeCompiler {
    pub fn new(program: impl Into<PathBuf>) -> Self {
        Self {
            program: program.into(),
        }
    }

    /// The in-tree build location of the executable.
    pub fn default_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../metatheory/.lake/build/bin/direct_logic_compile")
    }

    /// `DREGG_DIRECT_LOGIC_COMPILER`, else the in-tree build if it exists.
    pub fn locate() -> Result<Self, FrontendError> {
        if let Some(path) = std::env::var_os(DIRECT_LOGIC_COMPILER_ENV) {
            return Ok(Self::new(path));
        }
        let path = Self::default_path();
        if path.is_file() {
            Ok(Self::new(path))
        } else {
            Err(FrontendError::CompilerUnavailable(format!(
                "set {DIRECT_LOGIC_COMPILER_ENV} or run `lake build direct_logic_compile` in \
                 metatheory/ (looked for {})",
                path.display()
            )))
        }
    }
}

impl LogicCompiler for LeanExeCompiler {
    fn compile_request(&self, request: &str) -> Result<String, FrontendError> {
        let unavailable = |why: String| FrontendError::CompilerUnavailable(why);
        let mut child = Command::new(&self.program)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| unavailable(format!("{}: {e}", self.program.display())))?;
        {
            let mut stdin = child
                .stdin
                .take()
                .ok_or_else(|| unavailable("no stdin".into()))?;
            stdin
                .write_all(request.as_bytes())
                .and_then(|_| stdin.write_all(b"\n"))
                .map_err(|e| unavailable(format!("writing request: {e}")))?;
        }
        let output = child
            .wait_with_output()
            .map_err(|e| unavailable(format!("waiting for compiler: {e}")))?;
        if !output.status.success() {
            return Err(unavailable(format!(
                "compiler exited with {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            )));
        }
        let text = String::from_utf8(output.stdout)
            .map_err(|_| FrontendError::CompilerProtocol("reply is not UTF-8".into()))?;
        text.strip_suffix("end\n")
            .map(str::to_owned)
            .ok_or_else(|| FrontendError::CompilerProtocol("reply has no `end` line".into()))
    }
}

/// Replies the Lean executable produced earlier, keyed by the exact request line.  The corpus
/// format is the executable's own output with each reply preceded by `request <line>`.
#[derive(Clone, Debug, Default)]
pub struct RecordedCompiler {
    replies: BTreeMap<String, String>,
}

impl RecordedCompiler {
    pub fn parse(corpus: &str) -> Result<Self, FrontendError> {
        let mut replies = BTreeMap::new();
        let mut lines = corpus.lines();
        while let Some(line) = lines.next() {
            if line.is_empty() {
                continue;
            }
            let request = line.strip_prefix("request ").ok_or_else(|| {
                FrontendError::CompilerProtocol(format!("corpus line is not a request: {line:?}"))
            })?;
            let mut reply = String::new();
            loop {
                match lines.next() {
                    Some("end") => break,
                    Some(l) => {
                        reply.push_str(l);
                        reply.push('\n');
                    }
                    None => {
                        return Err(FrontendError::CompilerProtocol(
                            "corpus reply has no `end` line".into(),
                        ));
                    }
                }
            }
            replies.insert(request.to_owned(), reply);
        }
        Ok(Self { replies })
    }

    pub fn requests(&self) -> impl Iterator<Item = (&str, &str)> {
        self.replies.iter().map(|(k, v)| (k.as_str(), v.as_str()))
    }
}

impl LogicCompiler for RecordedCompiler {
    fn compile_request(&self, request: &str) -> Result<String, FrontendError> {
        self.replies.get(request).cloned().ok_or_else(|| {
            FrontendError::CompilerUnavailable(
                "no recorded Lean reply for this request; regenerate the corpus".into(),
            )
        })
    }
}

/// The request line for a program: limits, then the canonical source bytes in hex.
pub fn compile_request_line(program: &LogicProgram, limits: &CompileLimits) -> String {
    let bytes = canonical_source_bytes(program);
    let mut hex = String::with_capacity(bytes.len() * 2);
    for byte in &bytes {
        use std::fmt::Write as _;
        write!(&mut hex, "{byte:02x}").expect("writing to String cannot fail");
    }
    format!(
        "{DIRECT_LOGIC_REQUEST_TAG} {} {} {} {} {} {hex}",
        limits.maximum_source_nodes,
        limits.maximum_atoms,
        limits.maximum_predicate_entries,
        limits.maximum_quantifier_instances,
        limits.maximum_expanded_nodes,
    )
}

/// Compile a finite program with the Lean compiler located by [`LeanExeCompiler::locate`].
pub fn compile_logic_program(
    program: &LogicProgram,
    limits: &CompileLimits,
) -> Result<CompiledLogicArtifact, FrontendError> {
    compile_logic_program_with(&LeanExeCompiler::locate()?, program, limits)
}

/// Compile a finite program with an explicit compiler backend.
pub fn compile_logic_program_with(
    compiler: &dyn LogicCompiler,
    program: &LogicProgram,
    limits: &CompileLimits,
) -> Result<CompiledLogicArtifact, FrontendError> {
    let source_bytes = canonical_source_bytes(program);
    let source_blake3 = *blake3::hash(&source_bytes).as_bytes();
    let reply = compiler.compile_request(&compile_request_line(program, limits))?;
    parse_reply(program, &reply, source_blake3)
}

fn protocol(why: impl Into<String>) -> FrontendError {
    FrontendError::CompilerProtocol(why.into())
}

fn parse_reply(
    program: &LogicProgram,
    reply: &str,
    source_blake3: [u8; 32],
) -> Result<CompiledLogicArtifact, FrontendError> {
    let mut lines = reply.lines();
    if lines.next() != Some(DIRECT_LOGIC_REPLY_TAG) {
        return Err(protocol("missing reply tag"));
    }
    let status = lines.next().ok_or_else(|| protocol("missing status"))?;
    if let Some(error) = status.strip_prefix("error ") {
        return Err(parse_error(error)?);
    }
    if status != "ok" {
        return Err(protocol(format!("unknown status {status:?}")));
    }
    let mut field = |key: &str| -> Result<&str, FrontendError> {
        let line = lines
            .next()
            .ok_or_else(|| protocol(format!("missing {key}")))?;
        if line == key {
            return Ok("");
        }
        line.strip_prefix(key)
            .and_then(|rest| rest.strip_prefix(' '))
            .ok_or_else(|| protocol(format!("expected {key}, got {line:?}")))
    };
    let hash = field("source_blake3")?;
    let atoms = field("logical_atom_count")?;
    let layout = field("inputs")?;
    let relation = field("relation")?;
    let descriptor_json = field("descriptor")?.to_owned();

    let expected_hash = hex32(&source_blake3);
    if hash != expected_hash {
        return Err(FrontendError::InternalWireDrift(format!(
            "Lean hashed different source bytes: {hash} != {expected_hash}"
        )));
    }
    let logical_atom_count: usize = atoms
        .parse()
        .map_err(|_| protocol("bad logical_atom_count"))?;

    let mut inputs = Vec::with_capacity(program.inputs.len());
    let mut next = 0usize;
    let entries: Vec<&str> = layout.split(' ').filter(|s| !s.is_empty()).collect();
    if entries.len() != program.inputs.len() {
        return Err(FrontendError::InternalWireDrift(
            "input layout does not cover the declared inputs".into(),
        ));
    }
    for (decl, entry) in program.inputs.iter().zip(entries) {
        let (first, count) = entry
            .split_once(':')
            .and_then(|(f, c)| Some((f.parse::<usize>().ok()?, c.parse::<usize>().ok()?)))
            .ok_or_else(|| protocol(format!("bad layout entry {entry:?}")))?;
        let expected_count = match decl.ty {
            LogicType::Bool => 1,
            LogicType::Finite { cardinality } => cardinality,
            LogicType::UnboundedInteger => 0,
        };
        if first != next || count != expected_count {
            return Err(FrontendError::InternalWireDrift(format!(
                "input {:?} laid out at {first}:{count}, expected {next}:{expected_count}",
                decl.name
            )));
        }
        next += count;
        inputs.push(InputEncoding {
            name: decl.name.clone(),
            ty: decl.ty.clone(),
            first_atom: first,
            atom_count: count,
        });
    }
    if next != logical_atom_count {
        return Err(FrontendError::InternalWireDrift(
            "layout and logical_atom_count disagree".into(),
        ));
    }

    let formula_relation = parse_relation(relation, logical_atom_count)?;
    let descriptor =
        parse_vm_descriptor2(&descriptor_json).map_err(FrontendError::InternalWireDrift)?;
    let expected_name =
        format!("dregg-direct-logic-v{DIRECT_LOGIC_FRONTEND_VERSION}-{expected_hash}");
    if descriptor.name != expected_name
        || descriptor.trace_width != logical_atom_count.max(1)
        || descriptor.public_input_count != 0
        || descriptor
            .constraints
            .iter()
            .any(|constraint| !matches!(constraint, VmConstraint2::WindowGate(_)))
    {
        return Err(FrontendError::InternalWireDrift(
            "descriptor name, width, public inputs or constraint kinds contradict the request"
                .into(),
        ));
    }
    let descriptor_blake3 = *blake3::hash(descriptor_json.as_bytes()).as_bytes();
    Ok(CompiledLogicArtifact {
        descriptor,
        descriptor_json,
        descriptor_blake3,
        source_blake3,
        formula_relation,
        inputs,
        logical_atom_count,
    })
}

/// Postfix relation tokens (Lean `rpn`): `A<n>`, `T`, `F`, `N`, `&`, `|`.
fn parse_relation(tokens: &str, atom_count: usize) -> Result<BoolExpr, FrontendError> {
    let mut stack: Vec<BoolExpr> = Vec::new();
    let pop = |stack: &mut Vec<BoolExpr>| stack.pop().ok_or_else(|| protocol("relation underflow"));
    for token in tokens.split(' ').filter(|t| !t.is_empty()) {
        let node = match token {
            "T" => BoolExpr::Constant(true),
            "F" => BoolExpr::Constant(false),
            "N" => BoolExpr::Not(Box::new(pop(&mut stack)?)),
            "&" | "|" => {
                let right = pop(&mut stack)?;
                let left = pop(&mut stack)?;
                if token == "&" {
                    BoolExpr::And(Box::new(left), Box::new(right))
                } else {
                    BoolExpr::Or(Box::new(left), Box::new(right))
                }
            }
            atom => {
                let index: usize = atom
                    .strip_prefix('A')
                    .and_then(|n| n.parse().ok())
                    .ok_or_else(|| protocol(format!("bad relation token {atom:?}")))?;
                if index >= atom_count {
                    return Err(FrontendError::InternalWireDrift(format!(
                        "relation reads atom {index} of {atom_count}"
                    )));
                }
                BoolExpr::Atom(index)
            }
        };
        stack.push(node);
    }
    match (stack.pop(), stack.is_empty()) {
        (Some(expr), true) => Ok(expr),
        _ => Err(protocol("relation is not a single expression")),
    }
}

fn parse_type(text: &str) -> Result<LogicType, FrontendError> {
    match text {
        "bool" => Ok(LogicType::Bool),
        "unbounded" => Ok(LogicType::UnboundedInteger),
        other => other
            .strip_prefix("finite:")
            .and_then(|n| n.parse().ok())
            .map(|cardinality| LogicType::Finite { cardinality })
            .ok_or_else(|| protocol(format!("bad type {other:?}"))),
    }
}

fn unhex_utf8(text: &str) -> Result<String, FrontendError> {
    if text.len() % 2 != 0 {
        return Err(protocol("odd hex"));
    }
    let bytes = (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16))
        .collect::<Result<Vec<u8>, _>>()
        .map_err(|_| protocol("bad hex"))?;
    String::from_utf8(bytes).map_err(|_| protocol("bad UTF-8"))
}

/// Lean `renderError` back to the error value.
fn parse_error(text: &str) -> Result<FrontendError, FrontendError> {
    let parts: Vec<&str> = text.split(' ').collect();
    let num = |i: usize| -> Result<usize, FrontendError> {
        parts
            .get(i)
            .and_then(|p| p.parse::<u128>().ok())
            .map(|n| usize::try_from(n).unwrap_or(usize::MAX))
            .ok_or_else(|| protocol(format!("bad error {text:?}")))
    };
    Ok(match parts[0] {
        "EmptyFiniteDomain" => FrontendError::EmptyFiniteDomain,
        "UnboundedDomain" => FrontendError::UnboundedDomain,
        "DuplicateInputName" => {
            FrontendError::DuplicateInputName(unhex_utf8(parts.get(1).copied().unwrap_or(""))?)
        }
        "SourceTooLarge" => FrontendError::SourceTooLarge {
            nodes: num(1)?,
            maximum: num(2)?,
        },
        "TooManyAtoms" => FrontendError::TooManyAtoms {
            atoms: num(1)?,
            maximum: num(2)?,
        },
        "PredicateTooLarge" => FrontendError::PredicateTooLarge {
            entries: num(1)?,
            maximum: num(2)?,
        },
        "PredicateShapeMismatch" => FrontendError::PredicateShapeMismatch {
            expected: num(1)?,
            actual: num(2)?,
        },
        "PredicateArityMismatch" => FrontendError::PredicateArityMismatch {
            expected: num(1)?,
            actual: num(2)?,
        },
        "QuantifierExpansionTooLarge" => FrontendError::QuantifierExpansionTooLarge {
            instances: num(1)?,
            maximum: num(2)?,
        },
        "ExpandedRelationTooLarge" => FrontendError::ExpandedRelationTooLarge {
            nodes: num(1)?,
            maximum: num(2)?,
        },
        "InputOutOfRange" => FrontendError::InputOutOfRange {
            index: num(1)?,
            available: num(2)?,
        },
        "BoundVariableOutOfRange" => FrontendError::BoundVariableOutOfRange {
            index: num(1)?,
            depth: num(2)?,
        },
        "ConstantOutOfRange" => FrontendError::ConstantOutOfRange {
            value: num(1)?,
            cardinality: num(2)?,
        },
        "TypeMismatch" => FrontendError::TypeMismatch {
            expected: parse_type(parts.get(1).copied().unwrap_or(""))?,
            actual: parse_type(parts.get(2).copied().unwrap_or(""))?,
        },
        "MalformedRequest" => FrontendError::CompilerProtocol(format!(
            "Lean refused the request: {}",
            unhex_utf8(parts.get(1).copied().unwrap_or(""))?
        )),
        other => return Err(protocol(format!("unknown error kind {other:?}"))),
    })
}

#[derive(Clone, Debug)]
struct BoundValue {
    ty: LogicType,
    value: usize,
}

/// Transparent source evaluator, independent of descriptor construction.
pub fn evaluate_logic_program(
    program: &LogicProgram,
    inputs: &[LogicValue],
) -> Result<bool, FrontendError> {
    if inputs.len() != program.inputs.len() {
        return Err(FrontendError::InputCountMismatch {
            expected: program.inputs.len(),
            actual: inputs.len(),
        });
    }
    for (index, (decl, value)) in program.inputs.iter().zip(inputs).enumerate() {
        validate_value(index, &decl.ty, value)?;
    }
    eval_formula(program, &program.formula, inputs, &mut Vec::new())
}

fn validate_value(index: usize, ty: &LogicType, value: &LogicValue) -> Result<(), FrontendError> {
    match (ty, value) {
        (LogicType::Bool, LogicValue::Bool(_)) => Ok(()),
        (LogicType::Finite { cardinality }, LogicValue::Finite(value)) if *value < *cardinality => {
            Ok(())
        }
        (LogicType::Finite { cardinality }, LogicValue::Finite(value)) => {
            Err(FrontendError::InputValueOutOfRange {
                input: index,
                value: *value,
                cardinality: *cardinality,
            })
        }
        (LogicType::UnboundedInteger, _) => Err(FrontendError::UnboundedDomain),
        _ => Err(FrontendError::InputValueTypeMismatch { input: index }),
    }
}

fn eval_formula(
    program: &LogicProgram,
    formula: &Formula,
    inputs: &[LogicValue],
    bounds: &mut Vec<BoundValue>,
) -> Result<bool, FrontendError> {
    match formula {
        Formula::Top => Ok(true),
        Formula::Bottom => Ok(false),
        Formula::Equal(left, right) => {
            let (left_ty, left_value) = eval_term(program, left, inputs, bounds)?;
            let (right_ty, right_value) = eval_term(program, right, inputs, bounds)?;
            require_same_type(&left_ty, &right_ty)?;
            Ok(left_value == right_value)
        }
        Formula::Predicate { table, arguments } => {
            if table.argument_types.len() != arguments.len() {
                return Err(FrontendError::PredicateArityMismatch {
                    expected: table.argument_types.len(),
                    actual: arguments.len(),
                });
            }
            let mut flat = 0usize;
            let mut expected_entries = 1usize;
            for (expected_ty, term) in table.argument_types.iter().zip(arguments) {
                let cardinality = expected_ty.cardinality()?;
                expected_entries = expected_entries.saturating_mul(cardinality);
                let (actual_ty, value) = eval_term(program, term, inputs, bounds)?;
                require_same_type(expected_ty, &actual_ty)?;
                flat = flat.saturating_mul(cardinality).saturating_add(value);
            }
            if table.values.len() != expected_entries {
                return Err(FrontendError::PredicateShapeMismatch {
                    expected: expected_entries,
                    actual: table.values.len(),
                });
            }
            Ok(table.values[flat])
        }
        Formula::Not(value) => Ok(!eval_formula(program, value, inputs, bounds)?),
        Formula::And(left, right) => {
            let left = eval_formula(program, left, inputs, bounds)?;
            let right = eval_formula(program, right, inputs, bounds)?;
            Ok(left && right)
        }
        Formula::Or(left, right) => {
            let left = eval_formula(program, left, inputs, bounds)?;
            let right = eval_formula(program, right, inputs, bounds)?;
            Ok(left || right)
        }
        Formula::ForAll { binder, body } => {
            let cardinality = binder.cardinality()?;
            for value in 0..cardinality {
                bounds.push(BoundValue {
                    ty: binder.clone(),
                    value,
                });
                let result = eval_formula(program, body, inputs, bounds);
                bounds.pop();
                if !result? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Formula::Exists { binder, body } => {
            let cardinality = binder.cardinality()?;
            for value in 0..cardinality {
                bounds.push(BoundValue {
                    ty: binder.clone(),
                    value,
                });
                let result = eval_formula(program, body, inputs, bounds);
                bounds.pop();
                if result? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

fn eval_term(
    program: &LogicProgram,
    term: &Term,
    inputs: &[LogicValue],
    bounds: &[BoundValue],
) -> Result<(LogicType, usize), FrontendError> {
    match term {
        Term::Input(index) => {
            let decl = program
                .inputs
                .get(*index)
                .ok_or(FrontendError::InputOutOfRange {
                    index: *index,
                    available: program.inputs.len(),
                })?;
            let value = inputs.get(*index).ok_or(FrontendError::InputOutOfRange {
                index: *index,
                available: inputs.len(),
            })?;
            Ok((
                decl.ty.clone(),
                match value {
                    LogicValue::Bool(value) => usize::from(*value),
                    LogicValue::Finite(value) => *value,
                },
            ))
        }
        Term::Bound(index) => {
            let depth = bounds.len();
            let value = depth
                .checked_sub(index.saturating_add(1))
                .and_then(|position| bounds.get(position))
                .ok_or(FrontendError::BoundVariableOutOfRange {
                    index: *index,
                    depth,
                })?;
            Ok((value.ty.clone(), value.value))
        }
        Term::Constant { ty, value } => {
            let cardinality = ty.cardinality()?;
            if *value >= cardinality {
                return Err(FrontendError::ConstantOutOfRange {
                    value: *value,
                    cardinality,
                });
            }
            Ok((ty.clone(), *value))
        }
    }
}

fn require_same_type(expected: &LogicType, actual: &LogicType) -> Result<(), FrontendError> {
    if expected == actual {
        Ok(())
    } else {
        Err(FrontendError::TypeMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        })
    }
}

fn canonical_source_bytes(program: &LogicProgram) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"dregg-direct-logic-source\0");
    put_u64(&mut out, u64::from(DIRECT_LOGIC_FRONTEND_VERSION));
    put_u64(&mut out, program.inputs.len() as u64);
    for input in &program.inputs {
        put_bytes(&mut out, input.name.as_bytes());
        put_type(&mut out, &input.ty);
    }
    put_formula(&mut out, &program.formula);
    out
}

fn put_formula(out: &mut Vec<u8>, formula: &Formula) {
    match formula {
        Formula::Top => out.push(0),
        Formula::Bottom => out.push(1),
        Formula::Equal(left, right) => {
            out.push(2);
            put_term(out, left);
            put_term(out, right);
        }
        Formula::Predicate { table, arguments } => {
            out.push(3);
            put_bytes(out, table.name.as_bytes());
            put_u64(out, table.argument_types.len() as u64);
            for ty in &table.argument_types {
                put_type(out, ty);
            }
            put_u64(out, table.values.len() as u64);
            for value in &table.values {
                out.push(u8::from(*value));
            }
            put_u64(out, arguments.len() as u64);
            for term in arguments {
                put_term(out, term);
            }
        }
        Formula::Not(value) => {
            out.push(4);
            put_formula(out, value);
        }
        Formula::And(left, right) => {
            out.push(5);
            put_formula(out, left);
            put_formula(out, right);
        }
        Formula::Or(left, right) => {
            out.push(6);
            put_formula(out, left);
            put_formula(out, right);
        }
        Formula::ForAll { binder, body } => {
            out.push(7);
            put_type(out, binder);
            put_formula(out, body);
        }
        Formula::Exists { binder, body } => {
            out.push(8);
            put_type(out, binder);
            put_formula(out, body);
        }
    }
}

fn put_term(out: &mut Vec<u8>, term: &Term) {
    match term {
        Term::Input(index) => {
            out.push(0);
            put_u64(out, *index as u64);
        }
        Term::Bound(index) => {
            out.push(1);
            put_u64(out, *index as u64);
        }
        Term::Constant { ty, value } => {
            out.push(2);
            put_type(out, ty);
            put_u64(out, *value as u64);
        }
    }
}

fn put_type(out: &mut Vec<u8>, ty: &LogicType) {
    match ty {
        LogicType::Bool => out.push(0),
        LogicType::Finite { cardinality } => {
            out.push(1);
            put_u64(out, *cardinality as u64);
        }
        LogicType::UnboundedInteger => out.push(2),
    }
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, value: &[u8]) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value);
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("writing to String cannot fail");
    }
    out
}
