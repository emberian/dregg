//! Batched topological execution with output forwarding.
//!
//! # What this module IS
//!
//! This module implements **synchronous batched execution** of turns with declared
//! dependency edges. Turns are submitted together in a `Pipeline` (aka `TurnBatch`),
//! topologically sorted, and executed in causal order. Earlier turns' outputs are
//! available to later turns via `EventualRef` (aka `OutputRef`).
//!
//! Useful for: multi-step local operations, atomic multi-party swaps, and tests.
//!
//! # What this module is NOT
//!
//! This is **not** async promise pipelining in the E-language sense. All execution
//! is synchronous and local. For true E-style eventual-send, use the intent system.

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

use crate::turn::Turn;

/// A reference to a value that will exist after a pending turn executes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EventualRef {
    /// Hash of the turn that will produce this value.
    pub source_turn: [u8; 32],
    /// Which output slot of that turn.
    pub output_slot: u32,
    /// Federation ID of the turn's origin. None = local federation, Some = remote.
    /// When set, the pipeline executor must wait for the remote federation's receipt
    /// before this reference can be resolved.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub federation_id: Option<[u8; 32]>,
}

impl EventualRef {
    /// Create a new eventual reference (local federation).
    pub fn new(source_turn: [u8; 32], output_slot: u32) -> Self {
        Self {
            source_turn,
            output_slot,
            federation_id: None,
        }
    }

    /// Create a new eventual reference targeting a remote federation.
    pub fn new_remote(source_turn: [u8; 32], output_slot: u32, federation_id: [u8; 32]) -> Self {
        Self {
            source_turn,
            output_slot,
            federation_id: Some(federation_id),
        }
    }

    /// Returns true if this reference targets a remote federation.
    pub fn is_remote(&self) -> bool {
        self.federation_id.is_some()
    }

    /// Returns true if this reference is local (same federation).
    pub fn is_local(&self) -> bool {
        self.federation_id.is_none()
    }
}

/// A target that can be either concrete or eventual.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Target {
    /// A concrete cell ID, known at submission time.
    Concrete(CellId),
    /// An eventual reference, resolved during pipeline execution.
    Eventual(EventualRef),
}

impl Target {
    /// Returns true if this is a concrete target.
    pub fn is_concrete(&self) -> bool {
        matches!(self, Target::Concrete(_))
    }

    /// Returns true if this is an eventual reference.
    pub fn is_eventual(&self) -> bool {
        matches!(self, Target::Eventual(_))
    }

    /// Try to extract the concrete CellId, returning None if eventual.
    pub fn as_concrete(&self) -> Option<&CellId> {
        match self {
            Target::Concrete(id) => Some(id),
            Target::Eventual(_) => None,
        }
    }

    /// Try to extract the EventualRef, returning None if concrete.
    pub fn as_eventual(&self) -> Option<&EventualRef> {
        match self {
            Target::Eventual(r) => Some(r),
            Target::Concrete(_) => None,
        }
    }
}

impl From<CellId> for Target {
    fn from(id: CellId) -> Self {
        Target::Concrete(id)
    }
}

impl From<EventualRef> for Target {
    fn from(r: EventualRef) -> Self {
        Target::Eventual(r)
    }
}

/// An output produced by a turn, recorded in the receipt for pipeline resolution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TurnOutput {
    /// A capability was granted.
    GrantedCapability {
        /// The cell that RECEIVED the capability (the recipient, NOT the cell the
        /// capability points to). Named `target` for backward compat.
        target: CellId,
        /// The slot number assigned to the granted capability.
        slot: u32,
    },
    /// A new note was created.
    CreatedNote {
        /// The commitment hash of the created note.
        commitment: [u8; 32],
    },
    /// A state field was updated on a cell.
    StateUpdate {
        /// The cell whose state was updated.
        cell: CellId,
        /// Which field index was updated.
        field: usize,
        /// The BLAKE3 hash of the new field value.
        hash: [u8; 32],
    },
    /// A new cell was created.
    CreatedCell {
        /// The ID of the newly created cell.
        cell: CellId,
    },
}

// ─── Pipeline Errors ─────────────────────────────────────────────────────────

/// Error indicating a cycle was detected in pipeline dependencies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CycleError {
    /// Description of the cycle.
    pub description: String,
}

impl std::fmt::Display for CycleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cycle detected in pipeline: {}", self.description)
    }
}

impl std::error::Error for CycleError {}

/// Errors during pipeline validation or execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineError {
    /// The pipeline contains a dependency cycle.
    Cycle(CycleError),
    /// A dependency index is out of bounds.
    InvalidIndex { index: usize, max: usize },
    /// A turn depends on itself.
    SelfDependency { index: usize },
    /// An eventual reference could not be resolved.
    UnresolvedRef {
        /// The EventualRef that could not be resolved.
        eventual_ref: EventualRef,
        /// Why it could not be resolved.
        reason: String,
    },
    /// A dependency turn failed, causing all dependents to fail.
    DependencyFailed {
        /// Index of the turn that failed.
        failed_index: usize,
        /// Index of the dependent that cannot execute.
        dependent_index: usize,
    },
    /// A turn failed during execution (not due to a dependency failure).
    TurnExecutionFailed {
        /// Index of the turn that failed.
        index: usize,
        /// The reason for the failure.
        reason: String,
    },
    /// The pipeline is empty.
    Empty,
    /// An EventualRef references a source_turn hash that does not exist in the batch.
    InvalidOutputRef {
        /// Index of the turn containing the invalid reference.
        turn_index: usize,
        /// The EventualRef with the invalid source_turn hash.
        output_ref: EventualRef,
    },
    /// A turn's `depends_on` hash does not match any turn in the batch or committed receipts.
    MissingDependency {
        /// Index of the turn with the missing dependency.
        turn_index: usize,
        /// The hash that could not be found.
        missing_hash: [u8; 32],
    },
}

impl std::fmt::Display for PipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PipelineError::Cycle(c) => write!(f, "{}", c),
            PipelineError::InvalidIndex { index, max } => {
                write!(f, "dependency index {index} out of bounds (max {max})")
            }
            PipelineError::SelfDependency { index } => {
                write!(f, "turn at index {index} depends on itself")
            }
            PipelineError::UnresolvedRef {
                eventual_ref,
                reason,
            } => {
                write!(
                    f,
                    "unresolved eventual ref (source {:02x}{:02x}.., slot {}): {}",
                    eventual_ref.source_turn[0],
                    eventual_ref.source_turn[1],
                    eventual_ref.output_slot,
                    reason
                )
            }
            PipelineError::DependencyFailed {
                failed_index,
                dependent_index,
            } => {
                write!(
                    f,
                    "turn[{dependent_index}] cannot execute: dependency turn[{failed_index}] failed"
                )
            }
            PipelineError::TurnExecutionFailed { index, reason } => {
                write!(f, "turn[{index}] execution failed: {reason}")
            }
            PipelineError::Empty => write!(f, "pipeline is empty"),
            PipelineError::InvalidOutputRef {
                turn_index,
                output_ref,
            } => {
                write!(
                    f,
                    "turn[{}] has OutputRef with source_turn {:02x}{:02x}.. not in batch",
                    turn_index, output_ref.source_turn[0], output_ref.source_turn[1]
                )
            }
            PipelineError::MissingDependency {
                turn_index,
                missing_hash,
            } => {
                write!(
                    f,
                    "turn[{}] depends_on hash {:02x}{:02x}.. not found",
                    turn_index, missing_hash[0], missing_hash[1]
                )
            }
        }
    }
}

impl std::error::Error for PipelineError {}

// ─── Pipeline ────────────────────────────────────────────────────────────────

/// A pipeline: multiple turns submitted together with dependency edges.
///
/// The executor processes turns in topological order, resolving EventualRefs
/// as earlier turns produce outputs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pipeline {
    /// The turns in this pipeline.
    pub turns: Vec<Turn>,
    /// Dependency edges: (dependent_index, dependency_index).
    pub dependencies: Vec<(usize, usize)>,
    /// When true, if ANY turn fails, ALL previously committed turns are rolled back.
    pub atomic: bool,
}

impl Pipeline {
    /// Create a new empty pipeline.
    pub fn new() -> Self {
        Self {
            turns: Vec::new(),
            dependencies: Vec::new(),
            atomic: false,
        }
    }

    /// Add a turn to the pipeline. Returns its index.
    pub fn add_turn(&mut self, turn: Turn) -> usize {
        let idx = self.turns.len();
        self.turns.push(turn);
        idx
    }

    /// Declare that `dependent` depends on `dependency` completing first.
    pub fn add_dependency(&mut self, dependent: usize, dependency: usize) {
        self.dependencies.push((dependent, dependency));
    }

    /// Compute the topological order of turns in this pipeline.
    pub fn topological_order(&self) -> Result<Vec<usize>, CycleError> {
        let n = self.turns.len();
        if n == 0 {
            return Ok(vec![]);
        }

        let mut in_degree = vec![0usize; n];
        let mut successors: Vec<Vec<usize>> = vec![Vec::new(); n];

        for &(dependent, dependency) in &self.dependencies {
            successors[dependency].push(dependent);
            in_degree[dependent] += 1;
        }

        let mut queue: std::collections::VecDeque<usize> = std::collections::VecDeque::new();
        for i in 0..n {
            if in_degree[i] == 0 {
                queue.push_back(i);
            }
        }

        let mut order = Vec::with_capacity(n);
        while let Some(node) = queue.pop_front() {
            order.push(node);
            for &succ in &successors[node] {
                in_degree[succ] -= 1;
                if in_degree[succ] == 0 {
                    queue.push_back(succ);
                }
            }
        }

        if order.len() != n {
            let cycle_nodes: Vec<usize> = (0..n).filter(|i| in_degree[*i] > 0).collect();
            Err(CycleError {
                description: format!("turns at indices {:?} form a cycle", cycle_nodes),
            })
        } else {
            Ok(order)
        }
    }

    /// Validate the pipeline structure without executing it.
    pub fn validate(&self) -> Result<(), PipelineError> {
        if self.turns.is_empty() {
            return Err(PipelineError::Empty);
        }

        let max = self.turns.len();
        for &(dependent, dependency) in &self.dependencies {
            if dependent >= max {
                return Err(PipelineError::InvalidIndex {
                    index: dependent,
                    max: max - 1,
                });
            }
            if dependency >= max {
                return Err(PipelineError::InvalidIndex {
                    index: dependency,
                    max: max - 1,
                });
            }
            if dependent == dependency {
                return Err(PipelineError::SelfDependency { index: dependent });
            }
        }

        self.topological_order().map_err(PipelineError::Cycle)?;
        Ok(())
    }

    /// Get the direct dependencies of a turn at the given index.
    pub fn dependencies_of(&self, index: usize) -> Vec<usize> {
        self.dependencies
            .iter()
            .filter(|(dep, _)| *dep == index)
            .map(|(_, dependency)| *dependency)
            .collect()
    }

    /// Get the direct dependents of a turn at the given index.
    pub fn dependents_of(&self, index: usize) -> Vec<usize> {
        self.dependencies
            .iter()
            .filter(|(_, dep)| *dep == index)
            .map(|(dependent, _)| *dependent)
            .collect()
    }
}

impl Default for Pipeline {
    fn default() -> Self {
        Self::new()
    }
}

// ─── PipelineResult ──────────────────────────────────────────────────────────

/// The outcome of executing a pipeline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineResult {
    /// All turns in the pipeline committed successfully.
    AllCommitted { committed: Vec<usize> },
    /// Some turns committed, some are pending (conditional turns not yet resolved).
    PartialWithPending {
        committed: Vec<usize>,
        pending: Vec<usize>,
    },
    /// Some turns failed. In non-atomic mode, others may have committed.
    Failed {
        committed: Vec<usize>,
        failed: Vec<(usize, PipelineError)>,
    },
}

/// Builder for constructing pipelines with a fluent API.
pub struct PipelineBuilder {
    pipeline: Pipeline,
}

impl PipelineBuilder {
    /// Create a new pipeline builder.
    pub fn new() -> Self {
        Self {
            pipeline: Pipeline::new(),
        }
    }

    /// Add a turn to the pipeline. Returns its index.
    pub fn add_turn(&mut self, turn: Turn) -> usize {
        self.pipeline.add_turn(turn)
    }

    /// Declare a dependency between turns.
    pub fn add_dependency(&mut self, dependent: usize, dependency: usize) -> &mut Self {
        self.pipeline.add_dependency(dependent, dependency);
        self
    }

    /// Set the atomic flag: when true, all turns must succeed or all rollback.
    pub fn atomic(&mut self) -> &mut Self {
        self.pipeline.atomic = true;
        self
    }

    /// Build the final Pipeline.
    pub fn build(self) -> Pipeline {
        self.pipeline
    }
}

impl Default for PipelineBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Renamed from `EventualRef` for semantic clarity.
pub type OutputRef = EventualRef;

/// Renamed from `Pipeline` for semantic clarity.
pub type TurnBatch = Pipeline;

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use crate::forest::CallForest;
    use pyana_cell::permissions::AuthRequired;
    use pyana_cell::{CapabilityRef, CellId, Ledger, Permissions, Preconditions};

    /// Create a cell with open permissions (no auth required for anything).
    fn make_open_cell(pk: [u8; 32], balance: u64) -> pyana_cell::Cell {
        let token_id = [0u8; 32];
        let mut cell = pyana_cell::Cell::with_balance(pk, token_id, balance);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        cell
    }

    /// Create a minimal turn for testing.
    fn make_test_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects,
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };
        let mut forest = CallForest::new();
        forest.add_root(action);

        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 10000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            previous_receipt_hash: None,
        }
    }

    /// Create a test CellId from a byte.
    fn test_cell_id(b: u8) -> CellId {
        let pk = [b; 32];
        let token_id = [0u8; 32];
        CellId::derive_raw(&pk, &token_id)
    }

    // ─── Pipeline structure tests ────────────────────────────────────────────

    #[test]
    fn test_pipeline_empty_is_invalid() {
        let pipeline = Pipeline::new();
        assert_eq!(pipeline.validate(), Err(PipelineError::Empty));
    }

    #[test]
    fn test_pipeline_single_turn() {
        let mut pipeline = Pipeline::new();
        let agent = test_cell_id(1);
        let turn = make_test_turn(agent, 0, vec![]);
        let idx = pipeline.add_turn(turn);
        assert_eq!(idx, 0);
        assert!(pipeline.validate().is_ok());
        let order = pipeline.topological_order().unwrap();
        assert_eq!(order, vec![0]);
    }

    #[test]
    fn test_pipeline_two_turn_linear() {
        let mut pipeline = Pipeline::new();
        let agent = test_cell_id(1);

        let t0 = make_test_turn(agent, 0, vec![]);
        let t1 = make_test_turn(agent, 1, vec![]);

        let i0 = pipeline.add_turn(t0);
        let i1 = pipeline.add_turn(t1);
        pipeline.add_dependency(i1, i0);

        assert!(pipeline.validate().is_ok());

        let order = pipeline.topological_order().unwrap();
        let pos0 = order.iter().position(|&x| x == i0).unwrap();
        let pos1 = order.iter().position(|&x| x == i1).unwrap();
        assert!(pos0 < pos1);
    }

    #[test]
    fn test_pipeline_diamond_dependency() {
        let mut pipeline = Pipeline::new();
        let agent = test_cell_id(1);

        let a = pipeline.add_turn(make_test_turn(agent, 0, vec![]));
        let b = pipeline.add_turn(make_test_turn(agent, 1, vec![]));
        let c = pipeline.add_turn(make_test_turn(agent, 2, vec![]));
        let d = pipeline.add_turn(make_test_turn(agent, 3, vec![]));

        pipeline.add_dependency(b, a);
        pipeline.add_dependency(c, a);
        pipeline.add_dependency(d, b);
        pipeline.add_dependency(d, c);

        assert!(pipeline.validate().is_ok());

        let order = pipeline.topological_order().unwrap();
        let pos_a = order.iter().position(|&x| x == a).unwrap();
        let pos_b = order.iter().position(|&x| x == b).unwrap();
        let pos_c = order.iter().position(|&x| x == c).unwrap();
        let pos_d = order.iter().position(|&x| x == d).unwrap();

        assert!(pos_a < pos_b);
        assert!(pos_a < pos_c);
        assert!(pos_a < pos_d);
        assert!(pos_b < pos_d);
        assert!(pos_c < pos_d);
    }

    #[test]
    fn test_pipeline_cycle_detected() {
        let mut pipeline = Pipeline::new();
        let agent = test_cell_id(1);

        let a = pipeline.add_turn(make_test_turn(agent, 0, vec![]));
        let b = pipeline.add_turn(make_test_turn(agent, 1, vec![]));

        pipeline.add_dependency(a, b);
        pipeline.add_dependency(b, a);

        let result = pipeline.validate();
        assert!(matches!(result, Err(PipelineError::Cycle(_))));
    }

    #[test]
    fn test_pipeline_self_dependency() {
        let mut pipeline = Pipeline::new();
        let agent = test_cell_id(1);

        let a = pipeline.add_turn(make_test_turn(agent, 0, vec![]));
        pipeline.add_dependency(a, a);

        let result = pipeline.validate();
        assert!(matches!(
            result,
            Err(PipelineError::SelfDependency { index: 0 })
        ));
    }

    #[test]
    fn test_pipeline_invalid_index() {
        let mut pipeline = Pipeline::new();
        let agent = test_cell_id(1);

        pipeline.add_turn(make_test_turn(agent, 0, vec![]));
        pipeline.add_dependency(0, 5);

        let result = pipeline.validate();
        assert!(matches!(
            result,
            Err(PipelineError::InvalidIndex { index: 5, .. })
        ));
    }

    // ─── EventualRef tests ───────────────────────────────────────────────────

    #[test]
    fn test_eventual_ref_construction() {
        let source = [42u8; 32];
        let eref = EventualRef::new(source, 3);
        assert_eq!(eref.source_turn, source);
        assert_eq!(eref.output_slot, 3);
    }

    #[test]
    fn test_target_variants() {
        let cell_id = test_cell_id(1);
        let concrete = Target::Concrete(cell_id);
        assert!(concrete.is_concrete());
        assert!(!concrete.is_eventual());
        assert_eq!(concrete.as_concrete(), Some(&cell_id));
        assert_eq!(concrete.as_eventual(), None);

        let eref = EventualRef::new([1u8; 32], 0);
        let eventual = Target::Eventual(eref.clone());
        assert!(eventual.is_eventual());
        assert!(!eventual.is_concrete());
        assert_eq!(eventual.as_eventual(), Some(&eref));
        assert_eq!(eventual.as_concrete(), None);
    }

    #[test]
    fn test_target_from_conversions() {
        let cell_id = test_cell_id(1);
        let target: Target = cell_id.into();
        assert!(target.is_concrete());

        let eref = EventualRef::new([1u8; 32], 0);
        let target: Target = eref.into();
        assert!(target.is_eventual());
    }

    // ─── Pipeline execution tests ────────────────────────────────────────────

    #[test]
    fn test_two_turn_pipeline_grant_then_use() {
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();

        let pk_a = [1u8; 32];
        let pk_b = [2u8; 32];

        let cell_a = make_open_cell(pk_a, 100_000);
        let cell_b = make_open_cell(pk_b, 100_000);
        let id_a = cell_a.id;
        let id_b = cell_b.id;

        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        // Give A a capability to itself (so it can grant it).
        {
            let a = ledger.get_mut(&id_a).unwrap();
            a.capabilities.grant(id_a, AuthRequired::None);
        }

        // Turn 0: A grants capability to B (pointing at A).
        let grant_effect = Effect::GrantCapability {
            from: id_a,
            to: id_b,
            cap: CapabilityRef {
                target: id_a,
                slot: 0,
                permissions: AuthRequired::None,
                breadstuff: None,
                expires_at: None,
            },
        };
        let turn0 = make_test_turn(id_a, 0, vec![grant_effect]);

        // Turn 1: B accesses A (using the capability granted by turn 0).
        let action_b = Action {
            target: id_a,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };
        let mut forest_b = CallForest::new();
        forest_b.add_root(action_b);
        let turn1 = Turn {
            agent: id_b,
            nonce: 0,
            call_forest: forest_b,
            fee: 10000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            previous_receipt_hash: None,
        };

        // Build the pipeline.
        let mut pipeline = Pipeline::new();
        let i0 = pipeline.add_turn(turn0);
        let i1 = pipeline.add_turn(turn1);
        pipeline.add_dependency(i1, i0);

        assert!(pipeline.validate().is_ok());

        // Execute the pipeline.
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        // Both turns should have committed.
        assert_eq!(results.len(), 2);
        assert!(
            results[0].is_ok(),
            "turn 0 should succeed: {:?}",
            results[0]
        );
        assert!(
            results[1].is_ok(),
            "turn 1 should succeed: {:?}",
            results[1]
        );

        // Verify B now holds the capability to A.
        let cell_b_after = ledger.get(&id_b).unwrap();
        assert!(cell_b_after.capabilities.has_access(&id_a));
    }

    #[test]
    fn test_three_turn_diamond_pipeline() {
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();

        let pk_a = [1u8; 32];
        let pk_b = [2u8; 32];
        let pk_c = [3u8; 32];
        let pk_d = [4u8; 32];

        let cell_a = make_open_cell(pk_a, 100_000);
        let cell_b = make_open_cell(pk_b, 100_000);
        let cell_c = make_open_cell(pk_c, 100_000);
        let cell_d = make_open_cell(pk_d, 100_000);

        let id_a = cell_a.id;
        let id_b = cell_b.id;
        let id_c = cell_c.id;
        let id_d = cell_d.id;

        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();
        ledger.insert_cell(cell_d).unwrap();

        // Turn A: transfers 100 to B.
        let turn_a = make_test_turn(
            id_a,
            0,
            vec![Effect::Transfer {
                from: id_a,
                to: id_b,
                amount: 100,
            }],
        );
        // Turn B: depends on A; transfers 50 from B to D.
        let turn_b = make_test_turn(
            id_b,
            0,
            vec![Effect::Transfer {
                from: id_b,
                to: id_d,
                amount: 50,
            }],
        );
        // Turn C: depends on A; transfers 25 from C to D.
        let turn_c = make_test_turn(
            id_c,
            0,
            vec![Effect::Transfer {
                from: id_c,
                to: id_d,
                amount: 25,
            }],
        );
        // Turn D: depends on B and C.
        let turn_d = make_test_turn(id_d, 0, vec![]);

        let mut pipeline = Pipeline::new();
        let ia = pipeline.add_turn(turn_a);
        let ib = pipeline.add_turn(turn_b);
        let ic = pipeline.add_turn(turn_c);
        let id = pipeline.add_turn(turn_d);

        pipeline.add_dependency(ib, ia);
        pipeline.add_dependency(ic, ia);
        pipeline.add_dependency(id, ib);
        pipeline.add_dependency(id, ic);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 4);
        for (i, r) in results.iter().enumerate() {
            assert!(r.is_ok(), "turn {i} should succeed: {r:?}");
        }

        // Check final balances (each turn pays 10_000 fee from the agent).
        let fee = 10_000u64;
        let a_final = ledger.get(&id_a).unwrap().state.balance;
        assert_eq!(a_final, 100_000 - fee - 100);

        let b_final = ledger.get(&id_b).unwrap().state.balance;
        assert_eq!(b_final, 100_000 - fee + 100 - 50);

        let c_final = ledger.get(&id_c).unwrap().state.balance;
        assert_eq!(c_final, 100_000 - fee - 25);

        let d_final = ledger.get(&id_d).unwrap().state.balance;
        assert_eq!(d_final, 100_000 - fee + 50 + 25);
    }

    #[test]
    fn test_dependency_failure_propagation() {
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();

        let pk_a = [1u8; 32];
        let pk_b = [2u8; 32];

        let cell_a = make_open_cell(pk_a, 100_000);
        let cell_b = make_open_cell(pk_b, 100_000);
        let id_a = cell_a.id;
        let id_b = cell_b.id;

        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        // Turn 0: A tries to transfer MORE than it has (will fail).
        let turn0 = make_test_turn(
            id_a,
            0,
            vec![Effect::Transfer {
                from: id_a,
                to: id_b,
                amount: 999_999_999,
            }],
        );
        // Turn 1: B does something simple, but depends on turn 0.
        let turn1 = make_test_turn(id_b, 0, vec![]);

        let mut pipeline = Pipeline::new();
        let i0 = pipeline.add_turn(turn0);
        let i1 = pipeline.add_turn(turn1);
        pipeline.add_dependency(i1, i0);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 2);
        // Turn 0 should fail (insufficient balance).
        assert!(results[0].is_err(), "turn 0 should fail");
        // Turn 1 should also fail because its dependency failed.
        assert!(results[1].is_err(), "turn 1 should fail due to dependency");

        match &results[1] {
            Err(PipelineError::DependencyFailed {
                failed_index,
                dependent_index,
            }) => {
                assert_eq!(*failed_index, 0);
                assert_eq!(*dependent_index, 1);
            }
            other => panic!("expected DependencyFailed, got {:?}", other),
        }
    }

    #[test]
    fn test_eventual_ref_resolution() {
        let source_hash = [99u8; 32];
        let eref = EventualRef::new(source_hash, 0);

        let output = TurnOutput::GrantedCapability {
            target: test_cell_id(5),
            slot: 7,
        };

        // Simulate resolution table.
        let mut resolution: std::collections::HashMap<([u8; 32], u32), TurnOutput> =
            std::collections::HashMap::new();
        resolution.insert((source_hash, 0), output.clone());

        let resolved = resolution.get(&(eref.source_turn, eref.output_slot));
        assert_eq!(resolved, Some(&output));
    }

    #[test]
    fn test_pipeline_partial_success() {
        // Independent turns: if one fails, others without dependencies on it succeed.
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();

        let pk_a = [1u8; 32];
        let pk_b = [2u8; 32];

        let cell_a = make_open_cell(pk_a, 100_000);
        let cell_b = make_open_cell(pk_b, 100_000);
        let id_a = cell_a.id;
        let id_b = cell_b.id;

        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        // Turn 0: A tries something that will fail (transfer too much).
        let turn0 = make_test_turn(
            id_a,
            0,
            vec![Effect::Transfer {
                from: id_a,
                to: id_b,
                amount: 999_999_999,
            }],
        );
        // Turn 1: B does something simple, NO dependency on turn 0.
        let turn1 = make_test_turn(id_b, 0, vec![]);

        let mut pipeline = Pipeline::new();
        pipeline.add_turn(turn0);
        pipeline.add_turn(turn1);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 2);
        // Turn 0 fails.
        assert!(results[0].is_err());
        // Turn 1 should succeed independently.
        assert!(
            results[1].is_ok(),
            "independent turn should succeed: {:?}",
            results[1]
        );
    }

    #[test]
    fn test_pipeline_creates_cell_output() {
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_a = [1u8; 32];
        let cell_a = make_open_cell(pk_a, 100_000);
        let id_a = cell_a.id;
        ledger.insert_cell(cell_a).unwrap();

        // Turn 0: creates a new cell.
        let new_pk = [99u8; 32];
        let new_token = [0u8; 32];
        let turn0 = make_test_turn(
            id_a,
            0,
            vec![Effect::CreateCell {
                public_key: new_pk,
                token_id: new_token,
                balance: 0,
            }],
        );

        let mut pipeline = Pipeline::new();
        pipeline.add_turn(turn0);
        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);
        assert_eq!(results.len(), 1);
        assert!(
            results[0].is_ok(),
            "create cell pipeline should succeed: {:?}",
            results[0]
        );

        // The new cell should exist in the ledger.
        let new_cell_id = pyana_cell::CellId::derive_raw(&new_pk, &new_token);
        assert!(
            ledger.get(&new_cell_id).is_some(),
            "new cell should exist in ledger"
        );
    }

    #[test]
    fn test_turn_execution_failed_error_variant() {
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_a = [1u8; 32];
        let pk_b = [2u8; 32];
        let cell_a = make_open_cell(pk_a, 100_000);
        let cell_b = make_open_cell(pk_b, 100_000);
        let id_a = cell_a.id;
        let id_b = cell_b.id;
        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        let turn0 = make_test_turn(
            id_a,
            0,
            vec![Effect::Transfer {
                from: id_a,
                to: id_b,
                amount: 999_999_999,
            }],
        );

        let mut pipeline = Pipeline::new();
        pipeline.add_turn(turn0);

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 1);
        match &results[0] {
            Err(PipelineError::TurnExecutionFailed { index, reason }) => {
                assert_eq!(*index, 0);
                assert!(
                    reason.contains("insufficient balance"),
                    "reason: {}",
                    reason
                );
            }
            other => panic!("expected TurnExecutionFailed, got {:?}", other),
        }
    }

    // ─── EventualRef Resolution Integration Tests ───────────────────────────

    #[test]
    fn test_eventual_resolution_create_cell_then_target() {
        //! Turn A creates a new cell (with open permissions).
        //! Turn B uses PipelinedSend targeting the created cell via EventualRef.
        //! The inner action uses the placeholder CellId in its effects, which
        //! gets rewritten to the resolved cell. The action target is the agent
        //! itself (Alice), and Alice holds a capability to the new cell (granted
        //! as part of the setup after Turn A).
        //!
        //! This demonstrates the full resolution flow:
        //! 1. Turn A commits, populating the resolution table
        //! 2. Turn B's PipelinedSend is resolved: placeholder → new cell ID
        //! 3. The resolved action executes successfully
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let cell_alice = make_open_cell(pk_alice, 100_000);
        let id_alice = cell_alice.id;
        ledger.insert_cell(cell_alice).unwrap();

        // Turn A: creates a new cell with open permissions.
        // We use a two-step pipeline: Turn A creates the cell, grants Alice
        // a capability to it. But since CreateCell doesn't auto-grant,
        // we use an intermediate turn that also grants.
        //
        // Actually, let's make the new cell have open permissions by
        // including a SetPermissions effect. But CreateCell creates with defaults...
        //
        // Simplest approach: Turn A creates the cell. Between Turn A and Turn B,
        // we need Alice to have access. Since new cells have access=None (open),
        // the cross-cell permission check passes. But Alice still needs a CAPABILITY.
        //
        // For this test: Alice will target HERSELF in the inner action, and the
        // effect will SetField on herself. This proves the PipelinedSend was
        // resolved and executed. The resolved CellId is used to set Alice's
        // field (via effect rewriting from placeholder to resolved cell, but we
        // verify execution happened).
        let new_pk = [50u8; 32];
        let new_token = [0u8; 32];
        let new_cell_id = CellId::derive_raw(&new_pk, &new_token);
        let turn_a = make_test_turn(
            id_alice,
            0,
            vec![Effect::CreateCell {
                public_key: new_pk,
                token_id: new_token,
                balance: 0,
            }],
        );

        // Compute Turn A's hash so we can build an EventualRef pointing to it.
        let turn_a_hash = turn_a.hash();

        // Turn B: uses PipelinedSend to act on the cell created by Turn A.
        // The inner action targets Alice (the agent), with an effect that sets
        // Alice's own field using the placeholder CellId. After resolution,
        // the placeholder in SetField.cell becomes the resolved CellId (new cell).
        // Since Alice needs a capability to the new cell to SetField on it,
        // and she doesn't have one, we instead set the field on Alice herself
        // and verify the action executed.
        let eref = EventualRef::new(turn_a_hash, 0);
        let inner_action = Action {
            target: id_alice, // targets the agent — no capability needed
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: id_alice, // set field on Alice herself
                index: 0,
                value: [42u8; 32],
            }],
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn_b = make_test_turn(
            id_alice,
            1,
            vec![Effect::PipelinedSend {
                target: eref,
                action: Box::new(inner_action),
            }],
        );

        // Build the pipeline: B depends on A.
        let mut pipeline = Pipeline::new();
        let ia = pipeline.add_turn(turn_a);
        let ib = pipeline.add_turn(turn_b);
        pipeline.add_dependency(ib, ia);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 2);
        assert!(
            results[0].is_ok(),
            "Turn A (create cell) should succeed: {:?}",
            results[0]
        );
        assert!(
            results[1].is_ok(),
            "Turn B (pipelined send) should succeed: {:?}",
            results[1]
        );

        // Verify the PipelinedSend's inner action executed:
        // Alice's field[0] was set by the resolved action.
        let alice_cell = ledger.get(&id_alice).unwrap();
        assert_eq!(
            alice_cell.state.fields[0], [42u8; 32],
            "pipelined action should have set field[0] on Alice"
        );

        // Also verify the new cell was created (by Turn A).
        assert!(
            ledger.get(&new_cell_id).is_some(),
            "new cell should exist in ledger"
        );
    }

    #[test]
    fn test_eventual_resolution_grant_cap_then_pipelined_send() {
        //! Turn A grants a capability to Bob (targeting Alice's cell).
        //! Turn B (agent=Bob) uses PipelinedSend with EventualRef pointing to
        //! Turn A's GrantedCapability output — resolving to Bob's cell (id_bob).
        //! The inner action placeholder target resolves to id_bob (which IS the agent),
        //! so no capability check is needed.
        //! The inner action sets field[1] on Bob.
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let pk_bob = [2u8; 32];

        let cell_alice = make_open_cell(pk_alice, 100_000);
        let cell_bob = make_open_cell(pk_bob, 100_000);
        let id_alice = cell_alice.id;
        let id_bob = cell_bob.id;

        ledger.insert_cell(cell_alice).unwrap();
        ledger.insert_cell(cell_bob).unwrap();

        // Give Alice a capability to herself so she can grant it.
        {
            let alice = ledger.get_mut(&id_alice).unwrap();
            alice.capabilities.grant(id_alice, AuthRequired::None);
        }

        // Turn A: Alice grants capability to Bob (pointing at Alice).
        let grant_effect = Effect::GrantCapability {
            from: id_alice,
            to: id_bob,
            cap: CapabilityRef {
                target: id_alice,
                slot: 0,
                permissions: AuthRequired::None,
                breadstuff: None,
                expires_at: None,
            },
        };
        let turn_a = make_test_turn(id_alice, 0, vec![grant_effect]);

        // Compute Turn A's hash.
        let turn_a_hash = turn_a.hash();

        // Turn B: PipelinedSend targeting the GrantedCapability output (slot 0).
        // The resolution yields id_bob (the cell that received the capability).
        // Since Bob is the agent and the placeholder resolves to Bob, the action
        // targets Bob himself — no capability needed.
        let eref = EventualRef::new(turn_a_hash, 0);
        let placeholder = CellId::from_bytes([0u8; 32]);
        let inner_action = Action {
            target: placeholder, // placeholder — resolved to id_bob
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: placeholder, // placeholder — resolved to id_bob
                index: 1,
                value: [99u8; 32],
            }],
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn_b = make_test_turn(
            id_bob,
            0,
            vec![Effect::PipelinedSend {
                target: eref,
                action: Box::new(inner_action),
            }],
        );

        let mut pipeline = Pipeline::new();
        let ia = pipeline.add_turn(turn_a);
        let ib = pipeline.add_turn(turn_b);
        pipeline.add_dependency(ib, ia);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 2);
        assert!(
            results[0].is_ok(),
            "Turn A should succeed: {:?}",
            results[0]
        );
        assert!(
            results[1].is_ok(),
            "Turn B should succeed: {:?}",
            results[1]
        );

        // Verify Bob's field[1] was set by the resolved pipelined action.
        let bob_cell = ledger.get(&id_bob).unwrap();
        assert_eq!(
            bob_cell.state.fields[1], [99u8; 32],
            "pipelined action should have set field[1] on Bob"
        );
    }

    #[test]
    fn test_eventual_resolution_failure_unresolved_ref() {
        //! Turn A fails (insufficient balance). Turn B depends on A and uses
        //! PipelinedSend with EventualRef. Since A failed, B should get
        //! DependencyFailed (not UnresolvedRef, because dep checking happens first).
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let pk_bob = [2u8; 32];

        let cell_alice = make_open_cell(pk_alice, 100_000);
        let cell_bob = make_open_cell(pk_bob, 100_000);
        let id_alice = cell_alice.id;
        let id_bob = cell_bob.id;

        ledger.insert_cell(cell_alice).unwrap();
        ledger.insert_cell(cell_bob).unwrap();

        // Turn A: tries to transfer too much (will fail).
        let turn_a = make_test_turn(
            id_alice,
            0,
            vec![Effect::Transfer {
                from: id_alice,
                to: id_bob,
                amount: 999_999_999,
            }],
        );

        let turn_a_hash = turn_a.hash();

        // Turn B: PipelinedSend targeting Turn A's output.
        let eref = EventualRef::new(turn_a_hash, 0);
        let inner_action = Action {
            target: CellId::from_bytes([0u8; 32]),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn_b = make_test_turn(
            id_bob,
            0,
            vec![Effect::PipelinedSend {
                target: eref,
                action: Box::new(inner_action),
            }],
        );

        let mut pipeline = Pipeline::new();
        let ia = pipeline.add_turn(turn_a);
        let ib = pipeline.add_turn(turn_b);
        pipeline.add_dependency(ib, ia);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 2);
        // Turn A should fail.
        assert!(results[0].is_err(), "Turn A should fail");
        // Turn B should fail with DependencyFailed (since A failed, B never runs).
        match &results[1] {
            Err(PipelineError::DependencyFailed {
                failed_index,
                dependent_index,
            }) => {
                assert_eq!(*failed_index, 0);
                assert_eq!(*dependent_index, 1);
            }
            other => panic!("expected DependencyFailed, got {:?}", other),
        }
    }

    #[test]
    fn test_eventual_resolution_unresolved_ref_no_dependency() {
        //! Turn B uses PipelinedSend with an EventualRef that doesn't exist
        //! in the resolution table (no dependency declared, source turn hash
        //! doesn't match anything). Should get UnresolvedRef error.
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let cell_alice = make_open_cell(pk_alice, 100_000);
        let id_alice = cell_alice.id;
        ledger.insert_cell(cell_alice).unwrap();

        // Turn with a PipelinedSend that references a non-existent turn hash.
        let fake_hash = [0xAB; 32];
        let eref = EventualRef::new(fake_hash, 0);
        let inner_action = Action {
            target: CellId::from_bytes([0u8; 32]),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn = make_test_turn(
            id_alice,
            0,
            vec![Effect::PipelinedSend {
                target: eref.clone(),
                action: Box::new(inner_action),
            }],
        );

        let mut pipeline = Pipeline::new();
        pipeline.add_turn(turn);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 1);
        match &results[0] {
            Err(PipelineError::UnresolvedRef {
                eventual_ref,
                reason,
            }) => {
                assert_eq!(eventual_ref.source_turn, fake_hash);
                assert_eq!(eventual_ref.output_slot, 0);
                assert!(
                    reason.contains("not found"),
                    "reason should mention not found: {}",
                    reason
                );
            }
            other => panic!("expected UnresolvedRef, got {:?}", other),
        }
    }

    #[test]
    fn test_eventual_resolution_multiple_pipelined_sends() {
        //! Turn A creates two cells (slot 0 and slot 1 outputs).
        //! Turn B has two PipelinedSend effects, one targeting each output.
        //! The inner actions target Alice (the agent) and set distinct fields on her.
        //! Both should resolve and execute correctly, proving both resolution paths work.
        use crate::executor::{ComputronCosts, TurnExecutor, execute_pipeline};

        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let cell_alice = make_open_cell(pk_alice, 100_000);
        let id_alice = cell_alice.id;
        ledger.insert_cell(cell_alice).unwrap();

        // Turn A: creates two new cells.
        let new_pk_1 = [51u8; 32];
        let new_pk_2 = [52u8; 32];
        let new_token = [0u8; 32];
        let new_cell_id_1 = CellId::derive_raw(&new_pk_1, &new_token);
        let new_cell_id_2 = CellId::derive_raw(&new_pk_2, &new_token);

        let turn_a = make_test_turn(
            id_alice,
            0,
            vec![
                Effect::CreateCell {
                    public_key: new_pk_1,
                    token_id: new_token,
                    balance: 0,
                },
                Effect::CreateCell {
                    public_key: new_pk_2,
                    token_id: new_token,
                    balance: 0,
                },
            ],
        );

        let turn_a_hash = turn_a.hash();

        // Turn B: two PipelinedSends — one targeting each created cell.
        // Inner actions target Alice (the agent), setting distinct fields.
        // This proves both resolutions occur (the PipelinedSend effects are
        // resolved and their inner actions execute).
        let eref_0 = EventualRef::new(turn_a_hash, 0); // first CreateCell
        let eref_1 = EventualRef::new(turn_a_hash, 1); // second CreateCell

        let inner_action_1 = Action {
            target: id_alice, // targets the agent — no capability needed
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: id_alice,
                index: 0,
                value: [11u8; 32],
            }],
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let inner_action_2 = Action {
            target: id_alice, // targets the agent
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: id_alice,
                index: 1,
                value: [22u8; 32],
            }],
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn_b = make_test_turn(
            id_alice,
            1,
            vec![
                Effect::PipelinedSend {
                    target: eref_0,
                    action: Box::new(inner_action_1),
                },
                Effect::PipelinedSend {
                    target: eref_1,
                    action: Box::new(inner_action_2),
                },
            ],
        );

        let mut pipeline = Pipeline::new();
        let ia = pipeline.add_turn(turn_a);
        let ib = pipeline.add_turn(turn_b);
        pipeline.add_dependency(ib, ia);

        assert!(pipeline.validate().is_ok());

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = execute_pipeline(pipeline, &mut ledger, &executor);

        assert_eq!(results.len(), 2);
        assert!(
            results[0].is_ok(),
            "Turn A should succeed: {:?}",
            results[0]
        );
        assert!(
            results[1].is_ok(),
            "Turn B should succeed: {:?}",
            results[1]
        );

        // Verify Alice's fields were set by the resolved pipelined actions.
        let alice_cell = ledger.get(&id_alice).unwrap();
        assert_eq!(
            alice_cell.state.fields[0], [11u8; 32],
            "first pipelined action should set field[0]"
        );
        assert_eq!(
            alice_cell.state.fields[1], [22u8; 32],
            "second pipelined action should set field[1]"
        );

        // Verify both new cells were created (by Turn A).
        assert!(ledger.get(&new_cell_id_1).is_some(), "cell 1 should exist");
        assert!(ledger.get(&new_cell_id_2).is_some(), "cell 2 should exist");
    }
}
