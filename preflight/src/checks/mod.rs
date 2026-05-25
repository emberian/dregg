pub mod apps;
pub mod backends;
pub mod blocklace;
pub mod boot;
pub mod bridges;
pub mod caps;
pub mod captp;
pub mod cells;
pub mod cli;
pub mod composition;
pub mod demo_agent;
pub mod effect_vm;
pub mod federation;
pub mod intents;
pub mod nameservice;
pub mod node;
pub mod privacy;
pub mod proofs;
pub mod relay;
pub mod routing;
pub mod solver;
pub mod sovereign;
pub mod storage;
pub mod turns;
pub mod wire;

// Preflight gate for the substrate-correctness mandate: lightweight
// sanity checks that the cell-side StateConstraint evaluator and the
// γ.2 canonical id derivations behave as documented. If these fail,
// none of the heavier substrate tests are worth running.
pub mod state_constraints;

// Preflight: bridge phase-log + portable-note sanity checks. Smoke
// tests for `pyana_cell::note_bridge` invariants. Separate from
// `bridges.rs` (Mina bridge state machine).
pub mod note_bridge;
