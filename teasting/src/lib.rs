//! `pyana-teasting`: Integration test simulation suite.
//!
//! "Tease testing" — if it wasn't a test it would be the live chain.
//!
//! This crate provides a multi-node simulation harness for end-to-end testing of
//! pyana's authorization, consensus, and privacy systems. Unlike the unit tests in
//! individual crates (circuit, turn, federation), these tests exercise complete flows:
//!
//! - Token lifecycle: mint → attenuate → delegate → present → verify
//! - Proof round-trips: prove → serialize → transmit → deserialize → verify
//! - Cross-federation interactions: atomic swaps, note bridges
//! - Consensus liveness: N nodes reach agreement, finalize blocks
//! - Privacy guarantees: unlinkability, non-correlation across presentations
//! - Soundness: forge attempts MUST fail
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    SimulationHarness                                  │
//! │                                                                      │
//! │  ┌──────────────┐                         ┌──────────────────────┐  │
//! │  │ SimFederation│  (in-process gossip)     │ SimFederation        │  │
//! │  │  ┌────────┐  │◄──────────────────────►  │  ┌────────┐         │  │
//! │  │  │SimNode │  │                          │  │SimNode │         │  │
//! │  │  │SimNode │  │                          │  │SimNode │         │  │
//! │  │  │SimNode │  │                          │  └────────┘         │  │
//! │  │  └────────┘  │                          └──────────────────────┘  │
//! │  └──────────────┘                                                    │
//! │                                                                      │
//! │  ┌──────────────────────────────────────────────────────────────┐   │
//! │  │ SimAgents: wallet + actions + proof generation                │   │
//! │  └──────────────────────────────────────────────────────────────┘   │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```

pub mod agent;
pub mod assertions;
pub mod captp_sim;
pub mod fault;
pub mod federation;
pub mod harness;
pub mod mesh_sim;
pub mod router_sim;
