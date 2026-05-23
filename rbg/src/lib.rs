//! Robigalia-inspired designs mapped to pyana's distributed capability runtime.
//!
//! This crate explores how OS-level abstractions (VFS, volumes, blobs) translate
//! into a content-addressed, capability-secure, proof-generating distributed system.

pub mod directory;
pub mod routing;
pub mod vfs;
