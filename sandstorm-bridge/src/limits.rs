//! **L4 — resource bounds.** A grain runs only within what its funded lease
//! authorizes; it cannot exhaust the host.
//!
//! Sandstorm bounds a grain loosely (idle-shutdown frees RAM after ~90 s). the hosting substrate
//! bounds it *economically*: a workload runs only under a **funded lease**
//! (`bridge/src/lib.rs::Lease::funded`, "no run beyond what the lease authorizes"),
//! and every metered resource is charged against that lease. When a bound is hit the
//! grain is refused/reaped — a hostile `.spk` cannot run unmetered, fork-bomb the CPU,
//! balloon memory, or fill the disk.
//!
//! This module is the lease's resource ledger: four independent quotas (uptime,
//! CPU-ms, peak memory, stored bytes), each `Option`al — `None` = unbounded (the
//! default a detached spike uses; **a real deployment always supplies a bounded,
//! funded lease**). A charge that would exceed a bound returns [`LeaseError::Exhausted`]
//! and does *not* apply, so the refusal is fail-closed.

use serde::{Deserialize, Serialize};

/// Which resource a charge concerns (and which quota was exhausted on refusal).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResourceKind {
    /// Wall-clock periods the grain has been `Running` (the StandingObligation tick).
    Uptime,
    /// CPU milliseconds consumed.
    Cpu,
    /// Peak resident memory (a high-water bound, not cumulative).
    Memory,
    /// Bytes stored in the grain's umem heap (`/var`).
    Storage,
}

/// A resource bound was exceeded; the operation is refused and not applied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeaseError {
    pub kind: ResourceKind,
    /// The quota that was exceeded.
    pub limit: u64,
    /// What the charge would have brought the usage to.
    pub attempted: u64,
}

impl std::fmt::Display for LeaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "lease exhausted: {:?} would reach {} > limit {}",
            self.kind, self.attempted, self.limit
        )
    }
}
impl std::error::Error for LeaseError {}

/// A grain's resource lease: the bounds the funded lease authorizes plus the usage
/// charged so far. Each quota is `Option<u64>` (`None` = unbounded).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResourceLease {
    pub uptime_limit: Option<u64>,
    pub cpu_ms_limit: Option<u64>,
    pub mem_bytes_limit: Option<u64>,
    pub storage_bytes_limit: Option<u64>,

    uptime_used: u64,
    cpu_ms_used: u64,
    mem_bytes_peak: u64,
    storage_bytes_now: u64,
}

impl Default for ResourceLease {
    fn default() -> Self {
        Self::unbounded()
    }
}

impl ResourceLease {
    /// An unbounded lease — the detached-spike / legacy default. Real deployments
    /// never use this; they call [`bounded`](Self::bounded) with the funded quotas.
    pub fn unbounded() -> Self {
        ResourceLease {
            uptime_limit: None,
            cpu_ms_limit: None,
            mem_bytes_limit: None,
            storage_bytes_limit: None,
            uptime_used: 0,
            cpu_ms_used: 0,
            mem_bytes_peak: 0,
            storage_bytes_now: 0,
        }
    }

    /// A lease bounded by what a funded lease authorizes.
    pub fn bounded(uptime: u64, cpu_ms: u64, mem_bytes: u64, storage_bytes: u64) -> Self {
        ResourceLease {
            uptime_limit: Some(uptime),
            cpu_ms_limit: Some(cpu_ms),
            mem_bytes_limit: Some(mem_bytes),
            storage_bytes_limit: Some(storage_bytes),
            uptime_used: 0,
            cpu_ms_used: 0,
            mem_bytes_peak: 0,
            storage_bytes_now: 0,
        }
    }

    fn check(kind: ResourceKind, limit: Option<u64>, attempted: u64) -> Result<(), LeaseError> {
        match limit {
            Some(l) if attempted > l => Err(LeaseError {
                kind,
                limit: l,
                attempted,
            }),
            _ => Ok(()),
        }
    }

    /// Charge `periods` of uptime. Refused (and not applied) if it would exceed the
    /// uptime quota — the grain has outrun its funded lease and must be reaped.
    pub fn charge_uptime(&mut self, periods: u64) -> Result<u64, LeaseError> {
        let attempted = self.uptime_used.saturating_add(periods);
        Self::check(ResourceKind::Uptime, self.uptime_limit, attempted)?;
        self.uptime_used = attempted;
        Ok(self.uptime_used)
    }

    /// Charge `ms` of CPU. Refused if it would exceed the CPU quota (a fork-bomb /
    /// busy-loop grain cannot run unmetered).
    pub fn charge_cpu(&mut self, ms: u64) -> Result<u64, LeaseError> {
        let attempted = self.cpu_ms_used.saturating_add(ms);
        Self::check(ResourceKind::Cpu, self.cpu_ms_limit, attempted)?;
        self.cpu_ms_used = attempted;
        Ok(self.cpu_ms_used)
    }

    /// Observe `peak_bytes` of resident memory. Refused if it exceeds the memory
    /// quota — a memory-ballooning grain is over budget (the OOM-cap).
    pub fn observe_mem(&mut self, peak_bytes: u64) -> Result<u64, LeaseError> {
        Self::check(ResourceKind::Memory, self.mem_bytes_limit, peak_bytes)?;
        if peak_bytes > self.mem_bytes_peak {
            self.mem_bytes_peak = peak_bytes;
        }
        Ok(self.mem_bytes_peak)
    }

    /// Admit a new total stored size of `bytes` for the grain's `/var`. Refused if it
    /// exceeds the storage quota — a hostile grain cannot fill the host disk; the
    /// write that would breach the quota is rejected (fail-closed) and the caller must
    /// not persist it.
    pub fn admit_storage(&mut self, bytes: u64) -> Result<u64, LeaseError> {
        Self::check(ResourceKind::Storage, self.storage_bytes_limit, bytes)?;
        self.storage_bytes_now = bytes;
        Ok(self.storage_bytes_now)
    }

    pub fn uptime_used(&self) -> u64 {
        self.uptime_used
    }
    pub fn cpu_ms_used(&self) -> u64 {
        self.cpu_ms_used
    }
    pub fn mem_bytes_peak(&self) -> u64 {
        self.mem_bytes_peak
    }
    pub fn storage_bytes_now(&self) -> u64 {
        self.storage_bytes_now
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unbounded_lease_never_refuses() {
        let mut l = ResourceLease::unbounded();
        assert_eq!(l.charge_uptime(1_000_000).unwrap(), 1_000_000);
        assert_eq!(l.charge_cpu(1_000_000).unwrap(), 1_000_000);
        assert!(l.observe_mem(1 << 40).is_ok());
        assert!(l.admit_storage(1 << 40).is_ok());
    }

    #[test]
    fn uptime_beyond_the_lease_is_refused() {
        let mut l = ResourceLease::bounded(3, u64::MAX, u64::MAX, u64::MAX);
        assert_eq!(l.charge_uptime(2).unwrap(), 2);
        // The next tick would reach 4 > 3 — refused, and NOT applied.
        let err = l.charge_uptime(2).unwrap_err();
        assert_eq!(err.kind, ResourceKind::Uptime);
        assert_eq!(l.uptime_used(), 2);
    }

    #[test]
    fn a_cpu_busy_loop_is_capped() {
        let mut l = ResourceLease::bounded(u64::MAX, 500, u64::MAX, u64::MAX);
        l.charge_cpu(400).unwrap();
        assert_eq!(l.charge_cpu(200).unwrap_err().kind, ResourceKind::Cpu);
        // Usage stayed at the last admitted value — the refused charge did not apply.
        assert_eq!(l.cpu_ms_used(), 400);
    }

    #[test]
    fn a_memory_balloon_is_capped() {
        let mut l = ResourceLease::bounded(u64::MAX, u64::MAX, 64 * 1024 * 1024, u64::MAX);
        assert!(l.observe_mem(32 * 1024 * 1024).is_ok());
        assert_eq!(
            l.observe_mem(128 * 1024 * 1024).unwrap_err().kind,
            ResourceKind::Memory
        );
        // The peak high-water stayed at the last admitted observation.
        assert_eq!(l.mem_bytes_peak(), 32 * 1024 * 1024);
    }

    #[test]
    fn a_disk_filling_grain_is_capped() {
        let mut l = ResourceLease::bounded(u64::MAX, u64::MAX, u64::MAX, 1024);
        assert!(l.admit_storage(512).is_ok());
        // A write that would push `/var` past 1 KiB is refused (fail-closed).
        assert_eq!(
            l.admit_storage(4096).unwrap_err().kind,
            ResourceKind::Storage
        );
        assert_eq!(l.storage_bytes_now(), 512);
    }
}
