//! **THE DURABLE-IMAGE WELD for the windowed desktop** — make "your world is one
//! durable image" LITERALLY TRUE for `--desktop`.
//!
//! The headline claim of deos is that your world is a single durable, verifiable
//! image: close it, reopen it, land EXACTLY where you were — every cell, balance,
//! receipt, every verified turn. The login/cockpit path already lives that (see
//! [`crate::session::open_session_world`], over [`World::open_recovering`]). The
//! windowed desktop (`run_desktop_window`) did NOT: it booted `world::demo_world()`
//! FRESH every launch, so only the layout sidecar (window positions) persisted —
//! the World itself was thrown away and re-seeded each boot. This module closes
//! that gap by giving the desktop the SAME durable spine, mirroring the session
//! front door exactly.
//!
//! # What this does (and does NOT rebuild)
//!
//! It builds NO persistence — the substrate is [`crate::persistence`] (redb commit
//! log + genesis mirror + fail-closed convergence) and [`World::open`] /
//! [`World::open_recovering`] (recover → re-execute → verify, then attach the store
//! so every future `commit_turn` dual-writes). This module is only the BOOT policy
//! for the desktop's World:
//!
//!   * **Ephemeral escape hatch** ([`WorldImageSpec::Ephemeral`]) — the OLD
//!     `world::demo_world()` behavior verbatim, for bakes / tests / CI (hermetic +
//!     deterministic). The `--render-woven` bake routes here; it stays ephemeral.
//!   * **Durable image** ([`WorldImageSpec::Durable`]) — open (recovering) the redb
//!     image beside the layout sidecar. On an EMPTY image (first run) it seeds the
//!     demo genesis + drives all 5 [`crate::world::DemoSeed`] turns ONTO the durable
//!     world so they PERSIST (genesis mirrored via `record_genesis`, turns
//!     dual-written) — the newcomer still gets the warm demo world, now durable. On
//!     a RECOVERED image it uses it as-is and re-derives the anchor ids
//!     deterministically (they are content-addresses of the fixed demo seeds).
//!
//! # Honest fallbacks (never strand, never silently wipe)
//!
//!   * A torn/divergent image is RECOVERED (the divergent tail truncated to the last
//!     consistent state) rather than refused — [`World::open_recovering`] does this;
//!     the drop count is reported. `OpenError::Divergent` never reaches the owner.
//!   * A wholly-unsalvageable store is QUARANTINED aside (kept for forensics, never
//!     deleted) and a fresh durable image is provisioned in its place — loud warning,
//!     never a silent wipe ([`BootOrigin::FreshAfterUnsalvageable`]).
//!   * If even a fresh provision fails (an unwritable disk/path), the desktop falls
//!     back to an EPHEMERAL demo world so the window still opens — loudly warned that
//!     this session will not persist ([`BootOrigin::EphemeralFallback`]).
//!
//! # Costs — the byte-identical-receipt constraint
//!
//! `demo_genesis` / the demo `DemoSeed` turns commit under [`ComputronCosts::zero`]
//! (the demo desktop meters free; see [`crate::world::demo_genesis_at`], which builds
//! its world with `World::with_costs_and_timestamp(ComputronCosts::zero(), …)`). The
//! receipts re-derive bit-identically only under the SAME cost model, so the durable
//! open MUST use the same zero costs — this module hard-codes it ([`DEMO_COSTS`])
//! rather than exposing it, so a caller cannot pass a mismatching model.
//!
//! The wall-clock, by contrast, need NOT be pinned across reopens: the timestamp is
//! folded into receipts (hence the per-agent receipt-chain head — which lives in the
//! executor's map, `World::chain_head`, NOT in cell state), so it does NOT enter the
//! `canonical_ledger_root` (cells only). Reopening at a different `now_unix()` still
//! CONVERGES — exactly the property the production session path relies on. So the
//! durable open uses the default [`World::open`] (`now_unix`), matching
//! `open_session_world`.
//!
//! gpui-free and `cargo test`-able — the caller (`main::run_desktop_window`) only
//! parses CLI/env into a [`WorldImageSpec`] and renders the returned [`DurableBoot`].

use std::path::PathBuf;

use dregg_cell::CellId;
use dregg_turn::ComputronCosts;

use crate::persistence::OpenError;
use crate::world::{self, World};

/// The demo desktop's cost model — the receipts re-derive bit-identically only under
/// the SAME `ComputronCosts` the image was committed with, and the demo genesis + its
/// seed turns commit under [`ComputronCosts::zero`] (`demo_genesis_at` builds its
/// world with `with_costs_and_timestamp(ComputronCosts::zero(), …)`). Hard-coded so
/// the durable open can never mismatch what the seed committed under.
fn demo_costs() -> ComputronCosts {
    ComputronCosts::zero()
}

/// Where the windowed desktop's World lives — the resolved choice a caller parses
/// from `--world-image` / `--fresh-world` / `DEOS_WORLD_IMAGE` (see
/// `main::resolve_world_image_spec`).
#[derive(Debug, Clone)]
pub enum WorldImageSpec {
    /// A DURABLE redb image at `path`. Opened recovering (never strands); an empty
    /// image is seeded with the demo world (which then persists). `fresh = true`
    /// (the `--fresh-world` override) quarantines any existing image aside first and
    /// provisions a brand-new durable world.
    Durable { path: PathBuf, fresh: bool },
    /// The EPHEMERAL in-RAM demo world (`world::demo_world()`) — the old behavior,
    /// kept for the `:memory:` / `ephemeral` escape hatch so bakes / tests / CI stay
    /// hermetic and deterministic (never touch disk).
    Ephemeral,
}

/// How the desktop's World was obtained — the honest provenance for the startup
/// report (durable vs ephemeral, the image path, recovered vs seeded).
#[derive(Debug, Clone)]
pub enum BootOrigin {
    /// The ephemeral in-RAM demo world (`:memory:` / a bake / CI) — not persisted.
    Ephemeral,
    /// First run on an EMPTY durable image: seeded the demo genesis + 5 turns onto
    /// it (now durable).
    SeededFresh { path: PathBuf },
    /// A durable image RECOVERED as-is. `dropped` torn turns were truncated to reach
    /// the last consistent state (`0` ⇒ a clean reopen — your world exactly as left).
    Recovered { path: PathBuf, dropped: u64 },
    /// The prior durable image was UNSALVAGEABLE; it was quarantined aside (kept for
    /// forensics) and a fresh durable world was seeded in its place.
    FreshAfterUnsalvageable { path: PathBuf, error: String },
    /// Not even a fresh durable image could be provisioned (an unwritable disk/path);
    /// fell back to an ephemeral demo world so the window still opens — NOT persisted.
    EphemeralFallback { error: String },
}

impl BootOrigin {
    /// Whether the world this origin describes is durable (persists across launches).
    pub fn is_durable(&self) -> bool {
        matches!(
            self,
            BootOrigin::SeededFresh { .. }
                | BootOrigin::Recovered { .. }
                | BootOrigin::FreshAfterUnsalvageable { .. }
        )
    }

    /// A one-line human summary for the startup proof block — names durable vs
    /// ephemeral, the image path, and recovered vs seeded (so a blank window reads as
    /// a render issue, and a non-persisting session reads LOUDLY as such).
    pub fn summary(&self) -> String {
        match self {
            BootOrigin::Ephemeral => {
                "EPHEMERAL in-RAM demo world (:memory:) — this session is NOT persisted".to_string()
            }
            BootOrigin::SeededFresh { path } => format!(
                "DURABLE image at {} — first run: seeded the demo genesis + 5 verified turns \
                 (now persisted; your next launch reopens THIS world)",
                path.display()
            ),
            BootOrigin::Recovered { path, dropped } if *dropped == 0 => format!(
                "DURABLE image at {} — recovered your world exactly as you left it",
                path.display()
            ),
            BootOrigin::Recovered { path, dropped } => format!(
                "DURABLE image at {} — recovered your world, truncating {dropped} torn turn(s) to \
                 the last consistent state (never stranded)",
                path.display()
            ),
            BootOrigin::FreshAfterUnsalvageable { path, error } => format!(
                "DURABLE image at {} — the prior image was UNSALVAGEABLE ({error}); quarantined it \
                 aside and seeded a fresh durable world",
                path.display()
            ),
            BootOrigin::EphemeralFallback { error } => format!(
                "EPHEMERAL fallback — could not open OR provision a durable image ({error}); \
                 the window opens but this session is NOT persisted"
            ),
        }
    }
}

/// The result of booting the windowed desktop's World: the live [`World`] (durable
/// or ephemeral), its `[treasury, service, user]` anchors, and the [`BootOrigin`]
/// (for the startup report). The caller renders `DeosDesktop::new` over the world +
/// the `user` anchor exactly as before.
pub struct DurableBoot {
    pub world: World,
    pub anchors: [CellId; 3],
    pub origin: BootOrigin,
}

/// **Boot the windowed desktop's World from a [`WorldImageSpec`].** The single entry
/// the desktop calls; it never strands and never silently wipes (see the module
/// docs). Ephemeral is the old `demo_world()`; durable opens-recovering, seeds an
/// empty image, and recovers a populated one.
pub fn boot_desktop_world(spec: WorldImageSpec) -> DurableBoot {
    match spec {
        WorldImageSpec::Ephemeral => {
            let (world, anchors) = world::demo_world();
            DurableBoot {
                world,
                anchors,
                origin: BootOrigin::Ephemeral,
            }
        }
        WorldImageSpec::Durable { path, fresh } => open_durable(path, fresh),
    }
}

/// Open (or provision) the durable image at `path`. `fresh` quarantines any existing
/// image first (the `--fresh-world` override). Mirrors `session::open_session_world`
/// / `start_fresh_session_world` but seeds the DEMO world (not the per-user session
/// anchors).
fn open_durable(path: PathBuf, fresh: bool) -> DurableBoot {
    // Ensure the parent dir exists (the default lives under the user data dir, which
    // may not exist yet) — mirrors `open_session_world`'s `create_dir_all(base_dir)`.
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }

    // `--fresh-world`: the owner explicitly wants to start over — quarantine the
    // existing image aside (never delete) so the open below provisions a fresh one.
    if fresh {
        quarantine(&path);
    }

    // RECOVER, NEVER STRAND: a torn/divergent image is truncated to its last
    // consistent ordinal and reopened at the last-good state rather than refused
    // (`OpenError::Divergent` never reaches the owner). Only a wholly-unsalvageable
    // image errs here — we then quarantine + seed fresh (never a dead-end).
    let (mut world, dropped) = match World::open_recovering(&path, demo_costs()) {
        Ok(t) => t,
        Err(e) => return seed_after_unsalvageable(path, e),
    };
    if dropped > 0 {
        eprintln!(
            "[deos-desktop] recovered a divergent durable image by truncating {dropped} torn \
             turn(s) to the last consistent state (the desktop opens on your last-good world)"
        );
    }

    // The deterministic demo anchor ids — content-addresses of the fixed seeds, the
    // SAME on a fresh provision and on a recovered image (balance/timestamp do not
    // enter the id). Learned from a throwaway `demo_genesis()` so the seeds have a
    // single source of truth (if the demo genesis changes, this follows).
    let (_probe_world, probe_anchors, _probe_seed) = world::demo_genesis();

    // FRESH iff the recovered image has no demo anchors yet (an empty store opens to
    // a genesis-empty World). On a relaunch every anchor + the seeded turns' effects
    // are RECOVERED from the durable image.
    let fresh_image = world.ledger().get(&probe_anchors[0]).is_none();
    if fresh_image {
        // FIRST RUN — seed the demo genesis + drive all 5 seed turns ONTO the durable
        // world so they PERSIST (genesis mirrored via `record_genesis`, each turn
        // dual-written). A checkpoint bounds the next recovery overlay.
        let anchors = seed_demo_and_checkpoint(&mut world);
        debug_assert_eq!(
            anchors, probe_anchors,
            "the seeded anchors must equal the deterministic demo anchor ids"
        );
        DurableBoot {
            world,
            anchors,
            origin: BootOrigin::SeededFresh { path },
        }
    } else {
        // RELAUNCH — use the recovered image as-is; the anchor ids re-derive
        // deterministically and the recovered ledger already holds them.
        debug_assert!(
            world.ledger().get(&probe_anchors[2]).is_some(),
            "the user anchor must be recovered from the durable image on relaunch"
        );
        DurableBoot {
            world,
            anchors: probe_anchors,
            origin: BootOrigin::Recovered { path, dropped },
        }
    }
}

/// Seed the demo genesis + drive all 5 [`crate::world::DemoSeed`] turns onto the
/// (durable) `world`, then flush a checkpoint. Returns the anchors. On a durable
/// world every install/turn dual-writes; on an ephemeral one this is just the
/// eager demo seed (the checkpoint is a no-op). Shared by the fresh-image and the
/// after-unsalvageable paths.
fn seed_demo_and_checkpoint(world: &mut World) -> [CellId; 3] {
    let (anchors, mut seed) = world::seed_demo_genesis_onto(world);
    // Drive every seed turn (the eager path — the same 5 real verified turns the
    // `demo_world()` route runs; each dual-writes when the world is durable).
    while seed.next(world).is_some() {}
    // Bound the next recovery overlay (mirrors the persistence tests' post-seed
    // `checkpoint_now`). No-op on an ephemeral world.
    world.checkpoint_now();
    anchors
}

/// The wholly-unsalvageable path: quarantine the corrupt image aside (WARN LOUDLY,
/// never delete) and provision a fresh durable world in its place. If even the fresh
/// open fails (an unwritable disk), fall back to an ephemeral demo world so the
/// window still opens — loudly warned that this session will not persist.
fn seed_after_unsalvageable(path: PathBuf, err: OpenError) -> DurableBoot {
    let error = err.to_string();
    eprintln!(
        "[deos-desktop] the durable image at {} is UNSALVAGEABLE: {error}",
        path.display()
    );
    quarantine(&path);
    match World::open(&path, demo_costs()) {
        Ok(mut world) => {
            let anchors = seed_demo_and_checkpoint(&mut world);
            eprintln!(
                "[deos-desktop] provisioned a FRESH durable world in its place (the corrupt image \
                 is kept aside for recovery)"
            );
            DurableBoot {
                world,
                anchors,
                origin: BootOrigin::FreshAfterUnsalvageable { path, error },
            }
        }
        Err(e) => {
            // Even a fresh provision failed — the disk/path is unwritable. Do NOT
            // dead-end: open an ephemeral demo world so the desktop is usable, but say
            // LOUDLY that nothing this session will persist.
            eprintln!(
                "[deos-desktop] could NOT provision a fresh durable image either ({e}); falling \
                 back to an EPHEMERAL demo world — THIS SESSION WILL NOT PERSIST"
            );
            let (world, anchors) = world::demo_world();
            DurableBoot {
                world,
                anchors,
                origin: BootOrigin::EphemeralFallback {
                    error: e.to_string(),
                },
            }
        }
    }
}

/// Rename an unsalvageable / to-be-replaced image aside as `<path>.corrupt-<nanos>`
/// (kept for forensics / manual salvage), never deleted — mirrors
/// `session::start_fresh_session_world`. A missing file is fine (nothing to move); a
/// rename failure is non-fatal (the fresh open below will create/overwrite).
fn quarantine(path: &std::path::Path) {
    if !path.exists() {
        return;
    }
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let aside = path.with_extension(format!("redb.corrupt-{nanos}"));
    match std::fs::rename(path, &aside) {
        Ok(()) => eprintln!(
            "[deos-desktop] quarantined the prior durable image aside at {} (kept for recovery)",
            aside.display()
        ),
        Err(e) => eprintln!(
            "[deos-desktop] could not quarantine the prior durable image ({e}) — proceeding to \
             provision a fresh one over it"
        ),
    }
}

// ===========================================================================
// Tests (headless — `cargo test --no-default-features --features embedded-executor`)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::transfer;
    use std::sync::atomic::{AtomicU64, Ordering};

    static COUNTER: AtomicU64 = AtomicU64::new(0);

    /// A unique throwaway redb path under the OS temp dir (no `tempfile` dep) —
    /// mirrors `persistence::tests::scratch_path`.
    fn scratch_path() -> PathBuf {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        std::env::temp_dir().join(format!("sbv2-durable-desktop-{pid}-{nanos}-{n}.redb"))
    }

    /// THE DURABLE-DESKTOP WELD, end to end (the twin of
    /// `persistence::close_and_reopen_restores_the_exact_image`): booting a durable
    /// desktop image seeds the demo world; an EXTRA verified turn committed on it
    /// survives a close + reopen — the reopened desktop lands on the exact post-turn
    /// state (height + the credited balance), and the earlier boot is recognized as a
    /// clean recovery (0 torn turns). This is the literal "your world is one durable
    /// image" for `--desktop`.
    #[test]
    fn a_durable_desktop_survives_close_and_reopen() {
        let path = scratch_path();

        // FIRST BOOT — a fresh (non-existent) durable image: seeds the demo genesis +
        // 5 turns onto it, then we commit ONE extra turn beyond the seed.
        let (extra_to, height_after_extra, user_balance_after_extra) = {
            let boot = boot_desktop_world(WorldImageSpec::Durable {
                path: path.clone(),
                fresh: false,
            });
            assert!(
                matches!(boot.origin, BootOrigin::SeededFresh { .. }),
                "first boot of an empty image seeds a fresh durable demo world"
            );
            assert!(boot.origin.is_durable(), "the seeded world is durable");
            let mut world = boot.world;
            assert!(
                world.is_durable(),
                "the opened world carries the redb store"
            );
            let [treasury, _service, user] = boot.anchors;

            // The demo seed left treasury at 1_000_000 - 250_000 - 50_000 = 700_000;
            // commit an EXTRA verified transfer (treasury → user, 7) beyond the seed.
            let t = world.turn(treasury, vec![transfer(treasury, user, 7)]);
            assert!(
                world.commit_turn(t).is_committed(),
                "the extra turn commits and dual-writes to the durable image"
            );
            world.checkpoint_now();

            let out = (
                user,
                world.height(),
                world.ledger().get(&user).unwrap().state.balance(),
            );
            out
            // `world` dropped here → the redb handle is released for the reopen.
        };

        // REOPEN — the durable image recovers exactly; the EXTRA turn survived.
        {
            let boot = boot_desktop_world(WorldImageSpec::Durable {
                path: path.clone(),
                fresh: false,
            });
            assert!(
                matches!(boot.origin, BootOrigin::Recovered { dropped: 0, .. }),
                "the second boot RECOVERS the durable image cleanly (0 torn turns)"
            );
            let world = boot.world;
            assert!(world.is_durable());
            assert_eq!(
                world.height(),
                height_after_extra,
                "the reopened height includes the extra turn (the seed + 1)"
            );
            assert_eq!(
                world.ledger().get(&extra_to).unwrap().state.balance(),
                user_balance_after_extra,
                "the extra turn's credited balance survived the close + reopen"
            );
        }

        let _ = std::fs::remove_file(&path);
    }

    /// The EPHEMERAL escape hatch is the old `demo_world()` verbatim: fully seeded, in
    /// RAM, never durable (so `--render-woven` / bakes / CI stay hermetic).
    #[test]
    fn the_ephemeral_hatch_is_the_old_demo_world_and_never_durable() {
        let boot = boot_desktop_world(WorldImageSpec::Ephemeral);
        assert!(matches!(boot.origin, BootOrigin::Ephemeral));
        assert!(!boot.origin.is_durable());
        assert!(
            !boot.world.is_durable(),
            "the ephemeral world carries no store"
        );
        // Fully seeded (the eager demo world runs all 5 turns).
        assert_eq!(
            boot.world.height(),
            crate::world::DemoSeed::TOTAL as u64,
            "the ephemeral hatch is the fully-seeded demo world"
        );
    }

    /// `--fresh-world` on an existing durable image quarantines it aside (kept, not
    /// deleted) and provisions a brand-new seeded durable world.
    #[test]
    fn fresh_world_quarantines_and_reseeds() {
        let path = scratch_path();

        // Seed an image and commit an extra turn (so a re-seed is observably distinct
        // from a recovery — the extra turn must be GONE after a fresh reseed).
        let height_seeded = {
            let boot = boot_desktop_world(WorldImageSpec::Durable {
                path: path.clone(),
                fresh: false,
            });
            let mut world = boot.world;
            let [treasury, _service, user] = boot.anchors;
            let t = world.turn(treasury, vec![transfer(treasury, user, 3)]);
            assert!(world.commit_turn(t).is_committed());
            world.checkpoint_now();
            world.height()
        };

        // FRESH boot: quarantines the prior image and seeds anew — height is back to
        // the pure demo seed (the extra turn is not present in the new image), and a
        // `.corrupt-*` quarantine sibling exists.
        {
            let boot = boot_desktop_world(WorldImageSpec::Durable {
                path: path.clone(),
                fresh: true,
            });
            assert!(
                matches!(boot.origin, BootOrigin::SeededFresh { .. }),
                "a --fresh-world boot seeds a brand-new durable world"
            );
            assert_eq!(
                boot.world.height(),
                crate::world::DemoSeed::TOTAL as u64,
                "the fresh image is the pure demo seed (the prior extra turn is gone)"
            );
            assert!(
                height_seeded > crate::world::DemoSeed::TOTAL as u64,
                "sanity: the prior image really had the extra turn"
            );
        }

        // The prior image was QUARANTINED (kept for forensics), not deleted.
        let dir = path.parent().unwrap();
        let stem = path.file_name().unwrap().to_string_lossy().to_string();
        let quarantined = std::fs::read_dir(dir)
            .unwrap()
            .filter_map(|e| e.ok())
            .any(|e| {
                let name = e.file_name().to_string_lossy().to_string();
                name.starts_with(&stem) && name.contains(".corrupt-")
            });
        assert!(
            quarantined,
            "the prior durable image is quarantined aside (kept, not deleted)"
        );

        // Cleanup: the canonical image + any quarantine siblings.
        let _ = std::fs::remove_file(&path);
        if let Ok(rd) = std::fs::read_dir(dir) {
            for e in rd.flatten() {
                let name = e.file_name().to_string_lossy().to_string();
                if name.starts_with(&stem) && name.contains(".corrupt-") {
                    let _ = std::fs::remove_file(e.path());
                }
            }
        }
    }
}
