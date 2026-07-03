//! **The program-in-cell weld** — an applet as a PORTABLE CELL-BLOB.
//!
//! ember's gap: today a [`crate::applet::Applet`] mints a cell whose state is the
//! applet's *model* (the seed fields), but the applet's *program* (its affordances +
//! its view source) lives only in Rust/JS at runtime. So a program is NOT a shareable
//! thing you can carry over the membrane and reconstitute elsewhere.
//!
//! This module closes that: the applet's program is serialized into an
//! [`AppletManifest`] and PERSISTED INTO THE CELL — chunked across the cell's committed
//! **heap** (`CellState::heap_map`, the sorted-Poseidon2 `(collection, key) → felt` map
//! whose digest is the committed `heap_root`). Storing the source in the heap means it
//! is part of the cell's committed state, travels with `to_cell_bytes()`, and is
//! recovered by [`PortableApplet::from_cell`].
//!
//! THE STORAGE MECHANISM (honest): a **heap blob**. The manifest JSON bytes are written
//! into heap collection [`PROGRAM_COLL`], 31 payload bytes per `FieldElement` leaf
//! (key 0 carries the byte-length header; keys `1..` carry the chunks). The heap is the
//! cell's blob area; the source is therefore committed by `heap_root`, not packed into
//! the scarce 16 fixed `fields[]` slots (those stay the model). Size limit: the heap key
//! is a `u32`, so the bound is ~`2^32 * 31` bytes — effectively unbounded for source.
//!
//! THE LOAD-AND-RUN PATH: [`PortableApplet::from_cell`] deserializes the cell, reads the
//! manifest out of the heap, rebuilds the affordance closures from the manifest's
//! declarative [`ApplyOp`]s, and stands a FRESH embedded executor up over the loaded
//! cell. A loaded affordance fire is the SAME cap-gated verified turn the originally-
//! minted applet runs (the turn semantics are intact — see the test, proven by running).

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell};
use serde::{Deserialize, Serialize};

use crate::applet::{pack_u64, Affordance, Applet, Slot};

/// The heap collection id reserved for the applet's program blob. Disjoint from any
/// model/heap collection an applet would use for data.
pub const PROGRAM_COLL: u32 = 0xC0DE;

/// Bytes of program payload per heap leaf (a `FieldElement` is 32 bytes; byte 0 is the
/// fill-length tag `0..=31`, bytes `1..=31` carry payload). The header leaf at key 0
/// holds the total byte length (little-endian u64) instead.
const CHUNK_BYTES: usize = 31;

/// A declarative apply rule — the portable shape of an affordance's effect. This is the
/// part of the program that, in the live applet, is a Rust `Box<dyn Fn(&CellModel,
/// i64)>`. Reconstituting it from the manifest is what makes a loaded affordance the
/// SAME affordance (same writes for the same model+arg).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApplyOp {
    /// `slot := slot + max(arg, 0)` (the counter `inc`).
    AddToSlot { slot: Slot },
    /// `slot := slot - max(arg, 0)` saturating at 0 (the counter `dec`).
    SubFromSlot { slot: Slot },
    /// `slot := value` — set a slot to a fixed u64 (the counter `reset` to 0).
    SetSlot { slot: Slot, value: u64 },
    /// `slot := max(arg, 0)` — TRACK an externally-observed value: the fire's arg is
    /// the new slot value. This is the Pulse→Signals weld's write verb — the cockpit
    /// mirrors a LIVE World reading (the ledger census) into a status card's model as
    /// a receipted verified turn, so the card's `bind` rows re-read committed state
    /// (never a side-channel), and the mirroring itself is on the audit tape. The
    /// SAME named power-up the boa twin (`deos-js-runtime`'s `ApplyOp::SetSlotFromArg`)
    /// already carries — one write vocabulary, two engines.
    SetSlotFromArg { slot: Slot },
}

impl ApplyOp {
    /// Reconstitute the live apply closure. The closure is a pure function of the live
    /// model + the JS-supplied arg, exactly as the originally-minted affordance was.
    pub(crate) fn into_closure(self) -> crate::applet::ApplyFn {
        match self {
            ApplyOp::AddToSlot { slot } => Box::new(move |model, arg| {
                let cur = model.field_u64(slot);
                // SATURATING — matches `SubFromSlot`'s saturating_sub AND the boa twin
                // (`deos-js-runtime`'s AddToSlot saturates). A plain `cur + arg` panicked
                // in debug / wrapped in release, so the two "twin" engines produced
                // DIFFERENT receipted state (or a crash) for the same authored applet on
                // an overflow. One vocabulary, one arithmetic, both engines.
                vec![(slot, pack_u64(cur.saturating_add(arg.max(0) as u64)))]
            }),
            ApplyOp::SubFromSlot { slot } => Box::new(move |model, arg| {
                let cur = model.field_u64(slot);
                vec![(slot, pack_u64(cur.saturating_sub(arg.max(0) as u64)))]
            }),
            ApplyOp::SetSlot { slot, value } => {
                Box::new(move |_model, _arg| vec![(slot, pack_u64(value))])
            }
            ApplyOp::SetSlotFromArg { slot } => {
                Box::new(move |_model, arg| vec![(slot, pack_u64(arg.max(0) as u64))])
            }
        }
    }
}

/// The portable description of one affordance: its name, the authority it requires, and
/// its declarative apply rule.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffordanceSpec {
    pub name: String,
    pub required: AuthRequired,
    pub op: ApplyOp,
}

/// **The applet manifest** — the whole program as a serializable, cell-carryable blob.
///
/// It carries everything needed to reconstitute a runnable applet from nothing but the
/// cell bytes: the seed model, the affordance declarations (name · auth · apply rule),
/// the driver's held authority, and the JS **view source** (the genuinely program-text
/// part — the view program a renderer runs).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AppletManifest {
    /// The model seed: `(slot, packed-u64)` written as the cell's genesis fields.
    pub seed_fields: Vec<(Slot, u64)>,
    /// The affordance declarations.
    pub affordances: Vec<AffordanceSpec>,
    /// The driver's held authority (what fires are cap-checked against).
    pub held: AuthRequired,
    /// The JS **view source** — the program text the applet carries for its view. A
    /// renderer re-runs this over the loaded cell's model. This is the literal program
    /// source stored in the cell (not just the model).
    pub view_source: String,
}

impl AppletManifest {
    /// Serialize the manifest to its canonical JSON bytes (the blob written into the
    /// cell heap).
    pub fn to_bytes(&self) -> Vec<u8> {
        serde_json::to_vec(self).expect("manifest serializes")
    }

    /// Parse a manifest from its JSON bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        serde_json::from_slice(bytes).map_err(|e| format!("manifest parse: {e}"))
    }

    /// Rebuild the live affordance set (the apply closures) from the declarations.
    fn affordances(&self) -> Vec<Affordance> {
        self.affordances
            .iter()
            .map(|spec| Affordance {
                name: spec.name.clone(),
                required: spec.required.clone(),
                apply: spec.op.clone().into_closure(),
            })
            .collect()
    }

    /// The seed fields as `(slot, FieldElement)` (the cell's genesis model).
    fn seed_field_elems(&self) -> Vec<(Slot, FieldElement)> {
        self.seed_fields
            .iter()
            .map(|(slot, v)| (*slot, pack_u64(*v)))
            .collect()
    }
}

/// Write a program blob into a cell's committed heap (collection [`PROGRAM_COLL`]).
///
/// Key 0 = the length header (u64 LE in the leaf's low 8 bytes); keys `1..=ceil(len/31)`
/// = the payload chunks (leaf byte 0 = this chunk's fill length, bytes `1..` = payload).
/// Mutating the heap re-seals `heap_root`, so the program becomes part of the cell's
/// committed state.
pub fn write_program_blob(cell: &mut Cell, blob: &[u8]) {
    // Header leaf: total byte length.
    let mut header = [0u8; 32];
    header[..8].copy_from_slice(&(blob.len() as u64).to_le_bytes());
    cell.state.set_heap(PROGRAM_COLL, 0, header);

    for (i, chunk) in blob.chunks(CHUNK_BYTES).enumerate() {
        let mut leaf = [0u8; 32];
        leaf[0] = chunk.len() as u8; // fill length (0..=31)
        leaf[1..1 + chunk.len()].copy_from_slice(chunk);
        cell.state.set_heap(PROGRAM_COLL, (i + 1) as u32, leaf);
    }
}

/// Read a program blob back out of a cell's committed heap. Returns `None` if no program
/// header leaf is present (the cell carries no program).
pub fn read_program_blob(cell: &Cell) -> Option<Vec<u8>> {
    let header = cell.state.get_heap(PROGRAM_COLL, 0)?;
    let mut len_bytes = [0u8; 8];
    len_bytes.copy_from_slice(&header[..8]);
    let total = u64::from_le_bytes(len_bytes) as usize;

    let mut out = Vec::with_capacity(total);
    let mut key: u32 = 1;
    while out.len() < total {
        let leaf = cell.state.get_heap(PROGRAM_COLL, key)?;
        let fill = leaf[0] as usize;
        out.extend_from_slice(&leaf[1..1 + fill]);
        key += 1;
    }
    out.truncate(total);
    Some(out)
}

/// A **portable applet** — the program-in-cell capability over the live [`Applet`].
///
/// `PortableApplet` is just the named constructors; the running value is a plain
/// [`Applet`] (so every existing affordance/fire/reflect/transclude path applies
/// unchanged). The difference is that the applet's program lives in its cell.
pub struct PortableApplet;

impl PortableApplet {
    /// Mint an applet from a [`AppletManifest`] AND persist the program into the minted
    /// cell's heap. The returned [`Applet`] is fully runnable; its cell now carries its
    /// own program source.
    pub fn mint(public_key: [u8; 32], token_id: [u8; 32], manifest: &AppletManifest) -> Applet {
        let mut applet = Applet::mint(
            public_key,
            token_id,
            &manifest.seed_field_elems(),
            manifest.affordances(),
            manifest.held.clone(),
        );
        // Persist the program into the cell's committed heap, in place on the ledger.
        let blob = manifest.to_bytes();
        applet.with_cell_mut(|cell| write_program_blob(cell, &blob));
        applet
    }

    /// Serialize an applet's CELL to bytes — the portable blob you carry over the
    /// membrane. The cell carries the model (its fields) AND the program (its heap blob).
    pub fn to_cell_bytes(applet: &Applet) -> Vec<u8> {
        let cell = applet
            .ledger()
            .get(&applet.cell())
            .expect("applet cell present on its own ledger");
        postcard::to_allocvec(cell).expect("cell serializes")
    }

    /// **Load + run from a cell** — reconstitute a runnable applet from cell bytes.
    ///
    /// Deserialize the cell, read its program manifest out of the committed heap, rebuild
    /// the affordance closures, and stand a FRESH embedded executor up over the loaded
    /// cell (its model is the cell's loaded fields). A subsequent affordance fire is a
    /// real cap-gated verified turn on the loaded cell.
    pub fn from_cell(bytes: &[u8]) -> Result<(Applet, AppletManifest), String> {
        let cell: Cell = postcard::from_bytes(bytes).map_err(|e| format!("cell parse: {e}"))?;
        let blob = read_program_blob(&cell).ok_or("cell carries no program blob")?;
        let manifest = AppletManifest::from_bytes(&blob)?;
        let applet = Applet::adopt_cell(cell, manifest.affordances(), manifest.held.clone());
        Ok((applet, manifest))
    }
}
