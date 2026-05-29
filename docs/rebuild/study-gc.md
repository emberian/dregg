# study-gc — Distributed Capability GC in dregg2: a design probe

> **Scope.** A hunt, not a description. Reads `dregg2.md` §1.7 (GC = cell-liveness)
> + §1 (CDT / coinductive cell), the real machinery in `captp/src/gc.rs` +
> `captp/src/session.rs`, against the CapTP/OCapN distributed-GC literature
> (`pdfs/captp-capability-transport-protocol-spritely.pdf`,
> `pdfs/ocapn-interoperable-capabilities-network-spritely.pdf`). Tags: `[C]`
> grounded-in-code (`file:line`), `[G]` grounded-in-paper, `[F]` forward-design,
> `[!]` impossibility / hard limit found.

---

## 0. The categorical model (what §1.7 actually commits to)

dregg2 models a cell as codata: `Cell = νC. µI. StepProof I × (Turn ⇒ C)` (§1.3).
The outer `νC` says the unfold **never bottoms out** — a cell, once live, produces
forever. §1.7 adds the side-condition that makes GC coherent with that:

> **A cell is live iff it is reachable; the `ν` carries an implicit "while
> reachable" guard.**

Stated categorically, reachability is a **predicate on the reference graph** `R`:

- **Objects** = cells. **Edges** = inbound `CapabilityRef`s (`cell/src/capability.rs:44`,
  `target: CellId` — an inbound edge into `target`) `[C]`. The CDT (§1.1) is the
  *authority* projection of this same graph; GC reuses it ("GC = reachability-pruning
  on the CDT", §1.7).
- **Roots** = the trust-roots / vat-resident holders that are live by fiat (a CSpace
  slot a running computation holds).
- **Live(c)** = `∃` a root-reachable path of un-dropped edges into `c`.
- **Collected** = the **terminal object** of the lifecycle category
  (`CellLifecycle::Destroyed/Archived`, the terminals of `00-synthesis §5.1`).

So GC is the functor `R ↦ {reachable subobject}`, and "collect c" = the unique
morphism `c → Destroyed` once `c` falls out of the reachable subobject. The runtime
implements the *local witness* of an edge's existence as a per-holder refcount: the
exporter's `RefCount{count, last_activity, session_id}` (`gc.rs:38`) is the
fan-in multiplicity of inbound edges from one peer; `total_refs == 0`
⇒ `DropResult::CanRevoke` (`gc.rs:207`) is "no inbound edges remain from any tracked
holder." `[C]`

**The duality §1.7 asserts** — drop = the *backward face* of the await/discharge
engine (§4) — is real in shape: `ImportGcManager::local_ref_dropped` emits a
`DropMessage` (`gc.rs:369-392`); the exporter `process_drop` discharges (decrements)
one unit of `Obs`-advancing acknowledgement (`gc.rs:153`). A `DropRef` *is* a settled
negative discharge. This composes cleanly **for the acyclic, single-direction case**
— and that caveat is the whole story below.

---

## 1. Distributed CYCLE collection — the impossibility, present and unsolved `[!]`

The famous hard case: cells `A@vat1` and `B@vat2`, `A` holds a cap to `B` and `B`
holds a cap to `A`, but **no root reaches either**. Each is the other's only inbound
holder ⇒ neither `total_refs` ever hits zero ⇒ `CanRevoke` never fires ⇒ **permanent
leak**.

**dregg2 has this leak, in full.** The evidence:

- The machinery is **pure per-holder reference counting** (`ExportGcManager` /
  `ImportGcManager`, `gc.rs`). There is **no** mark phase, no trace, no cycle
  detector, no back-edge accounting anywhere in `captp/` — `grep` for
  `cycle_collect|trace|mark|reachab` in `captp/src/` returns nothing. Refcounting is
  *definitionally* unable to collect cycles; this is the textbook limitation, lifted
  to the network. `[C][!]`
- The upstream protocol dregg2 inherits **admits exactly this**: CapTP "provides
  **(acyclic)** distributed garbage collection… Cycles between servers are not
  automatically recognized. Full cycle-collecting distributed GC has been written but
  requires special cooperation from the garbage collector not available in Guile (or
  most languages)" (`captp…spritely.pdf` §line 43-44) `[G]`. OCapN lists distributed
  GC as a feature but never claims cycle collection (`ocapn…spritely.pdf`) `[G]`.

**§1.7's framing actively hides this.** "Codata unfolds forever UNLESS unreachable"
is true; but the runtime's *unreachability test* is `total_refs == 0`, which is
**reachability-from-a-direct-holder**, NOT **reachability-from-a-root**. A cross-vat
cycle is unreachable-from-root yet has `total_refs > 0` at every node. The reduction
of "global reachability" to "local refcount" is **only valid on a forest** (acyclic
reference graph). §1.7 says "GC = reachability-pruning on the CDT" — but the CDT is a
*tree* (attenuation is monotone-narrowing parent→child), and **the runtime reference
graph is NOT the CDT**: the CDT omits the back-edges (a child cell handing a cap to an
ancestor) that create cycles. The doc conflates the authority DAG (acyclic by
attenuation) with the liveness graph (can cycle). This is the seam to fix in §1.7.

**Realistic scoping** (the only honest options, none free):
1. **Accept cross-vat cycle leaks + bound them by expiry.** This is what the code
   *already does* and is the local-first-correct answer: `expires_at` on
   `CapabilityRef` (`capability.rs:56`) + `stale_exports(max_idle_blocks)`
   (`gc.rs:219`) means a leaked cycle is reaped by **lease expiry / TTL**, not by
   reachability. Cycles don't leak *forever*, they leak *until their leases lapse*.
   This is the dregg2-coherent choice: it needs no global view, survives partition,
   and matches the doc's own "prefer short expiry + renewal over revocation" stance
   (§3). `[C/F]`
2. **Local (intra-vat) cycle collection only.** A vat can trace its own heap and
   collect cycles wholly inside one trust-root; cross-vat cycles remain leaked. This
   is the Goblins-available subset.
3. **Cooperative distributed cycle collection** (the "written but needs GC
   cooperation" approach — back-tracing / trial-deletion à la
   Bacon-Rajan over the network). `[!]` Rejected for dregg2: it requires
   **mutually-distrustful vats to truthfully report their internal back-edges**,
   which is unenforceable (see §2) and a privacy leak (it reveals the reference graph
   the §6a tier-3 stack exists to hide). Cycle-collection cooperation and graph
   privacy are in direct tension.

**Verdict:** lease-expiry (option 1) is the realistic and already-implemented scope.
The doc should state plainly: *distributed cycle collection is out of scope; cross-vat
cycles are reclaimed by lease expiry, never by reachability.* Promote `expires_at`
from "used for introduction-granted capabilities" (`capability.rs:53`) to **the
load-bearing liveness bound it actually is.**

---

## 2. Byzantine GC — and the asymmetry that saves safety `[!]/[C]`

Two adversarial moves, with opposite consequences:

- **Refusing to drop (or never dropping) = leak/grief, NOT a safety violation.** A
  Byzantine importer that never sends `DropRef` pins the exporter's `total_refs > 0`
  forever. The exporter cannot distinguish "still needs it" from "griefing." dregg2's
  only defense is the same as option-1 above: `last_activity` + `stale_exports`
  (`gc.rs:219`) let the exporter **unilaterally** reclaim after idle-timeout —
  liveness is recovered by lease, not by trusting the peer's drop. This is correct and
  already coded. A griefer can pin a *lease's worth* of memory, no more. `[C]`

- **Sending a FALSE drop (premature collection) = the safety question.** Is collecting
  a cell another vat still holds a cap to a **safety violation**? **Resolution: no —
  by the design's own structure, and the code enforces the boundary.** Two layers:
  1. **A `DropRef` only decrements the sender's OWN holder entry.** `process_drop`
     keys on `from_federation` and only touches `entry.holders[from_federation]`
     (`gc.rs:183`). A vat **cannot** drop another vat's references. So a false drop
     prematurely collects the cap *the liar itself held* — self-harm, not cross-harm.
     This is the GC analog of the capability discipline: you can only relinquish your
     own authority. `[C]`
  2. **Session/epoch gating blocks cross-session forgery.** `process_drop_with_session`
     rejects a `DropRef` whose `session_id` ≠ the export's session (`gc.rs:193`); the
     `byzantine_node_different_session_cannot_drop_others_refs` test
     (`gc.rs:670`) pins exactly the attack "B forges a drop of A's ref" → `Invalid`.
     `CapSession.epoch` (`session.rs:39`) makes stale-session drops from a torn-down
     connection fail (`session.rs:314` test). `[C]`

  The residual hazard is **drop-vs-use reordering on ONE session**: vat X sends `use`
  then `drop`; if they race and `drop` is processed first, the exporter could revoke
  before the `use` lands. But "revoke a cap *I* just relinquished" harms only X, and
  CapTP message ordering on a session is FIFO, so this is a self-inflicted ordering bug,
  not a cross-vat safety break.

**Does GC-safety need consensus? No — and this is the sharp, defensible result.**
GC-*safety* (never collect a still-reachable-from-a-still-holding-honest-vat cell) is
**purely local and bilateral**: it follows from "a drop touches only the dropper's own
holder count" + session-gating, with **zero** global agreement. This sits exactly
beside dregg2's thesis that **revocation is the lone consensus seam** (§3): GC is the
*positive* lifecycle (collect when unwanted) and needs no consensus; revocation is the
*negative* lifecycle (kill while still wanted) and needs root-epoch agreement. GC
deliberately does **not** inherit revocation's consensus cost. GC-*liveness* (actually
reclaiming) is best-effort, recovered by lease expiry under any adversary. The split:
**safety = local; liveness = leased; neither = consensus.**

---

## 3. The coinductive tension — is "this cell is dead" decidable? `[!]`

This is the deepest finding and it **mirrors the verify/find seam exactly** (§1.2, §4).

- **Reachable is cheap to WITNESS (semi-decidable, positively).** A live path is a
  finite object: exhibit the chain of un-dropped `CapabilityRef`s from a root. This is
  a `Verify`: tractable, local-to-the-path. It is the *positive* coinductive fact —
  "this codata is still productive" — and like all coinductive membership it is
  witnessed by a (here finite) **observation**.
- **UNreachable is NOT finitely witnessable in general.** To assert *dead* you must
  show **no** root-reachable path exists — a universally-quantified, *global* claim
  over a graph that **spans mutually-distrustful vats and is partly hidden by design**
  (tier-3 graph privacy, §6a, deliberately conceals who-points-at-whom). Under
  asynchrony with no global snapshot, "no path exists" is **co-semi-decidable at best,
  and undecidable in the adversarial/partitioned setting**: you cannot distinguish
  "dead" from "a holder is partitioned and will re-assert." `[!]`

So: **liveness is semi-decidable (witness a path); death is not co-witnessable
globally.** This is precisely the FIND/VERIFY asymmetry — *verifying* reachability is
the cheap gate; *finding* a proof of unreachability is the intractable search — and it
is *the same shape* as `Predicate ⊣ Witness` (`00-synthesis §1`). The honest move,
matching dregg2's whole philosophy: **never try to decide death; approximate it
soundly-for-liveness.** `total_refs == 0` is a **sound local approximation** (if no
holder, certainly collectible) that is **incomplete for cycles** (cyclic-dead reads as
live). Lease expiry is the **completing fallback**: it converts the
non-co-witnessable global predicate "dead" into a locally-decidable one "lease
lapsed." Death isn't decided; it's *timed out*. This is the only construction
consistent with codata + no-global-snapshot + graph-privacy simultaneously.

---

## 4. "drop = await/discharge" — termination and partition `[!]/[C]`

§1.7 frames the cross-vat drop as the backward face of the await engine: a `DropRef`
is a discharge the exporter awaits. Does it **terminate**?

- **In the synchronous, connected, acyclic case: yes, and trivially.** `DropMessage` is
  one-shot, fire-and-forget; the importer removes its entry *immediately* on emit
  (`gc.rs:384`, `self.imports.remove(&key)` before returning the message). The
  exporter's `process_drop` is a single decrement. There is no round-trip to await —
  unlike a discharge that gates a turn's admissibility, a drop **needs no
  acknowledgement to be locally complete on the sender.** So the "await" framing is
  **looser than discharge**: a discharge *blocks* a turn; a drop *advances* the
  exporter's `Obs` if and when it arrives, but the importer does not suspend on it.
  This is a real asymmetry the §1.7 "backward face of the same engine" claim
  papers over — the backward face is **fire-and-forget, not suspend-and-resume.** `[C]`

- **Under partition: the drop never arrives — and this is benign, by construction.** A
  lost `DropMessage` leaves the exporter's `total_refs` too high (a leak), never too
  low (no premature collection). So **partition degrades liveness, never safety** —
  the same fail-open-for-liveness / fail-closed-for-safety posture as the tier-1
  CRDT story (§2.2, "never blocks"). The exporter's `stale_exports` timeout
  (`gc.rs:219`) is what *closes the loop the partition opened*: a drop that never
  arrives is eventually superseded by idle-reclaim. Without the lease, a partitioned
  drop would leak forever; **with** it, partition costs one lease-interval of memory.
  `[C/F]`

- **The handoff (3-party) case is where termination gets subtle.** `[!]` A capability
  introduced via a third-party handoff (`handoff.rs`) creates an export edge whose
  *holder* may differ from the *session* it arrived on; `gc.rs:14`'s
  `TODO(unified-lace)` (key GC on `StrandId`, not `FederationId`) is the unfinished
  work that makes drop-attribution exact under handoff. Until that lands, a handed-off
  cap's drop could be mis-attributed across the group key, weakening the
  "drop touches only your own count" safety argument of §2. **This is the one place
  the Byzantine-safety result is currently load-bearing on an unfinished migration.**

---

## 5. Synthesis — the realistic GC design for dregg2

| Question | Honest answer |
|---|---|
| Cross-vat cycle collection? | **No.** Refcount-only; cross-vat cycles leak. Reclaimed by **lease expiry**, never reachability. Distributed cycle-collection rejected (unenforceable peer cooperation + breaks graph privacy). `[!]` |
| Byzantine refuse-to-drop? | Grief/leak only; bounded by `stale_exports` idle-reclaim. Liveness is **leased**, not trusted. |
| Byzantine false-drop? | **Not** a cross-vat safety violation: a drop touches only the dropper's own holder count (`gc.rs:183`) + session/epoch gating (`gc.rs:193`). Self-harm only. |
| Is "dead" decidable? | **No.** Reachable = semi-decidable (witness a path = a `Verify`); unreachable = not globally co-witnessable under async + privacy. Mirrors FIND/VERIFY. Death is **timed out**, never decided. `[!]` |
| Drop = await/discharge? | Shape holds but **fire-and-forget, not suspend/resume** — looser than discharge. Terminates trivially when connected; under partition leaks-not-corrupts, closed by lease. |
| GC-safety need consensus? | **No.** Safety is local+bilateral (own-count + session-gate); liveness is leased; **neither needs consensus.** GC is the positive lifecycle; only its dual, **revocation**, is the consensus seam (§3). |

**One-line scope to fold into §1.7:** *dregg2 ships acyclic distributed GC (per-holder
refcount, session/epoch-gated for Byzantine-safety), with cross-vat cycles and
partitioned/lost drops reclaimed by capability lease-expiry — not by global
reachability, which is non-co-witnessable by design. GC-safety is local; GC-liveness is
leased; neither is consensus-bound.*

**Two doc-level corrections §1.7 needs:** (1) stop conflating the acyclic CDT with the
possibly-cyclic liveness reference graph — `total_refs==0` is reachability-from-a-holder,
not reachability-from-a-root; (2) demote "drop = the await engine's backward face" to
"fire-and-forget settled-negative, completed by lease," and promote `expires_at` to the
first-class liveness bound it operationally already is.
