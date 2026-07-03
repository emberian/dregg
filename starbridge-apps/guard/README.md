# starbridge-guard — per-subject abuse-governance

The layer that makes a permissionless (KYC-free) substrate responsibly openable. A
substrate that lets any anonymous cap-account deploy anything with no identity check
is a spam / malware / phishing magnet *unless* the same openness is held to bounds.
This crate is that bound — a native **subject-account cell** whose two teeth are
ordinary verified turns.

## The two teeth

1. **A per-subject quota / rate ceiling.** A metered `consumed` counter under a
   frozen `ceiling`. A consume that would push the subject past its ceiling is refused
   IN-BAND — the budget-`402` / rate-`429` shape. This is **not a new mechanism**: it
   is the SAME verified counter+ceiling `starbridge-tool-access-delegation` proved for
   its rate-limited mandate (the `Monotonic(counter) + FieldLteField(counter <=
   ceiling)` slot-caveat pair, mirroring its Lean `mandateSpec`), reused here
   subject-scoped against a ceiling of the shape `cell/src/allowance.rs` seals into a
   cell's commitment. The differential test pins `consume_admit` to
   `starbridge_tool_access_delegation::deleg_admit`.

2. **Account standing.** A `standing` slot (`good` / `flagged` / `suspended`) that
   ONLY a governance-gated, receipted turn may move (a takedown / suspension /
   reinstatement). A subject can never flip its own standing:

   - the `set_standing` transition case carries a `SenderAuthorized(PublicRoot)` gate
     against a governance-authority root — the committee-gated shape
     `starbridge-governed-namespace` uses for its atomic table swap;
   - the `consume_quota` case FREEZES the standing slot (`Immutable`) — a consume can
     never launder a standing self-write through the metering path;
   - the `Cases` default-deny refuses any other method that would touch it.

   This is the ONLY genuinely new layer; the quota/rate is composed, not re-implemented.

## The four axes

| Axis | Where |
|------|-------|
| AX1/AX2 — verified core (FactoryDescriptor + `Cases` program) | `guard_factory_descriptor` / `guard_program` / `guard_app` / `register` (`src/lib.rs`) |
| AX3 — service-cell `invoke()` front door | `src/service.rs` (`constitute` / `consume` / `view`; `set_standing` published at its governance tier, built via the witnessed `build_set_standing_action`) |
| AX4 — deos-view card | `src/card.rs` |
| AX5 — abuse-audit reactor | `src/reactor.rs` (watches `consume_quota`, emits the automated-signal audit the operator-review queue reads) |

## The subject-account cell (slot ↦ meaning)

| Slot | Name | Caveat | Purpose |
|---:|---|---|---|
| 0 | `consumed` | `Monotonic` + `FieldLteField(<= ceiling)` | The rate/quota counter, advanced `c → c+1` per `consume_quota`; the ceiling never violated (the in-band refusal). |
| 1 | `ceiling` | `WriteOnce` | The granted per-window ceiling N, bound once, frozen. |
| 2 | `standing` | governance-gated (`set_standing` only) | `good` / `flagged` / `suspended`. |
| 3 | `governance_root` | `WriteOnce` | Merkle root of the governance authority set; the `SenderAuthorized(PublicRoot)` clause on `set_standing` reads THIS slot. |
| 4 | `subject` | `WriteOnce` | The subject's stable id hash (the legible scope). |

## The verified turns (the tests)

- **`tests/factory_birth.rs`** — birth → `constitute` → the full granted budget of
  consumes ACCEPT → the over-ceiling consume is REFUSED IN-BAND (the `402`/`429`), a
  counter rollback is refused (`Monotonic`), a ceiling raise is refused (`WriteOnce`).
  *A subject over its rate ceiling is refused* — on the real executor path.
- **`tests/governance_executor.rs`** — the standing gate on the REAL
  `SenderAuthorized` STARK: a WITNESSED governance `set_standing` COMMITS and flips
  standing; an UNWITNESSED self-write fails CLOSED; a non-governance signer (foreign
  authority) is REFUSED even carrying its own proof — while the subject still meters
  its own quota. *Standing flips only via the governance turn, not a self-write.*
- **`tests/governance.rs`** — the program-level `evaluate_with_meta` regression for
  both teeth (consume ceiling; `consume_quota` freezes standing; the witness-missing
  `set_standing` reject; default-deny on an unknown method; a standing turn cannot
  fabricate quota).

## Composition (what this reuses vs what is new)

- **counter+ceiling** ← `starbridge-tool-access-delegation` (the verified pair;
  `deleg_admit` pins the differential).
- **governance gate** ← `starbridge-governed-namespace` (the `SenderAuthorized(PublicRoot)`
  shape).
- **ceiling cell** ← `cell/src/allowance.rs` (the per-subject ceiling in the commitment).
- **genuinely new** — the abuse-governance / account-standing layer.

The enforceable MECHANISM only: the live abuse-report intake form, the operator-review
UI, and the moderation POLICY are out of scope (a reviewed-go call) — this crate gives
them teeth.
