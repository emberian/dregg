# starbridge-edge-mandate

**An access-edge identity, bound to a budget and a caps mandate, as a verified
cell** — and a thin deploy-side adapter that lowers that cell to an OpenSSH
`authorized_keys` forced-command line.

The hosted-attach distribution model: instead of a user installing the agent
runtime, an operator **hosts** a cap-bounded, budget-bounded, receipted
[`dregg-agent`](../../dregg-agent) session and the user **attaches over SSH**.
What decides *who attaches with what authority* is an **edge-identity map** — an
SSH public key bound to a dregg **account**, a **budget** ceiling, and a **cap
bundle**. This crate makes that map a first-class **mandate cell** on the dregg
substrate, not a mutable record in a file.

## The binding, as a mandate cell

One enrolled subject is one mandate cell whose committed state binds:

| slot | field | constraint | meaning |
|------|-------|------------|---------|
| 0 | `SUBJECT` | `WriteOnce` | digest of the SSH key identity (type+blob) |
| 1 | `ACCOUNT` | `WriteOnce` | digest of the `dga1_` account the session meters against |
| 2 | `BUDGET` | `WriteOnce` | the spend ceiling (cents) — never silently widened |
| 3 | `SPENT` | `Monotonic` + `AffineLe(spent ≤ budget)` | the running meter — an over-budget spend is a real refusal |
| 4 | `CAPS_DIGEST` | `WriteOnce` | digest of the sealed canonical granted tool-set |
| 5 | `REVOKED` | `Monotonic` | the kill switch — once revoked, stays revoked |
| 6 | `EPOCH` | `StrictMonotonic` | the no-replay witnessed-turn counter |

The full enrolment record (account / ssh-pubkey / canonical caps / brain) lives in
the committed heap (`REC_COLL`), folded into the cell's state commitment, so a
light client witnesses exactly what authority was granted and the `authorized_keys`
adapter reads it back.

## The SAME attenuation `agent-orchestration` proves

Enrol is an **attenuation**: the minted subject mandate is *no wider than* the
operator's held grant — `granted ⊑ held` on the exact lattice the sibling
[`agent-orchestration`](../agent-orchestration) coordinator→worker delegation
proves (a tool-set **subset** ∧ a **sub-budget**). Here the tool vocabulary is the
real `dregg-agent` caps grammar (`fs`, `http:HOST`, `pay:VENDOR`, `spend`,
`cell:/path`, …) rather than a fixed enum, so `CapMandate` mirrors that lattice
(`CapMandate::le` / `CapMandate::attenuate`) over a `BTreeSet<String>` of cap
tokens. A request for a tool the operator does not hold is **dropped**; a request
for more budget than held is **clamped** — the mandate that lands in the cell can
only ever be a narrowing of the operator's grant (`derive_no_amplify`).

The operator's held grant lifts from a [`dregg-auth`](../../dregg-auth) `Grant`
(`held_from_grant`): the grant's `tools` **are** the held cap-set, so "enrol mints
a mandate no wider than the grant" is literal.

The requested caps are additionally validated against the real grant vocabulary at
enrol via `dregg_agent::session::parse_caps_confined` under
`Confinement::Hosted` — a raw `shell` is refused (a hosted box holds the operator's
keys; a shell is restored only behind real per-tenant OS isolation, a deploy
concern this crate deliberately does not fake).

## Enrol / spend / revoke are witnessed turns

Each has a pure `Cell` form (`enrol` / `spend` / `revoke`) and a verified-turn form
(the `*_effects` / `build_*_action` builders + the `service` `invoke()` front
door), so the executor re-enforces the invariants on every real turn: an
over-budget spend is refused by `AffineLe`, a replay by `StrictMonotonic(EPOCH)`,
a widened tool-scope by `WriteOnce(CAPS_DIGEST)`.

## The `authorized_keys` adapter is a pure function of the cell

The deploy side is a thin **adapter** (`authorized_keys_line`): a pure function
from a mandate cell to one OpenSSH `authorized_keys` line that drops the connecting
key into its confined `dregg-agent attach` session — scoped to the cell's account +
budget + caps, `restrict`ed to the REPL. It reads only committed cell state; a
revoked mandate yields no line. It names the native `dregg-agent` attach binary and
nothing deployment-specific.

```text
command="dregg-agent attach --account dga1_alice --budget 500 --caps fs,http:api.github.com",restrict,pty ssh-ed25519 AAAA… alice@laptop
```

## The four axes (the unified starbridge-app template)

* **core** — the `FactoryDescriptor` + `mandate_cell_program` (src/lib.rs);
* **service** — the `invoke()` front door (src/service.rs): a typed
  `InterfaceDescriptor` over `enrol` / `spend` / `revoke` / `view`;
* **card** — the deos-view card (src/card.rs): the mandate dashboard as a
  `deos.ui.*` view-tree;
* **adapter** — the deploy-side `authorized_keys` generator.

## Tests

* `enrol_mints_a_mandate_no_wider_than_the_grant` — an out-of-grant cap is dropped,
  an over-ceiling budget is clamped, `granted ⊑ held`;
* `a_spend_past_the_sub_budget_is_refused` — the off-ledger pre-check, and
  (integration) the executor's `AffineLe` gate in the fire path;
* `the_authorized_keys_line_is_a_pure_function_of_the_cell` — deterministic,
  scoped, dark on revocation;
* `tests/edge_mandate.rs` — enrol / spend / over-budget-refused / revoke as real
  witnessed turns on a factory-born cell.

## What this supersedes

This is the AGPL, dregg-native rebirth of the IDENTITY→BUDGET→CAPS binding + the
`authorized_keys` lowering that a prior imperative SSH-attach hosting module carried
as a mutable key→record map persisted to JSON. Here the committed, witnessed cell
**is** the durable, tamper-evident record, the attenuation is the same one
`agent-orchestration` proves, and the prior module's unwired per-tenant OS-isolation
scaffolding is dropped (the hosted posture is enforced the honest way it always was:
a hosted `shell` is refused at enrol).
