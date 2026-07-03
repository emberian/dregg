# starbridge-org — teams / organizations (IAM) as a dregg-native cell

dregg identity is **single-subject** by default: a `dga1_` cap-account is the whole
subject, and a console scopes "my stuff" by `owner == subject`. Real clouds have
**organizations** with **members** and **roles** (AWS Organizations / IAM, GCP
projects + IAM, a Vercel/Cloudflare team). This crate adds that — with **no new
authorization primitive**.

## The one idea: a role IS an attenuation of the owner's authority

dregg's capability-attenuation lattice (the `dregg-auth` credential core, whose
`Credential::attenuate` provably only ever *narrows* — `metatheory/Dregg2/
Authority/Caveat.lean` `attenuate_subset`) **already is** the role mechanism:

* An **Org** is its own dregg cell with its own minting authority (an
 `OrgAuthority` holding a `RootKey`) and a stable id `org:<16hex>`.
* The **owner grant** is a credential pinning `AttrEq{org}` (the org-scoping tooth)
 and `AnyOf(all permissions)` (the full owner authority).
* A **role-cap** is that grant **attenuated** to the role's permission subset. So
 *"admin" = a cap attenuated to manage-but-not-delete-org*; *"viewer" = a
 read-only attenuation.* A member acts by presenting their role-cap, verified
 (`cap::authorize`) against the org root key + a context binding `org` (scoping)
 and `perm` (role-gating).
* A viewer-cap simply does not satisfy a `resource:write` (or `members:manage`)
 context — the action is **refused**, and by the no-amplify property it **cannot
 be forged wider** (appending a `write` caveat only makes the meet `read ∧ write`
 = unsatisfiable, never `write`).

**"viewer is read-only" / "admin can't delete the org" is the SAME no-amplify
lattice property `dregg-auth` already proves.**

## The four axes (the unified starbridge-app template)

Following the `execution-lease` exemplar:

* **the verified core** (`src/lib.rs`) — the `org_factory_descriptor` +
 `org_cell_program`: the org identity key + name are `WriteOnce` (a live org can
 never be re-pointed at a new signing key or silently renamed), and the
 membership-event sequence is `Monotonic` (the audit height never rewinds). The
 `member/role` roster is a witnessed committed heap image
 (`MEMBER_COLL`/`ROLE_COLL`); the org-scope + role-gate are the cap-context
 caveats `cap::authorize` checks on every membership turn. The receipted turns
 live in the pure `OrgAuthority` (`src/org.rs`);
* **the service `invoke()` front door** (`src/service.rs`) — a typed
 `InterfaceDescriptor` (`invite` / `accept` / `remove` / `change_role` /
 `transfer` / `view`), each mutator desugaring to ordinary verified effects;
* **the deos-view card** (`src/card.rs`) — the team dashboard as a `deos.ui.*`
 view-tree (a member-count gauge, the role-tier pills, the membership lifecycle
 breadcrumb, the invite/accept/change-role/transfer buttons);
* **the composed `DeosApp`** (`org_app` / `register_deos`).

## The verified turns

Every role transition is a receipted turn (a `MembershipEvent`, monotone `seq`),
authorized by a role-cap (not a trusted role flag):

| turn | who (role-cap perm) | effect |
|------|---------------------|--------|
| `invite` | owner/admin (`members:manage`) | a pending invite |
| `accept` | the named invitee | joins + **mints the member their attenuated role-cap** |
| `remove` | owner/admin (`members:manage`) | drops a member (never the owner) |
| `change_role` | owner/admin (`members:manage`) | re-roles + re-issues the cap |
| `transfer_ownership` | owner only (`org:transfer`) | moves the owner slot; old owner demoted to admin |

A member **cannot amplify past their role** — the executor/cap-verify refuses, and
the forged wider cap is inexpressible.

## Roles → permissions

| role | permissions |
|------|-------------|
| `owner` | everything (incl. `org:delete`, `org:transfer`, billing) |
| `admin` | resources (r/w/create/delete) + `members:manage` + `billing:view` |
| `member` | resources (r/w/create/delete) |
| `billing` | `billing:view` + `billing:pay` |
| `viewer` | `resource:read` |

## Honest gaps

The roster's source of truth is the pure serializable `Org` record (a console's
"team"); the cell mirrors its owner / member-count / seq into scalar slots (the
executor-enforced invariants) and its members into a committed heap image (a light
client witnesses the roster). The `WriteOnce(ROOT_PUBKEY/NAME)` + `Monotonic(SEQ)`
teeth and the role-cap authorize (a viewer's admin attempt refused, unforgeably)
are REAL. Threading the full roster mutation through a per-member `SetField`
allow-list program (so an off-roster write is itself an executor refusal, not just
a mirror the authority keeps honest) is the production lane this models.

## Supersedes

This crate is the dregg-native successor of `a prior org module` (`the migration plan`
§3.5, the `org` row). The reference's `webauth/cred.rs` caveat-chain is the native
`dregg-auth/src/credential`; the role/permission table and the `role-cap =
attenuated owner grant` bridge are ported natively here. **`a prior org module` can be
deleted.**
