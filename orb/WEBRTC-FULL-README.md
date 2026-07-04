# WebRTC stack: the full ICE / DTLS / SCTP / data-channel model

This is the deepened WebRTC transport rail. The first pass proved the one gate
that mattered (no data before a nominated, succeeded ICE pair) and named the rest
as follow-on. This pass discharges the follow-on: the full RFC 8445 checklist,
the DTLS 1.3 handshake with real EverCrypt key derivation and record protection,
the SCTP four-way association, and reliable/ordered data-channel delivery — each
a total transition system or pure function with real theorems, zero `sorry`.

Four files, each a single-file `lean_lib`:

| file | RFC(s) | what it is |
|------|--------|------------|
| `Stun.lean` | 5389 | STUN framing (read-only here; unchanged) |
| `Ice.lean` | 8445 | the ICE candidate-pair checklist, priority, roles, restart |
| `Dcep.lean` | 8832 / 8831 | DCEP open handshake, stream parity, reliability & priority |
| `WebrtcTransport.lean` | 9147 / 4960 / 8831 | DTLS 1.3 + SCTP + ordered delivery |

## `Ice.lean` — the full RFC 8445 checklist

The core candidate-pair FSM (`frozen → waiting → inProgress → succeeded/failed`)
and the nomination send gate were already present. This pass adds the rest of
RFC 8445:

* **Candidate priority (§5.1.2.1).** `Cand.priority` is the exact formula
  `2^24·typePref + 2^8·localPref + (256 − componentId)`.
  * `priority_type_dominates` — for well-formed candidates (`localPref ≤ 65535`,
    `1 ≤ component ≤ 256`), a strictly higher type preference gives a strictly
    higher priority. This proves the bit-packing realizes the intended
    lexicographic order: the `2^24` shift is wide enough that the lower fields
    can never close the gap.
  * `ice_priority_total_order` — the induced "priority ≤" relation is reflexive,
    total (connex), and transitive: a genuine total order on the checklist.
* **Pair priority (§6.1.2.3).** `pairPriority g d = 2^32·min + 2·max + (g>d)`.
  `pair_priority_tiebreak` proves the low tie-break bit distinguishes the two
  role assignments when the candidate priorities differ (the magnitude term is
  symmetric under the swap, so only the tie-break bit can break the tie).
* **Pair formation (§6.1.2.2).** `formPairs` pairs each local candidate with each
  same-component remote candidate; `formPairs_not_deliverable` proves every fresh
  pair is `frozen` and un-nominated — pairing alone lets nothing flow.
* **Triggered checks (§7.3.1.4).** `triggeredCheck` reschedules a
  frozen/waiting/failed pair to `waiting` while leaving inProgress/succeeded
  alone. Deliberately *not* rank-monotone (a failed pair is re-queued), which is
  the point of a triggered check.
* **Role-conflict resolution (§7.3.1.1).** `resolveConflict` picks the
  larger-tie-breaker agent as controlling. `ice_role_conflict_resolves` proves
  that with distinct tie-breakers the two agents always resolve to *opposite*
  roles — exactly one controller, never two, never zero.
* **ICE restart (§9).** `restart` resets every pair to `frozen`/un-nominated;
  `ice_restart_no_deliver` proves the send gate is closed for all pairs
  immediately after a restart.
* `ice_no_send_before_nominated` — the extended send-gate theorem: `mayDeliver`
  opens only for a nominated pair (compose with the retained
  `ice_no_send_before_succeeded` for "nominated *and* succeeded").

## `WebrtcTransport.lean` — DTLS 1.3, SCTP, ordered delivery (NEW)

`import Crypto`: the DTLS key schedule and record layer use the real
HACL*/EverCrypt primitives, not stubs.

* **DTLS 1.3 handshake (RFC 9147 §5).** `dtlsStep` walks
  `start → wait_sh → wait_finished → established`. Key derivation
  (`deriveHandshakeKeys`, `deriveAppKeys`) is real HKDF-Extract/Expand
  (`Crypto.hkdfExtract` / `Crypto.hkdfExpand`); record protection is
  `Crypto.chachaSeal` / `Crypto.chachaOpen`.
  * `dtls_no_appdata_before_established` — a protected application record is
    produced only in the `established` state (and `dtls_no_recv_before_established`
    for the inbound side).
  * `dtls_appdata_authentic` — composes the gate with
    `Crypto.Assumptions.chacha_open_authentic`: any accepted record's plaintext
    is exactly what the peer sealed. This is the one conditional-security
    theorem; its `#print axioms` names `chacha_open_authentic`, the intended
    EverCrypt boundary axiom (discharged upstream by the F* AEAD proof).
* **SCTP association (RFC 4960 §5.1).** `sctpStep` walks
  `closed → cookieWait → cookieEchoed → established` via
  INIT / INIT-ACK / COOKIE-ECHO / COOKIE-ACK.
  * `sctp_assoc_4way` — via a rank argument (`sctpStep_rank_incr` +
    `sctpRun_rank_bound`), reaching `established` from `closed` takes at least
    three state transitions: the four-way exchange cannot be short-circuited.
  * `sctp_data_after_established` — the user-data gate opens only when
    established. `sctp_enter_established` — the sole edge into `established` is
    COOKIE-ACK from `cookieEchoed`.
* **Ordered delivery (RFC 8831 §6.6).** `OrdRecv.recv` holds out-of-order chunks
  in a reorder buffer and releases (`flush`) a maximal run of consecutive stream
  sequence numbers.
  * `datachannel_ordered` — the released SSNs are strictly increasing
    (`StrictSorted`).
  * `datachannel_consecutive` — the sharper form: they are gap-free from the next
    expected SSN (`Consecutive`), so ordered delivery reproduces the sender's
    sequence exactly.
  * `datachannel_nextSsn_mono` — the delivery pointer never rewinds.

## `Dcep.lean` — full DCEP (reliability & priority)

The open/ack handshake and stream-id parity were present. This pass adds:

* **Channel types (RFC 8832 §5.1 / §8.2.2).** The six type codes as an
  inductive with `toByte`/`ofByte`; `channelType_byte_roundtrip` proves the
  encoding is a faithful injection.
* **Reliability (§5.1).** `Reliability` = fully-reliable / partial-rexmit(N) /
  partial-timed(ms), with `reliabilityOf` interpreting the Reliability Parameter
  under each type. `mustDeliver_iff_fullyReliable` proves the delivery guarantee
  and the regime agree.
* **Priority (RFC 8831 §6.4).** The four recommended levels (128/256/512/1024);
  `priority_levels_ordered` proves the wire values are strictly ordered.
* **Channel config.** `configOf` derives an ordering + reliability + priority
  from a parsed OPEN; `configOf_ordered_consistent` and
  `configOf_reliability_consistent` prove the derived fields never contradict the
  channel type.

## The crypto boundary

DTLS key derivation and record protection call `Crypto.lean`'s EverCrypt seam.
The only crypto axiom any theorem here depends on is
`Crypto.Assumptions.chacha_open_authentic` (in `dtls_appdata_authentic`) — the
functional shadow of AEAD INT-CTXT, discharged upstream by the HACL*/EverCrypt
F* proof. Everything else depends only on `propext` / `Quot.sound` (and nothing
uses `Classical.choice`).

## Verifying

```
# single-file libs with no imports
lake env lean Ice.lean
lake env lean Dcep.lean
# imports Crypto — build the dependency graph
lake build Crypto WebrtcTransport
# axiom ledger
lake env lean <a file that imports the three and #print axioms ...>
```

All four files elaborate with zero `sorry` and zero unclosed goals; every
`#print axioms` lands inside `{propext, Quot.sound, Classical.choice}` plus the
single named EverCrypt authenticity axiom on the one conditional-security
theorem.
