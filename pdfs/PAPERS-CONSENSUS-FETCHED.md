# Consensus / distributed-adversary papers acquired (2026-05-30)

For the distributed-adversary / Byzantine / GST work (`docs/rebuild/PHASE-DISTRIBUTED-ADVERSARY.md`).
ember's `~/zotero-site` is rich in *modern* (2018–2025) consensus but had no pre-2000 classics; the
classics were fetched from arxiv / MIT-TDS mirrors.

## Copied from ~/zotero-site (the high-value modern subset)
- `zotero-formal-verification-blockchain-bft.pdf` — **mechanization template** (formal BFT verification; the l4v/velisarios analog for our Lean BFT model).
- `zotero-reconfigurable-heterogeneous-quorum-systems.pdf` — **modern Malkhi–Reiter** (quorum intersection-with-honest-witness; grounds O1's full safety theorem).
- `zotero-simplicial-epistemic-logic-faulty-agents.pdf` — epistemic logic of faulty agents (ammo for the **constructive-knowledge metatheory** + the disclosure dial).
- `zotero-tendermint-latest-gossip-on-bft-consensus.pdf` — partial-synchrony protocol (O2 liveness shape).
- `zotero-bft-protocol-forensics.pdf` — accountability/forensics (slashing the double-voter).
- `zotero-information-structure-of-indulgent-consensus.pdf`, `zotero-consensus-under-adversary-majority.pdf`,
  `zotero-optimal-authenticated-byzantine-agreement.pdf`, `zotero-on-consensus-number-1-objects.pdf`.
- (~70 more modern consensus papers remain in `~/zotero-site/storage/` under "Consensus & Agreement" — copy on demand.)

## Fetched (classics)
- `fetch-FLP-impossibility-1985.pdf` — Fischer–Lynch–Paterson (the async-consensus impossibility; framing for O2).
- `fetch-DLS88-partial-synchrony.pdf` — Dwork–Lynch–Stockmeyer, *Consensus in Partial Synchrony* (the **GST model** for O2).
- `fetch-hotstuff-2019.pdf` — HotStuff (PODC'19; the responsive view-based liveness proof to port for O2).

## Still missing (non-blocking)
- Malkhi–Reiter *Byzantine Quorum Systems* (1998, pre-arxiv) — substituted by `zotero-reconfigurable-heterogeneous-quorum-systems.pdf`.
- Streamlet (eprint 2020/088) + Canetti UC (eprint 2000/067) — IACR served HTML to curl; HotStuff covers the
  liveness template and no current OPEN needs Canetti-UC. Fetch from ember's Zotero / IACR if specifically wanted.

## Mapping to the OPENs (now closed-or-bounded; these enable the STRONG forms)
- **O1 full BFT safety** (honest-vote-once contradiction, beyond the pigeonhole already proved): `reconfigurable-heterogeneous-quorum-systems` + `formal-verification-blockchain-bft` (template) + DLS88.
- **O2 GST-liveness** (modeled-protocol proof, beyond the assumed `World.gst_liveness` law): DLS88 (GST) + HotStuff (view-based liveness) + Tendermint.
