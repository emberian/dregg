-- Metatheory: candidate-independent core for the dregg2 vat model.
--
-- Three modules are candidate-INDEPENDENT (all three dregg2 candidates share
-- the conservation law, the Predicate ⊣ Witness law, and the positional
-- authority model lifted from seL4/l4v integrity):
--
--   * Metatheory.Core              — symmetric-monoidal cells/turns + Σ_k conservation
--   * Metatheory.Laws              — Predicate ⊣ Witness Galois connection + verify/find seam
--   * Metatheory.Authority.Positional — the l4v integrity lift / vat-boundary law template
--   * Metatheory.Confluence        — the THIRD judgement: I-confluence / tier-1 eligibility
--
-- The Boundary/Soundness module is candidate-DEPENDENT. The dregg2 decision picks
-- the COINDUCTIVE (A-style, ▶-guarded bisimulation) shape (see
-- docs/rebuild/dregg2.md §1.3/§8 and metatheory/README.md §"candidate-dependent").
import Metatheory.Tactics       -- shared proof automation
import Metatheory.Core
import Metatheory.Resource
import Metatheory.Laws
import Metatheory.Authority.Positional
import Metatheory.Confluence
import Metatheory.Boundary
-- Wave (multi-cell + distributed + privacy + coordination + effects + lifecycle):
import Metatheory.StepCamera     -- step-indexed Iris camera (higher-order resources; shares Boundary's ▶)
import Metatheory.JointTurn      -- cross-cell ⊗ : equalizer + CG-2 pullback + CG-5 aggregate, binding-as-hypothesis
import Metatheory.Finality       -- judgement 2: the 4-tier finality lattice + cross-tier join
import Metatheory.Privacy        -- field / value (Pedersen) / graph (stealth+nullifier) privacy tiers
import Metatheory.Coordination   -- MPST global type G → projection → protocol-cell; deadlock-freedom
import Metatheory.Projection     -- cand-D choreography front-end: blue/red split + epp_correspondence (= boundary_law at two altitudes)
import Metatheory.Await          -- algebraic effects + one-shot continuations; turn-as-rollback-handler
import Metatheory.Liveness       -- GC-as-cell-liveness; lease-expiry; cross-vat cycle leak (impossibility)
import Metatheory.Upgrade        -- anti-brick set_program: AIR_VERSION pin + signature fallback
import Metatheory.Execution      -- userspace programs: configurations, runs, invariant-preservation (PROVED)
import Metatheory.CryptoKernel    -- THE PORTAL: crypto ops as an uninterpreted interface (Lean⟷Rust); verify/find seam instantiated; cross-vat bridge closed
import Metatheory.PrivacyKernel   -- privacy realized over the portal: committed_conservation + nullifier anti-double-spend PROVED via the interface laws
import Metatheory.World           -- the sibling portal: network/clock/randomness oracle for consensus; quorum finality over it (PROVED) + Byzantine/GST OPEN
import Metatheory.Exec.Kernel     -- the EXECUTABLE kernel (Design-Spec layer): exec checks conservation+authority, fail-closed; PROVED + #eval
import Metatheory.Exec.Generators -- mint/burn conservation generators (mint_delta/burn_delta PROVED)
import Metatheory.Exec.Caps        -- capability ops (grant/attenuate/derive/revoke/invoke) + integrity bridge (PROVED)
import Metatheory.Exec.Unified      -- ONE KernelOp + step: unified conservation (step_delta) + ledger (PROVED)
import Metatheory.Exec.CellProgram -- the CellProgram DSL = the executable coalgebra structure-map; denote_conserves PROVED
import Metatheory.Proof.Refine    -- Exec ⊑ Abstract: conservation + integrity-intra refinement (PROVED), simulation diagram OPEN
-- Executable protocols (concrete, computable, theorems PROVED — no sorry):
import Metatheory.Protocol.Transfer  -- two-cell atomic token transfer + payment-channel run; conservation/CG-5/atomicity proved + #eval
import Metatheory.Protocol.Workflow  -- RDII demonstrator: authenticated, capability-gated, attested multi-party workflow (DocuSign-for-workflows); all guarantees PROVED + #eval
