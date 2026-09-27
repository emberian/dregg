/* lean_init.c — a tiny C shim performing the Lean C-embedding init ritual.
 *
 * Many of the runtime entry points the ritual needs (`lean_io_mk_world`,
 * `lean_io_result_is_ok`, `lean_dec_ref`) are `static inline` in <lean/lean.h>
 * and therefore have NO linkable symbol — they can only be used from C that
 * includes the header. So we wrap the whole ritual here and expose a single
 * helpers for the shared lifecycle in lib.rs. The public dregg_ffi_init ABI
 * enters that coordinator; no caller may start the runtime prefix twice.
 */
#include <stdint.h>
#include <string.h>
#include <lean/lean.h>
#include "lean_init_internal.h"

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

/* The @[export]ed Lean `String -> String` state-marshalling step. At the C ABI a Lean
 * `String` is a `lean_object*`, so this takes/returns boxed Lean strings — which is why
 * it must be driven from C (the `lean_mk_string`/`lean_string_cstr` helpers below). */
extern lean_object *dregg_record_kernel_step(lean_object *input);

/* The @[export]ed Lean `String -> String` CAPS-bearing step: same shape, but the wire also
 * carries the held-cap table so the cross-vat / held-cap branch of `authorizedB` is exercised. */
extern lean_object *dregg_record_kernel_step_caps(lean_object *input);

/* The @[export]ed Lean `String -> String` FULL-TURN executor: decodes a
 * (RecChainedState, List FullAction), runs the PROVED `execFullTurn` (all-or-nothing), and
 * re-encodes the resulting Option state (post-cells + post-caps + receipt-log length + commit). */
extern lean_object *dregg_exec_full_turn(lean_object *input);

/* The @[export]ed Lean `String -> String` GATED COMPLETE-TURN executor (FILL X): decodes the §WIDE wire
 * (Turn envelope + action-tree node=auth+action+children + the 10-variant Authorization + all 45 effect
 * arms + the escrow/nullifier/commitment/swiss/queue side-tables), runs the PROVED gated tree executor
 * `FullForestAuth.execFullForestG` (the credentialValid ∧ cap-authority ∧ caveat-discharge fail-closed
 * gate in front of `execFullA`, all-or-nothing), and re-encodes the §WIDE output (post-state + receipt-log
 * length + commit; on rollback ok:0 echoes the unchanged pre-state). */
extern lean_object *dregg_exec_full_forest_auth(lean_object *input);

/* The @[export]ed Lean `String -> String` HANDLER-CUTOVER COMPLETE-TURN executor: decodes the §WIDE wire
 * (Turn envelope + auth-decorated action-tree + full state), runs host-fed admission followed by the
 * credential-preserving handler fold (`lowerForestG`; four-leg `gateOK` on the exact pre-state before
 * each `execHandlerOne` dispatch), and re-encodes the §WIDE output (post-state + receipt-log length +
 * three-way status; a refused body is never reported committed).
 *
 * GATED on DREGG_HANDLER_TURN: this secondary export is absent from older archives. build.rs probes the
 * archive and only `#define`s DREGG_HANDLER_TURN when the symbol is present, so a stale archive does not
 * leave a dangling reference that `-dead_strip` would resolve by dropping the entire shim object. */
#ifdef DREGG_HANDLER_TURN
extern lean_object *dregg_exec_handler_turn(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED FINALITY GATE
 * (`Dregg2.Distributed.FinalityGate.finalizeGate`): decodes a wire-encoded
 * (wavelength, participants, lace), runs the VERIFIED `BlocklaceFinality.tauOrder` rule, and
 * re-encodes the finalized `(creator, seq)` order (or the `ERR` sentinel on a malformed wire). The
 * node calls this at the live commit point to compute finality FROM the verified rule, then admits a
 * turn to the executor ONLY when the verified rule finalizes it ("agreement-checked" -> "Lean-gated").
 *
 * GATED on DREGG_FINALIZE_GATE: this export lives in a module NOT in the FFI module's import closure,
 * so (a) build.rs probes the archive and only `#define`s DREGG_FINALIZE_GATE when the symbol is
 * present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer (it is not reached by
 * `initialize_Dregg2_Dregg2_Exec_FFI`). When absent, the bridge is compiled out and the node falls
 * back to the un-gated path with a loud warning. */
#ifdef DREGG_FINALIZE_GATE
extern lean_object *initialize_Dregg2_Dregg2_Distributed_FinalityGate(uint8_t builtin);
extern lean_object *dregg_blocklace_finalize(lean_object *input);
/* The RAW total-order export, co-located in `Dregg2.Distributed.FinalityGate`: returns the verified
 * `BlocklaceFinality.tauOrder` ITSELF (the ordered BlockId list `"T=<id>,<id>,..."`), proved
 * order-faithfully equal to `tauOrder` by `tau_order_export_eq`. Same module ⇒ same initializer ⇒
 * gated on the same DREGG_FINALIZE_GATE define. */
extern lean_object *dregg_tau_order(lean_object *input);
/* The verified FINALIZATION-VOTE QUORUM decision, co-located in `Dregg2.Distributed.FinalityGate`:
 * decodes a deduped `(signer, root)` tally + committee size, runs the VERIFIED
 * `FinalizationQuorum.quorumRoot` (proved sound + conflict-free), and returns `"R=<root>"` / `"NONE"`
 * / `"ERR"`. Same module ⇒ same initializer ⇒ gated on the same DREGG_FINALIZE_GATE define. */
extern lean_object *dregg_finalization_quorum(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED STRAND-ADMISSION GATE
 * (`Dregg2.Distributed.StrandAdmission.admitGate`): decodes a wire-encoded admission registry +
 * queried strand (`"N=<vouch-threshold>;m=<min-bond>;S=<seeds>;V=<vouches>;Bo=<bonds>;q=<strand>"`),
 * runs the VERIFIED hybrid stake-OR-vouch `admitted` predicate, and returns `"1"` (admitted) / `"0"`
 * (not admitted) / `"ERR"` (fail-closed on a malformed wire). The federation calls this at the
 * admission point to compute the F-4 Sybil verdict FROM the verified rule itself.
 *
 * GATED on DREGG_STRAND_ADMIT: like the finality gate, this export lives in a module OUTSIDE the FFI
 * module's import closure, so (a) build.rs probes the archive and only `#define`s DREGG_STRAND_ADMIT
 * when the symbol is present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer. */
#ifdef DREGG_STRAND_ADMIT
extern lean_object *initialize_Dregg2_Dregg2_Distributed_StrandAdmission(uint8_t builtin);
extern lean_object *dregg_strand_admit(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED ES ROUND-ADVANCE GATE
 * (`Dregg2.Distributed.RoundAdvanceGate.advanceWireGate`): decodes a wire-encoded
 * `(round, timeout-bit, wavelength, participants, lace)` query
 * (`"r=<round>;t=<0|1>;w=<W>;P=<participants>;B=<blocks>"` — the tail is the finality gate's lace
 * grammar), runs the VERIFIED Cordial-Miners Alg. 4:67-75 advance predicate (advance a cordial
 * round only on leader present/ratified/super-ratified or timeout), and returns `"1"` (advance) /
 * `"0"` (hold) / `"ERR"` (fail-closed - the node HOLDS). The round producer calls this before
 * honoring a `RoundPlan::Advance`.
 *
 * GATED on DREGG_ROUND_ADVANCE: like the finality/strand gates, this export lives in a module
 * OUTSIDE the FFI module's import closure, so (a) build.rs probes the archive and only `#define`s
 * DREGG_ROUND_ADVANCE when the symbol is present, and (b) `dregg_ffi_init` must ALSO run the
 * module's own initializer. */
#ifdef DREGG_ROUND_ADVANCE
extern lean_object *initialize_Dregg2_Dregg2_Distributed_RoundAdvanceGate(uint8_t builtin);
extern lean_object *dregg_round_advance(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED ACKNOWLEDGE-BEFORE-ADMIT GATE
 * (`Dregg2.Distributed.AckBeforeAdmit.ackWireGate`, blocklace paper s5.3): decodes a
 * wire-encoded `(head, buffered-set, wavelength, participants, lace)` query
 * (`"h=<head>;D=<blocks>;w=<W>;P=<participants>;B=<blocks>"` — the tail is the finality gate's
 * lace grammar), runs the VERIFIED batch-admission predicate (first-evidence OR acknowledged
 * head with the R_q freshness tooth — the discipline whose absence voids Prop. 5.5's finite
 * harm), and returns `"1:<ids>"` (admit, insertion order) / `"0"` (hold) / `"ERR"` (fail-closed
 * — the node HOLDS). The ingest path calls this before any fork-context insert.
 *
 * GATED on DREGG_ACK_ADMIT: like the finality/strand/round-advance gates, this export lives in
 * a module OUTSIDE the FFI module's import closure, so (a) build.rs probes the archive and only
 * `#define`s DREGG_ACK_ADMIT when the symbol is present, and (b) `dregg_ffi_init` must ALSO run
 * the module's own initializer. */
#ifdef DREGG_ACK_ADMIT
extern lean_object *initialize_Dregg2_Dregg2_Distributed_AckBeforeAdmit(uint8_t builtin);
extern lean_object *dregg_ack_admit(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED CapTP + COORDINATION decision gates
 * (`Dregg2.Exec.DistributedExports`): six wire-in/wire-out exports the captp/coord runtime invokes
 * so it computes its verdict FROM the verified Lean rule itself (dreggrs Rust → differential):
 *   dregg_captp_validate_handoff — §6 non-amplification (handoffNonAmplifyingC granted⊆held);
 *   dregg_captp_process_drop     — GC session-refcount verdict (CapTPGCConcrete.processDrop);
 *   dregg_captp_pipeline_resolve — promise-pipelining FIFO resolve/break drain;
 *   dregg_coord_2pc_decide       — 2PC evaluate_votes (TwoPhaseCommit.evaluate);
 *   dregg_coord_causal_order     — causal-DAG happened_before (CausalOrder via decidable hbBool);
 *   dregg_coord_shared_budget    — shared-budget tau-resolution (SharedBudgetDynamics.resolveOrdered).
 *
 * GATED on DREGG_DISTRIBUTED_EXPORTS: this module is OUTSIDE the FFI module's import closure, so
 * (a) build.rs probes the archive and only `#define`s it when `dregg_captp_validate_handoff` is
 * present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer. When absent the
 * bridges are compiled out and the captp/coord runtime falls back to its native Rust gates. */
#ifdef DREGG_DISTRIBUTED_EXPORTS
extern lean_object *initialize_Dregg2_Dregg2_Exec_DistributedExports(uint8_t builtin);
extern lean_object *dregg_captp_validate_handoff(lean_object *input);
extern lean_object *dregg_captp_process_drop(lean_object *input);
extern lean_object *dregg_captp_pipeline_resolve(lean_object *input);
extern lean_object *dregg_coord_2pc_decide(lean_object *input);
extern lean_object *dregg_coord_causal_order(lean_object *input);
extern lean_object *dregg_coord_shared_budget(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED FLOW-REFINEMENT DECISION GATE
 * (`Dregg2.Deos.FlowRefine.decideRefinesGate`): decodes a wire-encoded pair of σ-free `Proc`s
 * (`"A=<preorder-tokens>;B=<preorder-tokens>"`), runs the PROVED `decideRefines` (sound+complete for
 * the online-simulation refinement order `≤ᶠ`, per `decideRefines_iff`), and returns `"1"` (A ≤ᶠ B) /
 * `"0"` (A ⋠ B) / `"ERR"` (fail-closed on a malformed wire). `dregg-deploy/src/refine.rs` calls this
 * at the safe-upgrade / intent-conformance gate so it runs the verified procedure, not a mirror.
 *
 * GATED on DREGG_DECIDE_REFINES: this export lives in a module OUTSIDE the FFI module's import
 * closure, so (a) build.rs probes the archive and only `#define`s DREGG_DECIDE_REFINES when the symbol
 * is present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer. When absent the
 * bridge is compiled out and the deploy gate falls back to its in-process σ-free mirror. */
#ifdef DREGG_DECIDE_REFINES
extern lean_object *initialize_Dregg2_Dregg2_Deos_FlowRefine(uint8_t builtin);
extern lean_object *dregg_decide_refines(lean_object *input);
#endif

/* The NO-COPY (`lean_object*`) DIRECT boundary lives in `Dregg2.Exec.FFIDirect`, which IMPORTS
 * `Dregg2.Exec.FFI` — so its initializer is OUTSIDE the FFI module's import closure and is NOT run by
 * `initialize_Dregg2_Dregg2_Exec_FFI`. `dregg_ffi_init` must run it explicitly (like the gate modules
 * above). The builders/readers + `dregg_exec_full_forest_auth_direct` are called DIRECTLY from Rust
 * (plain C-ABI `lean_object*` functions), so no string bridge lives here — only the initializer.
 *
 * GATED on DREGG_DIRECT: build.rs probes the archive and only `#define`s it when the export is
 * present, so a stale archive does not leave a dangling `initialize_…_FFIDirect` reference. */
#ifdef DREGG_DIRECT
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFIDirect(uint8_t builtin);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED STORAGE CONTENT ROOT
 * (`Dregg2.Storage.Deployed.contentRootFFI`): decodes space-separated object int-triples, runs the
 * PROVED `contentRootDeployed` (bound by `contentRootDeployed_injective` over the deployed Poseidon2,
 * called back through `@[extern "dregg_poseidon2_2to1"]` = `circuit::storage_ffi`), returns the root
 * felt as a decimal string. The verified content-root LOGIC is Lean; the hot hash PRIMITIVE is fast
 * Rust — the real "Lean is the runtime" for storage. GATED on DREGG_STORAGE_CONTENT_ROOT (the module
 * is OUTSIDE the FFI closure; build.rs probes + defines it, and dregg_ffi_init runs its initializer). */
#ifdef DREGG_STORAGE_CONTENT_ROOT
extern lean_object *initialize_Dregg2_Dregg2_Storage_Deployed(uint8_t builtin);
extern lean_object *dregg_storage_content_root(lean_object *input);
#endif

/* The exported Lean `String -> String` deployed-constraint evaluator. */
#ifdef DREGG_CONSTRAINT_ADMITS
extern lean_object *initialize_Dregg2_Dregg2_Exec_DeployedConstraint(uint8_t builtin);
extern lean_object *dregg_constraint_admits(lean_object *input);
#endif

/* The exported Lean `String -> String` cross-cell per-asset conservation decision
 * (`Dregg2.Circuit.CrossCellConserveDecision.conservesFFI`): parses the `(asset, delta)` rows +
 * declared mint/burn supply, ADMITS iff every asset's signed sum is zero, else refuses with the first
 * imbalanced asset. Proved EQUAL to the committed Σδ=0 AIR boundary by
 * `CrossCellConserveRefine.decision_conserves_iff_air_boundary`. GATED on DREGG_CROSS_CELL_CONSERVES
 * (the module is OUTSIDE the FFI closure; build.rs probes + defines it, and dregg_ffi_init runs its
 * initializer). */
#ifdef DREGG_CROSS_CELL_CONSERVES
extern lean_object *initialize_Dregg2_Dregg2_Circuit_CrossCellConserveDecision(uint8_t builtin);
extern lean_object *dregg_cross_cell_conserves(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED ML-DSA VERIFY CORE
 * (`Dregg2.Crypto.Fips204Verify.verifyFFI`): decodes the wire `"thi μ c̃ z h"`, runs the extracted,
 * spec-agreeing `verifyCore` (= `Fips204Spec.MlDsaParams.verifyB` at the deployed ML-DSA-65 parameters —
 * the round-to-nearest rounding, the hint round-trip, the norm gate, the challenge fixed-point), returns
 * `"1"` (accept) / `"0"` (reject). The SECURITY-CRITICAL verify direction as leanc-native code — a forged
 * signature REJECTS. GATED on DREGG_FIPS204_VERIFY (the module is OUTSIDE the FFI closure; build.rs probes
 * + defines it, and dregg_ffi_init runs its initializer). */
#ifdef DREGG_FIPS204_VERIFY
extern lean_object *initialize_Dregg2_Dregg2_Crypto_Fips204Verify(uint8_t builtin);
extern lean_object *dregg_fips204_verify(lean_object *input);
#endif

/* BRICK 8 — the REAL, FULL-BYTE ML-DSA-65 verify export
 * (`Dregg2.Crypto.Fips204Verify.verifyRealFFI`): decodes the wire `"hex(pk) hex(msg) hex(ctx) hex(sig)"`,
 * runs the FULL-DIMENSION Lean-verified `MlDsaVerifyReal.verifyCore` (n=256 ring / NTT / SampleInBall /
 * ExpandA / real 1952/3309-byte codec) over the actual bytes, and returns `"1"` (accept) / `"0"` (reject).
 * This is the object that takes the `fips204` crate OUT of the deployed verify TCB. It lives in the SAME
 * module as `dregg_fips204_verify` (`Dregg2.Crypto.Fips204Verify`), so its initializer is the SAME
 * `initialize_Dregg2_Dregg2_Crypto_Fips204Verify` (run below) — no separate init is required. GATED on
 * DREGG_FIPS204_VERIFY_REAL (build.rs probes + defines it when the symbol is present). */
#ifdef DREGG_FIPS204_VERIFY_REAL
extern lean_object *dregg_fips204_verify_real(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED ML-DSA SIGN CORE
 * (`Dregg2.Crypto.Fips204Verify.signFFI`): decodes the wire `"s1 s2 t0 μ y"` (secret + message + the
 * sampled randomness/mask), runs the extracted, spec-agreeing `signCore` (the deterministic
 * Fiat–Shamir-with-aborts signer at the deployed ML-DSA-65 parameters), and returns the signature wire
 * `"c̃ z h"` on an ACCEPTED iteration or `"REJECT"` on a rejected sample / malformed wire. Together with
 * `dregg_fips204_verify` this discharges `Fips204Correct` FULLY (both directions extracted).
 *
 * GATED on DREGG_FIPS204_SIGN. The symbol is co-located in the SAME module as the verify core
 * (`Dregg2.Crypto.Fips204Verify`), so its initializer is the SAME
 * `initialize_Dregg2_Dregg2_Crypto_Fips204Verify` already run under DREGG_FIPS204_VERIFY — no separate
 * init is required here (build.rs probes + defines DREGG_FIPS204_SIGN when the symbol is present). */
#ifdef DREGG_FIPS204_SIGN
extern lean_object *dregg_fips204_sign(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED ML-KEM (FIPS 203) ENCAPS/DECAPS CORES
 * (`Dregg2.Crypto.Fips203Kem.encapsFFI` / `decapsFFI`): the extracted Kyber CPAPKE + Fujisaki–Okamoto
 * transform at the deployed q=3329 message-decode. encapsFFI reads `"A t m"` and returns `"u v K"` (the
 * ciphertext + encapsulated secret K=H(m)); decapsFFI reads `"A t s z u v"`, decrypts, RE-ENCRYPTS,
 * and returns the recovered shared secret K (H(m') on a matching re-encryption, else the implicit-reject
 * secret J(z‖c) — ML-KEM decaps never fails, a tampered ct yields a DIFFERENT message-independent
 * secret). The SECURITY-CRITICAL decaps direction as leanc-native code; together they discharge
 * `DreggKemRefinement.Fips203Correct` (the encaps→decaps round-trip) with no `ml-kem` crate hypothesis.
 *
 * GATED on DREGG_FIPS203 (the module is OUTSIDE the FFI closure; build.rs probes + defines it, and
 * dregg_ffi_init runs its initializer). Both cores share the SAME
 * `initialize_Dregg2_Dregg2_Crypto_Fips203Kem` (same module), so one init serves both; the individual
 * DREGG_FIPS203_ENCAPS / DREGG_FIPS203_DECAPS defines gate only the per-export extern + bridge. */
#ifdef DREGG_FIPS203
extern lean_object *initialize_Dregg2_Dregg2_Crypto_Fips203Kem(uint8_t builtin);
#endif
#ifdef DREGG_FIPS203_ENCAPS
extern lean_object *dregg_fips203_encaps(lean_object *input);
#endif
#ifdef DREGG_FIPS203_DECAPS
extern lean_object *dregg_fips203_decaps(lean_object *input);
#endif

/* BRICK K6 — the REAL, FULL-BYTE ML-KEM-768 DECAPS export
 * (`Dregg2.Crypto.MlKemDecaps.mlkemDecapsRealFFI`): decodes the wire `"hex(dk) hex(ct)"`, runs the
 * FULL-DIMENSION Lean-verified `mlkemDecaps` (the FO pipeline: SHA3-512 `G` split / K-PKE decrypt / NTT /
 * re-encryption / byte-exact implicit-reject over the real 2400-byte dk / 1088-byte ct — NOT the `A=1,n=1`
 * scalar toy of `Fips203Kem`) and returns `hex(K)` (the recovered 32-byte shared secret) or `"ERR"` on a
 * malformed wire. This is the object that takes the `ml-kem` crate OUT of the deployed KEM-decaps TCB. Unlike
 * the `Fips203Kem` cores, this lives in its OWN module `Dregg2.Crypto.MlKemDecaps`, so it needs its OWN
 * initializer `initialize_Dregg2_Dregg2_Crypto_MlKemDecaps` (run below). GATED on DREGG_MLKEM_DECAPS_REAL
 * (build.rs probes + defines it when the symbol is present). */
#ifdef DREGG_MLKEM_DECAPS_REAL
extern lean_object *initialize_Dregg2_Dregg2_Crypto_MlKemDecaps(uint8_t builtin);
extern lean_object *dregg_mlkem_decaps_real(lean_object *input);
#endif

/* BRICK K5 — the REAL, FULL-BYTE ML-KEM-768 ENCAPS export (the ENCAPS mirror of K6)
 * (`Dregg2.Crypto.MlKemEncaps.mlkemEncapsRealFFI`): decodes the wire `"hex(ek) hex(m)"`, runs the
 * FULL-DIMENSION Lean-verified `mlkemEncaps` (the deterministic FIPS 203 Alg 16 FO encaps: `H(ek)` SHA3-256 /
 * `G(m ‖ H(ek))` SHA3-512 split / K-PKE.Encrypt over the real 1184-byte ek — NOT the `A=1,n=1` scalar toy) and
 * returns `"hex(ct) hex(K)"` (the 1088-byte ciphertext + the 32-byte shared secret) or `"ERR"` on a malformed
 * wire. This is the object that takes the `ml-kem` crate OUT of the deployed KEM-ENCAPS TCB. Its OWN module
 * `Dregg2.Crypto.MlKemEncaps` (imports `MlKemDecaps` for `kpkeEncrypt`), so it needs its OWN initializer
 * `initialize_Dregg2_Dregg2_Crypto_MlKemEncaps` (run below). GATED on DREGG_MLKEM_ENCAPS_REAL (build.rs probes
 * + defines it when the symbol is present). */
#ifdef DREGG_MLKEM_ENCAPS_REAL
extern lean_object *initialize_Dregg2_Dregg2_Crypto_MlKemEncaps(uint8_t builtin);
extern lean_object *dregg_mlkem_encaps_real(lean_object *input);
#endif

/* BRICK K7 - the REAL, FULL-BYTE ML-KEM-768 KEYGEN export
 * (`Dregg2.Crypto.MlKemKeygen.mlkemKeygenRealFFI`): decodes the wire `"hex(d z)"` (64-byte seed), runs the
 * deterministic FIPS 203 ML-KEM.KeyGen_internal and returns `"hex(ek) hex(dk)"` (1184-byte ek + 2400-byte dk)
 * or `"ERR"` on a malformed wire. Takes the `ml-kem` crate OUT of the deployed KEM-KEYGEN TCB. Its OWN module
 * `Dregg2.Crypto.MlKemKeygen`, so it needs its OWN initializer `initialize_Dregg2_Dregg2_Crypto_MlKemKeygen`
 * (run below). GATED on DREGG_MLKEM_KEYGEN_REAL (build.rs probes + defines it when the symbol is present). */
#ifdef DREGG_MLKEM_KEYGEN_REAL
extern lean_object *initialize_Dregg2_Dregg2_Crypto_MlKemKeygen(uint8_t builtin);
extern lean_object *dregg_mlkem_keygen_real(lean_object *input);
#endif

/* THE identity-key KEYGEN mirror — the REAL, FULL-BYTE ML-DSA-65 KEYGEN export
 * (`Dregg2.Crypto.MlDsaKeygen.mldsaKeygenRealFFI`): decodes the wire `"hex(xi)"` (one 32-byte seed field),
 * runs the FULL-DIMENSION Lean-verified `mldsaKeygenInternal` (the deterministic FIPS 204
 * ML-DSA.KeyGen_internal: H split, ExpandA, ExpandS, t = NTT^-1(A.NTT(s1))+s2, Power2Round, pkEncode/skEncode)
 * and returns `"hex(pk) hex(sk)"` (1952-byte pk + 4032-byte sk) or `"ERR"` on a malformed wire. Takes the
 * `fips204` crate OUT of the deployed IDENTITY-KEY keygen TCB. Its OWN module `Dregg2.Crypto.MlDsaKeygen`,
 * so it needs its OWN initializer `initialize_Dregg2_Dregg2_Crypto_MlDsaKeygen` (run below). GATED on
 * DREGG_MLDSA_KEYGEN_REAL (build.rs probes + defines it when the symbol is present). */
#ifdef DREGG_MLDSA_KEYGEN_REAL
extern lean_object *initialize_Dregg2_Dregg2_Crypto_MlDsaKeygen(uint8_t builtin);
extern lean_object *dregg_mldsa_keygen_real(lean_object *input);
#endif

/* THE brick-8 SIGN analog — the REAL, FULL-BYTE ML-DSA-65 SIGN export
 * (`Dregg2.Crypto.MlDsaSignReal.signRealFFI`): decodes the wire `"hex(sk) hex(msg) hex(ctx)"`, runs the
 * FULL-DIMENSION Lean-verified `signCore` (skDecode / ExpandMask / NTT / SampleInBall / ExpandA / MakeHint /
 * the Fiat–Shamir-with-aborts rejection loop over the real 4032-byte sk — NOT the `A=id` scalar toy of
 * `Fips204Verify`) and returns `hex(sig)` (the 3309-byte signature) or `"ERR"` on a malformed wire. This is
 * the object that takes the `fips204` crate OUT of the deployed SIGN TCB. Unlike the co-located
 * `dregg_fips204_sign`, this lives in its OWN module `Dregg2.Crypto.MlDsaSignReal`, so it needs its OWN
 * initializer `initialize_Dregg2_Dregg2_Crypto_MlDsaSignReal` (run below). GATED on DREGG_FIPS204_SIGN_REAL
 * (build.rs probes + defines it when the symbol is present). */
#ifdef DREGG_FIPS204_SIGN_REAL
extern lean_object *initialize_Dregg2_Dregg2_Crypto_MlDsaSignReal(uint8_t builtin);
extern lean_object *dregg_fips204_sign_real(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED GRAIN R3 whole-history verify core
 * (`Dregg2.Grain.R3Verify.r3VerifyFFI`): decodes the wire `"aggregateVerified aggregateHead
 * anchoredHead"` (three decimal ints), runs the PROVED `r3VerifyCore`
 * (`aggregateVerified && aggregateHead == anchoredHead`) and returns `"1"` (accept) / `"0"` (reject;
 * also the fail-closed answer for a malformed wire). This is the R3-accept DECISION as leanc-native
 * code: `aggregateVerified` is the whole-chain STARK verifier's status and the head equality binds the
 * verified history to THIS grain's R1 anchor (`Dregg2.Grain.R3Verify.r3_unfoolable` — the unfoolable
 * whole history REDUCED to the named `EngineSound` boundary + head-binding, not an unconditional
 * proof). GATED on DREGG_GRAIN_R3_VERIFY (the module is OUTSIDE the FFI closure; build.rs probes +
 * defines it). NOTE: unlike the crypto cores, R3's export needs NO module initializer — its
 * generated C hoists the "1"/"0"/" " string literals into STATIC CONST `lean_string_object`s and its
 * one closure into a LAZY `lean_once_cell`, so `dregg_grain_r3_verify` is self-contained. We therefore
 * deliberately do NOT reference `initialize_Dregg2_Dregg2_Grain_R3Verify`: that initializer chains into
 * `Dregg2.Circuit.RecursiveAggregation`'s Mathlib-tactic import closure (ProofWidgets / Batteries
 * init symbols the leanc-native archive does not carry), so calling it would drag undefined
 * initializer symbols into the final link. Leaving it unreferenced lets `-dead_strip` drop the whole
 * proof closure — the pure verify core links and runs on the always-initialized Init runtime. */
#ifdef DREGG_GRAIN_R3_VERIFY
extern lean_object *dregg_grain_r3_verify(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED HOLDING grant-weight verdict core
 * (`Metatheory.Bridge.ProofOfHoldings.grantWeightFFI`): decodes the wire `"isConsensusProven slotFinal
 * amount"` (three decimal ints), runs the PROVED `grantWeightCore` (`if isConsensusProven && slotFinal
 * then amount else 0`) and returns the granted weight as a decimal string (`= amount` when granted,
 * `"0"` when refused; `"0"` is also the fail-closed answer for a negative amount / malformed wire). This
 * is the non-custodial proof-of-holdings → governance-weight DECISION as leanc-native code, proved to
 * realize the `grantsWeight` spec (`grantWeightCore_eq_grantsWeight`); `dregg-governance` does the
 * fast-Rust pre-checks and routes the weight verdict through it. GATED on DREGG_HOLDING_GRANT_WEIGHT
 * (build.rs probes + defines it). NOTE: like R3's export it needs NO module initializer — its generated
 * C hoists the string literals into STATIC CONST `lean_string_object`s and its closure into a LAZY
 * `lean_once_cell`, so `dregg_holding_grant_weight` is self-contained. We therefore deliberately do NOT
 * reference `initialize_Metatheory_Metatheory_Bridge_ProofOfHoldings`: that initializer chains into the
 * `Dregg2.Tactics` (Mathlib-tactic) import closure's init symbols the leanc-native archive does not
 * carry; leaving it unreferenced lets `-dead_strip` drop the proof closure — the pure verdict core links
 * and runs on the always-initialized Init runtime. */
#ifdef DREGG_HOLDING_GRANT_WEIGHT
extern lean_object *dregg_holding_grant_weight(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED INTERCHAIN reached-consensus verdict core
 * (`Dregg2.Bridge.InterchainAdapterDecision.reachedConsensusFFI`): decodes the wire `"tag payload"`
 * (two decimal ints — the rung selector `tag ∈ {0,1,2,3}` = proof/watchtower/committee/rpc, and the
 * watchtower/committee resolution bit `payload`), runs the PROVED `reachedConsensusWire` (over
 * `reachedConsensusCore`: `proof` / resolved-valid watchtower / quorum committee reach; `rpc`, a
 * fraud/unresolved watchtower, a no-quorum committee, and any UNKNOWN tag all refuse — the Nomad-law
 * default) and returns `"1"` (reached consensus) / `"0"` (refused; also the fail-closed answer for a
 * malformed wire). This is the bridge TRUST verdict as leanc-native code, proved to realize the
 * `reachesConsensusSpec` fail-closed spec (`reachedConsensusCore_correct` +
 * `reachedConsensusWire_realizes_core`); `dregg-bridge::interchain_adapter`'s
 * `TrustRung::reached_consensus` marshals the rung and routes the verdict through it. GATED on
 * DREGG_INTERCHAIN_REACHED_CONSENSUS (build.rs probes + defines it). NOTE: like R3's / holding's
 * export it needs NO module initializer — its generated C hoists the string literals into STATIC CONST
 * `lean_string_object`s and its closure into a LAZY `lean_once_cell`, so
 * `dregg_interchain_reached_consensus` is self-contained. We therefore deliberately do NOT reference
 * `initialize_Dregg2_Dregg2_Bridge_InterchainAdapterDecision`: that initializer chains into the
 * `Dregg2.Tactics` (Mathlib-tactic) import closure's init symbols the leanc-native archive does not
 * carry; leaving it unreferenced lets `-dead_strip` drop the proof closure — the pure verdict core
 * links and runs on the always-initialized Init runtime. */
#ifdef DREGG_INTERCHAIN_REACHED_CONSENSUS
extern lean_object *dregg_interchain_reached_consensus(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` AUTOMATAFL GAME ORACLE
 * (`Dregg2.Games.AutomataflFFI.rulesFFI`): the verb-dispatched wire over the rules-faithful spec
 * `Dregg2.Games.AutomataflRules` — `stock` / `goals` / `sense` / `step` / `mid` / `turn` / `legal` /
 * `clash` / `round`. Every board transition, legality verdict, conflict set and win the deployed
 * automatafl surface reports is computed HERE. It replaces `dregg-automatafl/src/reference.rs`, a
 * hand transcription of `~/dev/automatafl/logic` (a non-canonical experiment) that the conformance
 * audit found divergent from the ruleset on 2-cycles (it SWAPPED the pair; the ruleset keeps both
 * pieces put) and on the path check (its occlusion scan skipped the DESTINATION, so a mover
 * overwrote a stationary piece). GATED on DREGG_AUTOMATAFL_RULES (build.rs probes + defines it).
 *
 * UNLIKE R3's / holding's / interchain's / FRI's exports this one DOES need its module initializer:
 * the `stock` verb reads `Dregg2.Games.AutomataflRules.stockTwoPlayer`, a nullary def the generated
 * C compiles to a module-level global (`lp_Dregg2_Dregg2_Games_AutomataflRules_stockTwoPlayer`) that
 * only `initialize_Dregg2_Dregg2_Games_AutomataflRules` fills — an un-initialized call would read
 * NULL. It is therefore initialized explicitly in `dregg_ffi_init` below, exactly like
 * `Dregg2.Deos.FlowRefine` / `Dregg2.Crypto.Fips203Kem` (whose closures also contain
 * `Dregg2.Tactics`, so this drags in no init edge those do not already drag in). */
#ifdef DREGG_AUTOMATAFL_RULES
extern lean_object *initialize_Dregg2_Dregg2_Games_AutomataflFFI(uint8_t builtin);
extern lean_object *dregg_automatafl_rules(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` MULTIWAY-TUG RULES ORACLE
 * (`Dregg2.Games.MultiwayTugFFI.rulesFFI`): the verb-dispatched wire over the proven
 * pure-transition spec `Dregg2.Games.MultiwayTug` — `legal` / `legalresp` / `kinds` / `split` /
 * `act` / `respond` / `control` / `count` / `score` / `won` / `winner` / `total` / `charm` /
 * `turns`. Every legality verdict, escrow split, row control, tally and round winner the deployed
 * multiway-tug surface reports is computed HERE. It replaces the decisions of
 * `dregg-multiway-tug/src/reference.rs`, a Rust re-expression of the same rules that had ALREADY
 * DRIFTED: its `winner_of` is the model's `roundWinner` truncated to the two absolute thresholds,
 * so it answers "no winner" on every sub-threshold round the model ADJUDICATES by charm and then
 * by row count (`undecidedState_adjudicates` — the fix that took the draw rate from 66.1% to
 * 5.1%). GATED on DREGG_MULTIWAY_TUG_RULES (build.rs probes + defines it).
 *
 * LIKE automatafl's export (and UNLIKE R3's / holding's / interchain's / FRI's) this one DOES need
 * its module initializer: the `charm` verb reads `Dregg2.Games.MultiwayTug.charm` and every witness
 * state reads `blankState` — nullary defs the generated C compiles to module-level globals that
 * only `initialize_Dregg2_Dregg2_Games_MultiwayTug` fills; an un-initialized call would read NULL.
 * It is therefore initialized explicitly in `dregg_ffi_init` below. Its closure
 * (Games.MultiwayTug / Boundary / Tactics / Mathlib multiset+bigops) is re-entrant-safe under
 * Lean's init guards and drags in no init edge the automatafl oracle does not already drag in. */
#ifdef DREGG_MULTIWAY_TUG_RULES
extern lean_object *initialize_Dregg2_Dregg2_Games_MultiwayTugFFI(uint8_t builtin);
extern lean_object *dregg_multiway_tug_rules(lean_object *input);
#endif

/* The internal Path of Angels Signal evaluator (`NetworkJudge.signalJudgeFFI`). It consumes one
 * complete canonical `POA-SIGNAL-IN-1` value and returns canonical `POA-SIGNAL-OUT-1`, or the empty
 * string on any refusal. Availability does NOT authenticate the carrier/state: only an authority
 * adapter may derive those fields from finalized state before calling this evaluator.
 *
 * The initializer is mandatory. The accepted configuration reaches `Emit.signalRunSeed` and
 * `Emit.signalTarget`, both generated as module globals filled by the PathOfAngels initializer
 * chain. The same initializer is mirrored in `lean_init_st.cpp`. */
#ifdef DREGG_POA_SIGNAL_JUDGE
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkJudge(uint8_t builtin);
extern lean_object *dregg_poa_signal_judge(lean_object *input);
#define DREGG_POA_SIGNAL_WIRE_MAX_BYTES ((size_t)67108864u)
#endif

/* The Path of Angels RECORDS read model (`RecordsRuntime.recordsProjectFFI`). The host supplies the
 * exact persisted genesis config/Canon blobs and one row per durable finalized transition; Lean
 * re-judges every row and folds the finalized-run aggregate. Reading confers nothing: the export
 * authenticates no coordinate and commits no state. Its own module initializer is required because
 * the fold reaches the same Emit globals the evaluator does. */
#ifdef DREGG_POA_RECORDS_PROJECT
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_RecordsRuntime(uint8_t builtin);
extern lean_object *dregg_poa_records_project(lean_object *input);
#define DREGG_POA_RECORDS_WIRE_MAX_BYTES ((size_t)67108864u)
#endif

/* The Path of Angels STATION DAILY read (`StationDailyRuntime.stationDailyReadFFI`). The host
 * supplies a format tag and at most one crew key; Lean returns the communal ship instrument panel
 * and, when a crew key was named, that crew member's VISIBLE rotation over the curator-authored
 * beacon schedule. Its module initializer is required because the projection reaches the same Emit
 * globals the evaluator does.
 * ⚠ CORRECTED 2026-08-07. This note used to say "READ ONLY BY TYPE … `CurrentStateCapability`
 * is `opaque` with no producer". That is false at HEAD: the capability is a sealed structure
 * produced by `SalvageCrate.genesis` and by each accepted open's successor, and the write path is
 * exported beside this one as `dregg_poa_crate_open`. This export is still a read, but because ITS
 * REQUEST CARRIES NO OPEN HISTORY — it has no field by which a caller could reach an opening. */
#ifdef DREGG_POA_STATION_DAILY_READ
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_StationDailyRuntime(uint8_t builtin);
extern lean_object *dregg_poa_station_daily_read(lean_object *input);
/* Matches MAX_POA_STATION_DAILY_WIRE_BYTES in poa_station_daily_ffi.rs and
 * StationDailyRuntime.WIRE_BYTE_LIMIT in Lean for the request; the reply is bounded by the
 * authored schedule length, which is far below this. */
#define DREGG_POA_STATION_DAILY_WIRE_MAX_BYTES ((size_t)1048576u)
#endif

/* The station's crate-open WRITE (`StationCrateOpenRuntime.crateOpenFFI`). The caller supplies a
 * format tag, the authenticated opener's crew key and the node's durable open log; Lean replays the
 * log from `SalvageCrate.genesis` under the capability chain, appends the caller's open, folds the
 * crate's own sealed receipt into the communal panel and returns the MOVED ship, or a tagged
 * refusal carrying no gauge. Its module initializer is required because the ceremony reaches the
 * same Emit globals the read does.
 * ⚠ This export DOES write — that is its whole purpose — but it can write only what the crate
 * authorizes: `OpenResult.mk`, `OpenReceipt.mk`, `Receipt.mk` and `CurrentStateCapability.mk` are
 * all private, so no caller-authored contribution, draw, period or counter can reach the panel. */
#ifdef DREGG_POA_CRATE_OPEN
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_StationCrateOpenRuntime(uint8_t builtin);
extern lean_object *dregg_poa_crate_open(lean_object *input);
/* Matches MAX_POA_CRATE_OPEN_WIRE_BYTES in poa_crate_open_ffi.rs and
 * StationCrateOpenRuntime.WIRE_BYTE_LIMIT in Lean: a full 4096-row open log spells to about
 * 390 KB, so this is a malformed-caller guard rather than a semantic bound. */
#define DREGG_POA_CRATE_OPEN_WIRE_MAX_BYTES ((size_t)1048576u)
#endif

/* The Lean-owned first-head ceremony (`NetworkGenesis.networkGenesisFFI`). The input tuple has
 * already undergone external manifest/genesis/signature verification; Lean rederives its
 * deployment binding and emits the exact config/Canon bytes and faithful digest coordinates.
 * This bridge transports that emission only and never constructs a head itself. */
#ifdef DREGG_POA_NETWORK_GENESIS
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkGenesis(uint8_t builtin);
extern lean_object *dregg_poa_network_genesis(lean_object *input);
#define DREGG_POA_NETWORK_GENESIS_WIRE_MAX_BYTES ((size_t)16777216u)
#endif

/* Path of Angels PER-RUN INSTANCE DERIVATION. `Judged.admissionChecks` re-derives the
 * slot commitment and the run seed and refuses on mismatch, which is a CHECK only if the
 * node derived them independently — so the node derives, and it derives by calling Lean.
 * There is deliberately no Rust arithmetic on this path: `HiddenInstance.commit` and
 * `runSeedFor` are a Poseidon2-BabyBear-w16 sponge, and a Rust twin of it would be an
 * unproven second copy of a soundness function.
 * ⚠ The request carries the curator's SLOT SECRET. These bytes are node-internal. */
#ifdef DREGG_POA_SIGNAL_SLOT_DERIVE
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_SlotDeriveRuntime(uint8_t builtin);
extern lean_object *dregg_poa_signal_slot_derive(lean_object *input);
/* Matches MAX_POA_SLOT_DERIVE_WIRE_BYTES in poa_slot_derive_ffi.rs and
 * SlotDeriveRuntime.WIRE_BYTE_LIMIT in Lean: the wire is a fixed handful of digests. */
#define DREGG_POA_SLOT_DERIVE_WIRE_MAX_BYTES ((size_t)65536u)
#endif

/* The mid-run LOCKED/DRIFT oracle for judged Signal. It applies
 * `SignalTriangulation.feedback` — the SAME rule `step` scores a settling transcript with —
 * to the instance `SlotDeriveRuntime.derive` hands the judge, so a player's rounds are about
 * the run that will settle rather than about a practice draw. There is deliberately no Rust
 * classification: a second `exactCount`/`presentCount` that disagreed by one on a duplicate
 * band would hand players a different game than the one that settles.
 * ⚠ The request carries the curator's SLOT SECRET, as the derivation's does. These bytes are
 * node-internal. The REPLY carries two counts and nothing else — no secret, no run seed, no
 * commitment, no target — which is what makes this the one PoA export whose answer is meant
 * to reach an (authenticated) route. */
#ifdef DREGG_POA_SIGNAL_FEEDBACK
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_SignalFeedbackRuntime(uint8_t builtin);
extern lean_object *dregg_poa_signal_feedback(lean_object *input);
/* Matches MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES in poa_signal_feedback_ffi.rs and
 * SignalFeedbackRuntime.WIRE_BYTE_LIMIT in Lean. */
#define DREGG_POA_SIGNAL_FEEDBACK_WIRE_MAX_BYTES ((size_t)65536u)
#endif

/* Bounded four-order Dark Bazaar settlement evaluator. The only authorization
 * constructor lives behind its Lean descriptor check; this shim transports strings. */
#ifdef DREGG_POA_DARK_BAZAAR_JUDGE
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_DarkBazaarJudge(uint8_t builtin);
extern lean_object *dregg_poa_dark_bazaar_judge(lean_object *input);
#define DREGG_POA_DARK_BAZAAR_WIRE_MAX_BYTES ((size_t)16777216u)
#endif

/* Replay-first Galley daily. The public evaluator has no holder authority parameter. The former
 * caller-JSON sponsor bridge is intentionally absent until an atomically consumable wallet
 * capability can cross this boundary. */
#ifdef DREGG_POA_GALLEY_DAILY_JUDGE
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_GalleyMaintenanceDailyRuntime(uint8_t builtin);
#define DREGG_POA_GALLEY_DAILY_WIRE_MAX_BYTES ((size_t)1048576u)
#endif
#ifdef DREGG_POA_GALLEY_DAILY_JUDGE
extern lean_object *dregg_poa_galley_daily_judge(lean_object *input);
#endif

/* Path of Angels Night Watch campaign. The judge takes NO authority argument: the
 * rulebook is not a parameter, it is whatever the audited world's content root commits
 * to. ⚠ The input wire carries the node-held SLOT SECRET (as POA-SLOT-DERIVE-1 does) —
 * these bytes must never be echoed into a response, a trace, or an error. The reply
 * carries no activation field at all. */
#ifdef DREGG_POA_NIGHT_WATCH_CAMPAIGN_JUDGE
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_NightWatchCampaignWire(uint8_t builtin);
#define DREGG_POA_NIGHT_WATCH_CAMPAIGN_WIRE_MAX_BYTES ((size_t)1048576u)
extern lean_object *dregg_poa_night_watch_campaign_judge(lean_object *input);
#endif

/* Path of Angels CREW FIELD MISSION — one seat's signed handoff. The export takes BYTES
 * ONLY (world + manifest + step request); it accepts no `RunSeal` argument, because the
 * only public seals in the tree besides the production one are the FIXTURE seals, whose
 * signature pattern is publicly computable — an export taking a seal would be "anyone
 * completes any seat". `CrewFieldMissionAdmission` MINTS the seal from admitted bytes
 * instead, and refuses the fixture suite INSIDE the mint, before the world is consulted. */
#if defined(DREGG_POA_CREW_FIELD_STEP) || defined(DREGG_POA_CREW_FIELD_SEAT_PREIMAGE)
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_CrewFieldMissionAdmission(uint8_t builtin);
#endif
#ifdef DREGG_POA_CREW_FIELD_STEP
#define DREGG_POA_CREW_FIELD_STEP_WIRE_MAX_BYTES ((size_t)4194304u)
extern lean_object *dregg_poa_crew_field_step(lean_object *input);
#endif
/* The ENTRY POINT. Same 4 MiB ceiling as the step envelope and for the same reason:
 * the seat envelope carries a manifest, bounded by Lean's own ENVELOPE_BYTE_LIMIT. */
#ifdef DREGG_POA_CREW_FIELD_SEAT_PREIMAGE
#define DREGG_POA_CREW_FIELD_SEAT_PREIMAGE_WIRE_MAX_BYTES ((size_t)4194304u)
extern lean_object *dregg_poa_crew_field_seat_preimage(lean_object *input);
#endif

/* Post-finality, multi-stream EventBatch planner. The native host constructs the duplicated
 * authority envelope from its commit record and game-judge result; this bridge transports the
 * exact canonical bytes and never promotes a network caller's alleged authority. */
#if defined(DREGG_POA_EVENT_BATCH_RUNTIME_PLAN) || \
    defined(DREGG_POA_EVENT_BATCH_RUNTIME_INITIAL_HEADS_DIGEST)
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_EventBatchRuntime(uint8_t builtin);
#define DREGG_POA_EVENT_BATCH_RUNTIME_WIRE_MAX_BYTES ((size_t)67108864u)
#endif
#ifdef DREGG_POA_EVENT_BATCH_RUNTIME_PLAN
extern lean_object *dregg_poa_event_batch_runtime_plan(lean_object *input);
#endif
#ifdef DREGG_POA_EVENT_BATCH_RUNTIME_INITIAL_HEADS_DIGEST
extern lean_object *dregg_poa_event_batch_runtime_initial_heads_digest(lean_object *input);
#endif

/* Signed active-world lineage. Native persistence verifies Ed25519 and builds the state from its
 * durable history; this judge owns transition, rollback and exact-world semantics. */
#if defined(DREGG_POA_WORLD_ACTIVATION_JUDGE) || defined(DREGG_POA_WORLD_ACTIVATION_AUTHORIZES)
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_WorldActivation(uint8_t builtin);
#define DREGG_POA_WORLD_ACTIVATION_WIRE_MAX_BYTES ((size_t)16777216u)
#endif
#ifdef DREGG_POA_WORLD_ACTIVATION_JUDGE
extern lean_object *dregg_poa_world_activation_judge(lean_object *input);
#endif
#ifdef DREGG_POA_WORLD_ACTIVATION_AUTHORIZES
extern lean_object *dregg_poa_world_activation_authorizes(lean_object *input);
#endif

/* Exact activated-content membership under a persistence-authenticated world. The exported
 * runtime owns canonical manifest/component/policy semantics; the host only transports bytes. */
#ifdef DREGG_POA_ACTIVATED_CONTENT_AUTHORIZE
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_ActivatedContentRuntime(uint8_t builtin);
#define DREGG_POA_ACTIVATED_CONTENT_WIRE_MAX_BYTES ((size_t)4194304u)
extern lean_object *dregg_poa_activated_content_authorize(lean_object *input);
#endif

/* Persistent Bazaar runtime. Lean owns every typed codec and constructs both
 * dependent admissions; native code returns only a checked Bool after exact
 * hash-chained-journal CAS or replay-tail comparison. */
#ifdef DREGG_POA_BAZAAR_RUNTIME
extern lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_BazaarGameRuntime(uint8_t builtin);
extern uint8_t dregg_poa_bazaar_runtime_request_codec_valid(lean_object *request);
extern uint8_t dregg_poa_bazaar_runtime_request_expected_present(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_request_expected_encode(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_request_replacement_encode(lean_object *request);
extern uint8_t dregg_poa_bazaar_runtime_journaled_request_codec_valid(lean_object *request);
extern uint8_t dregg_poa_bazaar_runtime_journaled_expected_present(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_journaled_expected_encode(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_journaled_replacement_encode(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_journaled_event_encode(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_journaled_deployment_encode(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_journaled_store_encode(lean_object *request);
extern lean_object *dregg_poa_bazaar_runtime_state_from_game_encode(lean_object *state);
extern uint8_t dregg_poa_bazaar_runtime_durable_load_valid(
    lean_object *registry, lean_object *state, lean_object *wire);
extern uint8_t dregg_poa_bazaar_runtime_state_key_validate(lean_object *wire);
extern lean_object *dregg_poa_bazaar_runtime_fixture(lean_object *command);
extern int32_t dregg_poa_bazaar_native_perform_cas(
    uint8_t expected_present,
    const uint8_t *expected, size_t expected_len,
    const uint8_t *replacement, size_t replacement_len);
extern int32_t dregg_poa_bazaar_native_perform_journaled_cas(
    uint8_t expected_present,
    const uint8_t *expected, size_t expected_len,
    const uint8_t *replacement, size_t replacement_len,
    const uint8_t *event, size_t event_len,
    const uint8_t *store_identity, size_t store_identity_len,
    const uint8_t *deployment_id, size_t deployment_id_len);
extern int32_t dregg_poa_bazaar_native_durable_load_matches(
    const uint8_t *canonical, size_t canonical_len);
#define DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES ((size_t)16777216u)
#define DREGG_POA_BAZAAR_EVENT_WIRE_MAX_BYTES ((size_t)16777216u)

static lean_object *dregg_poa_bazaar_io_bool(uint8_t value) {
    return lean_io_result_mk_ok(lean_box(value != 0));
}

static lean_object *dregg_poa_bazaar_io_error(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

/* Checked primitive for `TrustedRuntimePortal.performCas`. Each helper gets its
 * own owned reference; the raw extern consumes the original exactly once. */
lean_object *dregg_poa_bazaar_perform_cas_checked(lean_object *request) {
    lean_inc(request);
    uint8_t codec_valid = dregg_poa_bazaar_runtime_request_codec_valid(request);
    if (!codec_valid) {
        lean_dec(request);
        return dregg_poa_bazaar_io_bool(0);
    }

    lean_inc(request);
    uint8_t expected_present =
        dregg_poa_bazaar_runtime_request_expected_present(request);
    lean_inc(request);
    lean_object *expected =
        dregg_poa_bazaar_runtime_request_expected_encode(request);
    lean_inc(request);
    lean_object *replacement =
        dregg_poa_bazaar_runtime_request_replacement_encode(request);
    lean_dec(request);

    size_t expected_size = lean_string_size(expected);
    size_t replacement_size = lean_string_size(replacement);
    if (expected_size == 0 || replacement_size == 0) {
        lean_dec(expected);
        lean_dec(replacement);
        return dregg_poa_bazaar_io_error("Bazaar codec returned an invalid Lean string");
    }
    size_t expected_len = expected_size - 1;
    size_t replacement_len = replacement_size - 1;
    if (expected_len > DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES ||
        replacement_len == 0 ||
        replacement_len > DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES ||
        ((!expected_present) != (expected_len == 0))) {
        lean_dec(expected);
        lean_dec(replacement);
        return dregg_poa_bazaar_io_bool(0);
    }

    int32_t result = dregg_poa_bazaar_native_perform_cas(
        expected_present,
        (const uint8_t *)lean_string_cstr(expected), expected_len,
        (const uint8_t *)lean_string_cstr(replacement), replacement_len);
    lean_dec(expected);
    lean_dec(replacement);
    if (result < 0) {
        return dregg_poa_bazaar_io_error("Bazaar durable CAS failed closed");
    }
    return dregg_poa_bazaar_io_bool(result == 1);
}

/* Event-bearing v3 CAS. Every byte passed to Rust is emitted independently by
 * Lean from one private `JournaledRuntimeCasRequest`; C retains no game
 * semantics and constructs no dependent admission. */
lean_object *dregg_poa_bazaar_perform_journaled_cas_checked(
    lean_object *request) {
    lean_inc(request);
    uint8_t codec_valid =
        dregg_poa_bazaar_runtime_journaled_request_codec_valid(request);
    if (!codec_valid) {
        lean_dec(request);
        return dregg_poa_bazaar_io_bool(0);
    }

    lean_inc(request);
    uint8_t expected_present =
        dregg_poa_bazaar_runtime_journaled_expected_present(request);
    lean_inc(request);
    lean_object *expected =
        dregg_poa_bazaar_runtime_journaled_expected_encode(request);
    lean_inc(request);
    lean_object *replacement =
        dregg_poa_bazaar_runtime_journaled_replacement_encode(request);
    lean_inc(request);
    lean_object *event =
        dregg_poa_bazaar_runtime_journaled_event_encode(request);
    lean_inc(request);
    lean_object *store =
        dregg_poa_bazaar_runtime_journaled_store_encode(request);
    lean_inc(request);
    lean_object *deployment =
        dregg_poa_bazaar_runtime_journaled_deployment_encode(request);
    lean_dec(request);

    size_t expected_size = lean_string_size(expected);
    size_t replacement_size = lean_string_size(replacement);
    size_t event_size = lean_string_size(event);
    size_t store_size = lean_string_size(store);
    size_t deployment_size = lean_string_size(deployment);
    if (expected_size == 0 || replacement_size == 0 || event_size == 0 ||
        store_size == 0 || deployment_size == 0) {
        lean_dec(expected);
        lean_dec(replacement);
        lean_dec(event);
        lean_dec(store);
        lean_dec(deployment);
        return dregg_poa_bazaar_io_error(
            "Bazaar journaled codec returned an invalid Lean string");
    }
    size_t expected_len = expected_size - 1;
    size_t replacement_len = replacement_size - 1;
    size_t event_len = event_size - 1;
    size_t store_len = store_size - 1;
    size_t deployment_len = deployment_size - 1;
    if (expected_len > DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES ||
        replacement_len == 0 ||
        replacement_len > DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES ||
        event_len == 0 || event_len > DREGG_POA_BAZAAR_EVENT_WIRE_MAX_BYTES ||
        store_len != 64 || deployment_len != 64 ||
        ((!expected_present) != (expected_len == 0))) {
        lean_dec(expected);
        lean_dec(replacement);
        lean_dec(event);
        lean_dec(store);
        lean_dec(deployment);
        return dregg_poa_bazaar_io_bool(0);
    }

    int32_t result = dregg_poa_bazaar_native_perform_journaled_cas(
        expected_present,
        (const uint8_t *)lean_string_cstr(expected), expected_len,
        (const uint8_t *)lean_string_cstr(replacement), replacement_len,
        (const uint8_t *)lean_string_cstr(event), event_len,
        (const uint8_t *)lean_string_cstr(store), store_len,
        (const uint8_t *)lean_string_cstr(deployment), deployment_len);
    lean_dec(expected);
    lean_dec(replacement);
    lean_dec(event);
    lean_dec(store);
    lean_dec(deployment);
    if (result < 0) {
        return dregg_poa_bazaar_io_error(
            "Bazaar durable journaled CAS failed closed");
    }
    return dregg_poa_bazaar_io_bool(result == 1);
}

/* Checked primitive for an already-materialized in-memory replay. This is not
 * a typed restart decoder: Lean validates the registry/state/wire equations,
 * and native code independently replays the journal and compares its tail. */
lean_object *dregg_poa_bazaar_admit_durable_load_checked(
    lean_object *registry, lean_object *state, lean_object *wire) {
    lean_inc(registry);
    lean_inc(state);
    lean_inc(wire);
    uint8_t typed_valid = dregg_poa_bazaar_runtime_durable_load_valid(
        registry, state, wire);
    if (!typed_valid) {
        lean_dec(registry);
        lean_dec(state);
        lean_dec(wire);
        return dregg_poa_bazaar_io_bool(0);
    }

    lean_inc(state);
    lean_object *canonical = dregg_poa_bazaar_runtime_state_from_game_encode(state);
    lean_dec(registry);
    lean_dec(state);
    lean_dec(wire);
    size_t canonical_size = lean_string_size(canonical);
    if (canonical_size <= 1 ||
        canonical_size - 1 > DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES) {
        lean_dec(canonical);
        return dregg_poa_bazaar_io_bool(0);
    }
    int32_t result = dregg_poa_bazaar_native_durable_load_matches(
        (const uint8_t *)lean_string_cstr(canonical), canonical_size - 1);
    lean_dec(canonical);
    if (result < 0) {
        return dregg_poa_bazaar_io_error("Bazaar journal replay failed closed");
    }
    return dregg_poa_bazaar_io_bool(result == 1);
}
#endif

/* The @[export]ed Lean `String -> String` FRI SOUNDNESS LEDGER
 * (`Dregg2.Circuit.FriLedger.friLedgerFFI`): decodes the wire
 * `"logBlowup numQueries powBits maxLogArity logFinalPolyLen extDeg logD0 bciksM"` (eight decimal
 * nats — one shipped FRI knob set, the extension degree that fixes |F|, and the two ε_C inputs that
 * are NOT knobs) and returns
 * `"arity foldedDomain goodCount perFoldBits johnsonBits capacityBits commitBits"` (the seven ledger
 * columns; `""` fail-closed for a malformed wire, an out-of-window knob set, or ε_C inputs outside
 * `epsCInWindow` — notably `bciksM < 3`, BCIKS20 Thm 8.3's own hypothesis). This is the per-config
 * soundness ARITHMETIC as leanc-native code: `friLedger` is the very function
 * `Dregg2.Circuit.FriLedgerSound` proves about (`ledger_perFold_soundness` — the parametric per-fold
 * bound instantiating `FriArityTransfer.good_card_le_of_phase_injective` at each config's arity and
 * folded-domain size), so the numbers Rust reports are the numbers Lean proved rather than a
 * hand-written Rust twin of the same formulas. `circuit-prove/tests/fri_params_soundness_budget.rs`
 * and `circuit-prove/tests/fri_regrid_post_s2_measure.rs` hand it each deployed knob set and
 * gate/report what comes back. GATED on DREGG_FRI_LEDGER (build.rs probes + defines it). NOTE: like
 * R3's / holding's / interchain's export it needs NO module initializer — its generated C hoists the
 * string literals into STATIC CONST `lean_string_object`s and its closures into LAZY
 * `lean_once_cell`s, so `dregg_fri_ledger` is self-contained. We therefore deliberately do NOT
 * reference `initialize_Dregg2_Dregg2_Circuit_FriLedger`: that initializer chains into the
 * `Dregg2.Tactics` (Mathlib-tactic) import closure's init symbols the leanc-native archive does not
 * carry; leaving it unreferenced lets `-dead_strip` drop the proof closure — the pure ledger core
 * links and runs on the always-initialized Init runtime. */
#ifdef DREGG_FRI_LEDGER
extern lean_object *dregg_fri_ledger(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` DELEGATED TOOL/MCP-ACCESS ADMISSION decision
 * (`Dregg2.Apps.DelegAdmit.delegAdmitFFI`). Runs `delegAdmit` — the five-conjunct predicate
 * `Dregg2.Apps.ToolAccessDelegation.tool_invocation_commit_iff_admit` proves the production
 * caveat-gated executor commits a metered `calls_made : c -> c+1` write IFF, and whose negations are
 * the `tool_invocation_over_rate_rejected` / `_past_deadline_rejected` / `_out_of_scope_rejected`
 * teeth. The SDK tool gateway, the starbridge tool-access-delegation app and the dreggnet offerings
 * session all marshal to THIS instead of re-deciding the policy in Rust; their three hand-maintained
 * mirrors are deleted, so an absent export means those gateways REFUSE, not that a twin answers.
 * DREGG_DELEG_ADMIT requires BOTH the export and its generated module initializer.
 * DelegAdmit imports only Init: initialize that exact closure before the first
 * call, without loading the unrelated executor/proof modules. */
#ifdef DREGG_DELEG_ADMIT
extern lean_object *dregg_deleg_admit(lean_object *input);
extern lean_object *initialize_Dregg2_Dregg2_Apps_DelegAdmit(uint8_t builtin);
#endif

/* The @[export]ed Lean `String -> String` TRUSTLINE DRAW/REPAY/SETTLE decision
 * (`Dregg2.Apps.TrustlineCore.trustlineStepFFI`). Runs `draw` / `repay` / `settlePay` /
 * `settleAll` — the objects `Dregg2.Apps.Trustline`'s 101 kernel-clean theorems are stated over
 * (`over_line_draw_refused`, `draw_replay_refused`, `draw_replay_refused_across_epochs`,
 * `over_repay_refused`, `bilateral_conserved`, `settlePay_conserves_hard`, `settleAll_clears`).
 * The wire carries the FULL channel state INCLUDING the digest registry, deliberately: the
 * anti-replay verdict is DECIDED HERE, never summarised into a Rust-computed freshness bit —
 * which is exactly the check `turn/src/budget_gate.rs:29` keeps a `debits` list for and never
 * performs. NOTHING ROUTES THROUGH IT YET (the ~16 Rust spend-authority implementations still
 * decide it themselves), so an absent export today means a probe fails, not that a gateway
 * refuses; that changes the moment the first call site is routed.
 * GATED on DREGG_TRUSTLINE_STEP (build.rs probes + defines it). Like R3's / holding's /
 * interchain's / FRI's / DelegAdmit's export it needs NO module initializer:
 * `Dregg2.Apps.TrustlineCore` imports nothing beyond core Init — its emitted `.c` carries exactly
 * `initialize_Init` and its own — so it is self-contained on the always-initialized Init runtime. */
#ifdef DREGG_TRUSTLINE_STEP
extern lean_object *dregg_trustline_step(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED LIGHT-CLIENT verify-logic gates — the three
 * foreign-chain admission decisions the interchain bridge routes through
 * (`Dregg2.Bridge.LightClient{Eth,Mpt,Tendermint}Gate`):
 *
 *   dregg_eth_lc_verify — the Ethereum sync-committee update decision (`ethLcVerifyGate`). Input
 *     `"cl=<committee-len>;bl=<bitfield-len>;pc=<popcount>;bls=<BIT>;fl=<finality-depth>;fr=<BIT>;
 *     el=<exec-depth>;er=<BIT>"`. Runs the PROVED `ethVerifyDecision` — the ≥ 2/3 multiply-form
 *     quorum (`3·pc ≥ 2·cl`), the committee-size/bitfield agreement, and the branch-DEPTH
 *     admissibility (6|7 finality, 4 execution) — which `ethVerifyDecision_refines` proves is
 *     DEFINITIONALLY `verifyFinalizedUpdate`, the decision `eth_no_forgery` is proven over. The
 *     heavy crypto (BLS12-381 aggregate verify, SHA-256 SSZ branch folds) stays in Rust and enters
 *     as the `bls`/`fr`/`er` RESULT bits — the named `blsSound`/`hashPairCR` carriers.
 *   dregg_tm_lc_verify — the Tendermint/Cosmos adjacent-advance decision (`tmLcVerifyGate`), incl.
 *     the STRICT stake-weighted `2·total < 3·signed` threshold, chain-id match, height advance and
 *     the trusting-period/clock-drift window. Refined to `tmVerify` (`tmVerifyDecision_refines`).
 *   dregg_mpt_lc_verify — the EIP-1186 EVM state-inclusion decision (`mptLcVerifyGate`): the
 *     Nomad-law nonzero-balance floor plus the three anchor bindings (state root / token /
 *     mapping slot must equal the TRUSTED ones). Refined to `mptVerify`
 *     (`mptVerifyDecision_refines`). The keccak MPT path walk stays in Rust (alloy-trie) and
 *     enters as the `ap`/`sp` RESULT bits.
 *
 * All three return `"1"` (ACCEPT) / `"0"` (REJECT) / `"ERR"` (malformed wire ⇒ the caller REJECTS:
 * fail-closed, an unproven foreign update is never admitted).
 *
 * GATED on DREGG_{ETH,TM,MPT}_LC_VERIFY (build.rs probes the archive and defines each only when
 * its symbol is present). NOTE: like the R3 / holding / interchain verdict cores these need NO
 * module initializer, and this is CHECKED against the emitted C rather than assumed: every string
 * literal in `LightClient{Eth,Mpt,Tendermint}Gate.c` is a STATIC CONST `lean_string_object` and the
 * generated `initialize_Dregg2_Dregg2_Bridge_LightClient*Gate` body assigns NO module global (it
 * only chains its imports) — so each gate is self-contained on the always-initialized Init runtime.
 * We therefore deliberately do NOT reference those initializers: they chain into the light-client
 * models' Mathlib-tactic import closure, whose init symbols the leanc-native archive does not
 * carry, and referencing them would drag undefined symbols into the final link. Leaving them
 * unreferenced lets `-dead_strip` drop the proof closure while the pure verdict cores link. */
#ifdef DREGG_ETH_LC_VERIFY
extern lean_object *dregg_eth_lc_verify(lean_object *input);
#endif
/* dregg_eth_committee_rotation — the SECOND Ethereum gate, from the SAME module
 * (`Dregg2.Bridge.LightClientEthGate.ethCommitteeRotationGate`). Input `"nl=<Nat>;nr=<BIT>"`
 * (next_sync_committee branch depth + the SHA-256 reconstruction result). Runs the PROVED
 * `committeeRotationDecision` — the branch-DEPTH admissibility (5 Altair..Deneb | 6 Electra+,
 * subtree index 23 in both) composed with the reconstruction — which
 * `committeeRotationDecision_refines` proves is DEFINITIONALLY `verifyCommitteeRotation`.
 * This is the decision that advances the light client's TRUSTED SYNC COMMITTEE, i.e. its
 * trust ROOT, on both `WeakSubjectivityStore::bootstrap_committee` and `advance`. Absent ⇒
 * `eth-lightclient::verify_committee_update` refuses; there is no Rust twin left. */
#ifdef DREGG_ETH_COMMITTEE_ROTATION
extern lean_object *dregg_eth_committee_rotation(lean_object *input);
#endif
#ifdef DREGG_TM_LC_VERIFY
extern lean_object *dregg_tm_lc_verify(lean_object *input);
#endif
/* dregg_tm_skip_verify — the NON-ADJACENT (skipping) Tendermint decision
 * (`Dregg2.Bridge.LightClientTendermintSkip.tmSkipVerifyGate`). A DIFFERENT rule set from
 * `dregg_tm_lc_verify`, not a superset: the `next_validators_hash` epoch binding is gone (a skip
 * target's validator set was never committed by the trusted header) and the TRUST-OVERLAP
 * threshold takes its place — strictly more than `trust_threshold` of the TRUSTED epoch's voting
 * power must have signed the target, ON TOP of the full strict `> 2/3` over the target's own set.
 * `tmSkip_height_disjoint_from_adjacent` proves the two gates cover disjoint height ranges. */
#ifdef DREGG_TM_SKIP_VERIFY
extern lean_object *dregg_tm_skip_verify(lean_object *input);
#endif
#ifdef DREGG_MPT_LC_VERIFY
extern lean_object *dregg_mpt_lc_verify(lean_object *input);
#endif
/* dregg_mina_lc_verify — the MINA (Ouroboros Samasika / Pickles) anchored-segment decision
 * (`minaLcVerifyGate`, `Dregg2.Bridge.LightClientMinaGate`): the exhibited segment is non-empty,
 * the settlement's submitted height is AT OR ABOVE the pinned weak-subjectivity anchor, and the
 * WITNESSED confirmation depth meets the Samasika requirement. Refined to `minaVerify`
 * (`minaVerifyDecision_refines`, axiom-free `rfl`), the decision `mina_no_forgery` is proven over.
 * The Poseidon linkage fold, the per-block Pickles/Kimchi Wrap-proof results and the state-row
 * canonicality enter as the `lk`/`pk`/`cn` RESULT bits (the named carriers; the first and third are
 * DERIVED in `Dregg2.Circuit.Emit.LightClientMinaHashFold` rather than trusted). Same
 * `"1"`/`"0"`/`"ERR"` fail-closed contract, same no-module-initializer property as the three
 * gates above. */
#ifdef DREGG_MINA_LC_VERIFY
extern lean_object *dregg_mina_lc_verify(lean_object *input);
#endif
/* dregg_mina_wrap_shape_ok — the PER-BLOCK Pickles Wrap-proof PREAMBLE decision
 * (`minaWrapShapeGate`, `Dregg2.Bridge.PicklesWrapShapeGate`), which is
 * `KimchiVerify.shapeOkRec` (the `verifier.rs:810-830` length asserts) plus the two length
 * agreements a RECURSIVE Wrap proof owes. This is what retired the Mina observer's
 * `NEUTRAL_PICKLES_OK` constant: the observer now decodes each block's `protocolStateProof`
 * (a CODEC, `bridge/src/mina_pickles.rs`) and the ARCHIVE renders the `pk` bit that used to be
 * a compile-time `true`. Same `"1"`/`"0"`/`"ERR"` fail-closed contract and the same
 * no-module-initializer property as the gates above. */
#ifdef DREGG_MINA_WRAP_SHAPE_OK
extern lean_object *dregg_mina_wrap_shape_ok(lean_object *input);
#endif
/* dregg_mina_proof_chain_ok — the PER-ADJACENT-PAIR Pickles PROOF-CHAIN decision
 * (`minaProofChainGate`, `Dregg2.Bridge.PicklesProofChainGate`): block N's Wrap proof must NAME
 * block N-1's Wrap proof, on both fingerprints Pickles recursion leaves in the clear — the
 * parent's own IPA accumulator `sg` and the parent's 16 IPA challenges. This is the first thing
 * in the tree that ties a served proof to anything outside its own bytes, and it is what makes
 * one real proof replayed under a whole fabricated segment a REFUSAL. It does NOT bind a proof to
 * its block's `stateHash`; see the module header for why that needs `expand_deferred`. Same
 * `"1"`/`"0"`/`"ERR"` fail-closed contract and no-module-initializer property as the gates
 * above. */
#ifdef DREGG_MINA_PROOF_CHAIN_OK
extern lean_object *dregg_mina_proof_chain_ok(lean_object *input);
#endif
/* dregg_mina_state_hash_word_ok — the PER-BLOCK proof<->stateHash DERIVATION
 * (`headerOk`, `Dregg2.Bridge.MinaStateHashWordGate`): public-input words 11 and 12 recomputed,
 * from the SERVED header and the served proof bytes, as the 93-element Poseidon over
 * `[dlog_plonk_index(56) || state_hash(1) || accumulators(36)]` over Fp and the 32-element one
 * over Fq. Word 12 is the ONLY place a Mina block enters a Wrap verification. This does NOT
 * verify the Wrap proof and must never be described as doing so; the equation that a wrong word
 * 12 falsifies is the terminal IPA opening, whose per-block cost includes a 2^15-point MSM.
 * Same `"1"`/`"0"`/`"ERR"` fail-closed contract as the gates above. */
#ifdef DREGG_MINA_STATE_HASH_WORD_OK
extern lean_object *dregg_mina_state_hash_word_ok(lean_object *input);
/* ⚑ THIS ONE NEEDS ITS MODULE INITIALIZER, and the gates above do not. `minaProofChainGate` and
 * friends decide over their ARGUMENTS only; `headerOk` reads three top-level constants —
 * `VK_INDEX` (the 56 verification-key field elements) and the `fpParams`/`fqParams` Poseidon
 * parameter records in `PastaPoseidonFq`. Those live in initialized module data, so calling the
 * export before `initialize_Dregg2_Dregg2_Bridge_MinaStateHashWordGate` dereferences uninitialized
 * globals and the process takes SIGSEGV with no Rust panic — measured 2026-07-29, and it looks
 * exactly like the missing-archive SIGABRT, which is why it is written down here rather than
 * discovered twice. The initializer chains into `PastaPoseidonFq`/`PastaPoseidon`/`KimchiVerify`
 * and is re-entrant-safe under Lean's init guards. */
extern lean_object *initialize_Dregg2_Dregg2_Bridge_MinaStateHashWordGate(uint8_t builtin);
#endif
/* dregg_mina_wrap_challenges — ⚑ THE PER-BLOCK CHALLENGE DERIVATION
 * (`Dregg2.Bridge.MinaWrapChallenges`): a Wrap proof's own Fiat-Shamir challenges — beta, gamma,
 * alpha', zeta', the phase-1 digest, `t`, `c'` and the FIFTEEN raw IPA prechallenges — run forward
 * from the block's own absorbed coordinates. This is what retires `mina_opening_check.rs`'s
 * one-height `PINNED_CHALLENGES`.
 *
 * ⚑ THE EXPORT LANDED 2026-07-30 AND HAD NO BRIDGE. `Dregg2/FFI.lean` rooted the module and
 * `build.rs` probed the symbol, so the archive carried it and `cargo` set
 * `dregg_mina_wrap_challenges_present` — and there was no `_str` bridge here and no wrapper in
 * `lib.rs`, so nothing could call it. That is the GATING-DEFAULTS-TO-SILENCE class: not broken
 * code, code never connected. The bridge is here now.
 *
 * ⚑ NEEDS ITS MODULE INITIALIZER, for the reason `headerOk` does: the sponge schedules read the
 * top-level `fpParams` record out of initialized module data, and calling the export first
 * dereferences uninitialized globals and takes SIGSEGV with no Rust panic. */
#ifdef DREGG_MINA_WRAP_CHALLENGES
extern lean_object *dregg_mina_wrap_challenges(lean_object *input);
extern lean_object *initialize_Dregg2_Dregg2_Bridge_MinaWrapChallenges(uint8_t builtin);
#endif
/* dregg_mina_wrap_ft_eval0 — ⚑ THE OTHER HALF (`Dregg2.Bridge.MinaWrapFtEval0`): the linearization
 * constant term DERIVED from the six transcribed gate bodies, `ft_eval0`, the domain generator and
 * the two challenge lifts, at either side of the Pasta cycle. `MinaWrapChallenges` above cannot
 * supply `public_comm` or `cipShifted` without it. Same `"ERR"` fail-closed contract; same module
 * initializer requirement (`pN`/`qN` and every `KimchiVerify` constant are module data). */
#ifdef DREGG_MINA_WRAP_FT_EVAL0
extern lean_object *dregg_mina_wrap_ft_eval0(lean_object *input);
extern lean_object *initialize_Dregg2_Dregg2_Bridge_MinaWrapFtEval0(uint8_t builtin);
#endif
/* dregg_mina_account_state_ok — ⚑ MINA *STATE*, NOT MINA'S CHAIN
 * (`Dregg2.Bridge.MinaAccountOpening.minaAccountOpeningGate`). Every Mina bridge above decides
 * about headers, proofs and forks; none of them can observe a balance, a nonce or a delegation.
 * This one recomputes an account's ledger LEAF from its own fields — `Account.to_input` in
 * REVERSED declaration order, the `Mina*` (not `Coda*`) hash prefixes, `Untimed`'s
 * `vesting_period = 1`, `txn_version` inside the controller run — and folds it up a 35-level
 * level-indexed Poseidon opening to `staged_ledger_hash.non_snark.ledger_hash`, which it DECODES
 * out of the block's own binprot bytes. No argument lets a caller name the root it opens against.
 * Same `"1"`/`"0"`/`"ERR"` fail-closed contract as the gates above.
 *
 * ⚑ NEEDS ITS MODULE INITIALIZER, for exactly the reason `headerOk` does: the gate reads top-level
 * constants out of initialized module data — the pinned `mainnet` `Constants` record, `dummyVkHash`
 * and the derived `defaultZkappDigest`, plus the `fpParams` Poseidon parameters underneath them.
 * Calling the export before `initialize_Dregg2_Dregg2_Bridge_MinaAccountOpening` dereferences
 * uninitialized globals and the process takes SIGSEGV with no Rust panic, which looks exactly like
 * the missing-archive SIGABRT. */
/* ⚑ THE DEFERRED-ACCUMULATOR DISCHARGE gate (`Dregg2.Circuit.Emit.PastaIpaDeferral` §5). Decides a
 * BATCH of carried `<s, srs.g>` accumulator claims: `2^k = |srs.g|`, non-empty, every claim at
 * exactly `k` challenges, AND `d=1` — the batched MSM was evaluated and found to vanish.
 * `deferral_gate_refuses_undischarged` is the theorem that the fourth conjunct cannot be skipped:
 * the gate has no way to say "deferred, looks fine so far".
 *
 * ⚠ `d` is the ONE field of that wire that is not a shape read. Its earner is
 * `dregg_bridge::mina_accumulator_discharge`, which runs the |G|+N-point MSM natively over the real
 * Vesta SRS. Before 2026-08-04 there was no earner and no caller at all — the export shipped and
 * `d` was whatever a hypothetical wire said. */
#ifdef DREGG_MINA_DEFERRAL_OK
extern lean_object *dregg_mina_deferral_ok(lean_object *input);
/* Needs its module initializer: `parseField?`/`parseNats?`/`decodeBatchWire` reference compiled
 * string literals, which live in initialized module data — the same reason
 * `DREGG_MINA_STATE_HASH_WORD_OK` takes one, and the same SIGSEGV-with-no-panic if it is skipped. */
extern lean_object *initialize_Dregg2_Dregg2_Circuit_Emit_PastaIpaDeferral(uint8_t builtin);
#endif

#ifdef DREGG_MINA_ACCOUNT_STATE_OK
extern lean_object *dregg_mina_account_state_ok(lean_object *input);
extern lean_object *initialize_Dregg2_Dregg2_Bridge_MinaAccountOpening(uint8_t builtin);
#endif
/* dregg_mina_better_tip / dregg_mina_head_advance — the SAMASIKA FORK-CHOICE decision and the
 * ROLLING VERIFIED HEAD (`Dregg2.Bridge.MinaForkChoiceGate`, over the `select` rule of
 * `Dregg2.Bridge.MinaChainSelection`). The anchored-segment gate above deliberately decides no fork
 * choice; these two do. `dregg_mina_better_tip` compares ONE candidate tip against the existing one
 * and answers `"1"` (take the candidate) / `"0"` / `"ERR"`; `dregg_mina_head_advance` rolls the
 * persisted head and answers `"adv=<0|1>;fin=<Nat>"` / `"ERR"`.
 *
 * ⚑ PAIRWISE, NEVER FOLDED: `MinaChainSelection.beats_not_transitive` proves `select` has genuine
 * 3-cycles at real mainnet constants, so a "best of a set" is a function of presentation order and
 * a hostile peer picks the order. What survives that is the ratchet —
 * `rollHead_finalized_monotone`: `fin` never decreases, on any input.
 *
 * ⚑ THESE NEED THE MODULE INITIALIZER, for the same reason `headerOk` above does: the gate reads
 * the top-level `MinaChainSelection.mainnet` constants record (`k = 290`, `grace_period_end = 2237`,
 * `sub_windows_per_window`, …), which is initialized module data. Those constants are pinned in the
 * Lean and are NOT carried on the wire — a peer that supplied both the states and the constants
 * would supply the ones that make its fork win. Calling either export before initialization
 * dereferences uninitialized globals and takes SIGSEGV with no Rust panic, which looks exactly like
 * the missing-archive SIGABRT. */
#if defined(DREGG_MINA_BETTER_TIP) || defined(DREGG_MINA_HEAD_ADVANCE)
extern lean_object *initialize_Dregg2_Dregg2_Bridge_MinaForkChoiceGate(uint8_t builtin);
#endif
#ifdef DREGG_MINA_BETTER_TIP
extern lean_object *dregg_mina_better_tip(lean_object *input);
#endif
#ifdef DREGG_MINA_HEAD_ADVANCE
extern lean_object *dregg_mina_head_advance(lean_object *input);
#endif
/* dregg_mina_checkpoint_advance — ⚑ THE PER-CHECKPOINT LOOP (`Dregg2.Bridge.MinaCheckpoint`): the
 * TWO-TIER head the fork-choice pair above cannot express. Mina's Pickles proof is RECURSIVE, so
 * verifying ONE block's Wrap proof attests the validity of the whole chain behind it; a client
 * therefore verifies at a CHECKPOINT cadence it chooses and runs a cheap provisional tier in
 * between. Input is a mode byte, the Wrap ARITHMETIC verdict, the persisted ratchet/run/cap and
 * FOUR protocol states (parent, tip, verified head, candidate) with the hash each is claimed under;
 * output is `"mv=<0|1>;adv=<0|1>;fin=<Nat>;rn=<Nat>"` / `"ERR"` (fail-closed).
 *
 * ⚑ THE TIER SPLIT IS THE SAFETY ARGUMENT, and it is a theorem rather than a convention:
 * `provisional_never_ratchets` — a between-checkpoint step is DEFINITIONALLY unable to raise
 * `finalized` — and `runSteps_finalized_monotone` — the ratchet survives ANY interleaving of the two
 * tiers, any order, any length. So a longer cadence buys LATENCY and LIVENESS cost, never a safety
 * one, and `MinaChainSelection.beats_not_transitive`'s genuine 3-cycles are CONTAINED to the tier
 * that decides nothing.
 *
 * ⚑ RUST SUPPLIES NO CHEAP VERDICT. The parent link and the density RE-DERIVATION (
 * `MinaSlidingWindow.step` from the decoded parent, not a bound check on a served value) happen
 * INSIDE the gate — `MinaCheckpoint.okOf`. The one bit that crosses is `wk`, the Wrap arithmetic,
 * which is arithmetic Rust did not do either.
 *
 * ⚑ NEEDS ITS MODULE INITIALIZER, for exactly the reason the fork-choice pair above does: `okOf`
 * reads the pinned `MinaChainSelection.mainnet` constants record out of initialized module data, and
 * the density step reads `MinaSlidingWindow`'s. Calling the export first dereferences uninitialized
 * globals and takes SIGSEGV with no Rust panic, which looks exactly like the missing-archive
 * SIGABRT. Initializing THIS module chains into both imports. */
#ifdef DREGG_MINA_CHECKPOINT_ADVANCE
extern lean_object *dregg_mina_checkpoint_advance(lean_object *input);
extern lean_object *initialize_Dregg2_Dregg2_Bridge_MinaCheckpoint(uint8_t builtin);
#endif

/* ── NO-COPY BOUNDARY runtime helpers (linkable wrappers over the `static inline`
 * <lean/lean.h> primitives the no-copy `lean_direct.rs` boundary needs). `lean_inc_ref`,
 * `lean_dec_ref`, `lean_box`, and `lean_string_cstr` are `static inline` in the header (no
 * linkable symbol), so Rust cannot call them directly — exactly the reason this C shim exists.
 * These thin `dregg_rt_*` wrappers give them a linkable C-ABI symbol. (`lean_mk_string` is a real
 * LEAN_EXPORT and is called directly from Rust.) */
/* Use the SCALAR-CHECKING `lean_inc`/`lean_dec` (not `lean_inc_ref`/`lean_dec_ref`): small
 * `Nat`/`Int`/no-field-enum (Auth) values are TAGGED POINTERS, not heap objects, so the `_ref`
 * variants would dereference an invalid address. `lean_inc`/`lean_dec` short-circuit on scalars. */
void dregg_rt_inc(lean_object *o) { lean_inc(o); }
void dregg_rt_dec(lean_object *o) { lean_dec(o); }
lean_object *dregg_rt_box(size_t n) { return lean_box(n); }
const char *dregg_rt_string_cstr(lean_object *s) { return lean_string_cstr(s); }

/* Returns 0 on success, 1 if module initialization reported an IO error. */
/* Called only by the shared coordinator. Runtime startup already initialized
 * the current thread's allocator; it must not also call lean_initialize_thread. */
void dregg_ffi_start_runtime(void) {
    lean_initialize_runtime_module();
}

void dregg_ffi_finish_initialization(void) {
    lean_io_mark_end_initialization();
}

int dregg_ffi_init_deleg_admit_module(void) {
#ifdef DREGG_DELEG_ADMIT
    lean_object *res = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Apps_DelegAdmit);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
    return 0;
#else
    return 2; /* No linked initializer/export pair: no admission verdict. */
#endif
}

/* The generated FFIDirect initializer initializes FFI and its exact import
 * closure. Pure executor calls hold the lifecycle lock until full initialization
 * closes registration; this function must never mark full readiness itself. */
int dregg_ffi_init_executor_module(void) {
#ifdef DREGG_DIRECT
    lean_object *res = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_FFIDirect);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
    return 0;
#else
    return 1;
#endif
}

/* THE NARROW PQ FAMILY: the modules of the verified ML-DSA and ML-KEM cores and
 * nothing else. They are outside the FFI closure, and their import closures are
 * the Crypto bricks. Measured on the default family (DREGG_LEAN_INIT_PROFILE=1,
 * 2026-09-23): these modules cost about 0.2 s of a 146 s default init, and the
 * Path of Angels game modules cost about 144 s of it. A process whose only Lean
 * use is signing, verifying or key generation initializes this family alone.
 * Like the DelegAdmit and FFIDirect families it never marks the end of
 * initialization, so a later full init still runs every module it lists; a
 * module initialized here is a no-op there, through its generated guard.
 * Returns 0 on success, 1 on a failed initializer, 2 when no PQ core is linked. */
static int dregg_ffi_init_one_pq_module(lean_object *res) {
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
    return 0;
}

int dregg_ffi_init_pq_modules(void) {
    int linked = 0;
#if defined(DREGG_FIPS204_VERIFY) || defined(DREGG_FIPS204_VERIFY_REAL)
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_Fips204Verify)) != 0)
        return 1;
#endif
#ifdef DREGG_FIPS203
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_Fips203Kem)) != 0)
        return 1;
#endif
#ifdef DREGG_MLKEM_DECAPS_REAL
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlKemDecaps)) != 0)
        return 1;
#endif
#ifdef DREGG_MLKEM_ENCAPS_REAL
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlKemEncaps)) != 0)
        return 1;
#endif
#ifdef DREGG_MLKEM_KEYGEN_REAL
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlKemKeygen)) != 0)
        return 1;
#endif
#ifdef DREGG_MLDSA_KEYGEN_REAL
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlDsaKeygen)) != 0)
        return 1;
#endif
#ifdef DREGG_FIPS204_SIGN_REAL
    linked = 1;
    if (dregg_ffi_init_one_pq_module(
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlDsaSignReal)) != 0)
        return 1;
#endif
    return linked ? 0 : 2;
}

/* Preserve the complete default module list; runtime start and end-of-init are
 * separate so an earlier narrow admission does not restart or prematurely end it. */
int dregg_ffi_init_modules(void) {
    lean_object *res = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_FFI);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
#ifdef DREGG_FINALIZE_GATE
    /* The finality-gate module is OUTSIDE the FFI closure, so its initializer is not run above.
     * Initialize it explicitly so `dregg_blocklace_finalize` is callable. Its own dependency
     * closure (Blocklace/ConsensusExec) is re-entrant-safe under Lean's init guards. */
    lean_object *gres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_FinalityGate);
    if (!lean_io_result_is_ok(gres)) {
        lean_io_result_show_error(gres);
        lean_dec_ref(gres);
        return 1;
    }
    lean_dec_ref(gres);
#endif
#ifdef DREGG_STRAND_ADMIT
    /* The strand-admission module is also OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_strand_admit` is callable. Its dependency closure (BlocklaceFinality/StrandIntegrity)
     * is re-entrant-safe under Lean's init guards (shared with the finality gate above). */
    lean_object *ares = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_StrandAdmission);
    if (!lean_io_result_is_ok(ares)) {
        lean_io_result_show_error(ares);
        lean_dec_ref(ares);
        return 1;
    }
    lean_dec_ref(ares);
#endif
#ifdef DREGG_ROUND_ADVANCE
    /* The ES round-advance module is also OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_round_advance` is callable. Its dependency closure (BlocklaceFinality/FinalityGate)
     * is re-entrant-safe under Lean's init guards (shared with the gates above). */
    lean_object *ragres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_RoundAdvanceGate);
    if (!lean_io_result_is_ok(ragres)) {
        lean_io_result_show_error(ragres);
        lean_dec_ref(ragres);
        return 1;
    }
    lean_dec_ref(ragres);
#endif
#ifdef DREGG_ACK_ADMIT
    /* The acknowledge-before-admit module is also OUTSIDE the FFI closure; initialize it
     * explicitly so `dregg_ack_admit` is callable. Its dependency closure
     * (BlocklaceFinality/FinalityGate) is re-entrant-safe under Lean's init guards (shared with
     * the gates above). */
    lean_object *ackres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_AckBeforeAdmit);
    if (!lean_io_result_is_ok(ackres)) {
        lean_io_result_show_error(ackres);
        lean_dec_ref(ackres);
        return 1;
    }
    lean_dec_ref(ackres);
#endif
#ifdef DREGG_DISTRIBUTED_EXPORTS
    /* The CapTP+coord distributed-exports module is also OUTSIDE the FFI closure; initialize it
     * explicitly so the six `dregg_captp_*` / `dregg_coord_*` exports are callable. Its dependency
     * closure (CapTPConcrete/CapTPGCConcrete/CapTPPipeline/Coord.*) is re-entrant-safe under Lean's
     * init guards. */
    lean_object *dres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_DistributedExports);
    if (!lean_io_result_is_ok(dres)) {
        lean_io_result_show_error(dres);
        lean_dec_ref(dres);
        return 1;
    }
    lean_dec_ref(dres);
#endif
#ifdef DREGG_DECIDE_REFINES
    /* The flow-refinement module is also OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_decide_refines` is callable. Its dependency closure (Deos.FlowAlgebra) is
     * re-entrant-safe under Lean's init guards. */
    lean_object *rres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Deos_FlowRefine);
    if (!lean_io_result_is_ok(rres)) {
        lean_io_result_show_error(rres);
        lean_dec_ref(rres);
        return 1;
    }
    lean_dec_ref(rres);
#endif
#ifdef DREGG_DIRECT
    /* The no-copy direct boundary module is OUTSIDE the FFI closure (it imports FFI); initialize it
     * explicitly so the `dregg_d_*` builders/readers + `dregg_exec_full_forest_auth_direct` are
     * callable. Its dependency closure (Dregg2.Exec.FFI and below) is re-entrant-safe under Lean's
     * init guards (already initialized by `initialize_Dregg2_Dregg2_Exec_FFI` above). */
    lean_object *fdres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_FFIDirect);
    if (!lean_io_result_is_ok(fdres)) {
        lean_io_result_show_error(fdres);
        lean_dec_ref(fdres);
        return 1;
    }
    lean_dec_ref(fdres);
#endif
#ifdef DREGG_STORAGE_CONTENT_ROOT
    /* The verified-storage content-root module is OUTSIDE the FFI closure; initialize it explicitly
     * so `dregg_storage_content_root` is callable. Its dependency closure (Storage.BucketCommitment /
     * Lightclient.MMR) is re-entrant-safe under Lean's init guards. */
    lean_object *sres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Storage_Deployed);
    if (!lean_io_result_is_ok(sres)) {
        lean_io_result_show_error(sres);
        lean_dec_ref(sres);
        return 1;
    }
    lean_dec_ref(sres);
#endif
#ifdef DREGG_CONSTRAINT_ADMITS
    lean_object *cares = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_DeployedConstraint);
    if (!lean_io_result_is_ok(cares)) {
        lean_io_result_show_error(cares);
        lean_dec_ref(cares);
        return 1;
    }
    lean_dec_ref(cares);
#endif
#ifdef DREGG_MINA_STATE_HASH_WORD_OK
    lean_object *mshres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Bridge_MinaStateHashWordGate);
    if (!lean_io_result_is_ok(mshres)) {
        lean_io_result_show_error(mshres);
        lean_dec_ref(mshres);
        return 1;
    }
    lean_dec_ref(mshres);
#endif
#ifdef DREGG_MINA_WRAP_CHALLENGES
    lean_object *mwcres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Bridge_MinaWrapChallenges);
    if (!lean_io_result_is_ok(mwcres)) {
        lean_io_result_show_error(mwcres);
        lean_dec_ref(mwcres);
        return 1;
    }
    lean_dec_ref(mwcres);
#endif
#ifdef DREGG_MINA_WRAP_FT_EVAL0
    lean_object *mwfres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Bridge_MinaWrapFtEval0);
    if (!lean_io_result_is_ok(mwfres)) {
        lean_io_result_show_error(mwfres);
        lean_dec_ref(mwfres);
        return 1;
    }
    lean_dec_ref(mwfres);
#endif
#ifdef DREGG_MINA_ACCOUNT_STATE_OK
    lean_object *maores = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Bridge_MinaAccountOpening);
    if (!lean_io_result_is_ok(maores)) {
        lean_io_result_show_error(maores);
        lean_dec_ref(maores);
        return 1;
    }
    lean_dec_ref(maores);
#endif
#ifdef DREGG_MINA_DEFERRAL_OK
    lean_object *mdores = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Circuit_Emit_PastaIpaDeferral);
    if (!lean_io_result_is_ok(mdores)) {
        lean_io_result_show_error(mdores);
        lean_dec_ref(mdores);
        return 1;
    }
    lean_dec_ref(mdores);
#endif
#if defined(DREGG_MINA_BETTER_TIP) || defined(DREGG_MINA_HEAD_ADVANCE)
    /* ONE initializer for BOTH fork-choice exports — they share a module, and it is what brings the
     * pinned `mainnet` selection constants into existence. Re-entrant-safe under Lean's init
     * guards, so the `||` gate is correct even when only one export is present. */
    lean_object *mfcres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Bridge_MinaForkChoiceGate);
    if (!lean_io_result_is_ok(mfcres)) {
        lean_io_result_show_error(mfcres);
        lean_dec_ref(mfcres);
        return 1;
    }
    lean_dec_ref(mfcres);
#endif
#ifdef DREGG_MINA_CHECKPOINT_ADVANCE
    /* `Dregg2.Bridge.MinaCheckpoint` imports `MinaForkChoiceGate` and `MinaSlidingWindow`, so this
     * one call brings BOTH the pinned `mainnet` selection constants and the density window's module
     * data into existence. Re-entrant-safe under Lean's init guards, so it is correct alongside the
     * fork-choice initializer above whether or not that gate is also present. */
    lean_object *mckres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Bridge_MinaCheckpoint);
    if (!lean_io_result_is_ok(mckres)) {
        lean_io_result_show_error(mckres);
        lean_dec_ref(mckres);
        return 1;
    }
    lean_dec_ref(mckres);
#endif
#ifdef DREGG_CROSS_CELL_CONSERVES
    lean_object *cccres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Circuit_CrossCellConserveDecision);
    if (!lean_io_result_is_ok(cccres)) {
        lean_io_result_show_error(cccres);
        lean_dec_ref(cccres);
        return 1;
    }
    lean_dec_ref(cccres);
#endif
#if defined(DREGG_FIPS204_VERIFY) || defined(DREGG_FIPS204_VERIFY_REAL)
    /* The verified ML-DSA verify-core module is OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_fips204_verify` AND the full-byte `dregg_fips204_verify_real` (BRICK 8, same module) are
     * callable. Its dependency closure (Crypto.Fips204Spec / Crypto.DreggPqRefinement /
     * Crypto.HybridCombiner / — for the real verify — Crypto.MlDsaVerifyReal and its Keccak/Ring/Codec
     * bricks) is re-entrant-safe under Lean's init guards. */
    lean_object *fvres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_Fips204Verify);
    if (!lean_io_result_is_ok(fvres)) {
        lean_io_result_show_error(fvres);
        lean_dec_ref(fvres);
        return 1;
    }
    lean_dec_ref(fvres);
#endif
#ifdef DREGG_FIPS203
    /* The verified ML-KEM encaps/decaps-core module is OUTSIDE the FFI closure; initialize it explicitly
     * so `dregg_fips203_encaps` / `dregg_fips203_decaps` are callable. Its dependency closure
     * (Crypto.MlKemIndCca / Crypto.DreggKemRefinement / Crypto.HybridCombiner) is re-entrant-safe under
     * Lean's init guards (shared with the ML-DSA verify-core module above). */
    lean_object *kres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_Fips203Kem);
    if (!lean_io_result_is_ok(kres)) {
        lean_io_result_show_error(kres);
        lean_dec_ref(kres);
        return 1;
    }
    lean_dec_ref(kres);
#endif
#ifdef DREGG_MLKEM_DECAPS_REAL
    /* BRICK K6 — the REAL, FULL-BYTE ML-KEM-768 decaps-core module (`Dregg2.Crypto.MlKemDecaps`) is OUTSIDE
     * the FFI closure and is its OWN module (distinct from `Fips203Kem`), so initialize it explicitly so
     * `dregg_mlkem_decaps_real` is callable. Its dependency closure (Crypto.Keccak / MlKemRing / MlKemSample
     * / MlKemCodec) is re-entrant-safe under Lean's init guards. */
    lean_object *kdres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlKemDecaps);
    if (!lean_io_result_is_ok(kdres)) {
        lean_io_result_show_error(kdres);
        lean_dec_ref(kdres);
        return 1;
    }
    lean_dec_ref(kdres);
#endif
#ifdef DREGG_MLKEM_ENCAPS_REAL
    /* BRICK K5 — the REAL, FULL-BYTE ML-KEM-768 encaps-core module (`Dregg2.Crypto.MlKemEncaps`) is OUTSIDE
     * the FFI closure and is its OWN module (imports `MlKemDecaps`), so initialize it explicitly so
     * `dregg_mlkem_encaps_real` is callable. Its dependency closure (Crypto.Keccak / MlKemRing / MlKemSample /
     * MlKemCodec / MlKemDecaps) is re-entrant-safe under Lean's init guards (shared with the decaps module). */
    lean_object *keres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlKemEncaps);
    if (!lean_io_result_is_ok(keres)) {
        lean_io_result_show_error(keres);
        lean_dec_ref(keres);
        return 1;
    }
    lean_dec_ref(keres);
#endif
#ifdef DREGG_MLKEM_KEYGEN_REAL
    /* BRICK K7 — the REAL, FULL-BYTE ML-KEM-768 keygen-core module (`Dregg2.Crypto.MlKemKeygen`) is OUTSIDE
     * the FFI closure and is its OWN module (imports `MlKemDecaps` for SHA3), so initialize it explicitly so
     * `dregg_mlkem_keygen_real` is callable. Its dependency closure (Crypto.Keccak / MlKemRing / MlKemSample /
     * MlKemCodec / MlKemDecaps) is re-entrant-safe under Lean's init guards (shared with the encaps/decaps
     * modules). */
    lean_object *kgres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlKemKeygen);
    if (!lean_io_result_is_ok(kgres)) {
        lean_io_result_show_error(kgres);
        lean_dec_ref(kgres);
        return 1;
    }
    lean_dec_ref(kgres);
#endif

#ifdef DREGG_MLDSA_KEYGEN_REAL
    /* The identity-key KEYGEN mirror — the REAL, FULL-BYTE ML-DSA-65 keygen-core module
     * (`Dregg2.Crypto.MlDsaKeygen`) is OUTSIDE the FFI closure and is its OWN module, so initialize it
     * explicitly so `dregg_mldsa_keygen_real` is callable. Its dependency closure (Crypto.Keccak / MlDsaRing /
     * MlDsaExpandA / MlDsaCodec / MlKemDecaps) is re-entrant-safe under Lean's init guards. */
    lean_object *dkgres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlDsaKeygen);
    if (!lean_io_result_is_ok(dkgres)) {
        lean_io_result_show_error(dkgres);
        lean_dec_ref(dkgres);
        return 1;
    }
    lean_dec_ref(dkgres);
#endif
#ifdef DREGG_FIPS204_SIGN_REAL
    /* THE brick-8 SIGN analog — the REAL, FULL-BYTE ML-DSA-65 sign-core module
     * (`Dregg2.Crypto.MlDsaSignReal`) is OUTSIDE the FFI closure and is its OWN module (distinct from
     * `Fips204Verify`), so initialize it explicitly so `dregg_fips204_sign_real` is callable. Its dependency
     * closure (Crypto.Keccak / MlDsaRing / MlDsaSampleInBall / MlDsaExpandA / MlDsaCodec / MlDsaVerifyReal)
     * is re-entrant-safe under Lean's init guards (shared with the real verify-core module above). */
    lean_object *sdres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Crypto_MlDsaSignReal);
    if (!lean_io_result_is_ok(sdres)) {
        lean_io_result_show_error(sdres);
        lean_dec_ref(sdres);
        return 1;
    }
    lean_dec_ref(sdres);
#endif
#ifdef DREGG_AUTOMATAFL_RULES
    /* The automatafl game-oracle module is OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_automatafl_rules` is callable. Unlike the self-contained cores below it MUST be
     * initialized: its `stock` verb reads the `stockTwoPlayer` module global (see the extern-decl
     * note above). Its dependency closure (Games.AutomataflRules / Games.Automatafl / Tactics /
     * Mathlib.Data.List.Dedup) is re-entrant-safe under Lean's init guards. */
    lean_object *afres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_AutomataflFFI);
    if (!lean_io_result_is_ok(afres)) {
        lean_io_result_show_error(afres);
        lean_dec_ref(afres);
        return 1;
    }
    lean_dec_ref(afres);
#endif
#ifdef DREGG_MULTIWAY_TUG_RULES
    /* The multiway-tug rules-oracle module is OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_multiway_tug_rules` is callable. Like automatafl's (and unlike the self-contained cores
     * below) it MUST be initialized: its `charm` verb reads the `charm` module global and every
     * witness state reads `blankState` (see the extern-decl note above). Its dependency closure
     * (Games.MultiwayTug / Boundary / Tactics / Mathlib multiset+bigops) is re-entrant-safe under
     * Lean's init guards. */
    lean_object *mtres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_MultiwayTugFFI);
    if (!lean_io_result_is_ok(mtres)) {
        lean_io_result_show_error(mtres);
        lean_dec_ref(mtres);
        return 1;
    }
    lean_dec_ref(mtres);
#endif
#ifdef DREGG_POA_SIGNAL_JUDGE
    /* Initialize the complete PoA evaluator closure, including the Emit globals its exact active
     * configuration reads. This remains an evaluator only; initialization confers no authority. */
    lean_object *poares =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkJudge);
    if (!lean_io_result_is_ok(poares)) {
        lean_io_result_show_error(poares);
        lean_dec_ref(poares);
        return 1;
    }
    lean_dec_ref(poares);
#endif
#ifdef DREGG_POA_RECORDS_PROJECT
    /* The Records read model closes over the same evaluator globals; initialize it explicitly and
     * keep both runtime init paths in exact parity. Initialization confers no read authority. */
    lean_object *poarecres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_RecordsRuntime);
    if (!lean_io_result_is_ok(poarecres)) {
        lean_io_result_show_error(poarecres);
        lean_dec_ref(poarecres);
        return 1;
    }
    lean_dec_ref(poarecres);
#endif
#ifdef DREGG_POA_STATION_DAILY_READ
    /* The station daily read closes over the same evaluator globals; initialize it explicitly and
     * keep both runtime init paths in exact parity. Initialization confers no read authority, and
     * confers no write path at all — there is none to confer. */
    lean_object *poastationres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_StationDailyRuntime);
    if (!lean_io_result_is_ok(poastationres)) {
        lean_io_result_show_error(poastationres);
        lean_dec_ref(poastationres);
        return 1;
    }
    lean_dec_ref(poastationres);
#endif
#ifdef DREGG_POA_CRATE_OPEN
    /* ⚑ INITIALIZED, not merely linked, and in LOCKSTEP with lean_init_st.cpp. A module whose
     * initializer never runs answers with an uninitialized closure the first time it is called;
     * this one is the daily ritual's only write path, so a cold-start fault here is every crew
     * member's open silently refusing rather than failing loudly. */
    lean_object *poacrateres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_StationCrateOpenRuntime);
    if (!lean_io_result_is_ok(poacrateres)) {
        lean_io_result_show_error(poacrateres);
        lean_dec_ref(poacrateres);
        return 1;
    }
    lean_dec_ref(poacrateres);
#endif
#ifdef DREGG_POA_NETWORK_GENESIS
    /* This module imports NetworkGenesisWire/Emit and therefore has initialized constants; keep
     * both runtime init paths in exact parity. Initialization does not verify the external tuple. */
    lean_object *poagenres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkGenesis);
    if (!lean_io_result_is_ok(poagenres)) {
        lean_io_result_show_error(poagenres);
        lean_dec_ref(poagenres);
        return 1;
    }
    lean_dec_ref(poagenres);
#endif
#ifdef DREGG_POA_SIGNAL_SLOT_DERIVE
    /* ⚑ INITIALIZED, not merely linked. A module whose initializer never runs answers
     * with an uninitialized closure the first time it is called; the derivation is on the
     * scored-run preparation path, so a cold-start fault here is a silent refusal of every
     * scored run rather than a loud one. */
    lean_object *slotderiveres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_SlotDeriveRuntime);
    if (!lean_io_result_is_ok(slotderiveres)) {
        lean_io_result_show_error(slotderiveres);
        lean_dec_ref(slotderiveres);
        return 1;
    }
    lean_dec_ref(slotderiveres);
#endif
#ifdef DREGG_POA_SIGNAL_FEEDBACK
    /* ⚑ INITIALIZED, not merely linked — same reason as the derivation above: an
     * uninitialized closure would answer the first judged guess with a fault, which the
     * session route cannot tell from a semantic refusal. */
    lean_object *signalfeedbackres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_SignalFeedbackRuntime);
    if (!lean_io_result_is_ok(signalfeedbackres)) {
        lean_io_result_show_error(signalfeedbackres);
        lean_dec_ref(signalfeedbackres);
        return 1;
    }
    lean_dec_ref(signalfeedbackres);
#endif
#ifdef DREGG_POA_DARK_BAZAAR_JUDGE
    lean_object *bazaarres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_DarkBazaarJudge);
    if (!lean_io_result_is_ok(bazaarres)) {
        lean_io_result_show_error(bazaarres);
        lean_dec_ref(bazaarres);
        return 1;
    }
    lean_dec_ref(bazaarres);
#endif
#ifdef DREGG_POA_GALLEY_DAILY_JUDGE
    lean_object *galleyres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_GalleyMaintenanceDailyRuntime);
    if (!lean_io_result_is_ok(galleyres)) {
        lean_io_result_show_error(galleyres);
        lean_dec_ref(galleyres);
        return 1;
    }
    lean_dec_ref(galleyres);
#endif
#ifdef DREGG_POA_NIGHT_WATCH_CAMPAIGN_JUDGE
    lean_object *nightwatchres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_NightWatchCampaignWire);
    if (!lean_io_result_is_ok(nightwatchres)) {
        lean_io_result_show_error(nightwatchres);
        lean_dec_ref(nightwatchres);
        return 1;
    }
    lean_dec_ref(nightwatchres);
#endif
#if defined(DREGG_POA_CREW_FIELD_STEP) || defined(DREGG_POA_CREW_FIELD_SEAT_PREIMAGE)
    lean_object *crewfieldres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_CrewFieldMissionAdmission);
    if (!lean_io_result_is_ok(crewfieldres)) {
        lean_io_result_show_error(crewfieldres);
        lean_dec_ref(crewfieldres);
        return 1;
    }
    lean_dec_ref(crewfieldres);
#endif
#if defined(DREGG_POA_EVENT_BATCH_RUNTIME_PLAN) || \
    defined(DREGG_POA_EVENT_BATCH_RUNTIME_INITIAL_HEADS_DIGEST)
    lean_object *batchres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_EventBatchRuntime);
    if (!lean_io_result_is_ok(batchres)) {
        lean_io_result_show_error(batchres);
        lean_dec_ref(batchres);
        return 1;
    }
    lean_dec_ref(batchres);
#endif
#if defined(DREGG_POA_WORLD_ACTIVATION_JUDGE) || defined(DREGG_POA_WORLD_ACTIVATION_AUTHORIZES)
    lean_object *worldactivationres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_WorldActivation);
    if (!lean_io_result_is_ok(worldactivationres)) {
        lean_io_result_show_error(worldactivationres);
        lean_dec_ref(worldactivationres);
        return 1;
    }
    lean_dec_ref(worldactivationres);
#endif
#ifdef DREGG_POA_ACTIVATED_CONTENT_AUTHORIZE
    lean_object *activatedcontentres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_ActivatedContentRuntime);
    if (!lean_io_result_is_ok(activatedcontentres)) {
        lean_io_result_show_error(activatedcontentres);
        lean_dec_ref(activatedcontentres);
        return 1;
    }
    lean_dec_ref(activatedcontentres);
#endif
#ifdef DREGG_POA_BAZAAR_RUNTIME
    lean_object *bazaarpersistres =
        DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_BazaarGameRuntime);
    if (!lean_io_result_is_ok(bazaarpersistres)) {
        lean_io_result_show_error(bazaarpersistres);
        lean_dec_ref(bazaarpersistres);
        return 1;
    }
    lean_dec_ref(bazaarpersistres);
#endif
    /* NOTE: DREGG_GRAIN_R3_VERIFY needs NO module initializer here — `dregg_grain_r3_verify`'s
     * generated C is self-contained (static-const string literals + a lazy once-cell), and calling
     * `initialize_Dregg2_Dregg2_Grain_R3Verify` would drag its Mathlib-tactic import closure's
     * undefined initializer symbols into the link. See the extern-decl note above. */
    return 0;
}

/* dregg_record_kernel_step_str — a plain-C string bridge over the Lean `String -> String`
 * record-cell-state step export.
 *
 * `in_utf8` is a NUL-terminated UTF-8 wire string (the JSON `RecordKernelState` + turn).
 * We box it into a Lean string, call the verified `dregg_record_kernel_step`, copy the
 * result into the caller-owned `out` buffer (NUL-terminated, truncated to `out_cap-1`),
 * and decref the Lean objects.
 *
 * Returns the FULL byte length of the result string (excluding the NUL). If that is
 * >= out_cap the output was truncated and the caller should retry with a larger buffer.
 * Returns (size_t)-1 only if `out`/`out_cap` are unusable. */
size_t dregg_record_kernel_step_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);   /* takes ownership semantics: refcount 1 */
    lean_object *res = dregg_record_kernel_step(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_record_kernel_step_caps_str — the caps-bearing analog of the bridge above. Identical
 * marshalling discipline; the only difference is it drives `dregg_record_kernel_step_caps`,
 * whose input wire also carries the `Caps` table. Same return contract (full byte length;
 * (size_t)-1 only on an unusable buffer). */
size_t dregg_record_kernel_step_caps_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_record_kernel_step_caps(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_exec_full_turn_str — the C string bridge over the Lean `String -> String` FULL-TURN
 * executor export. Identical marshalling discipline as the step bridges above; it drives
 * `dregg_exec_full_turn`, whose input wire is `{"cells":CELLS,"caps":CAPS,"actions":ACTIONS}`
 * and whose output is `{"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}`. Same return contract
 * (full byte length; (size_t)-1 only on an unusable buffer). */
size_t dregg_exec_full_turn_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_full_turn(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

#ifdef DREGG_STORAGE_CONTENT_ROOT
/* dregg_storage_content_root_str — the C string bridge over the VERIFIED Lean `String -> String`
 * storage content-root export (`Dregg2.Storage.Deployed.contentRootFFI`). Input: space-separated
 * object int-triples (`"key ctype body key ctype body …"`). Output: the deployed Poseidon2 content
 * root as a decimal string. Runs the PROVED `contentRootDeployed` (bound by
 * `contentRootDeployed_injective`), calling the fast Rust Poseidon2 through `@[extern]`. Same return
 * contract as the bridges above. */
size_t dregg_storage_content_root_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_storage_content_root(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_SIGNAL_SLOT_DERIVE
/* Host-bounded string bridge for the per-run instance derivation. Zero-length output is
 * Lean's semantic refusal; `(size_t)-1` is an unusable or over-limit host transport. */
size_t dregg_poa_signal_slot_derive_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_SLOT_DERIVE_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_signal_slot_derive(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_SLOT_DERIVE_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_SIGNAL_FEEDBACK
/* Host-bounded string bridge for the mid-run LOCKED/DRIFT oracle. Zero-length output is
 * Lean's semantic refusal (a non-canonical wire, or a secret that does not open the stated
 * commitment); `(size_t)-1` is an unusable or over-limit host transport. */
size_t dregg_poa_signal_feedback_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_SIGNAL_FEEDBACK_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_signal_feedback(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_SIGNAL_FEEDBACK_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_DARK_BAZAAR_JUDGE
/* Host-bounded string bridge. Zero-length output is Lean's semantic refusal;
 * `(size_t)-1` is an unusable or over-limit host transport. */
size_t dregg_poa_dark_bazaar_judge_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_DARK_BAZAAR_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_dark_bazaar_judge(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_DARK_BAZAAR_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_GALLEY_DAILY_JUDGE
size_t dregg_poa_galley_daily_judge_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_GALLEY_DAILY_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_galley_daily_judge(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_GALLEY_DAILY_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_NIGHT_WATCH_CAMPAIGN_JUDGE
size_t dregg_poa_night_watch_campaign_judge_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_NIGHT_WATCH_CAMPAIGN_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_night_watch_campaign_judge(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_NIGHT_WATCH_CAMPAIGN_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_CREW_FIELD_STEP
size_t dregg_poa_crew_field_step_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_CREW_FIELD_STEP_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_crew_field_step(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_CREW_FIELD_STEP_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_CREW_FIELD_SEAT_PREIMAGE
size_t dregg_poa_crew_field_seat_preimage_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_CREW_FIELD_SEAT_PREIMAGE_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_crew_field_seat_preimage(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_CREW_FIELD_SEAT_PREIMAGE_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_EVENT_BATCH_RUNTIME_PLAN
size_t dregg_poa_event_batch_runtime_plan_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_EVENT_BATCH_RUNTIME_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_event_batch_runtime_plan(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_EVENT_BATCH_RUNTIME_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_EVENT_BATCH_RUNTIME_INITIAL_HEADS_DIGEST
size_t dregg_poa_event_batch_runtime_initial_heads_digest_str(
    const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_EVENT_BATCH_RUNTIME_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_event_batch_runtime_initial_heads_digest(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_EVENT_BATCH_RUNTIME_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_WORLD_ACTIVATION_JUDGE
size_t dregg_poa_world_activation_judge_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_WORLD_ACTIVATION_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_world_activation_judge(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_WORLD_ACTIVATION_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_WORLD_ACTIVATION_AUTHORIZES
size_t dregg_poa_world_activation_authorizes_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_WORLD_ACTIVATION_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_world_activation_authorizes(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > 1) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_ACTIVATED_CONTENT_AUTHORIZE
size_t dregg_poa_activated_content_authorize_str(
    const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_ACTIVATED_CONTENT_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_activated_content_authorize(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_ACTIVATED_CONTENT_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_BAZAAR_RUNTIME
size_t dregg_poa_bazaar_state_key_validate_str(
    const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap < 2) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len == 0 || input_len > DREGG_POA_BAZAAR_STATE_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    uint8_t valid = dregg_poa_bazaar_runtime_state_key_validate(
        lean_mk_string(in_utf8));
    out[0] = valid ? '1' : '0';
    out[1] = '\0';
    return 1;
}

size_t dregg_poa_bazaar_runtime_fixture_str(
    const char *command_utf8, char *out, size_t out_cap) {
    if (command_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *result = dregg_poa_bazaar_runtime_fixture(
        lean_mk_string(command_utf8));
    if (!lean_io_result_is_ok(result)) {
        out[0] = '\0';
        lean_dec_ref(result);
        return (size_t)-1;
    }
    lean_object *value = lean_io_result_get_value(result);
    size_t value_size = lean_string_size(value);
    if (value_size == 0 || value_size - 1 > 64) {
        out[0] = '\0';
        lean_dec_ref(result);
        return (size_t)-1;
    }
    size_t full = value_size - 1;
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, lean_string_cstr(value), copy);
    out[copy] = '\0';
    lean_dec_ref(result);
    return full;
}
#endif

#ifdef DREGG_CONSTRAINT_ADMITS
size_t dregg_constraint_admits_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_constraint_admits(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

/* dregg_cross_cell_conserves_str — the C string bridge over the exported Lean `String -> String`
 * cross-cell per-asset conservation decision (`CrossCellConserveDecision.conservesFFI`). Input: the
 * `(asset, delta)` rows + declared supply wire; output: `"1"` (conserves / ADMIT), `"0 <asset>
 * <imbalance>"` (first imbalanced asset / REFUSE), or `"0"` (malformed / fail-closed REFUSE). Same
 * return contract as the bridges above. */
#ifdef DREGG_CROSS_CELL_CONSERVES
size_t dregg_cross_cell_conserves_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_cross_cell_conserves(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FIPS204_VERIFY
/* dregg_fips204_verify_str — the C string bridge over the VERIFIED Lean `String -> String` ML-DSA
 * verify-core export (`Dregg2.Crypto.Fips204Verify.verifyFFI`). Input: `"thi μ c̃ z h"` (five decimal
 * ints). Output: `"1"` (accept) / `"0"` (reject). Runs the extracted `verifyCore` — the
 * `Fips204Spec.verifyB` predicate at the deployed ML-DSA-65 parameters, PROVED to reject forgeries by
 * the `#guard` teeth. Same return contract as the bridges above. */
size_t dregg_fips204_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fips204_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_GRAIN_R3_VERIFY
/* dregg_grain_r3_verify_str — the C string bridge over the VERIFIED Lean `String -> String` GRAIN R3
 * whole-history verify-core export (`Dregg2.Grain.R3Verify.r3VerifyFFI`). Input:
 * `"aggregateVerified aggregateHead anchoredHead"` (three decimal ints). Output: `"1"` (accept) /
 * `"0"` (reject). Runs the PROVED `r3VerifyCore` — a lying host cannot serve a fabricated/truncated
 * history under an honest-looking anchored head (reduced to `EngineSound` + head-binding). Same return
 * contract as the bridges above. */
size_t dregg_grain_r3_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_grain_r3_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_HOLDING_GRANT_WEIGHT
/* dregg_holding_grant_weight_str — the C string bridge over the VERIFIED Lean `String -> String` HOLDING
 * grant-weight verdict-core export (`Metatheory.Bridge.ProofOfHoldings.grantWeightFFI`). Input:
 * `"isConsensusProven slotFinal amount"` (three decimal ints). Output: the granted weight as a decimal
 * string (`= amount` when granted, `"0"` when refused / fail-closed). Runs the PROVED `grantWeightCore`
 * — the non-custodial proof-of-holdings → governance-weight decision, proved to realize the
 * `grantsWeight` spec. Same return contract as the bridges above. */
size_t dregg_holding_grant_weight_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_holding_grant_weight(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_INTERCHAIN_REACHED_CONSENSUS
/* dregg_interchain_reached_consensus_str — the C string bridge over the VERIFIED Lean
 * `String -> String` INTERCHAIN reached-consensus verdict-core export
 * (`Dregg2.Bridge.InterchainAdapterDecision.reachedConsensusFFI`). Input: `"tag payload"` (two decimal
 * ints — the rung selector + the watchtower/committee resolution bit). Output: `"1"` (reached
 * consensus) / `"0"` (refused / fail-closed). Runs the PROVED `reachedConsensusWire` — the bridge-trust
 * decision, proved to realize the `reachesConsensusSpec` fail-closed spec (the `rpc`/fraud/no-quorum/
 * unknown-tag rungs refuse; proof/resolved-watchtower/quorum-committee reach). Same return contract as
 * the bridges above. */
size_t dregg_interchain_reached_consensus_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_interchain_reached_consensus(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_AUTOMATAFL_RULES
/* dregg_automatafl_rules_str — the C string bridge over the Lean `String -> String` AUTOMATAFL GAME
 * ORACLE export (`Dregg2.Games.AutomataflFFI.rulesFFI`). Input: a verb-first token wire (see the
 * extern-decl note above and the module's header table). Output: `"1 …"` with the verb's payload, or
 * `"0"` fail-closed for a malformed wire. Runs `Dregg2.Games.AutomataflRules` — the spec the emitted
 * Leg-R / Leg-A descriptors are refined against — so the witness generator, the playable surface and
 * the AIR all take their answer from one object. Same return contract as the bridges above. */
size_t dregg_automatafl_rules_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_automatafl_rules(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MULTIWAY_TUG_RULES
/* dregg_multiway_tug_rules_str — the C string bridge over the Lean `String -> String` MULTIWAY-TUG
 * RULES ORACLE export (`Dregg2.Games.MultiwayTugFFI.rulesFFI`). Input: a verb-first token wire (see
 * the extern-decl note above and the module's header table). Output: `"1 …"` with the verb's
 * payload, or `"0"` fail-closed for a malformed wire. Runs `Dregg2.Games.MultiwayTug` — the spec
 * whose conservation, one-action-per-round, offer-interlock, scoring and win-safety theorems the
 * emitted `MultiwayTugProgram` teeth are pinned against — so the playable surface, the witness path
 * and the deployed teeth all take their answer from one object. Same return contract as the bridges
 * above. */
size_t dregg_multiway_tug_rules_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_multiway_tug_rules(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_SIGNAL_JUDGE
/* Bounded C string bridge over the internal PoA Signal evaluator. Both accepted input and emitted
 * output are capped at a 64 MiB HOST ceiling. This is deliberately distinct from Lean's 16 MiB
 * semantic pre-parser limit: exceeding 64 MiB is a host transport refusal, while 16..64 MiB still
 * reaches Lean and is its fail-closed judgement. Returns the full output length on success/refusal
 * (zero means the Lean evaluator refused) and `(size_t)-1` for an unusable/over-limit transport. */
size_t dregg_poa_signal_judge_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_SIGNAL_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_signal_judge(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_SIGNAL_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_RECORDS_PROJECT
/* Bounded C string bridge over the Records read model. Same return contract as the evaluator
 * bridge above: the full output length on success, zero for Lean's refusal sentinel, `(size_t)-1`
 * for an unusable or over-limit host transport. */
size_t dregg_poa_records_project_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_RECORDS_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_records_project(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_RECORDS_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_STATION_DAILY_READ
/* Bounded C string bridge over the station daily read. Same return contract as the Records bridge
 * above: the full output length on success, zero for Lean's refusal sentinel, `(size_t)-1` for an
 * unusable or over-limit host transport. */
size_t dregg_poa_station_daily_read_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_STATION_DAILY_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_station_daily_read(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_STATION_DAILY_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_CRATE_OPEN
/* Bounded C string bridge over the station crate-open write. Same return contract as the station
 * read bridge above: the full output length on success, zero for Lean's refusal sentinel (a wire
 * the canonical seal declined), `(size_t)-1` for an unusable or over-limit host transport. A
 * SEMANTIC refusal — the crate declining the open — is a nonempty document with `"opened":false`
 * and no gauge, not a zero length. */
size_t dregg_poa_crate_open_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_CRATE_OPEN_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_crate_open(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_CRATE_OPEN_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_POA_NETWORK_GENESIS
/* Bounded opaque transport for the Lean authority-head emission. Zero output is semantic refusal;
 * `(size_t)-1` is an unusable or over-limit host transport. */
size_t dregg_poa_network_genesis_str(const char *in_utf8, char *out, size_t out_cap) {
    if (in_utf8 == 0 || out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    size_t input_len = strlen(in_utf8);
    if (input_len > DREGG_POA_NETWORK_GENESIS_WIRE_MAX_BYTES) {
        out[0] = '\0';
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_poa_network_genesis(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    if (full > DREGG_POA_NETWORK_GENESIS_WIRE_MAX_BYTES) {
        out[0] = '\0';
        lean_dec_ref(res);
        return (size_t)-1;
    }
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FRI_LEDGER
/* dregg_fri_ledger_str — the C string bridge over the Lean `String -> String` FRI SOUNDNESS LEDGER
 * export (`Dregg2.Circuit.FriLedger.friLedgerFFI`). Input:
 * `"logBlowup numQueries powBits maxLogArity logFinalPolyLen extDeg logD0 bciksM"` (eight decimal
 * nats). Output: `"arity foldedDomain goodCount perFoldBits johnsonBits capacityBits commitBits"`
 * (`""` fail-closed). Runs `friLedger` — the function `FriLedgerSound.ledger_perFold_soundness`
 * proves the per-fold bound of, per config — plus `friCommitLedger`'s ε_C column, so no Rust caller
 * re-types the soundness arithmetic. Same return contract as the bridges above. */
size_t dregg_fri_ledger_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fri_ledger(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_DELEG_ADMIT
/* dregg_deleg_admit_str — the C string bridge over the Lean `String -> String` DELEGATED
 * TOOL/MCP-ACCESS ADMISSION export (`Dregg2.Apps.DelegAdmit.delegAdmitFFI`). Input:
 * `"toolId rateLimit deadline now tool old new"` (seven signed decimal integers — the grant
 * flattened first, then the presentation, then the counter transition). Output: `"1"` ADMIT / `"0"`
 * REFUSE (the delegated policy said no) / `""` malformed wire (NO VERDICT — the Rust wrapper turns an
 * empty answer into an `Err` and every caller refuses). Runs `delegAdmit`, the predicate
 * `tool_invocation_commit_iff_admit` is stated over, so a routed gateway's verdict IS the proven
 * one. Same return contract as the bridges above. */
size_t dregg_deleg_admit_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_deleg_admit(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_TRUSTLINE_STEP
/* dregg_trustline_step_str — the C string bridge over the Lean `String -> String` TRUSTLINE
 * DRAW/REPAY/SETTLE export (`Dregg2.Apps.TrustlineCore.trustlineStepFFI`). Input:
 * `"op ceiling drawn holderAcct issuerWell issuerHard holderHard a1 a2 n d1 ... dn"` — the verb,
 * the six channel registers (ceiling/drawn unsigned; the two credit wells and the two hard
 * balances SIGNED), two op arguments, then the draw-digest registry as a length-prefixed run.
 * `op` is 0=draw(digest=a1, amt=a2) / 1=repay(amt=a1) / 2=settlePay(amt=a1) / 3=settleAll.
 * Output: the six post-state registers plus the post-state registry (COMMITTED) / `"0"` (REFUSED —
 * replayed digest, over-line, or over-repay) / `""` (malformed wire, NO VERDICT — the Rust wrapper
 * turns an empty answer into an `Err` and every caller refuses). The three shapes are deliberately
 * distinguishable: `"0"` is a verdict, `""` is "no verdict was reached".
 * ⚠ A digest is an arbitrary-precision Lean `Nat`, so a 32-byte hash marshals as its FULL decimal.
 * A caller that folds it to 64 bits would collide two distinct debits onto one burned digest and
 * silently defeat the anti-replay leg this export exists to provide.
 * Same return contract as the bridges above. */
size_t dregg_trustline_step_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_trustline_step(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_ETH_LC_VERIFY
/* dregg_eth_lc_verify_str — the C string bridge over the VERIFIED Lean `String -> String` ETHEREUM
 * light-client verify-logic gate (`Dregg2.Bridge.LightClientEthGate.dregg_eth_lc_verify`). Input:
 * `"cl=<Nat>;bl=<Nat>;pc=<Nat>;bls=<BIT>;fl=<Nat>;fr=<BIT>;el=<Nat>;er=<BIT>"`. Output: `"1"`
 * (ACCEPT) / `"0"` (REJECT) / `"ERR"` (malformed wire — the caller treats it as REJECT). Runs the
 * PROVED `ethVerifyDecision`, which `ethVerifyDecision_refines` proves is DEFINITIONALLY
 * `verifyFinalizedUpdate` — so an ACCEPT here is, with the named `blsSound`/`hashPairCR` crypto
 * carriers sound, exactly `eth_no_forgery`'s `EthValidAt`. Same return contract as the bridges
 * above. */
size_t dregg_eth_lc_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_eth_lc_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_ETH_COMMITTEE_ROTATION
/* dregg_eth_committee_rotation_str — the C string bridge over the VERIFIED Lean
 * `String -> String` ETHEREUM COMMITTEE-ROTATION gate
 * (`Dregg2.Bridge.LightClientEthGate.dregg_eth_committee_rotation`). Input `"nl=<Nat>;nr=<BIT>"`.
 * Output: `"1"` (ACCEPT — rotate) / `"0"` (REJECT) / `"ERR"` (malformed wire — the caller treats
 * it as REJECT). Runs the PROVED `committeeRotationDecision`; by
 * `committeeRotationDecision_binding` an ACCEPT under a given beacon state root pins a UNIQUE
 * next committee (given the named SHA-256 CR carrier), which is what makes advancing the trust
 * anchor safe. Same return contract as the bridges above. */
size_t dregg_eth_committee_rotation_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_eth_committee_rotation(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_TM_LC_VERIFY
/* dregg_tm_lc_verify_str — the C string bridge over the VERIFIED Lean `String -> String`
 * TENDERMINT/COSMOS light-client verify-logic gate
 * (`Dregg2.Bridge.LightClientTendermintGate.dregg_tm_lc_verify`). Input:
 * `"ci=<Nat>;tci=<Nat>;h=<Nat>;th=<Nat>;ht=<Nat>;t=<Nat>;nw=<Nat>;cd=<Nat>;tp=<Nat>;eb=<BIT>;
 * vb=<BIT>;tot=<Nat>;sp=<Nat>"`. Output: `"1"` / `"0"` / `"ERR"` (fail-closed). Runs the PROVED
 * `tmVerifyDecision` — the STRICT stake-weighted `2·tot < 3·sp` threshold plus chain-id / adjacent
 * height / trusting-window / epoch-binding rules — which `tmVerifyDecision_refines` proves is
 * DEFINITIONALLY `tmVerify`, the decision `tmNoForgery` is proven over. Same return contract as the
 * bridges above. */
size_t dregg_tm_lc_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_tm_lc_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_TM_SKIP_VERIFY
/* dregg_tm_skip_verify_str — the C string bridge over the VERIFIED Lean `String -> String`
 * TENDERMINT/COSMOS NON-ADJACENT (skipping) verify-logic gate
 * (`Dregg2.Bridge.LightClientTendermintSkip.dregg_tm_skip_verify`). Input:
 * `"ci=<Nat>;tci=<Nat>;h=<Nat>;th=<Nat>;ht=<Nat>;t=<Nat>;nw=<Nat>;cd=<Nat>;tp=<Nat>;vb=<BIT>;
 * tn=<Nat>;td=<Nat>;ttot=<Nat>;tsp=<Nat>;tot=<Nat>;sp=<Nat>"` — SIXTEEN fields, deliberately not
 * a superset of the adjacent gate's thirteen, so a mis-routed wire decodes to `"ERR"` rather than
 * a verdict about the wrong rule set. Output: `"1"` / `"0"` / `"ERR"` (fail-closed). Runs the
 * PROVED `tmSkipVerifyDecision`, which `tmSkipVerifyDecision_refines` proves is DEFINITIONALLY
 * `tmSkipVerify` — the decision `tmSkipNoForgery` is proven over, whose fourth conjunct is the
 * trust-overlap anchor a skip trades the epoch binding for. Same return contract as the bridges
 * above. */
size_t dregg_tm_skip_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_tm_skip_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MPT_LC_VERIFY
/* dregg_mpt_lc_verify_str — the C string bridge over the VERIFIED Lean `String -> String` EVM
 * state-inclusion (EIP-1186 / MPT) light-client verify-logic gate
 * (`Dregg2.Bridge.LightClientMptGate.dregg_mpt_lc_verify`). Input:
 * `"bal=<Nat>;sr=<Nat>;tsr=<Nat>;tk=<Nat>;ttk=<Nat>;ms=<Nat>;tms=<Nat>;ap=<BIT>;sp=<BIT>"`.
 * Output: `"1"` / `"0"` / `"ERR"` (fail-closed). Runs the PROVED `mptVerifyDecision` — the
 * Nomad-law nonzero-balance floor plus the state-root / token / mapping-slot anchor bindings —
 * which `mptVerifyDecision_refines` proves is DEFINITIONALLY `mptVerify`, the decision
 * `mpt_noForgery` AND `mpt_balance_binding` are proven over. Same return contract as the bridges
 * above. */
size_t dregg_mpt_lc_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mpt_lc_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_LC_VERIFY
/* dregg_mina_lc_verify_str — the C string bridge over the VERIFIED Lean `String -> String` MINA
 * (Ouroboros Samasika / Pickles) light-client verify-logic gate
 * (`Dregg2.Bridge.LightClientMinaGate.dregg_mina_lc_verify`). Input:
 * `"sl=<Nat>;ah=<Nat>;sh=<Nat>;wd=<Nat>;rd=<Nat>;lk=<BIT>;pk=<BIT>;cn=<BIT>"`. Output: `"1"` /
 * `"0"` / `"ERR"` (fail-closed). Runs the PROVED `minaVerifyDecision` — the non-empty segment, the
 * `anchorHeight <= submittedHeight` bound (without which "depth" is measured from OUTSIDE the
 * exhibited evidence, and a one-block segment witnesses a depth of 1001), and the WITNESSED
 * confirmation depth — which `minaVerifyDecision_refines` proves is DEFINITIONALLY `minaVerify`,
 * the decision `mina_no_forgery` is proven over. Same return contract as the bridges above. */
size_t dregg_mina_lc_verify_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_lc_verify(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_WRAP_SHAPE_OK
/* dregg_mina_wrap_shape_ok_str — the C string bridge over the VERIFIED Lean `String -> String`
 * per-block Pickles Wrap-proof preamble gate
 * (`Dregg2.Bridge.PicklesWrapShapeGate.dregg_mina_wrap_shape_ok`). Input:
 * `"ip=<Nat>;pc=<Nat>;pv=<Nat>;pl=<Nat>;w=<Nat>;s=<Nat>;cf=<Nat>;tc=<Nat>;ck=<Nat>;ir=<Nat>;pr=<Nat>"`
 * — four PINNED verifier-index counts (`ip`,`pl`,`ck`,`ir`) and seven read out of the block's own
 * proof by the Rust decoder. Output: `"1"` / `"0"` / `"ERR"` (fail-closed). Runs
 * `picklesWrapShapeOk`, which `picklesWrapShapeOk_is_shapeOkRec` proves is DEFINITIONALLY
 * `shapeOkRec` conjoined with the accumulator-count and IPA-round agreements, and which
 * `real_block_wrap_shape_accepts` / `real_block_wrap_shape_refused_by_freeze` pin on the REAL
 * devnet block 539508 — accepted at `prev_challenges = 2`, refused by the retired `prevLen = 0`
 * freeze. Same return contract as the bridges above. */
size_t dregg_mina_wrap_shape_ok_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_wrap_shape_ok(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_PROOF_CHAIN_OK
/* dregg_mina_proof_chain_ok_str — the C string bridge over the VERIFIED Lean `String -> String`
 * per-adjacent-pair Pickles PROOF-CHAIN gate
 * (`Dregg2.Bridge.PicklesProofChainGate.dregg_mina_proof_chain_ok`). Input:
 * `"px=<Nat>;py=<Nat>;pc=<Nat>,...x16;cx=<Nat>;cy=<Nat>;cc=<Nat>,...x16"` — the PARENT block's own
 * `bulletproof.challenge_polynomial_commitment` and its 16 `deferred_values.bulletproof_challenges`,
 * against the CHILD block's exhibited
 * `messages_for_next_step_proof.challenge_polynomial_commitments[0]` and
 * `...old_bulletproof_challenges[0]`. Every one of those is read out of the two blocks' own proofs
 * by the Rust codec (`bridge/src/mina_pickles.rs`) with no arithmetic. Output: `"1"` / `"0"` /
 * `"ERR"` (fail-closed). Runs `linkOk`, over which `chainOk_adjacent_proofs_differ` proves an
 * accepted segment cannot serve the same proof twice in a row and `chainOk_iff_chain'` proves an
 * accept IS a `List.Chain'` of links; `real_devnet_run_chains` pins the accept on the REAL devnet
 * run 539795->539796->539797 and `real_devnet_chain_discriminates` pins the REPLAY, SWAP, REORDER,
 * SPLICE, tamper and degenerate-accumulator refusals on the same real objects. Note the wire is
 * ~1.6 KB (two 16-element decimal lists), an order of magnitude past the other gates' — the
 * caller's growable output buffer already handles it. Same return contract as the bridges above. */
size_t dregg_mina_proof_chain_ok_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_proof_chain_ok(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_STATE_HASH_WORD_OK
/* dregg_mina_state_hash_word_ok_str — the C string bridge over the VERIFIED Lean `String -> String`
 * per-block proof<->stateHash derivation
 * (`Dregg2.Bridge.MinaStateHashWordGate.dregg_mina_state_hash_word_ok`). Input:
 * `"sh=<Nat>;acc=<Nat>,...x36;mnw=<Nat>,...x32;w12=<Nat>;w11=<Nat>"` — the served `stateHash`
 * Base58Check-decoded into Fp, the proof's own 36 accumulator field elements and 32
 * messages-for-next-wrap elements, and the two public-input words the verification consumed.
 * Output: `"1"` / `"0"` / `"ERR"` (fail-closed). The wire is ~5 KB (two long decimal lists); the
 * caller's growable output buffer already handles it. Same return contract as the bridges above. */
size_t dregg_mina_state_hash_word_ok_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_state_hash_word_ok(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_DEFERRAL_OK
/* dregg_mina_deferral_ok_str — the C string bridge over the VERIFIED Lean `String -> String`
 * DEFERRED-ACCUMULATOR discharge gate (`Dregg2.Circuit.Emit.PastaIpaDeferral.dregg_mina_deferral_ok`).
 * Input: `"n=<Nat>;k=<Nat>;c=<Nat>(,<Nat>)*;d=(0|1)"` — `|srs.g|`, the IPA round count, the
 * per-claim challenge counts (one entry per deferred claim), and whether the batched MSM was
 * evaluated and found to VANISH. Output: `"1"` / `"0"` / `"ERR"` (fail-closed). The wire grows with
 * the batch (one small decimal per claim); the caller's growable output buffer handles it. Same
 * return contract as the bridges above. */
size_t dregg_mina_deferral_ok_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_deferral_ok(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_ACCOUNT_STATE_OK
/* dregg_mina_account_state_ok_str — the C string bridge over the VERIFIED Lean `String -> String`
 * MINA ACCOUNT-OPENING gate
 * (`Dregg2.Bridge.MinaAccountOpening.dregg_mina_account_state_ok`). Input, 15 `;`-separated
 * segments:
 *   `"blk=<hex>;pk=<Nat>,<0|1>;tk=<Nat>;ts=<Nat>;bal=<Nat>;non=<Nat>;rch=<Nat>;dlg=<Nat>,<0|1>"`
 *   `";vf=<Nat>;tm=<0|1>,<Nat>x5;perm=<Auth>|x7...<txnVersion>...;zk=[<Nat>];idx=<Nat>"`
 *   `";sib=<Nat>,...x35;dir=<0|1>x35"`
 * — the block's binprot `Protocol_state.Value.Stable.V2` PREFIX as lowercase hex (the rest of the
 * block may follow and is not read), the account's every leaf field, and its 35-level Merkle
 * opening LEAF FIRST. `zk=` empty is a CLAIM that the account has no zkApp, not a default.
 * Output: `"1"` / `"0"` / `"ERR"` (fail-closed). The wire is ~7 KB (4 KB of block hex plus 35
 * 255-bit decimals); the caller's growable output buffer already handles it. Same return contract
 * as the bridges above. */
size_t dregg_mina_account_state_ok_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_account_state_ok(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_WRAP_CHALLENGES
/* dregg_mina_wrap_challenges_str — the C string bridge over the VERIFIED Lean `String -> String`
 * per-block Fiat-Shamir derivation (`Dregg2.Bridge.MinaWrapChallenges.minaWrapChallengesGate`).
 * Input:
 *   `"vk=<Nat>;er=<Nat>;pc=<NATS>;pu=<NATS>;wc=<NATS>;zc=<NATS>;tc=<NATS>;cs=<Nat>;lr=<NATS>;dl=<NATS>"`
 * — the verifier-index digest (TRUSTED CONFIG), the Pallas `endo_r`, the 2 accumulator
 * commitments, `public_comm`, the 15 witness commitments, `z_comm`, the 7 `t_comm` chunks,
 * `shift_scalar(combined_inner_product)`, the 15 IPA rounds FLAT (60 numbers, re-chunked in Lean
 * because a caller that chunks is a caller that can mis-chunk) and `delta`.
 * Output: `"b=..;g=..;a=..;z=..;fq=..;t=..;c=..;ch=<15 NATS>"` or `"ERR"` (fail-closed).
 * The wire is ~3 KB of decimals; the caller's growable output buffer already handles it. */
size_t dregg_mina_wrap_challenges_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_wrap_challenges(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_WRAP_FT_EVAL0
/* dregg_mina_wrap_ft_eval0_str — the C string bridge over the VERIFIED Lean `String -> String`
 * per-block `ft_eval0` derivation (`Dregg2.Bridge.MinaWrapFtEval0.minaWrapFtEval0Gate`). Input:
 *   `"m=<p|q>;lg=<Nat>;al=<Nat>;be=<Nat>;ga=<Nat>;ze=<Nat>;ez=<43 NATS>;ew=<43 NATS>;pz=<Nat>;
 *     er=<Nat>;en=<Nat>;sh=<7 NATS>;md=<9 NATS>"`
 * — the field selector (`p` = STEP/Tick, `q` = WRAP/Tock), the domain log2, the four RAW plonk
 * challenges, the 43 evaluation columns at zeta and at zeta*omega in `to_absorption_sequence`
 * order, the public polynomial at zeta, the challenge-lift endomorphism scalar, the gate
 * `endo_coefficient` (a DIFFERENT constant), the seven coset shifts and the nine MDS entries.
 * Output: `"lct=..;ft0=..;om=..;ze=..;al=.."` or `"ERR"` (fail-closed).
 *
 * ⚑ There is deliberately no Rust linearization and no Rust modular inverse: the inverse the C5
 * fold needs is produced AND CHECKED (`x*y = 1`) inside the archive. */
size_t dregg_mina_wrap_ft_eval0_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_wrap_ft_eval0(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_BETTER_TIP
/* dregg_mina_better_tip_str — the C string bridge over the VERIFIED Lean `String -> String`
 * pairwise Samasika fork-choice decision (`Dregg2.Bridge.MinaForkChoiceGate.minaBetterTipGate`).
 * Input: `"eh=<Nat>;ch=<Nat>;e=<hex>;c=<hex>"` — the two tips' state hashes as Fp elements, and the
 * RAW binprot `Protocol_state.Value.Stable.V2` bytes of the EXISTING and CANDIDATE tips in
 * lowercase hex. Output: `"1"` (the candidate is canonical, drop the existing tip) / `"0"` (keep
 * the existing one) / `"ERR"` (fail-closed).
 *
 * The bytes are DECODED HERE, by `Dregg2.Bridge.MinaBinprot` — the caller hands over what a socket
 * gave it and knows nothing about which bytes are which consensus field, so there is no Rust mirror
 * of openmina's `p2p-messages` whose correctness would rest on a differential test. `eh`/`ch` are
 * the ONE supplied input, read only as the final tie-break after length and the VRF digest tie.
 * The wire is ~3 KB (two full protocol states in hex), well past the other gates'; the caller's
 * growable output buffer is unaffected since the OUTPUT is one byte. Same return contract as the
 * bridges above. */
size_t dregg_mina_better_tip_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_better_tip(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_HEAD_ADVANCE
/* dregg_mina_head_advance_str — the C string bridge over the VERIFIED Lean `String -> String` head
 * roll (`Dregg2.Bridge.MinaForkChoiceGate.minaHeadAdvanceGate`). Input:
 * `"sg=<0|1>;fz=<Nat>;eh=<Nat>;ch=<Nat>;e=<hex>;c=<hex>"` — the anchored-segment verdict for the
 * candidate (i.e. whether `dregg_mina_lc_verify` returned `"1"`), the persisted finalized height,
 * and the tip pair with the PERSISTED HEAD as `e`. Output: `"adv=<0|1>;fin=<Nat>"` / `"ERR"`
 * (fail-closed).
 *
 * Both halves come back because the caller persists a decision it did not make: `adv` says whether
 * to replace the head, `fin` is the new finalized height. `rollHead_fails_closed_without_the_segment`
 * proves `sg=0` moves nothing, so an unavailable segment gate supplies `0` and never a skip;
 * `rollHead_finalized_monotone` proves `fin` is never below the `fz` that went in. Same return
 * contract as the bridges above. */
size_t dregg_mina_head_advance_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_head_advance(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MINA_CHECKPOINT_ADVANCE
/* dregg_mina_checkpoint_advance_str — the C string bridge over the VERIFIED Lean `String -> String`
 * two-tier checkpoint roll (`Dregg2.Bridge.MinaCheckpoint.minaCheckpointGate`). Input:
 * `"md=<p|c>;wk=<0|1>;fz=<Nat>;rn=<Nat>;rc=<Nat>;ph=<Nat>;th=<Nat>;vh=<Nat>;ch=<Nat>;`
 * `p=<hex>;t=<hex>;v=<hex>;c=<hex>"` — the mode (provisional / CHECKPOINT), the Wrap arithmetic
 * verdict (read ONLY on a checkpoint call), the persisted finalized height, the provisional run
 * counter and its cap, then the four `Protocol_state.Value.Stable.V2` byte strings with the state
 * hash each is claimed under. Output: `"mv=<0|1>;adv=<0|1>;fin=<Nat>;rn=<Nat>"` / `"ERR"`.
 *
 * Four fields come back because the caller persists a decision it did not make: `mv` says the
 * provisional tip moved, `adv` says the VERIFIED head moved, `fin` is the ratchet and `rn` the new
 * run. `provisional_never_ratchets` proves `md=p` cannot raise `fin`; `runSteps_finalized_monotone`
 * proves `fin` is never below the `fz` that went in under ANY interleaving. Each side's bytes are
 * re-hashed against the hash presented WITH them inside the gate, so all four hashes are claims and
 * none is trusted framing. Same return contract as the bridges above. */
size_t dregg_mina_checkpoint_advance_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mina_checkpoint_advance(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FIPS204_VERIFY_REAL
/* dregg_fips204_verify_real_str — the C string bridge over the VERIFIED Lean `String -> String` REAL,
 * FULL-BYTE ML-DSA-65 verify export (`Dregg2.Crypto.Fips204Verify.verifyRealFFI`, BRICK 8). Input:
 * `"hex(pk) hex(msg) hex(ctx) hex(sig)"` (four space-separated lowercase-hex fields over the real
 * 1952-byte key / 3309-byte signature). Output: `"1"` (accept) / `"0"` (reject; also the fail-closed
 * answer for any malformed wire). Runs the FULL-DIMENSION `MlDsaVerifyReal.verifyCore` (proved to accept a
 * genuine crate signature and reject tampers by `verify_accepts_real` / `verify_rejects_tampered`) — the
 * object that takes the `fips204` crate OUT of the deployed verify TCB. Same return contract as the
 * bridges above. */
size_t dregg_fips204_verify_real_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fips204_verify_real(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MLKEM_DECAPS_REAL
/* dregg_mlkem_decaps_real_str — the C string bridge over the VERIFIED Lean `String -> String` REAL,
 * FULL-BYTE ML-KEM-768 decaps export (`Dregg2.Crypto.MlKemDecaps.mlkemDecapsRealFFI`, BRICK K6). Input:
 * `"hex(dk) hex(ct)"` (two space-separated lowercase-hex fields over the real 2400-byte dk / 1088-byte ct).
 * Output: `hex(K)` (the recovered 32-byte shared secret as lowercase hex) or `"ERR"` (the fail-closed answer
 * for any malformed wire). Runs the FULL-DIMENSION `mlkemDecaps` (proved to recover a genuine crate secret
 * and diverge on a tamper by `mlkemDecapsRealFFI_recovers_real_secret` / `mlkemDecapsRealFFI_rejects_tampered`)
 * — the object that takes the `ml-kem` crate OUT of the deployed KEM-decaps TCB. Same return contract as the
 * bridges above. */
size_t dregg_mlkem_decaps_real_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mlkem_decaps_real(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MLKEM_ENCAPS_REAL
/* dregg_mlkem_encaps_real_str — the C string bridge over the VERIFIED Lean `String -> String` REAL,
 * FULL-BYTE ML-KEM-768 encaps export (`Dregg2.Crypto.MlKemEncaps.mlkemEncapsRealFFI`, BRICK K5). Input:
 * `"hex(ek) hex(m)"` (two space-separated lowercase-hex fields over the real 1184-byte ek / 32-byte message).
 * Output: `"hex(ct) hex(K)"` (the 1088-byte ciphertext + 32-byte shared secret as lowercase hex) or `"ERR"`
 * (the fail-closed answer for any malformed wire). Runs the FULL-DIMENSION `mlkemEncaps` (proved BYTE-EXACT vs
 * the crate's `EncapsulateDeterministic` by `encaps_matches_crate`) — the object that takes the `ml-kem` crate
 * OUT of the deployed KEM-ENCAPS TCB. Same return contract as the bridges above. */
size_t dregg_mlkem_encaps_real_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mlkem_encaps_real(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MLKEM_KEYGEN_REAL
/* dregg_mlkem_keygen_real_str — the C string bridge over the VERIFIED Lean `String -> String` REAL,
 * FULL-BYTE ML-KEM-768 keygen export (`Dregg2.Crypto.MlKemKeygen.mlkemKeygenRealFFI`, BRICK K7). Input:
 * `"hex(d z)"` (one lowercase-hex field over the real 64-byte (d,z) seed). Output: `"hex(ek) hex(dk)"`
 * (the 1184-byte encapsulation key + 2400-byte decapsulation key as lowercase hex) or `"ERR"` (the
 * fail-closed answer for any malformed wire). Runs the deterministic FIPS 203 ML-KEM.KeyGen_internal
 * (KAT-anchored vs the NIST ACVP keyGen vectors) — the object that takes the `ml-kem` crate OUT of the
 * deployed KEM-KEYGEN TCB. Same return contract as the bridges above. */
size_t dregg_mlkem_keygen_real_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mlkem_keygen_real(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_MLDSA_KEYGEN_REAL
/* dregg_mldsa_keygen_real_str — the C string bridge over the VERIFIED Lean `String -> String` REAL,
 * FULL-BYTE ML-DSA-65 keygen export (`Dregg2.Crypto.MlDsaKeygen.mldsaKeygenRealFFI`). Input: `"hex(xi)"`
 * (one lowercase-hex field over the real 32-byte ξ seed). Output: `"hex(pk) hex(sk)"` (the 1952-byte public
 * key + 4032-byte secret key as lowercase hex) or `"ERR"` (the fail-closed answer for any malformed wire).
 * Runs the deterministic FIPS 204 ML-DSA.KeyGen_internal (KAT-anchored vs the NIST ACVP ML-DSA-65 keyGen
 * vectors) — the object that takes the `fips204` crate OUT of the deployed IDENTITY-KEY keygen TCB. Same
 * return contract as the bridges above. */
size_t dregg_mldsa_keygen_real_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_mldsa_keygen_real(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FIPS204_SIGN
/* dregg_fips204_sign_str — the C string bridge over the VERIFIED Lean `String -> String` ML-DSA
 * sign-core export (`Dregg2.Crypto.Fips204Verify.signFFI`). Input: `"s1 s2 t0 μ y"` (secret + message +
 * the sampled randomness/mask). Output: `"c̃ z h"` (an accepted signature) or `"REJECT"` (a rejected
 * sample / malformed wire — the caller resamples `y`). Runs the extracted `signCore` — the deterministic
 * Fiat–Shamir-with-aborts signer at the deployed ML-DSA-65 parameters, PROVED to agree with the spec
 * (`signCore_eq_spec`) and to round-trip through `verifyCore` (`signCore_verifies`). Same return contract
 * as the bridges above. */
size_t dregg_fips204_sign_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fips204_sign(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FIPS204_SIGN_REAL
/* dregg_fips204_sign_real_str — the C string bridge over the VERIFIED Lean `String -> String` REAL,
 * FULL-BYTE ML-DSA-65 sign export (`Dregg2.Crypto.MlDsaSignReal.signRealFFI`, the brick-8 SIGN analog).
 * Input: `"hex(sk) hex(msg) hex(ctx)"` (three space-separated lowercase-hex fields over the real 4032-byte
 * secret key). Output: `hex(sig)` (the 3309-byte signature as lowercase hex) or `"ERR"` (the fail-closed
 * answer for any malformed wire). Runs the FULL-DIMENSION `signCore` (proved to reproduce a genuine crate
 * deterministic signature byte-for-byte by `signRealFFI_matches_crate_deterministic`) — the object that
 * takes the `fips204` crate OUT of the deployed SIGN TCB. Same return contract as the bridges above. */
size_t dregg_fips204_sign_real_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fips204_sign_real(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FIPS203_ENCAPS
/* dregg_fips203_encaps_str — the C string bridge over the VERIFIED Lean `String -> String` ML-KEM
 * encaps-core export (`Dregg2.Crypto.Fips203Kem.encapsFFI`). Input: `"A t m"` (three decimal ints).
 * Output: `"u v K"` (the ciphertext (u,v) + the encapsulated secret K=H(m)). Runs the extracted encaps
 * core (the Kyber CPAPKE + FO derandomisation at the deployed q=3329). Same return contract as the
 * bridges above (full byte length; (size_t)-1 only on an unusable buffer). */
size_t dregg_fips203_encaps_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fips203_encaps(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

#ifdef DREGG_FIPS203_DECAPS
/* dregg_fips203_decaps_str — the C string bridge over the VERIFIED Lean `String -> String` ML-KEM
 * decaps-core export (`Dregg2.Crypto.Fips203Kem.decapsFFI`). Input: `"A t s z u v"` (six decimal ints —
 * the encapsulation key (A,t), secret s, implicit-reject seed z, ciphertext (u,v)). Output: the recovered
 * shared secret K as a decimal string (H(m') on a matching re-encryption, else the implicit-reject secret
 * J(z‖c); "ERR" only on a malformed wire). Runs the SECURITY-CRITICAL extracted decaps core (the
 * re-encryption check + implicit reject). Same return contract as the bridges above. */
size_t dregg_fips203_decaps_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_fips203_decaps(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

/* dregg_exec_full_forest_auth_str — the C string bridge over the Lean `String -> String` GATED
 * COMPLETE-TURN executor export (FILL X). Identical marshalling discipline as the bridges above; it drives
 * `dregg_exec_full_forest_auth`, whose input wire is the §WIDE `{"state":STATEW,"turn":TURNW}` and whose
 * output is `{"state":STATEW,"loglen":N,"ok":B}`. The executed object is the credential-AWARE
 * `FullForestAuth.execFullForestG` (a forged per-node credential ⇒ whole-turn rollback). Same return
 * contract (full byte length; (size_t)-1 only on an unusable buffer). */
size_t dregg_exec_full_forest_auth_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_full_forest_auth(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_exec_handler_turn_str — the C string bridge over the Lean `String -> String` HANDLER-CUTOVER
 * COMPLETE-TURN executor export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_exec_handler_turn`, whose input wire is the §WIDE `{"state":STATEW,"turn":TURNW}` and whose
 * output is `{"state":STATEW,"loglen":N,"status":S,"ok":B}`. The executed object is host-fed
 * admission followed by the auth-preserving handler-registry fold: every lowered `(NodeAuth, action)`
 * passes the four-leg gate before handler dispatch. Same return contract (full byte length;
 * (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_HANDLER_TURN
size_t dregg_exec_handler_turn_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_handler_turn(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_HANDLER_TURN */

/* dregg_blocklace_finalize_str — the C string bridge over the Lean `String -> String` VERIFIED
 * FINALITY GATE export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_blocklace_finalize`, whose input wire is `"w=<W>;P=<participants>;B=<blocks>"` and whose
 * output is `"F=<creator>:<seq>,..."` (the verified finalized order) or `"ERR"` (fail-closed on a
 * malformed wire). Same return contract (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_FINALIZE_GATE
size_t dregg_blocklace_finalize_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_blocklace_finalize(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_tau_order_str — the C string bridge over the Lean `String -> String` RAW TOTAL-ORDER export.
 * Identical marshalling discipline as the bridges above; it drives `dregg_tau_order`, whose input
 * wire is the SAME `"w=<W>;P=<participants>;B=<blocks>"` the finality gate consumes and whose output
 * is `"T=<id>,<id>,..."` (the verified `BlocklaceFinality.tauOrder` total order as the ordered BlockId
 * list) or `"ERR"` (fail-closed on a malformed wire). `tau_order_export_eq` proves the output is the
 * encoding of `tauOrder` order-faithfully. Same return contract (full byte length; (size_t)-1 only on
 * an unusable buffer). Co-located in the FinalityGate module ⇒ gated on the same DREGG_FINALIZE_GATE. */
size_t dregg_tau_order_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_tau_order(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_finalization_quorum_str — the C string bridge over the Lean `String -> String` VERIFIED
 * finalization-vote QUORUM decision. Identical marshalling discipline as the bridges above; it drives
 * `dregg_finalization_quorum`, whose input wire is `"n=<committee-size>;V=<signer:root,...>"` (the
 * collector's deduped tally) and whose output is `"R=<root>"` (the consensus-attested root),
 * `"NONE"` (no root reached quorum), or `"ERR"` (fail-closed on a malformed wire).
 * `quorum_gate_finalizes_iff_verified` proves the decision IS `FinalizationQuorum.quorumRoot`. Same
 * return contract (full byte length; (size_t)-1 only on an unusable buffer). Co-located in the
 * FinalityGate module ⇒ gated on the same DREGG_FINALIZE_GATE. */
size_t dregg_finalization_quorum_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_finalization_quorum(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_FINALIZE_GATE */

/* dregg_strand_admit_str — the C string bridge over the Lean `String -> String` VERIFIED
 * STRAND-ADMISSION GATE export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_strand_admit`, whose input wire is
 * `"N=<vouch-threshold>;m=<min-bond>;S=<seeds>;V=<vouches>;Bo=<bonds>;q=<strand>"` and whose output
 * is `"1"` (admitted) / `"0"` (not admitted) / `"ERR"` (fail-closed on a malformed wire). Same return
 * contract (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_STRAND_ADMIT
size_t dregg_strand_admit_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_strand_admit(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_STRAND_ADMIT */

/* dregg_round_advance_str — the C string bridge over the Lean `String -> String` VERIFIED ES
 * ROUND-ADVANCE GATE export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_round_advance`, whose input wire is
 * `"r=<round>;t=<0|1>;w=<W>;P=<participants>;B=<blocks>"` and whose output is `"1"` (advance) /
 * `"0"` (hold) / `"ERR"` (fail-closed on a malformed wire - the node HOLDS). Same return contract
 * (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_ROUND_ADVANCE
size_t dregg_round_advance_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_round_advance(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_ROUND_ADVANCE */

/* dregg_ack_admit_str — the C string bridge over the Lean `String -> String` VERIFIED
 * ACKNOWLEDGE-BEFORE-ADMIT GATE export. Identical marshalling discipline as the bridges above;
 * it drives `dregg_ack_admit`, whose input wire is
 * `"h=<head>;D=<blocks>;w=<W>;P=<participants>;B=<blocks>"` and whose output is `"1:<ids>"`
 * (admit the batch, insertion order) / `"0"` (hold) / `"ERR"` (fail-closed on a malformed wire
 * - the node HOLDS). Same return contract (full byte length; (size_t)-1 only on an unusable
 * buffer). */
#ifdef DREGG_ACK_ADMIT
size_t dregg_ack_admit_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_ack_admit(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_ACK_ADMIT */

/* dregg_decide_refines_str — the C string bridge over the Lean `String -> String` VERIFIED
 * FLOW-REFINEMENT DECISION GATE export. Identical marshalling discipline as the bridges above; it
 * drives `dregg_decide_refines`, whose input wire is `"A=<preorder-tokens>;B=<preorder-tokens>"` (a
 * pair of σ-free `Proc`s) and whose output is `"1"` (A ≤ᶠ B) / `"0"` (A ⋠ B) / `"ERR"` (fail-closed on
 * a malformed wire). Same return contract (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_DECIDE_REFINES
size_t dregg_decide_refines_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_decide_refines(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_DECIDE_REFINES */

/* dregg_captp_validate_handoff_str / dregg_captp_process_drop_str / dregg_captp_pipeline_resolve_str
 * / dregg_coord_2pc_decide_str / dregg_coord_causal_order_str / dregg_coord_shared_budget_str — the
 * six C string bridges over the VERIFIED CapTP+coord decision exports. Identical marshalling
 * discipline as the bridges above; each drives its `dregg_captp_*` / `dregg_coord_*` Lean export over
 * the compact wire grammar documented in `Dregg2.Exec.DistributedExports`. Same return contract (full
 * byte length; (size_t)-1 only on an unusable buffer). Gated on DREGG_DISTRIBUTED_EXPORTS. */
#ifdef DREGG_DISTRIBUTED_EXPORTS
size_t dregg_captp_validate_handoff_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_captp_validate_handoff(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_captp_process_drop_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_captp_process_drop(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_captp_pipeline_resolve_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_captp_pipeline_resolve(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_coord_2pc_decide_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_coord_2pc_decide(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_coord_causal_order_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_coord_causal_order(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_coord_shared_budget_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_coord_shared_budget(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_DISTRIBUTED_EXPORTS */
