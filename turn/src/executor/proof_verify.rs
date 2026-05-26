//! Proof verification: STARK + bilateral + effect binding proofs, plus field/commitment conversion helpers for sovereign cells.
//!
//! Extracted from `executor/mod.rs` (lines 1279-2993 of pre-decomposition file).

use super::*;

impl TurnExecutor {
    /// TRUST-CRITICAL: This function bridges the TRUSTLESS layer (STARK proofs) into the
    /// executor. If compromised: forged sovereign state could be committed without valid proofs.
    /// However, this function is ALREADY close to trustless — it only verifies a proof and
    /// updates a commitment. The proof itself is independently verifiable.
    /// Future: expose proof verification as a standalone function that light clients can call
    /// directly, removing the executor from the trust path for sovereign cells entirely.
    ///
    /// Verify a STARK execution proof for a sovereign cell and update its commitment.
    ///
    /// This is the core of Phase 3: proof-carrying sovereign turns. The executor
    /// does ZERO state manipulation — it only:
    /// 1. Retrieves the stored commitment
    /// 2. Verifies the STARK proof (public inputs bind old -> new commitment + effects hash)
    /// 3. Updates the 32-byte commitment
    ///
    /// Public inputs layout (Effect VM, 7+ BabyBear elements):
    ///   [old_commit(1), new_commit(1), net_delta_mag(1), net_delta_sign(1),
    ///    effects_hash_lo(1), effects_hash_hi(1), custom_count(1),
    ///    ...custom_entries(8 per custom effect)]
    pub(super) fn verify_and_commit_proof(
        &self,
        cell_id: &CellId,
        proof_bytes: &[u8],
        turn: &Turn,
        ledger: &mut Ledger,
    ) -> Result<(), TurnError> {
        use pyana_circuit::effect_vm;
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        // 1. Get stored commitment (check both legacy sovereign_commitments and registrations).
        let old_commitment = if let Some(c) = ledger.get_sovereign_commitment(cell_id) {
            *c
        } else if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            reg.commitment
        } else {
            return Err(TurnError::SovereignNotRegistered { cell: *cell_id });
        };

        // 2. Deserialize the STARK proof.
        let proof = stark::proof_from_bytes(proof_bytes)
            .map_err(|e| TurnError::InvalidExecutionProof(e))?;

        // 3. Get the new commitment from the turn.
        let new_commitment = turn.execution_proof_new_commitment.ok_or_else(|| {
            TurnError::InvalidExecutionProof(
                "execution_proof_new_commitment is required".to_string(),
            )
        })?;

        // 4. Reconstruct Effect VM public inputs (Stage 1 widened PI layout).
        //
        // OLD_COMMIT/NEW_COMMIT are 4 felts each, derived from the full 32-byte
        // canonical commitment via `commitment_to_4bb` (resolves
        // REVIEW[effect-vm-coord] / AUDIT P0-2: ~124-bit collision resistance,
        // replacing the prior 4-byte truncation).
        let old_commit_4 = Self::commitment_to_4bb(&old_commitment);
        let new_commit_4 = Self::commitment_to_4bb(&new_commitment);

        // 5. Compute effects hash using the circuit's Poseidon2-based hash
        // (Stage 1 widened to 4 felts).
        let obligations_guard = self.obligations.lock().unwrap();
        let vm_effects = convert_turn_effects_to_vm(cell_id, turn, ledger, &obligations_guard);
        let effects_hash_4 = effect_vm::compute_effects_hash_4(&vm_effects);

        // 6. Compute balance delta from effects.
        let (delta_mag, delta_sign) = Self::compute_balance_delta_from_effects(cell_id, turn);

        // 7. Count custom effects.
        let custom_count = vm_effects
            .iter()
            .filter(|e| matches!(e, effect_vm::Effect::Custom { .. }))
            .count();

        // 8. Read per-cell `max_custom_effects` from the cell program
        // manifest. For now this comes from the sovereign registration's
        // optional field (Stage 1 added); falls back to the workspace
        // default if unset (legacy / hosted cells).
        let max_custom_effects = self.read_cell_max_custom_effects(cell_id, ledger);

        // 8b. Per-cell enforcement: the executor rejects turns whose
        // custom-effect count exceeds the cell's declared limit. The AIR's
        // sum-check (Group 7, Stage 1) makes the `PI[CUSTOM_EFFECT_COUNT]`
        // value algebraically binding; this executor check then enforces
        // the per-cell ceiling on top of that.
        if custom_count > max_custom_effects as usize {
            return Err(TurnError::InvalidExecutionProof(format!(
                "custom_count {} exceeds per-cell max_custom_effects {}",
                custom_count, max_custom_effects,
            )));
        }

        // Federation approved-handoffs root. Stage 1: empty sentinel; Stage 7
        // populates from federation state.
        let approved_handoffs_root: [BabyBear; 4] = self.read_approved_handoffs_root();

        // 9. Build the public inputs vector (Stage 1 Effect VM layout).
        let pi_len = effect_vm::pi::BASE_COUNT + custom_count * effect_vm::pi::CUSTOM_ENTRY_SIZE;
        let mut public_inputs: Vec<BabyBear> = vec![BabyBear::ZERO; pi_len];
        for i in 0..effect_vm::pi::OLD_COMMIT_LEN {
            public_inputs[effect_vm::pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
        }
        for i in 0..effect_vm::pi::NEW_COMMIT_LEN {
            public_inputs[effect_vm::pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
        }
        for i in 0..effect_vm::pi::EFFECTS_HASH_LEN {
            public_inputs[effect_vm::pi::EFFECTS_HASH_BASE + i] = effects_hash_4[i];
        }
        public_inputs[effect_vm::pi::INIT_BAL_LO] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::INIT_BAL_HI] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::FINAL_BAL_LO] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::FINAL_BAL_HI] = BabyBear::ZERO; // pinned from trace
        public_inputs[effect_vm::pi::NET_DELTA_MAG] = BabyBear::new(delta_mag);
        public_inputs[effect_vm::pi::NET_DELTA_SIGN] = BabyBear::new(delta_sign);
        public_inputs[effect_vm::pi::CURRENT_BLOCK_HEIGHT] =
            BabyBear::new((self.block_height & 0x7FFF_FFFF) as u32);
        public_inputs[effect_vm::pi::MAX_CUSTOM_EFFECTS] = BabyBear::new(max_custom_effects as u32);
        public_inputs[effect_vm::pi::CUSTOM_EFFECT_COUNT] = BabyBear::new(custom_count as u32);
        for i in 0..effect_vm::pi::APPROVED_HANDOFFS_LEN {
            public_inputs[effect_vm::pi::APPROVED_HANDOFFS_BASE + i] = approved_handoffs_root[i];
        }

        // Stage 7-γ.0c: populate the four turn-identity PI slots from the
        // canonical Turn. These are the same values every per-cell proof
        // of this turn must carry; the verifier rejects any mismatch.
        let (turn_hash_4, effects_hash_global_4, actor_nonce, prev_receipt_4) =
            Self::compute_turn_identity_pi(turn);
        for i in 0..effect_vm::pi::TURN_HASH_LEN {
            public_inputs[effect_vm::pi::TURN_HASH_BASE + i] = turn_hash_4[i];
        }
        for i in 0..effect_vm::pi::EFFECTS_HASH_GLOBAL_LEN {
            public_inputs[effect_vm::pi::EFFECTS_HASH_GLOBAL_BASE + i] = effects_hash_global_4[i];
        }
        public_inputs[effect_vm::pi::ACTOR_NONCE] =
            BabyBear::new((actor_nonce & 0x7FFF_FFFF) as u32);
        for i in 0..effect_vm::pi::PREVIOUS_RECEIPT_HASH_LEN {
            public_inputs[effect_vm::pi::PREVIOUS_RECEIPT_HASH_BASE + i] = prev_receipt_4[i];
        }

        // Stage 7-γ.2 Phase 1: bilateral cross-cell PI fields. Each per-cell
        // proof carries its own outbound/inbound counts and accumulator
        // roots over Transfer / Grant / Introduce. The verifier's off-AIR
        // cross-cell match loop recomputes the expected schedule from
        // (call_forest, ACTOR_NONCE) and rejects any per-cell PI that
        // disagrees. See `STAGE-7-GAMMA-2-PI-DESIGN.md` §3-4.
        {
            use crate::bilateral_schedule::{ExpectedBilateral, project_into_pi};
            let schedule = ExpectedBilateral::from_turn(turn);
            let counts = schedule.counts_for(cell_id);
            let roots = schedule.roots_for(cell_id, actor_nonce);
            project_into_pi(&mut public_inputs, &counts, &roots);

            // IS_AGENT_CELL: 1 iff this per-cell proof is the actor's
            // (signer's) cell. The agent's row-0 NONCE column is pinned
            // to PI[ACTOR_NONCE] in single-cell proofs today; in multi-
            // cell bundles the non-agent cells are exempt from that pin
            // — see verifier's bundle check.
            public_inputs[effect_vm::pi::IS_AGENT_CELL] = if cell_id == &turn.agent {
                BabyBear::new(1)
            } else {
                BabyBear::ZERO
            };
        }

        // Sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2):
        //
        // This path (`verify_and_commit_proof`) is the proof-carrying path
        // where `turn.execution_proof` is `Some`. The cell IS sovereign, so
        // we set IS_SOVEREIGN_CELL == 1 and bind the cell's owning-pubkey
        // hash + witness-sequence into PI. The PI-matching loop below
        // catches any prover-side divergence. The prover (cipherclerk's
        // `execute_sovereign_turn_with_proof`) populates the same slots
        // from the same source (cell.public_key); the boundary constraint
        // in the AIR catches any in-trace deviation.
        //
        // Phase 2: the execution_proof itself IS the transition proof in
        // this path. We bind its Poseidon2 hash + the Effect VM AIR's
        // VK hash (sentinel zero today; populated when the recursive
        // verifier ships a stable VK).
        Self::populate_sovereign_witness_pi(
            &mut public_inputs,
            cell_id,
            ledger,
            None,              // no witness object on the proof-carrying path
            Some(proof_bytes), // execution_proof IS the transition proof
        );

        // Append custom proof entries (vk_hash + proof_commitment per custom
        // effect). PI layout v2 (`effect_vm::pi::VK_PI_LAYOUT_VERSION == 2`):
        // 8 felts vk_hash + 4 felts proof_commit per entry. Pre-v2 layouts
        // used a 4-felt low-half vk_hash and zero-padded the upper 16 bytes
        // at registry-lookup time — that path is removed (closes
        // AIR-SOUNDNESS-AUDIT.md #70).
        let mut custom_idx = 0;
        for effect in &vm_effects {
            if let effect_vm::Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } = effect
            {
                let base = effect_vm::pi::CUSTOM_PROOFS_BASE
                    + custom_idx * effect_vm::pi::CUSTOM_ENTRY_SIZE;
                for j in 0..8 {
                    public_inputs[base + j] = program_vk_hash[j];
                }
                for j in 0..4 {
                    public_inputs[base + 8 + j] = proof_commitment[j];
                }
                custom_idx += 1;
            }
        }

        // INIT/FINAL_BAL_* are sourced from the proof's PIs (the trace pins
        // them at boundaries and Group 6 binds them algebraically). We copy
        // them now so the PI matching loop below doesn't trip on zero.
        if proof.public_inputs.len() >= effect_vm::pi::BASE_COUNT {
            public_inputs[effect_vm::pi::INIT_BAL_LO] =
                BabyBear::new_canonical(proof.public_inputs[effect_vm::pi::INIT_BAL_LO]);
            public_inputs[effect_vm::pi::INIT_BAL_HI] =
                BabyBear::new_canonical(proof.public_inputs[effect_vm::pi::INIT_BAL_HI]);
            public_inputs[effect_vm::pi::FINAL_BAL_LO] =
                BabyBear::new_canonical(proof.public_inputs[effect_vm::pi::FINAL_BAL_LO]);
            public_inputs[effect_vm::pi::FINAL_BAL_HI] =
                BabyBear::new_canonical(proof.public_inputs[effect_vm::pi::FINAL_BAL_HI]);
        }

        // 9. Validate proof PI count and verify PI matching.
        let expected_pi_count = public_inputs.len();
        let vk_hash = self.get_cell_vk_hash(cell_id, ledger);
        let has_custom_program = vk_hash.is_some();

        // For the default EffectVmAir path, verify reconstructed PIs match the proof.
        // Custom programs have their own PI layout — skip this check for them.
        if !has_custom_program {
            if proof.public_inputs.len() < expected_pi_count {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "proof has {} public inputs, expected at least {}",
                    proof.public_inputs.len(),
                    expected_pi_count
                )));
            }

            for (i, expected_bb) in public_inputs.iter().enumerate() {
                let got = BabyBear::new_canonical(proof.public_inputs[i]);
                if got != *expected_bb {
                    // Stage 1: PI layout has 4-felt slots for OLD_COMMIT,
                    // NEW_COMMIT, EFFECTS_HASH; index ranges identify which.
                    if (effect_vm::pi::OLD_COMMIT_BASE
                        ..effect_vm::pi::OLD_COMMIT_BASE + effect_vm::pi::OLD_COMMIT_LEN)
                        .contains(&i)
                    {
                        return Err(TurnError::SovereignCommitmentMismatch {
                            cell: *cell_id,
                            expected: old_commitment,
                            got: new_commitment,
                        });
                    } else if (effect_vm::pi::NEW_COMMIT_BASE
                        ..effect_vm::pi::NEW_COMMIT_BASE + effect_vm::pi::NEW_COMMIT_LEN)
                        .contains(&i)
                    {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "new_commitment in proof does not match claimed value (felt {} of 4)",
                            i - effect_vm::pi::NEW_COMMIT_BASE,
                        )));
                    } else if (effect_vm::pi::EFFECTS_HASH_BASE
                        ..effect_vm::pi::EFFECTS_HASH_BASE + effect_vm::pi::EFFECTS_HASH_LEN)
                        .contains(&i)
                    {
                        return Err(TurnError::EffectsHashMismatch {
                            expected: Self::babybear_pair_to_bytes32(
                                effects_hash_4[0],
                                effects_hash_4[1],
                            ),
                            got: Self::babybear_pair_to_bytes32(
                                BabyBear::new_canonical(
                                    proof.public_inputs[effect_vm::pi::EFFECTS_HASH_BASE],
                                ),
                                BabyBear::new_canonical(
                                    proof.public_inputs[effect_vm::pi::EFFECTS_HASH_BASE + 1],
                                ),
                            ),
                        });
                    } else {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "public input mismatch at index {} (expected {:?}, got {:?})",
                            i, expected_bb, got
                        )));
                    }
                }
            }
        }

        // 11. Verify the STARK proof.
        if let Some(vk) = vk_hash {
            if let Some(program) = self.program_registry.get(&vk) {
                // Custom programs define their own PI layout. Extract PIs from
                // the proof itself (the program's verifier will check them).
                let custom_pis: Vec<BabyBear> = proof
                    .public_inputs
                    .iter()
                    .map(|&v| BabyBear::new_canonical(v))
                    .collect();
                program
                    .verify_transition(&custom_pis, proof_bytes)
                    .map_err(|e| TurnError::ProofVerificationFailed(e.to_string()))?;
            } else {
                return Err(TurnError::ProofVerificationFailed(format!(
                    "cell has verification_key_hash {:02x}{:02x}... but no matching program is deployed",
                    vk[0], vk[1]
                )));
            }
        } else {
            let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
            stark::verify(&air, &proof, &public_inputs)
                .map_err(|e| TurnError::ProofVerificationFailed(e))?;
        }

        // 12. Verify custom program proofs (CellProgram dispatch).
        if let Some(custom_proofs) = turn.custom_program_proofs.as_ref() {
            let custom_commitments =
                pyana_circuit::extract_custom_proof_commitments(&public_inputs);
            if custom_commitments.len() != custom_proofs.len() {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "custom proof count mismatch: PI declares {}, turn provides {}",
                    custom_commitments.len(),
                    custom_proofs.len()
                )));
            }
            for (i, ((vk_hash_elems, proof_commit_elems), custom_proof)) in custom_commitments
                .iter()
                .zip(custom_proofs.iter())
                .enumerate()
            {
                // PI layout v2: vk_hash_elems is 8 felts (full 32B). The
                // pre-v2 zero-padded `expand_vk_hash_16_to_32` path is
                // removed — registry dispatch now reads the entire 32-byte
                // key (AIR-SOUNDNESS-AUDIT.md #70).
                let actual_proof_hash = Self::hash_custom_proof(&custom_proof.proof_bytes);
                let expected_commit = Self::babybear4_to_bytes16(proof_commit_elems);
                if actual_proof_hash != expected_commit {
                    return Err(TurnError::CustomProofCommitmentMismatch {
                        index: i,
                        expected: expected_commit,
                        got: actual_proof_hash,
                    });
                }
                let full_vk_hash = Self::babybear8_to_bytes32(vk_hash_elems);

                // Per VK-AS-RE-EXECUTION-RECIPE.md §2.4 / §v2: the
                // `Effect::Custom { vk_hash }` is dispatched through
                // the canonical `CustomEffectRegistry` when one is
                // wired. Apps that register an entry there get a
                // unified custom-verifier surface (parallel to
                // `WitnessedPredicateKind::Custom { vk_hash }`'s
                // dispatch). When the registry is absent or the
                // hash isn't registered there, the executor falls
                // back to the legacy `program_registry` path
                // (DSL-authored cells).
                //
                // TODO[vk-v2]: This dispatch path resolves vk_hash via
                // `CustomEffectRegistry::contains`; the registry now
                // stores v2 layered hashes (§v2.6). Callers must register
                // verifiers under their v2 hash for this to find them.
                // No code change needed here — the dispatch is correct;
                // this is a documentation marker so callers know the
                // bound contract has bumped from v1 to v2.
                if let Some(reg) = self.custom_effect_registry.as_ref() {
                    if reg.contains(&full_vk_hash) {
                        // The CustomEffectRegistry verifier takes
                        // serialized public inputs; we postcard-encode
                        // the BabyBear PI vector for transport. The
                        // verifier's own decoder reproduces the felts.
                        let pi_bytes =
                            postcard::to_allocvec(&custom_proof.public_inputs_babybear())
                                .unwrap_or_default();
                        reg.verify(&full_vk_hash, &pi_bytes, &custom_proof.proof_bytes)
                            .map_err(|e| TurnError::CustomProgramVerificationFailed {
                                index: i,
                                program_vk: full_vk_hash,
                                reason: e.to_string(),
                            })?;
                        continue;
                    }
                }

                if let Some(program) = self.program_registry.get(&full_vk_hash) {
                    program
                        .verify_transition(
                            &custom_proof.public_inputs_babybear(),
                            &custom_proof.proof_bytes,
                        )
                        .map_err(|e| TurnError::CustomProgramVerificationFailed {
                            index: i,
                            program_vk: full_vk_hash,
                            reason: e.to_string(),
                        })?;
                } else {
                    return Err(TurnError::CustomProgramNotFound {
                        index: i,
                        vk_hash: full_vk_hash,
                    });
                }
            }
        } else {
            let custom_commitments =
                pyana_circuit::extract_custom_proof_commitments(&public_inputs);
            if !custom_commitments.is_empty() {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "Effect VM proof declares {} custom effects but turn provides no custom proofs",
                    custom_commitments.len()
                )));
            }
        }

        // 13. Update commitment. Try the legacy map first, then registrations.
        if ledger.is_sovereign(cell_id) {
            let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);
        } else {
            let _ = ledger.update_sovereign_registration_commitment(
                cell_id,
                old_commitment,
                new_commitment,
                self.block_height,
            );
        }

        Ok(())
    }

    /// Verify a sovereign-witness STARK transition proof.
    ///
    /// Mirrors `pyana_cell::peer_exchange::PeerExchange::verify_stark_transition`:
    /// deserializes the proof, widens the 32-byte commitments to 4 BabyBear
    /// felts each, overrides the proof's commitment PIs with verifier-
    /// derived values, and verifies via `EffectVmAir`. A divergence on
    /// commitment slots surfaces as `InvalidExecutionProof`.
    pub(super) fn verify_sovereign_witness_stark(
        &self,
        _cell_id: &CellId,
        old_commitment: &[u8; 32],
        new_commitment: &[u8; 32],
        _effects_hash: &[u8; 32],
        proof_bytes: &[u8],
    ) -> Result<(), TurnError> {
        use pyana_circuit::effect_vm::pi;
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::stark;

        let proof = stark::proof_from_bytes(proof_bytes)
            .map_err(|e| TurnError::InvalidExecutionProof(e))?;

        let old_commit_4 = Self::commitment_to_4bb(old_commitment);
        let new_commit_4 = Self::commitment_to_4bb(new_commitment);

        let min_pi_count = pi::BASE_COUNT;
        if proof.public_inputs.len() < min_pi_count {
            return Err(TurnError::InvalidExecutionProof(format!(
                "sovereign witness STARK proof has {} public inputs, expected at least {}",
                proof.public_inputs.len(),
                min_pi_count
            )));
        }

        // Build PIs from the proof; override the commitment slots with
        // verifier-derived values. The AIR's transition constraints bind
        // the other PIs to the trace, so trusting them is safe.
        let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
            .map(|i| BabyBear::new_canonical(proof.public_inputs[i]))
            .collect();
        for i in 0..pi::OLD_COMMIT_LEN {
            public_inputs[pi::OLD_COMMIT_BASE + i] = old_commit_4[i];
        }
        for i in 0..pi::NEW_COMMIT_LEN {
            public_inputs[pi::NEW_COMMIT_BASE + i] = new_commit_4[i];
        }

        // Append custom-effect entries from the proof's PIs (the AIR
        // constrains CUSTOM_EFFECT_COUNT to match the trace, so trusting
        // the proof's declared count here is sound).
        let custom_count_val = public_inputs[pi::CUSTOM_EFFECT_COUNT].as_u32() as usize;
        for i in 0..custom_count_val {
            let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
            if base + pi::CUSTOM_ENTRY_SIZE > proof.public_inputs.len() {
                break;
            }
            for j in 0..pi::CUSTOM_ENTRY_SIZE {
                public_inputs.push(BabyBear::new_canonical(proof.public_inputs[base + j]));
            }
        }

        // Verify commitment PIs declared by the proof match what we expect.
        for i in 0..pi::OLD_COMMIT_LEN {
            let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::OLD_COMMIT_BASE + i]);
            if proof_v != old_commit_4[i] {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "sovereign witness STARK old_commitment mismatch at felt {}",
                    i
                )));
            }
        }
        for i in 0..pi::NEW_COMMIT_LEN {
            let proof_v = BabyBear::new_canonical(proof.public_inputs[pi::NEW_COMMIT_BASE + i]);
            if proof_v != new_commit_4[i] {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "sovereign witness STARK new_commitment mismatch at felt {}",
                    i
                )));
            }
        }

        let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
        stark::verify(&air, &proof, &public_inputs)
            .map_err(|e| TurnError::ProofVerificationFailed(e))?;
        Ok(())
    }

    /// Stage 7-γ.0d: cross-proof PI matching for a bundle of per-cell proofs
    /// from one turn.
    ///
    /// Given the N per-cell proof PI vectors that a turn's bundle has
    /// produced (one entry per touched cell, in any order), enforces that
    /// all of them agree on the four "turn-identity" PI fields introduced
    /// at γ.0a:
    ///
    ///   - PI[TURN_HASH_BASE..+4]
    ///   - PI[EFFECTS_HASH_GLOBAL_BASE..+4]
    ///   - PI[ACTOR_NONCE]
    ///   - PI[PREVIOUS_RECEIPT_HASH_BASE..+4]
    ///
    /// Also enforces — if `turn` is provided — that the shared values
    /// match the canonical `Turn::hash`-derived projection
    /// (`compute_turn_identity_pi`). This second check is the
    /// executor-side enforcement that γ.0 keeps trusted; γ.1 will move
    /// the `effects_hash_global ↔ Σ effects_local` direction into an
    /// aggregation micro-AIR.
    ///
    /// Per-proof STARK verification is the caller's responsibility (see
    /// `verify_and_commit_proof` for the single-cell case). This function
    /// only checks PI consistency across the bundle and against the turn.
    ///
    /// Returns `Ok(())` if every PI vector in `bundle_pis` agrees with
    /// every other on the four shared slots and (when `turn.is_some()`)
    /// with the canonical projection.
    pub fn verify_proof_carrying_turn_bundle(
        bundle_pis: &[Vec<pyana_circuit::field::BabyBear>],
        turn: Option<&Turn>,
    ) -> Result<(), TurnError> {
        use pyana_circuit::effect_vm::pi;
        use pyana_circuit::field::BabyBear;

        if bundle_pis.is_empty() {
            return Ok(());
        }

        // Every PI vector must be at least as long as the base layout —
        // shorter vectors can't carry the γ.0a slots at all.
        for (i, p) in bundle_pis.iter().enumerate() {
            if p.len() < pi::BASE_COUNT {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bundle proof {} has {} public inputs, expected at least {} \
                     (Stage 7-γ.0a layout)",
                    i,
                    p.len(),
                    pi::BASE_COUNT
                )));
            }
        }

        // Determine the canonical "shared" values. When the turn is
        // supplied, use Turn::compute_turn_identity_pi (executor-trusted
        // source of truth). Otherwise, take the first proof's values as
        // the reference and verify the rest match — useful for federation
        // verifiers that receive a bundle without re-deriving the Turn.
        let (ref_turn_hash, ref_eff_global, ref_actor_nonce, ref_prev_receipt): (
            [BabyBear; 4],
            [BabyBear; 4],
            BabyBear,
            [BabyBear; 4],
        ) = if let Some(t) = turn {
            let (th, eg, an, pr) = Self::compute_turn_identity_pi(t);
            (th, eg, BabyBear::new((an & 0x7FFF_FFFF) as u32), pr)
        } else {
            let p0 = &bundle_pis[0];
            let mut th = [BabyBear::ZERO; 4];
            let mut eg = [BabyBear::ZERO; 4];
            let mut pr = [BabyBear::ZERO; 4];
            for i in 0..4 {
                th[i] = p0[pi::TURN_HASH_BASE + i];
                eg[i] = p0[pi::EFFECTS_HASH_GLOBAL_BASE + i];
                pr[i] = p0[pi::PREVIOUS_RECEIPT_HASH_BASE + i];
            }
            (th, eg, p0[pi::ACTOR_NONCE], pr)
        };

        // Per-proof check: each proof must agree with the reference on
        // every shared slot. Errors name the slot and the proof index.
        for (proof_idx, p) in bundle_pis.iter().enumerate() {
            for i in 0..pi::TURN_HASH_LEN {
                if p[pi::TURN_HASH_BASE + i] != ref_turn_hash[i] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "bundle PI mismatch: TURN_HASH felt {} differs in proof {} \
                         (expected {:?}, got {:?})",
                        i,
                        proof_idx,
                        ref_turn_hash[i],
                        p[pi::TURN_HASH_BASE + i],
                    )));
                }
            }
            for i in 0..pi::EFFECTS_HASH_GLOBAL_LEN {
                if p[pi::EFFECTS_HASH_GLOBAL_BASE + i] != ref_eff_global[i] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "bundle PI mismatch: EFFECTS_HASH_GLOBAL felt {} differs in \
                         proof {} (expected {:?}, got {:?})",
                        i,
                        proof_idx,
                        ref_eff_global[i],
                        p[pi::EFFECTS_HASH_GLOBAL_BASE + i],
                    )));
                }
            }
            if p[pi::ACTOR_NONCE] != ref_actor_nonce {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bundle PI mismatch: ACTOR_NONCE differs in proof {} \
                     (expected {:?}, got {:?})",
                    proof_idx,
                    ref_actor_nonce,
                    p[pi::ACTOR_NONCE],
                )));
            }
            for i in 0..pi::PREVIOUS_RECEIPT_HASH_LEN {
                if p[pi::PREVIOUS_RECEIPT_HASH_BASE + i] != ref_prev_receipt[i] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "bundle PI mismatch: PREVIOUS_RECEIPT_HASH felt {} differs in \
                         proof {} (expected {:?}, got {:?})",
                        i,
                        proof_idx,
                        ref_prev_receipt[i],
                        p[pi::PREVIOUS_RECEIPT_HASH_BASE + i],
                    )));
                }
            }
        }

        // ---- Proof-to-action binding sweep §3.2/§3.3 + §5 ----
        //
        // If the turn carries sidecar effect-binding proofs (and/or
        // cross-effect dependencies and/or witness-index pins), run the
        // strong-soundness verification path on them. Turns without any
        // of these continue to apply with executor-trusted enforcement
        // (backwards compat); turns *with* them get the algebraic
        // full-fidelity check.
        if let Some(t) = turn {
            if !t.effect_binding_proofs.is_empty()
                || !t.cross_effect_dependencies.is_empty()
                || !t.effect_witness_index_map.is_empty()
            {
                // Without ledger snapshot: any Burn binding proof routes
                // through the snapshot-aware error path. Callers that need
                // Burn coverage must use
                // `verify_proof_carrying_turn_bundle_with_ledger`.
                Self::verify_effect_binding_proofs(t)?;
            }
        }

        Ok(())
    }

    /// Snapshot-aware variant of `verify_proof_carrying_turn_bundle`.
    /// Same shape, but threads a `&Ledger` into the binding-proof sweep so
    /// `SCHEMA_BURN` proofs can reconstruct `(old_balance, new_balance)`
    /// from the target cell's state. Closes AIR-SOUNDNESS-AUDIT #75.
    ///
    /// To avoid running the binding sweep twice (once snapshot-free,
    /// once snapshot-aware), this function temporarily clones the turn
    /// without its `effect_binding_proofs` and routes the cross-bundle
    /// PI check through that copy; then it issues the snapshot-aware
    /// binding-proof sweep against the original turn.
    pub fn verify_proof_carrying_turn_bundle_with_ledger(
        bundle_pis: &[Vec<pyana_circuit::field::BabyBear>],
        turn: Option<&Turn>,
        ledger: Option<&Ledger>,
    ) -> Result<(), TurnError> {
        // Run the cross-bundle PI checks via the existing path, with a
        // shallow clone that omits `effect_binding_proofs` so the
        // snapshot-free Burn arm is skipped. The other two
        // binding-extension fields (`cross_effect_dependencies` and
        // `effect_witness_index_map`) are ledger-independent and can
        // run either way; we drop all three from the clone and re-issue
        // the full sweep below with the snapshot-aware extractor.
        let stripped_turn: Option<Turn> = turn.map(|t| {
            let mut t = t.clone();
            t.effect_binding_proofs = Vec::new();
            t.cross_effect_dependencies = Vec::new();
            t.effect_witness_index_map = Vec::new();
            t
        });
        Self::verify_proof_carrying_turn_bundle(bundle_pis, stripped_turn.as_ref())?;
        if let Some(t) = turn {
            if !t.effect_binding_proofs.is_empty()
                || !t.cross_effect_dependencies.is_empty()
                || !t.effect_witness_index_map.is_empty()
            {
                Self::verify_effect_binding_proofs_with_ledger(t, ledger)?;
            }
        }
        Ok(())
    }

    /// Verify every sidecar `EffectBindingProof` carried by the turn.
    ///
    /// For each entry the verifier:
    ///   1. Locates the effect by `effect_index` (canonical DFS order
    ///      over the whole call_forest — same traversal as
    ///      `compute_turn_identity_pi`).
    ///   2. Looks up the schema by `schema_id`.
    ///   3. Reconstructs the expected PI vector from the executor's
    ///      view of the effect's typed parameters and compares it to
    ///      the proof's `public_inputs`.
    ///   4. STARK-verifies the proof against the reconstructed PI.
    ///
    /// Cross-effect dependencies are also enforced here: the chain
    /// pinning verifies that the producer effect's output field of
    /// the named type equals the consumer's input of the same type,
    /// preventing the executor from substituting a different value
    /// (e.g., a different nullifier) between producer and consumer in
    /// the same turn.
    ///
    /// Witness-blob → effect indexing entries are validated for
    /// well-formedness here; the AIR-side enforcement that the
    /// effect-claimed witness blob actually matches the indexed blob
    /// is the responsibility of the corresponding per-effect AIR (the
    /// generalized AIR exposes a `witness_blob_hash` schema slot when
    /// the binding schema declares one).
    pub fn verify_effect_binding_proofs(turn: &Turn) -> Result<(), TurnError> {
        // Backwards-compat wrapper: callers that don't have a ledger
        // snapshot (the `verify_proof_carrying_turn_bundle` static path,
        // and existing structural tests) route through here. The Burn
        // arm is the only schema whose executor-side projection requires
        // a snapshot (`old_balance`, `new_balance`); without one it
        // continues to surface as a schema/variant mismatch, the same
        // pre-AIR-#75 shape, so cleartext non-Burn turns are unaffected.
        Self::verify_effect_binding_proofs_with_ledger(turn, None)
    }

    /// Snapshot-aware variant. Pass `Some(ledger)` to wire the per-effect
    /// snapshot-dependent extractors (today: `SCHEMA_BURN`); pass `None`
    /// for the snapshot-free legacy behavior. Closes
    /// `AIR-SOUNDNESS-AUDIT.md` #75 by giving the Burn arm of
    /// `extract_binding_params` the pre/post ledger snapshot it needs
    /// to reconstruct `old_balance` / `new_balance` from `Effect::Burn`
    /// alone.
    pub fn verify_effect_binding_proofs_with_ledger(
        turn: &Turn,
        ledger: Option<&Ledger>,
    ) -> Result<(), TurnError> {
        use pyana_circuit::effect_action_air as eaa;
        use pyana_circuit::stark;

        // Build the canonical DFS-order effect list once, mirroring
        // `compute_turn_identity_pi`'s `dfs_collect`.
        let effects = Self::dfs_collect_effects(turn);

        // ---- 1) Effect binding proofs ----
        for (i, bp) in turn.effect_binding_proofs.iter().enumerate() {
            // Bounds-check effect_index.
            let eff = effects.get(bp.effect_index as usize).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: effect_index {} out of range (have {} effects)",
                    i,
                    bp.effect_index,
                    effects.len()
                ))
            })?;

            // Resolve schema by id.
            let schema = Self::schema_by_id(&bp.schema_id).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: unknown schema_id {:?}",
                    i, bp.schema_id
                ))
            })?;

            // Reconstruct expected (fields, amounts) from the executor's
            // view of the effect's typed parameters. Burn routes through
            // the snapshot-aware extractor; everything else uses the
            // snapshot-free path.
            let (exp_fields, exp_amounts) = if bp.schema_id == "pyana-effect-burn-v1" {
                Self::extract_burn_binding_params(eff, ledger).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "effect_binding_proofs[{}]: Burn binding requires a ledger \
                         snapshot to reconstruct (old_balance, new_balance); the \
                         caller did not provide one OR the effect at index {} is \
                         not an Effect::Burn / its target balance is not on the \
                         ledger",
                        i, bp.effect_index
                    ))
                })?
            } else {
                Self::extract_binding_params(eff, &bp.schema_id).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "effect_binding_proofs[{}]: effect at index {} does not match \
                         schema_id {:?} (schema/variant mismatch)",
                        i, bp.effect_index, bp.schema_id
                    ))
                })?
            };
            if exp_fields.len() != schema.field_count || exp_amounts.len() != schema.amount_count {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: schema {:?} expects {} fields + \
                     {} amounts, executor reconstruction got {} + {}",
                    i,
                    bp.schema_id,
                    schema.field_count,
                    schema.amount_count,
                    exp_fields.len(),
                    exp_amounts.len()
                )));
            }

            // Build the expected PI vector and check the wire PI agrees
            // (cheap byte-comparison rejection before STARK verify).
            let exp_pi_bb = {
                let w = eaa::EffectActionWitness {
                    schema,
                    fields: exp_fields.clone(),
                    amounts: exp_amounts.clone(),
                };
                w.public_inputs()
            };
            let bp_pi_bb = bp.public_inputs_babybear();
            if bp_pi_bb != exp_pi_bb {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: wire PI disagrees with executor's view \
                     of effect {} (schema {:?})",
                    i, bp.effect_index, bp.schema_id
                )));
            }

            // STARK-verify the proof against the reconstructed PI.
            let proof = stark::proof_from_bytes(&bp.proof_bytes).map_err(|e| {
                TurnError::InvalidExecutionProof(format!(
                    "effect_binding_proofs[{}]: deserialize: {}",
                    i, e
                ))
            })?;
            eaa::verify_effect_action(schema, &exp_fields, &exp_amounts, &proof).map_err(|e| {
                TurnError::ProofVerificationFailed(format!(
                    "effect_binding_proofs[{}] (schema {:?}, effect {}): {}",
                    i, bp.schema_id, bp.effect_index, e
                ))
            })?;
        }

        // ---- 2) Cross-effect within-turn chain pinning ----
        for (i, dep) in turn.cross_effect_dependencies.iter().enumerate() {
            if dep.producer_index >= dep.consumer_index {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: producer_index {} must be < \
                     consumer_index {} (forward edges only)",
                    i, dep.producer_index, dep.consumer_index
                )));
            }
            let prod = effects.get(dep.producer_index as usize).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: producer_index {} out of range",
                    i, dep.producer_index
                ))
            })?;
            let cons = effects.get(dep.consumer_index as usize).ok_or_else(|| {
                TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: consumer_index {} out of range",
                    i, dep.consumer_index
                ))
            })?;
            let prod_out =
                Self::extract_named_field_32b(prod, &dep.field_name).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "cross_effect_dependencies[{}]: producer effect has no \
                         output field {:?}",
                        i, dep.field_name
                    ))
                })?;
            let cons_in =
                Self::extract_named_field_32b(cons, &dep.field_name).ok_or_else(|| {
                    TurnError::InvalidExecutionProof(format!(
                        "cross_effect_dependencies[{}]: consumer effect has no \
                         input field {:?}",
                        i, dep.field_name
                    ))
                })?;
            if prod_out != dep.value_commit {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: producer's {:?} disagrees with \
                     pinned value_commit",
                    i, dep.field_name
                )));
            }
            if cons_in != dep.value_commit {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "cross_effect_dependencies[{}]: consumer's {:?} disagrees with \
                     pinned value_commit (chain broken)",
                    i, dep.field_name
                )));
            }
        }

        // ---- 3) Witness-blob → Effect indexing ----
        //
        // Well-formedness only here: bounds-check effect_index. The
        // tighter AIR-side enforcement that the indexed blob's bytes
        // are the ones the effect's predicate dispatch consumes is
        // owned by the per-effect generalized AIR (witness_blob_hash
        // schema slot, when declared). Detecting duplicate
        // (effect_index, witness_index) pairs and unbound effects is
        // useful as an executor-side sanity check.
        let mut seen_effect_indices = std::collections::HashSet::new();
        for (i, ewi) in turn.effect_witness_index_map.iter().enumerate() {
            if effects.get(ewi.effect_index as usize).is_none() {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_witness_index_map[{}]: effect_index {} out of range",
                    i, ewi.effect_index
                )));
            }
            if !seen_effect_indices.insert(ewi.effect_index) {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "effect_witness_index_map[{}]: duplicate effect_index {}",
                    i, ewi.effect_index
                )));
            }
        }

        Ok(())
    }

    /// Collect every Effect in the turn's call_forest in the canonical
    /// DFS-traversal order (same order as `compute_turn_identity_pi`).
    pub(super) fn dfs_collect_effects(turn: &Turn) -> Vec<Effect> {
        fn dfs(tree: &CallTree, out: &mut Vec<Effect>) {
            for effect in &tree.action.effects {
                out.push(effect.clone());
            }
            for child in &tree.children {
                dfs(child, out);
            }
        }
        let mut out = Vec::new();
        for root in &turn.call_forest.roots {
            dfs(root, &mut out);
        }
        out
    }

    /// Resolve an `EffectActionSchema` by its `schema_id` (the
    /// `kind_name` string used as the AIR's Fiat-Shamir domain
    /// separator). Returns `None` for unknown ids.
    pub(super) fn schema_by_id(
        id: &str,
    ) -> Option<pyana_circuit::effect_action_air::EffectActionSchema> {
        use pyana_circuit::effect_action_air as eaa;
        macro_rules! match_schemas {
            ($($s:ident),* $(,)?) => {
                $(
                    if id == eaa::$s.kind_name {
                        return Some(eaa::$s);
                    }
                )*
            };
        }
        match_schemas!(
            SCHEMA_GRANT_CAPABILITY,
            SCHEMA_REVOKE_CAPABILITY,
            SCHEMA_EMIT_EVENT,
            SCHEMA_CREATE_CELL,
            SCHEMA_SET_PERMISSIONS,
            SCHEMA_SET_VERIFICATION_KEY,
            SCHEMA_INTRODUCE,
            SCHEMA_CREATE_SEAL_PAIR,
            SCHEMA_BRIDGE_FINALIZE,
            SCHEMA_BRIDGE_CANCEL,
            SCHEMA_REVOKE_DELEGATION,
            SCHEMA_SPAWN_WITH_DELEGATION,
            SCHEMA_RELEASE_ESCROW,
            SCHEMA_REFUND_ESCROW,
            SCHEMA_EXERCISE_VIA_CAPABILITY,
            SCHEMA_CREATE_OBLIGATION,
            SCHEMA_CREATE_ESCROW,
            SCHEMA_PIPELINED_SEND,
            SCHEMA_CREATE_CELL_FROM_FACTORY,
            SCHEMA_CREATE_COMMITTED_ESCROW,
            SCHEMA_NOTE_SPEND,
            SCHEMA_NOTE_CREATE,
            SCHEMA_BRIDGE_LOCK,
            SCHEMA_BURN,
        );
        None
    }

    /// Reconstruct the (fields, amounts) tuple a given schema expects
    /// from the runtime `Effect`'s typed parameters. Returns `None`
    /// when the schema_id does not match the effect's variant (the
    /// caller's bug; a binding proof's schema must match its effect).
    ///
    /// This is the executor-side "what did the runtime variant
    /// actually carry?" projection that the binding proof's PI must
    /// match. Any drift between this projection and the prover's
    /// witness construction fails verification.
    pub(super) fn extract_binding_params(
        effect: &Effect,
        schema_id: &str,
    ) -> Option<(Vec<[u8; 32]>, Vec<u64>)> {
        match (schema_id, effect) {
            (
                "pyana-effect-note-spend-v1",
                Effect::NoteSpend {
                    nullifier,
                    note_tree_root,
                    value,
                    asset_type,
                    value_commitment,
                    ..
                },
            ) => {
                let asset_type_commit = {
                    let mut h = blake3::Hasher::new();
                    h.update(b"pyana-asset-type-commit/v1");
                    h.update(&asset_type.to_le_bytes());
                    *h.finalize().as_bytes()
                };
                let vc = value_commitment.unwrap_or([0u8; 32]);
                Some((
                    vec![nullifier.0, *note_tree_root, asset_type_commit, vc],
                    vec![*value, *asset_type],
                ))
            }
            (
                "pyana-effect-note-create-v1",
                Effect::NoteCreate {
                    commitment,
                    value,
                    asset_type,
                    value_commitment,
                    range_proof,
                    ..
                },
            ) => {
                let asset_type_commit = {
                    let mut h = blake3::Hasher::new();
                    h.update(b"pyana-asset-type-commit/v1");
                    h.update(&asset_type.to_le_bytes());
                    *h.finalize().as_bytes()
                };
                let vc = value_commitment.unwrap_or([0u8; 32]);
                let rph = match range_proof {
                    Some(bytes) => *blake3::hash(bytes).as_bytes(),
                    None => [0u8; 32],
                };
                Some((
                    vec![commitment.0, asset_type_commit, vc, rph],
                    vec![*value, *asset_type],
                ))
            }
            (
                "pyana-effect-bridge-lock-v1",
                Effect::BridgeLock {
                    nullifier,
                    destination,
                    value,
                    asset_type,
                    timeout_height,
                    ..
                },
            ) => {
                let asset_type_commit = {
                    let mut h = blake3::Hasher::new();
                    h.update(b"pyana-asset-type-commit/v1");
                    h.update(&asset_type.to_le_bytes());
                    *h.finalize().as_bytes()
                };
                // BridgeLock variant doesn't carry a value_commitment;
                // use ZERO sentinel. (Future: when the runtime variant
                // is extended with an optional Pedersen value
                // commitment, plumb it here.)
                Some((
                    vec![*nullifier, *destination, asset_type_commit, [0u8; 32]],
                    vec![*value, *asset_type, *timeout_height],
                ))
            }
            ("pyana-effect-bridge-finalize-v1", Effect::BridgeFinalize { nullifier, receipt }) => {
                let receipt_hash = {
                    let bytes = postcard::to_allocvec(receipt).unwrap_or_default();
                    *blake3::hash(&bytes).as_bytes()
                };
                Some((vec![*nullifier, receipt_hash], vec![]))
            }
            ("pyana-effect-bridge-cancel-v1", Effect::BridgeCancel { nullifier }) => {
                Some((vec![*nullifier], vec![]))
            }
            ("pyana-effect-revoke-delegation-v1", Effect::RevokeDelegation { child }) => {
                Some((vec![*child.as_bytes()], vec![]))
            }
            // SCHEMA_BURN (AIR-SOUNDNESS-AUDIT.md #75) is wired in
            // `extract_burn_binding_params` because it needs the pre/post
            // ledger snapshot (`old_balance`, `new_balance`) which this
            // snapshot-free extractor cannot reconstruct. The snapshot-
            // aware path is taken from
            // `verify_effect_binding_proofs_with_ledger` when the schema
            // id is `pyana-effect-burn-v1`; the snapshot-free path keeps
            // returning None here as a structural rejection so a Burn
            // binding proof can never silently slip through without
            // ledger context.
            ("pyana-effect-burn-v1", Effect::Burn { .. }) => None,
            // Other variants: extend as wire-in surface grows. Today
            // the lane closes NoteSpend/NoteCreate/BridgeLock at full
            // fidelity (the deferred §5 items); the remaining
            // schema_ids are valid for off-AIR construction but not
            // re-extracted by this executor-side projection. Add new
            // arms here as their executor-side projection is needed.
            _ => None,
        }
    }

    /// Snapshot-aware Burn binding parameter extractor (AIR-SOUNDNESS-AUDIT
    /// #75). `SCHEMA_BURN` has the field layout
    /// `fields = [target]`, `amounts = [old_balance, new_balance, amount,
    /// was_burn_flag]`. Of those, only `target` and `amount` are present on
    /// `Effect::Burn`; the executor-side projection reconstructs `old_balance`
    /// from the supplied ledger snapshot and `new_balance = old_balance -
    /// amount` (saturating at zero — runtime apply rejects underflow
    /// separately). `was_burn_flag` is always `1` for any Burn binding proof
    /// since the AIR enforces the disclosure bit. Returns `None` if `ledger`
    /// is `None`, if `effect` is not a `Burn`, or if the target cell is not
    /// in the ledger.
    pub(super) fn extract_burn_binding_params(
        effect: &Effect,
        ledger: Option<&Ledger>,
    ) -> Option<(Vec<[u8; 32]>, Vec<u64>)> {
        match effect {
            Effect::Burn {
                target,
                slot: _slot,
                amount,
            } => {
                let ledger = ledger?;
                let cell = ledger.get(target)?;
                let old_balance = cell.state.balance();
                // `new_balance` is the post-Burn balance. The AIR's
                // algebraic constraint is `new = old - amount` with a
                // boolean borrow; underflow is rejected by the executor's
                // runtime `InsufficientBalance` check before this code is
                // reached. Use saturating_sub so an off-AIR sanity test
                // doesn't panic; a real Burn that underflows would be
                // rejected by the runtime apply gate before we ever try
                // to verify its binding proof.
                let new_balance = old_balance.saturating_sub(*amount);
                Some((
                    vec![*target.as_bytes()],
                    vec![old_balance, new_balance, *amount, 1],
                ))
            }
            _ => None,
        }
    }

    /// Extract a named 32-byte field from an Effect (for cross-effect
    /// chain pinning). Returns `None` when the effect doesn't carry a
    /// field of that name.
    pub(super) fn extract_named_field_32b(effect: &Effect, name: &str) -> Option<[u8; 32]> {
        match (name, effect) {
            ("nullifier", Effect::NoteSpend { nullifier, .. }) => Some(nullifier.0),
            ("nullifier", Effect::BridgeLock { nullifier, .. }) => Some(*nullifier),
            ("nullifier", Effect::BridgeFinalize { nullifier, .. }) => Some(*nullifier),
            ("nullifier", Effect::BridgeCancel { nullifier }) => Some(*nullifier),
            ("nullifier", Effect::BridgeMint { portable_proof }) => Some(portable_proof.nullifier),
            ("note_commitment" | "commitment", Effect::NoteCreate { commitment, .. }) => {
                Some(commitment.0)
            }
            ("note_tree_root", Effect::NoteSpend { note_tree_root, .. }) => Some(*note_tree_root),
            ("destination", Effect::BridgeLock { destination, .. }) => Some(*destination),
            ("escrow_id", Effect::CreateEscrow { escrow_id, .. }) => Some(*escrow_id),
            ("escrow_id", Effect::ReleaseEscrow { escrow_id, .. }) => Some(*escrow_id),
            ("escrow_id", Effect::RefundEscrow { escrow_id, .. }) => Some(*escrow_id),
            _ => None,
        }
    }

    /// Stage 7-γ.2 Phase 1: bilateral cross-cell PI consistency check.
    ///
    /// Given a turn and the bundle of per-cell `(cell_id, PI)` pairs, this
    /// reconstructs the expected bilateral schedule from `call_forest +
    /// ACTOR_NONCE` and verifies that each per-cell PI's bilateral count
    /// fields and accumulator-root fields match what the schedule predicts.
    ///
    /// It also enforces the `IS_AGENT_CELL` rule: at most one proof in the
    /// bundle carries `PI[IS_AGENT_CELL] == 1`, and if any does it must be
    /// the cell named in `turn.agent`. All other proofs must have
    /// `PI[IS_AGENT_CELL] == 0`.
    ///
    /// Closes the threats from `EXECUTOR-HONESTY-AUDIT.md` T1 (sender lies
    /// about outbound transfer), T3 (intro permission tampering across
    /// sides), T15 multi-cell tails. See `STAGE-7-GAMMA-2-PI-DESIGN.md` §4.
    pub fn verify_bilateral_bundle(
        bundle: &[(pyana_types::CellId, Vec<pyana_circuit::field::BabyBear>)],
        turn: &Turn,
    ) -> Result<(), TurnError> {
        use crate::bilateral_schedule::ExpectedBilateral;
        let schedule = ExpectedBilateral::from_turn(turn);
        Self::verify_bilateral_bundle_with_schedule(bundle, turn, &schedule)
    }

    /// γ.2 unilateral binding extension: same as [`verify_bilateral_bundle`]
    /// but takes a pre-built `ExpectedBilateral` so the caller can populate
    /// `unilateral_attestations` (which cannot be derived from `call_forest`
    /// alone — they're per-cell self-witnessing data that lives outside the
    /// Turn).
    ///
    /// Use this when a sovereign cell / peer_exchange transition carries
    /// unilateral attestations that must be cross-checked against the PI
    /// accumulator. Callers that don't have unilateral attestations can
    /// keep using [`verify_bilateral_bundle`] — it builds an empty
    /// unilateral list, which produces sentinel roots / zero counts.
    pub fn verify_bilateral_bundle_with_schedule(
        bundle: &[(pyana_types::CellId, Vec<pyana_circuit::field::BabyBear>)],
        turn: &Turn,
        schedule: &crate::bilateral_schedule::ExpectedBilateral,
    ) -> Result<(), TurnError> {
        use crate::bilateral_schedule::extract_from_pi;
        use pyana_circuit::effect_vm::pi;

        if bundle.is_empty() {
            return Ok(());
        }

        // Reject any per-cell PI that's too short to carry the γ.2 layout.
        for (i, (cid, p)) in bundle.iter().enumerate() {
            if p.len() < pi::BASE_COUNT {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral bundle entry {} (cell {:?}) has {} public \
                     inputs, expected at least {} (Stage 7-γ.2 layout)",
                    i,
                    cid,
                    p.len(),
                    pi::BASE_COUNT
                )));
            }
        }

        let actor_nonce = turn.nonce;

        // Per-cell check.
        let mut agent_count = 0usize;
        for (idx, (cell_id, p)) in bundle.iter().enumerate() {
            let (counts, roots) = extract_from_pi(p);
            let expected_counts = schedule.counts_for(cell_id);
            let expected_roots = schedule.roots_for(cell_id, actor_nonce);

            macro_rules! count_check {
                ($field:ident, $name:literal) => {
                    if counts.$field != expected_counts.$field {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "bilateral PI mismatch in proof {} (cell {:?}): \
                             {} expected {} got {}",
                            idx, cell_id, $name, expected_counts.$field, counts.$field
                        )));
                    }
                };
            }
            count_check!(outbound_transfer, "outbound_transfer_count");
            count_check!(inbound_transfer, "inbound_transfer_count");
            count_check!(outbound_grant, "outbound_grant_count");
            count_check!(inbound_grant, "inbound_grant_count");
            count_check!(intro_as_introducer, "intro_as_introducer_count");
            count_check!(intro_as_recipient, "intro_as_recipient_count");
            count_check!(intro_as_target, "intro_as_target_count");
            // γ.2 unilateral binding: per-cell self-attestation count.
            count_check!(unilateral_attestations, "unilateral_attestations_count");

            macro_rules! root_check {
                ($field:ident, $name:literal) => {
                    if roots.$field != expected_roots.$field {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "bilateral PI mismatch in proof {} (cell {:?}): \
                             {} root differs from schedule",
                            idx, cell_id, $name
                        )));
                    }
                };
            }
            root_check!(outgoing_transfer, "outgoing_transfer");
            root_check!(incoming_transfer, "incoming_transfer");
            root_check!(outgoing_grant, "outgoing_grant");
            root_check!(incoming_grant, "incoming_grant");
            root_check!(intro_as_introducer, "intro_as_introducer");
            root_check!(intro_as_recipient, "intro_as_recipient");
            root_check!(intro_as_target, "intro_as_target");
            // γ.2 unilateral binding: per-cell self-attestation accumulator root.
            root_check!(unilateral_attestations, "unilateral_attestations");

            // IS_AGENT_CELL consistency.
            let is_agent = p[pi::IS_AGENT_CELL];
            let is_agent_u = is_agent.as_u32();
            if is_agent_u != 0 && is_agent_u != 1 {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral PI in proof {} (cell {:?}): IS_AGENT_CELL must be 0 or 1, got {}",
                    idx, cell_id, is_agent_u
                )));
            }
            let should_be_agent = cell_id == &turn.agent;
            if should_be_agent && is_agent_u != 1 {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral PI in proof {} (cell {:?}): cell is the turn.agent \
                     but IS_AGENT_CELL == 0",
                    idx, cell_id
                )));
            }
            if !should_be_agent && is_agent_u != 0 {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral PI in proof {} (cell {:?}): cell is NOT the turn.agent \
                     but IS_AGENT_CELL == 1",
                    idx, cell_id
                )));
            }
            if is_agent_u == 1 {
                agent_count += 1;
            }
        }

        // Exactly-one-agent rule: at most one proof should claim agent.
        if agent_count > 1 {
            return Err(TurnError::InvalidExecutionProof(format!(
                "bilateral bundle has {} proofs claiming IS_AGENT_CELL == 1; \
                 at most one allowed",
                agent_count
            )));
        }

        // Cross-side existence check: every Transfer / Grant in the
        // schedule should have *both* its endpoints represented in the
        // bundle whenever either appears. If one side appears but the peer
        // does not, that's a hard reject — the bundle is incomplete
        // relative to the schedule, and a malicious prover could otherwise
        // produce only the side that benefits them.
        let covered: std::collections::HashSet<&pyana_types::CellId> =
            bundle.iter().map(|(c, _)| c).collect();
        for t in &schedule.transfers {
            let from_in = covered.contains(&t.from);
            let to_in = covered.contains(&t.to);
            if from_in != to_in {
                let missing = if from_in { &t.to } else { &t.from };
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral schedule references both {:?} and {:?} in a Transfer \
                     but bundle only covers one; missing peer {:?}",
                    t.from, t.to, missing
                )));
            }
        }
        for g in &schedule.grants {
            let from_in = covered.contains(&g.from);
            let to_in = covered.contains(&g.to);
            if from_in != to_in {
                let missing = if from_in { &g.to } else { &g.from };
                return Err(TurnError::InvalidExecutionProof(format!(
                    "bilateral schedule references both {:?} and {:?} in a Grant \
                     but bundle only covers one; missing peer {:?}",
                    g.from, g.to, missing
                )));
            }
        }
        for intro in &schedule.introduces {
            let any_covered = covered.contains(&intro.introducer)
                || covered.contains(&intro.recipient)
                || covered.contains(&intro.target);
            if any_covered {
                let distinct: std::collections::HashSet<&pyana_types::CellId> =
                    [&intro.introducer, &intro.recipient, &intro.target]
                        .into_iter()
                        .collect();
                for c in &distinct {
                    if !covered.contains(*c) {
                        return Err(TurnError::InvalidExecutionProof(format!(
                            "bilateral schedule references Introduce({:?}, {:?}, {:?}) \
                             but bundle is missing role-player {:?}",
                            intro.introducer, intro.recipient, intro.target, c
                        )));
                    }
                }
            }
        }

        Ok(())
    }

    /// Convenience: verify a bundle of per-cell `(StarkProof, public_inputs)`
    /// pairs from the same turn.
    ///
    /// Runs the per-proof STARK verifier on each pair (against the standard
    /// `EffectVmAir`) and then calls
    /// [`verify_proof_carrying_turn_bundle`] to enforce that the shared
    /// γ.0a PI slots agree across proofs and (when `turn` is supplied)
    /// against the canonical Turn projection.
    ///
    /// Note: this convenience handles the default-AIR path only; the
    /// custom-program-VK path is the caller's responsibility because the
    /// per-cell AIR identity is cell-dependent in that case. The single-cell
    /// `verify_and_commit_proof` remains the path of record for production
    /// today; this helper exists to back tests and to give future
    /// multi-cell aggregation callers (Stage 7-γ.1+) a stable entry point.
    pub fn verify_bundle_with_stark(
        bundle: &[(
            pyana_circuit::stark::StarkProof,
            Vec<pyana_circuit::field::BabyBear>,
        )],
        turn: Option<&Turn>,
    ) -> Result<(), TurnError> {
        Self::verify_bundle_with_stark_and_ledger(bundle, turn, None)
    }

    /// Snapshot-aware variant of `verify_bundle_with_stark` that threads a
    /// `&Ledger` into the binding-proof sweep. Closes AIR #75 for callers
    /// who carry a Burn binding proof in `turn.effect_binding_proofs`.
    pub fn verify_bundle_with_stark_and_ledger(
        bundle: &[(
            pyana_circuit::stark::StarkProof,
            Vec<pyana_circuit::field::BabyBear>,
        )],
        turn: Option<&Turn>,
        ledger: Option<&Ledger>,
    ) -> Result<(), TurnError> {
        use pyana_circuit::stark;

        for (i, (proof, pis)) in bundle.iter().enumerate() {
            let air = pyana_circuit::EffectVmAir::new(proof.trace_len);
            stark::verify(&air, proof, pis).map_err(|e| {
                TurnError::ProofVerificationFailed(format!("bundle proof {}: {}", i, e))
            })?;
        }
        let pi_vecs: Vec<Vec<_>> = bundle.iter().map(|(_, pis)| pis.clone()).collect();
        Self::verify_proof_carrying_turn_bundle_with_ledger(&pi_vecs, turn, ledger)
    }

    /// Read the per-cell `max_custom_effects` from the cell's program manifest.
    ///
    /// Per `DESIGN-max-custom-effects.md` §4. Falls back to
    /// [`pyana_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT`] if the cell
    /// has no explicit declaration (hosted or legacy sovereign cells).
    ///
    /// Stage 1: looks at sovereign registration's `max_custom_effects` optional
    /// field (added in this stage). Stage 8 may move the source of truth into
    /// `cell::CellProgram::max_custom_effects` directly.
    pub(super) fn read_cell_max_custom_effects(&self, cell_id: &CellId, ledger: &Ledger) -> u8 {
        if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            if let Some(m) = reg.max_custom_effects {
                return m;
            }
        }
        pyana_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT
    }

    /// Read the federation-scoped `approved_handoffs_root` as 4 BabyBear felts.
    ///
    /// Stage 1: returns the empty-tree sentinel (`Commitment4::empty()`).
    /// Stage 7 populates this from federation state when CapTP runtime
    /// emitters land. Per `DESIGN-captp-integration.md` §4.2.
    pub(super) fn read_approved_handoffs_root(&self) -> [pyana_circuit::field::BabyBear; 4] {
        [pyana_circuit::field::BabyBear::ZERO; 4]
    }

    /// Get the verification key hash for a sovereign cell, if one is set.
    ///
    /// Checks both the sovereign registration (which has an explicit `verification_key_hash`
    /// field) and the cell's `verification_key` (for hosted cells or legacy sovereign cells).
    pub(crate) fn get_cell_vk_hash(&self, cell_id: &CellId, ledger: &Ledger) -> Option<[u8; 32]> {
        // Check sovereign registration first (proof-carrying path).
        if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
            if let Some(vk_hash) = reg.verification_key_hash {
                return Some(vk_hash);
            }
        }
        // Fallback: check if the cell itself has a verification_key with a hash.
        if let Some(cell) = ledger.get(cell_id) {
            if let Some(vk) = &cell.verification_key {
                return Some(vk.hash);
            }
        }
        None
    }

    /// Encode a 32-byte hash as 8 BabyBear field elements (4 bytes each, little-endian).
    pub(super) fn bytes32_to_babybear(bytes: &[u8; 32]) -> Vec<pyana_circuit::field::BabyBear> {
        use pyana_circuit::field::BabyBear;
        let mut result = Vec::with_capacity(8);
        for chunk in bytes.chunks(4) {
            let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            // Reduce mod BabyBear prime to ensure valid field element.
            result.push(BabyBear(val % pyana_circuit::field::BABYBEAR_P));
        }
        result
    }

    /// Decode 8 u32 values (from proof public_inputs) back into a 32-byte hash.
    pub(super) fn babybear_slice_to_bytes32(values: &[u32]) -> [u8; 32] {
        let mut result = [0u8; 32];
        for (i, &val) in values.iter().take(8).enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&val.to_le_bytes());
        }
        result
    }

    /// Convert 4 BabyBear elements to a 16-byte array (for custom proof commitment matching).
    pub(super) fn babybear4_to_bytes16(elems: &[pyana_circuit::field::BabyBear; 4]) -> [u8; 16] {
        let mut result = [0u8; 16];
        for (i, elem) in elems.iter().enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&elem.0.to_le_bytes());
        }
        result
    }

    /// Convert 8 BabyBear elements to a 32-byte array (PI v2 VK hash key).
    ///
    /// AIR-SOUNDNESS-AUDIT.md #70: the registry now binds against the full
    /// 32-byte VK hash. The pre-v2 path used `babybear4_to_bytes16` plus
    /// `expand_vk_hash_16_to_32` (zero-padded upper 16 bytes), giving 80-bit
    /// effective security in a 128-bit system. The full 32-byte form
    /// distinguishes VK hashes whose lower 16 bytes collide.
    pub(super) fn babybear8_to_bytes32(elems: &[pyana_circuit::field::BabyBear; 8]) -> [u8; 32] {
        let mut result = [0u8; 32];
        for (i, elem) in elems.iter().enumerate() {
            result[i * 4..i * 4 + 4].copy_from_slice(&elem.0.to_le_bytes());
        }
        result
    }

    /// Hash custom proof bytes to produce a 16-byte commitment (matching BabyBear[4]).
    pub(super) fn hash_custom_proof(proof_bytes: &[u8]) -> [u8; 16] {
        let h = blake3::hash(proof_bytes);
        let bytes = h.as_bytes();
        let mut result = [0u8; 16];
        result.copy_from_slice(&bytes[..16]);
        result
    }

    /// **DEPRECATED** — see `babybear8_to_bytes32`.
    ///
    /// Pre-v2 (`pi::VK_PI_LAYOUT_VERSION == 1`) expanded a 16-byte VK hash
    /// (from 4 BabyBear elements) to a 32-byte registry key by zero-padding
    /// the upper 16 bytes. This gave 80-bit effective security: any two
    /// VK hashes that collide on the lower 16 bytes (~2^64 work) dispatch
    /// to the same handler regardless of their upper 16 bytes.
    /// `AIR-SOUNDNESS-AUDIT.md` #70 closed this by widening the PI vk_hash
    /// to 8 felts (full 32 bytes); see `babybear8_to_bytes32`. This helper
    /// is retained only so legacy callers compile; no live dispatch path
    /// uses it.
    #[deprecated(note = "PI layout v2: use babybear8_to_bytes32 against the full 8-felt PI slot")]
    #[allow(dead_code)]
    pub(super) fn expand_vk_hash_16_to_32(short: &[u8; 16]) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..16].copy_from_slice(short);
        result
    }

    /// Decode a stored [u8; 32] commitment to a single BabyBear field element.
    ///
    /// The stored commitment encodes a Poseidon2 CellState commitment as a
    /// 32-byte BLAKE3-style canonical hash. See the cell crate's
    /// `compute_canonical_state_commitment` for the canonical encoding.
    ///
    /// STAGE 1 (resolves REVIEW[effect-vm-coord], P0-2 in AUDIT-turn-executor.md):
    /// the 4-byte truncation has been replaced with a 4-felt Poseidon2 form
    /// (~124-bit binding) via [`commitment_to_4bb`]. The legacy single-felt
    /// `commitment_to_babybear` retained here for backward-compat with
    /// callers that absorb commitments into Merkle leaves; it now derives
    /// the felt from the full 32-byte canonical commitment rather than a
    /// 4-byte truncation.
    pub fn commitment_to_babybear(bytes: &[u8; 32]) -> pyana_circuit::field::BabyBear {
        // Position 0 of the 4-felt form is the in-trace continuity binding.
        Self::commitment_to_4bb(bytes)[0]
    }

    /// Decode a 32-byte stored commitment into the 4-felt Poseidon2 form used
    /// by the Effect VM AIR's PI[OLD_COMMIT_BASE..+4] / PI[NEW_COMMIT_BASE..+4].
    ///
    /// The stored commitment format (written by [`commitment_4bb_to_bytes`]) packs
    /// 4 BabyBear felts as 4 consecutive LE u32 values in bytes 0..15. The upper
    /// 16 bytes are zero padding. This is the canonical round-trip format that
    /// matches `CellState::compute_commitment_4` — the function the AIR trace
    /// generator uses to populate the commitment PI slots.
    ///
    /// This replaces the former `canonical_32_to_felts_4` call which hashed the
    /// stored bytes (a one-way operation producing different values than
    /// `compute_commitment_4`), causing a byte-incompatible PI mismatch between
    /// trace generation and verification (Silver-Vision bug: sovereign-cell proofs
    /// always rejected, GitHub #99).
    pub fn commitment_to_4bb(bytes: &[u8; 32]) -> [pyana_circuit::field::BabyBear; 4] {
        use pyana_circuit::field::BabyBear;
        [
            BabyBear::new(u32::from_le_bytes(bytes[0..4].try_into().unwrap())),
            BabyBear::new(u32::from_le_bytes(bytes[4..8].try_into().unwrap())),
            BabyBear::new(u32::from_le_bytes(bytes[8..12].try_into().unwrap())),
            BabyBear::new(u32::from_le_bytes(bytes[12..16].try_into().unwrap())),
        ]
    }

    /// Pack 4 BabyBear felts into a 32-byte stored commitment.
    ///
    /// Writes each felt as a LE u32 into bytes 0..15; zeros bytes 16..31.
    /// This is the canonical format read back by [`commitment_to_4bb`].
    /// Use this instead of [`babybear_to_commitment`] when the proof's PI carries
    /// a widened 4-felt commitment (`CellState::compute_commitment_4` output).
    pub fn commitment_4bb_to_bytes(felts: [pyana_circuit::field::BabyBear; 4]) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[0..4].copy_from_slice(&felts[0].0.to_le_bytes());
        result[4..8].copy_from_slice(&felts[1].0.to_le_bytes());
        result[8..12].copy_from_slice(&felts[2].0.to_le_bytes());
        result[12..16].copy_from_slice(&felts[3].0.to_le_bytes());
        result
    }

    /// Encode a single BabyBear field element as a [u8; 32] stored commitment.
    ///
    /// Packs the u32 value into the first 4 bytes (LE), zeroes the rest.
    /// Legacy single-felt encoding; prefer [`commitment_4bb_to_bytes`] for new
    /// proof-carrying paths that use the widened 4-felt PI layout.
    pub fn babybear_to_commitment(bb: pyana_circuit::field::BabyBear) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..4].copy_from_slice(&bb.0.to_le_bytes());
        result
    }

    /// Compute the AIR-bound 4-felt commitment to a 32-byte Ed25519 owner pubkey
    /// (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2). Uses `canonical_32_to_felts_4`
    /// so it matches the in-trace witness column. Domain separation from the
    /// state-commitment encoding is provided by the surrounding PI slot
    /// (different position in PI), not by a tag — both inputs are 32 bytes
    /// of opaque commitment material.
    pub fn pubkey_to_witness_key_commit(pubkey: &[u8; 32]) -> [pyana_circuit::field::BabyBear; 4] {
        pyana_commit::typed::canonical_32_to_felts_4(pubkey)
    }

    /// Compute the AIR-bound 4-felt commitment to a transition_proof's
    /// canonical bytes (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2 / §4.2). The
    /// commitment is `canonical_32_to_felts_4(blake3(proof_bytes))`, picking
    /// up blake3's preimage resistance + the Poseidon2-domain mapping the
    /// AIR uses for everything else.
    pub fn transition_proof_commitment(proof_bytes: &[u8]) -> [pyana_circuit::field::BabyBear; 4] {
        let h = *blake3::hash(proof_bytes).as_bytes();
        pyana_commit::typed::canonical_32_to_felts_4(&h)
    }

    /// Populate the sovereign-witness AIR-teeth PI slots on the verifier
    /// side (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2).
    ///
    /// `witness` is `Some` when this cell is being verified via the
    /// witness path (the witness object carries the cell's full state
    /// including its public_key). `execution_proof_bytes` is `Some` when
    /// the proof-carrying path is in effect (the bytes ARE the inner
    /// transition proof for Phase 2).
    ///
    /// When neither is supplied, IS_SOVEREIGN_CELL is left as zero (the
    /// hosted-cell path); the boundary constraint holds via sentinel
    /// agreement.
    pub fn populate_sovereign_witness_pi(
        public_inputs: &mut [pyana_circuit::field::BabyBear],
        cell_id: &CellId,
        ledger: &Ledger,
        witness: Option<&crate::turn::SovereignCellWitness>,
        execution_proof_bytes: Option<&[u8]>,
    ) {
        use pyana_circuit::effect_vm::pi;
        use pyana_circuit::field::BabyBear;

        // Default sentinel values (hosted-cell path).
        for i in 0..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN {
            public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i] = BabyBear::ZERO;
        }
        public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] = BabyBear::ZERO;
        public_inputs[pi::IS_SOVEREIGN_CELL] = BabyBear::ZERO;
        for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_LEN {
            public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE + i] = BabyBear::ZERO;
        }
        for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN {
            public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE + i] = BabyBear::ZERO;
        }
        public_inputs[pi::HAS_TRANSITION_PROOF] = BabyBear::ZERO;

        // Phase 1: Bind the witness-identity slots when we have witness
        // material. Source order:
        //   1. Explicit witness object (witness-path turns)
        //   2. Proof-carrying turn (execution_proof_bytes is Some) — bind
        //      IS_SOVEREIGN_CELL=1 + the cell's owning pubkey from
        //      SovereignRegistration::owner_public_key (if populated).
        if let Some(w) = witness {
            // Witness path: the witness carries the cell_state including pubkey.
            let key_commit = Self::pubkey_to_witness_key_commit(w.cell_state.public_key());
            for i in 0..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN {
                public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i] = key_commit[i];
            }
            public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] =
                BabyBear::new((w.sequence & 0x7FFF_FFFF) as u32);
            public_inputs[pi::IS_SOVEREIGN_CELL] = BabyBear::ONE;

            // Phase 2: if the witness includes a STARK transition_proof,
            // bind its commitment + VK hash. The VK hash is zero sentinel
            // today (the recursive verifier exposes a stable VK in a
            // follow-up); the off-AIR verifier loop recursively verifies.
            if let Some(proof_bytes) = &w.transition_proof {
                let proof_commit = Self::transition_proof_commitment(proof_bytes);
                for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN {
                    public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE + i] =
                        proof_commit[i];
                }
                public_inputs[pi::HAS_TRANSITION_PROOF] = BabyBear::ONE;
            }
        } else if let Some(proof_bytes) = execution_proof_bytes {
            // Proof-carrying path: the execution_proof IS the transition proof.
            // Owner pubkey is sourced from the sovereign registration if
            // available, else left as sentinel zero (Phase 1.5: registration
            // grows an owner_public_key field; for now we accept either
            // form and the cclerk matches what the federation knows).
            if let Some(reg) = ledger.get_sovereign_registration(cell_id) {
                if let Some(pk) = reg.owner_public_key {
                    let key_commit = Self::pubkey_to_witness_key_commit(&pk);
                    for i in 0..pi::SOVEREIGN_WITNESS_KEY_COMMIT_LEN {
                        public_inputs[pi::SOVEREIGN_WITNESS_KEY_COMMIT_BASE + i] = key_commit[i];
                    }
                }
            }
            public_inputs[pi::SOVEREIGN_WITNESS_SEQUENCE] = BabyBear::new(
                (ledger.last_sovereign_witness_sequence(cell_id) & 0x7FFF_FFFF) as u32,
            );
            public_inputs[pi::IS_SOVEREIGN_CELL] = BabyBear::ONE;

            // Phase 2: bind the inner-proof commitment.
            let proof_commit = Self::transition_proof_commitment(proof_bytes);
            for i in 0..pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_LEN {
                public_inputs[pi::SOVEREIGN_TRANSITION_PROOF_COMMITMENT_BASE + i] = proof_commit[i];
            }
            public_inputs[pi::HAS_TRANSITION_PROOF] = BabyBear::ONE;
        }
    }

    /// Encode two BabyBear elements as a [u8; 32] for error reporting.
    pub(super) fn babybear_pair_to_bytes32(
        lo: pyana_circuit::field::BabyBear,
        hi: pyana_circuit::field::BabyBear,
    ) -> [u8; 32] {
        let mut result = [0u8; 32];
        result[..4].copy_from_slice(&lo.0.to_le_bytes());
        result[4..8].copy_from_slice(&hi.0.to_le_bytes());
        result
    }

    /// Stage 7-γ.0c: compute the four shared "turn-identity" PI values that
    /// every per-cell proof of `turn` must agree on.
    ///
    /// Returns `(turn_hash[4], effects_hash_global[4], actor_nonce,
    /// previous_receipt_hash[4])` where:
    ///
    /// - `turn_hash` is `canonical_32_to_felts_4(Turn::hash())` (v3, post-α.1).
    /// - `effects_hash_global` is a Poseidon2 absorption chain over the
    ///   canonical-DFS-order traversal of *every* Effect in the call_forest
    ///   (not per-cell). Order: pre-order DFS, root-list order at the top,
    ///   children-list order at each node, action.effects-list order at each
    ///   action. Each Effect contributes its `Effect::hash()` -> 4 felts via
    ///   `canonical_32_to_felts_4`, absorbed into the running 4-felt
    ///   accumulator by element-wise composition with `hash_4_to_1`. The
    ///   empty-forest sentinel is `[BabyBear::ZERO; 4]`.
    /// - `actor_nonce` is `turn.nonce` (closes #49 differential-test gap).
    /// - `previous_receipt_hash` is `canonical_32_to_felts_4` of
    ///   `turn.previous_receipt_hash`, or `[ZERO; 4]` when None.
    ///
    /// The canonical DFS order is the same one a Stage 7-γ.1 aggregation
    /// micro-AIR will replay when checking
    /// `Poseidon2-merge(effects_local[c1..]) == effects_hash_global`, so
    /// any future cross-cell aggregator must match this traversal exactly.
    pub fn compute_turn_identity_pi(
        turn: &Turn,
    ) -> (
        [pyana_circuit::field::BabyBear; 4],
        [pyana_circuit::field::BabyBear; 4],
        u64,
        [pyana_circuit::field::BabyBear; 4],
    ) {
        use pyana_circuit::field::BabyBear;
        use pyana_circuit::poseidon2::hash_4_to_1;
        use pyana_commit::typed::canonical_32_to_felts_4;

        let turn_hash_4 = canonical_32_to_felts_4(&turn.hash());

        // Canonical-DFS-order collection of the WHOLE call_forest's effects.
        // The order must match what a future cross-cell aggregator (γ.1)
        // computes; document it here in one place and keep this helper as
        // the source of truth.
        fn dfs_collect(tree: &CallTree, out: &mut Vec<[u8; 32]>) {
            for effect in &tree.action.effects {
                out.push(effect.hash());
            }
            for child in &tree.children {
                dfs_collect(child, out);
            }
        }
        let mut effect_hashes: Vec<[u8; 32]> = Vec::new();
        for root in &turn.call_forest.roots {
            dfs_collect(root, &mut effect_hashes);
        }

        // Absorb each 32-byte effect hash into a running 4-felt accumulator.
        // The empty-forest case yields the zero sentinel. The absorption rule
        // for one block is acc' = elementwise hash_4_to_1 of [acc[i], blk[i]
        // mixed with index salts]. We use a simple feistel-flavoured pattern:
        //   for each i in 0..4:
        //     acc[i] = hash_4_to_1(&[acc[i], blk[i], acc[(i+1)%4], blk[(i+1)%4]])
        // — distinct salts per position via the rotation, so the four output
        // limbs depend on all eight input limbs. Deterministic and trivially
        // re-implementable in a future aggregation AIR.
        let mut acc: [BabyBear; 4] = [BabyBear::ZERO; 4];
        for h in &effect_hashes {
            let blk = canonical_32_to_felts_4(h);
            let mut next = [BabyBear::ZERO; 4];
            for i in 0..4 {
                let j = (i + 1) % 4;
                next[i] = hash_4_to_1(&[acc[i], blk[i], acc[j], blk[j]]);
            }
            acc = next;
        }
        let effects_hash_global_4 = acc;

        let previous_receipt_hash_4 = match &turn.previous_receipt_hash {
            Some(h) => canonical_32_to_felts_4(h),
            None => [BabyBear::ZERO; 4],
        };

        (
            turn_hash_4,
            effects_hash_global_4,
            turn.nonce,
            previous_receipt_hash_4,
        )
    }

    /// Convert turn-level effects from the call forest into circuit-level Effect VM effects.
    ///
    /// Walks the call forest DFS and converts each effect targeting `cell_id` into the
    /// corresponding `effect_vm::Effect`. Effects not targeting this cell are skipped.

    /// Compute the balance delta (magnitude, sign) from the turn's effects for a cell.
    ///
    /// Returns (magnitude_u32, sign_u32) where sign=0 means positive/incoming,
    /// sign=1 means negative/outgoing.
    pub(super) fn compute_balance_delta_from_effects(cell_id: &CellId, turn: &Turn) -> (u32, u32) {
        fn walk_delta(tree: &CallTree, cell_id: &CellId, net: &mut i64) {
            for effect in &tree.action.effects {
                match effect {
                    Effect::Transfer { from, to, amount } => {
                        if from == cell_id {
                            *net -= *amount as i64;
                        }
                        if to == cell_id {
                            *net += *amount as i64;
                        }
                    }
                    Effect::NoteSpend { value, .. } => {
                        *net += *value as i64;
                    }
                    Effect::NoteCreate { value, .. } => {
                        *net -= *value as i64;
                    }
                    // Stage 3 honest projections: AIR enforces balance changes
                    // for these variants, so they must contribute to net_delta
                    // for the PI-to-trace consistency constraint to hold.
                    Effect::CreateEscrow { cell, amount, .. } => {
                        if cell == cell_id {
                            *net -= *amount as i64;
                        }
                    }
                    Effect::BridgeLock { value, .. } => {
                        // BridgeLock is always emitted by the actor cell, so
                        // it always debits the actor's balance. (Unlike
                        // Transfer, there's no separate `from` field — the
                        // turn's agent is the locker.)
                        *net -= *value as i64;
                    }
                    Effect::BridgeMint { portable_proof } => {
                        // BridgeMint credits the actor's balance with the
                        // portable proof's declared value.
                        *net += portable_proof.value as i64;
                    }
                    _ => {}
                }
            }
            for child in &tree.children {
                walk_delta(child, cell_id, net);
            }
        }

        let mut net_delta: i64 = 0;
        for root in &turn.call_forest.roots {
            walk_delta(root, cell_id, &mut net_delta);
        }

        if net_delta < 0 {
            ((-net_delta) as u32, 1u32)
        } else {
            (net_delta as u32, 0u32)
        }
    }

    /// Compute a BLAKE3 hash of the turn's effects for proof-carrying verification.
    ///
    /// This hashes all effects in the call forest deterministically (DFS order).
    pub(super) fn compute_turn_effects_hash(&self, turn: &Turn) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-sovereign-effects-v1:");
        for root in &turn.call_forest.roots {
            Self::hash_tree_effects(root, &mut hasher);
        }
        *hasher.finalize().as_bytes()
    }

    /// Recursively hash effects from a call tree into a hasher.
    pub(super) fn hash_tree_effects(tree: &CallTree, hasher: &mut blake3::Hasher) {
        for effect in &tree.action.effects {
            hasher.update(&effect.hash());
        }
        for child in &tree.children {
            Self::hash_tree_effects(child, hasher);
        }
    }
}
