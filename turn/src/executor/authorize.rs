//! Authorization verification: signature/proof/bearer-cap/captp paths, signing-message construction, permission analysis.
//!
//! Extracted from `executor/mod.rs` (lines 4628-6149 of pre-decomposition file).

use super::*;

impl TurnExecutor {
    pub(crate) fn verify_authorization(
        &self,
        action: &Action,
        target_cell: &Cell,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // OneOf: disjunctive multi-mode authorization
        // (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3 / §9.2.3). Pick the
        // candidate at `proof_index`, validate the structural rules
        // (in-bounds, not Unchecked, not nested OneOf), then recurse
        // with a clone of the action carrying the chosen candidate
        // as its authorization. The bindings of the inner candidate
        // (signing message, nonce, federation_id) carry the replay
        // protection — the outer OneOf is a pure switch.
        if let Authorization::OneOf {
            candidates,
            proof_index,
        } = &action.authorization
        {
            let idx = *proof_index as usize;
            if idx >= candidates.len() {
                return Err((
                    TurnError::InvalidAuthorization {
                        reason: format!(
                            "Authorization::OneOf proof_index {} out of bounds (candidates.len()={})",
                            proof_index,
                            candidates.len()
                        ),
                    },
                    path.to_vec(),
                ));
            }
            let chosen = &candidates[idx];
            // Reject Unchecked at the indexed slot — OneOf must not
            // become an auth-bypass-by-naming-Unchecked surface.
            if matches!(chosen, Authorization::Unchecked) {
                return Err((
                    TurnError::InvalidAuthorization {
                        reason: format!(
                            "Authorization::OneOf indexed candidate {} is Unchecked; \
                             OneOf cannot reduce to an auth bypass",
                            proof_index
                        ),
                    },
                    path.to_vec(),
                ));
            }
            // Reject nested OneOf at the indexed slot — flatten the
            // candidate list at the app layer instead.
            if matches!(chosen, Authorization::OneOf { .. }) {
                return Err((
                    TurnError::InvalidAuthorization {
                        reason: format!(
                            "Authorization::OneOf indexed candidate {} is itself a OneOf; \
                             nested OneOf is rejected — flatten the candidates list",
                            proof_index
                        ),
                    },
                    path.to_vec(),
                ));
            }
            // Recurse with the chosen candidate as the action's
            // authorization. We clone the action so the recursive call
            // sees a coherent (action, authorization) pair.
            let mut inner_action = action.clone();
            inner_action.authorization = chosen.clone();
            self.verify_authorization(
                &inner_action,
                target_cell,
                ledger,
                actor_cell_id,
                path,
                turn_nonce,
            )?;
            info!(
                kind = "authorization",
                auth_kind = "one_of",
                target = %action.target,
                chosen_index = idx,
                num_candidates = candidates.len(),
            );
            return Ok(());
        }

        // Custom: app-defined authorization via WitnessedPredicate
        // (AUTHORIZATION-CUSTOM-DESIGN). Verified by dispatching the
        // predicate's kind through the WitnessedPredicateRegistry with
        // the canonical signing message as input.
        if let Authorization::Custom { predicate } = &action.authorization {
            self.verify_custom_authorization(action, target_cell, predicate, path, turn_nonce)?;
            info!(
                kind = "authorization",
                auth_kind = "custom",
                target = %action.target,
                pred_kind = ?predicate.kind,
            );
            return Ok(());
        }

        // CapTpDelivered carries the cryptographic provenance of a CapTP wire
        // delivery (introducer-signed handoff cert + recipient-signed turn
        // binding). Verified holistically here regardless of the target cell's
        // permission level — the upstream CapTP handshake already established
        // legitimacy through (cert.introducer_signature, recipient.sender_signature).
        if let Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature,
        } = &action.authorization
        {
            self.verify_captp_delivered(
                action,
                handoff_cert,
                introducer_pk,
                sender_pk,
                sender_signature,
                turn_nonce,
                path,
            )?;
            // Studio trace: authorization verified (CapTpDelivered).
            info!(kind = "authorization", auth_kind = "captp_delivered", target = %action.target, cert_nonce = hex::encode(handoff_cert.nonce));
            return Ok(());
        }

        // Bearer caps carry their own delegation proof and MUST always be verified,
        // regardless of target cell permission level.
        if let Authorization::Bearer(bearer_proof) = &action.authorization {
            self.verify_bearer_cap(bearer_proof, ledger, path)?;

            // Enforce bearer facet: if the bearer proof has an allowed_effects mask,
            // verify that all effects in the action are within it.
            // If the bearer proof has no explicit mask, check whether the delegator's
            // capability has a facet constraint (inherited facet).
            let effective_mask = bearer_proof.allowed_effects.or_else(|| {
                // Look up the delegator's capability to see if it has a facet.
                // For SignedDelegation, we can find the delegator by pk.
                match &bearer_proof.delegation_proof {
                    crate::action::DelegationProofData::SignedDelegation {
                        delegator_pk, ..
                    } => ledger
                        .iter()
                        .find(|(_, cell)| *cell.public_key() == *delegator_pk)
                        .and_then(|(_, cell)| {
                            cell.capabilities
                                .capabilities_for(&bearer_proof.target)
                                .into_iter()
                                .find(|cap| cap.permissions != AuthRequired::Impossible)
                                .and_then(|cap| cap.allowed_effects)
                        }),
                    // For STARK delegations, the delegator is anonymous — facet must be
                    // explicitly specified in the bearer proof if needed.
                    crate::action::DelegationProofData::StarkDelegation { .. } => None,
                }
            });

            if let Some(mask) = effective_mask {
                if mask != 0 {
                    let effects_mask = action
                        .effects
                        .iter()
                        .fold(0u32, |acc, e| acc | e.effect_kind_mask());
                    if effects_mask != 0 && effects_mask & mask != effects_mask {
                        return Err((
                            TurnError::BearerCapFacetViolation {
                                target: bearer_proof.target,
                                attempted_effects_mask: effects_mask,
                                allowed_mask: mask,
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }

            // Studio trace: authorization verified (Bearer) — facet check passed.
            info!(kind = "authorization", auth_kind = "bearer", target = %bearer_proof.target, expires_at = bearer_proof.expires_at);
            return Ok(());
        }

        // Token: first-class biscuit/macaroon credential
        // (TOKEN-CAPABILITY-UNIFICATION.md). Verified holistically by the
        // turn-side TokenAuthorityVerifier: cryptographic verify + caveat /
        // Datalog evaluation bound to THIS call's AuthRequest + capability
        // cover + block-height-bound expiry. Fail-closed.
        if let Authorization::Token {
            encoded,
            key_ref,
            discharges,
        } = &action.authorization
        {
            self.verify_token_authorization(
                action,
                target_cell,
                encoded,
                key_ref,
                discharges,
                path,
                turn_nonce,
            )?;
            info!(kind = "authorization", auth_kind = "token", target = %action.target);
            return Ok(());
        }

        // Stealth: one-time-key invocation (anonymity of the actor). The
        // one-time signature is verified against the stealth-spend relation
        // P == c·G + S, where S is the target cell's public key (treated as a
        // stealth spend pubkey). This MUST be checked regardless of the
        // permission level for the *signature* itself, but we still funnel
        // through the per-permission requirement check below so a cell that
        // forbids the action (Impossible) is honored. We verify the stealth
        // signature up front (fail-closed) and let the permission lattice
        // accept it via `to_auth_kind() == Signature`.
        if let Authorization::Stealth { .. } = &action.authorization {
            self.verify_stealth_authorization(action, target_cell, path, turn_nonce)?;
            // Fall through to the permission-requirement checks so that
            // `AuthRequired::Impossible` / `Proof`-only / `Custom` cells still
            // reject a stealth signature that does not match their lattice.
        }

        // Determine ALL required permissions for this action's effects.
        let required_actions = self.determine_required_permissions(action);

        // If no effects produced any specific permission, check general access.
        if required_actions.is_empty() {
            let access_req = target_cell
                .permissions
                .for_action(dregg_cell::permissions::Action::Access);
            self.check_single_auth_requirement(
                action,
                target_cell,
                ledger,
                actor_cell_id,
                access_req,
                "Access",
                path,
                turn_nonce,
            )?;
        } else {
            // Check EACH permission requirement independently. This avoids the
            // is_narrower_or_equal partial-order problem where Signature vs Proof
            // are incomparable and the "most restrictive" finder could pick wrong.
            for (perm_action, action_name) in &required_actions {
                let auth_req = target_cell.permissions.for_action(*perm_action);
                self.check_single_auth_requirement(
                    action,
                    target_cell,
                    ledger,
                    actor_cell_id,
                    auth_req,
                    action_name,
                    path,
                    turn_nonce,
                )?;
            }
        }

        // Additionally, check Receive permission on transfer destinations.
        for effect in &action.effects {
            if let Effect::Transfer { to, .. } = effect {
                if let Some(dest_cell) = ledger.get(to) {
                    let receive_req = dest_cell
                        .permissions
                        .for_action(dregg_cell::permissions::Action::Receive);
                    if matches!(receive_req, AuthRequired::Impossible) {
                        return Err((
                            TurnError::PermissionDenied {
                                cell: *to,
                                action: "Receive".to_string(),
                                required: AuthRequired::Impossible,
                            },
                            path.to_vec(),
                        ));
                    }
                    if !matches!(receive_req, AuthRequired::None) {
                        return Err((
                            TurnError::PermissionDenied {
                                cell: *to,
                                action: "Receive".to_string(),
                                required: receive_req.clone(),
                            },
                            path.to_vec(),
                        ));
                    }
                }
            }
        }

        // Studio trace: authorization verified (Signature / Proof / Breadstuff / Unchecked).
        // The auth_kind discriminator matches the observability schema (observability/src/events.rs §AuthorizationPayload).
        let auth_kind = match &action.authorization {
            Authorization::Signature(_, _) => "signature",
            Authorization::Proof { .. } => "proof",
            Authorization::Breadstuff(_) => "breadstuff",
            Authorization::Unchecked => "unchecked",
            Authorization::Custom { .. } => "custom",
            _ => "other",
        };
        info!(kind = "authorization", auth_kind, target = %action.target);
        Ok(())
    }

    /// Verify a CapTP-delivered authorization.
    ///
    /// Closes the receipt-mirror loop (Seam 3, GAP-12/13): every CapTP wire
    /// delivery carries proof of (a) introducer signing the handoff cert and
    /// (b) the recipient signing this specific Turn. Both are checked here
    /// before the executor commits the mirroring effects.
    pub(super) fn verify_captp_delivered(
        &self,
        action: &Action,
        handoff_cert: &dregg_captp::HandoffCertificate,
        introducer_pk: &[u8; 32],
        sender_pk: &[u8; 32],
        sender_signature: &[u8; 64],
        turn_nonce: u64,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // 1. Sender pk must match the certificate's recipient pk.
        if sender_pk != &handoff_cert.recipient_pk {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: "captp-delivered: sender_pk does not match cert.recipient_pk"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }

        // 2. The cert must target this federation and this action's cell. The
        // cert's introducer is a federation identity; introducer_pk is the
        // concrete committee/signer key that verifies the cert.
        if handoff_cert.target_federation.0 != self.local_federation_id {
            return Err((
                TurnError::InvalidAuthorization {
                    reason:
                        "captp-delivered: cert.target_federation does not match local federation"
                            .to_string(),
                },
                path.to_vec(),
            ));
        }
        if handoff_cert.target_cell != action.target {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: "captp-delivered: cert.target_cell does not match action target"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }

        // 3. Verify the introducer signature on the certificate.
        let intro_pk_wrapper = dregg_types::PublicKey(*introducer_pk);
        if !handoff_cert.verify_signature(&intro_pk_wrapper) {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: "captp-delivered: introducer signature on handoff cert is invalid"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }

        // 4. Verify the sender signature over the canonical CapTP-delivery message.
        let agent_for_msg = path
            .first()
            .copied()
            .map(|_| action.target) // path-driven; sender binds to action.target as below
            .unwrap_or(action.target);
        // Currently the message binds target only; agent is enforced via the Turn-level path.
        let _ = agent_for_msg;
        // The signing message binds: federation_id, cert.nonce, agent (= target_cell of this
        // action's immediate frame), action.target, turn_nonce, and serialized effects.
        // We use action.target as both "agent" and "target" here because at the
        // wire-construction site the agent cell IS the gateway and the action's
        // target IS the cell being mutated. The wire builder computes this exact
        // message; the executor recomputes it from the on-chain Turn.
        let message = Authorization::captp_delivered_signing_message_for_federation(
            &self.local_federation_id,
            &handoff_cert.nonce,
            &action.target,
            &action.target,
            turn_nonce,
            &action.effects,
        );
        let sender_verifying = VerifyingKey::from_bytes(sender_pk).map_err(|_| {
            (
                TurnError::InvalidAuthorization {
                    reason: "captp-delivered: sender_pk is not a valid Ed25519 point".to_string(),
                },
                path.to_vec(),
            )
        })?;
        let sig = Signature::from_bytes(sender_signature);
        sender_verifying
            .verify_strict(&message, &sig)
            .map_err(|_| {
                (
                    TurnError::InvalidAuthorization {
                        reason: "captp-delivered: sender signature verification failed".to_string(),
                    },
                    path.to_vec(),
                )
            })?;

        // 5. If the cert restricts allowed_effects, enforce the mask.
        if let Some(mask) = handoff_cert.allowed_effects {
            let effects_mask = action
                .effects
                .iter()
                .fold(0u32, |acc, e| acc | e.effect_kind_mask());
            if effects_mask != 0 && effects_mask & mask != effects_mask {
                return Err((
                    TurnError::InvalidAuthorization {
                        reason: format!(
                            "captp-delivered: action effects mask {effects_mask:#x} not within \
                             cert.allowed_effects {mask:#x}"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        }

        // 6. Expiration check.
        if !handoff_cert.is_valid(self.block_height) {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: "captp-delivered: handoff cert has expired".to_string(),
                },
                path.to_vec(),
            ));
        }

        // 7. Block1-bind closure (BLOCK1-BIND-CLOSURE-NOTES.md
        // `ValidateHandoff-runtime-variant-extend`): any
        // `Effect::ValidateHandoff` carried in this action must declare
        // the same `(recipient_pk, introducer_pk)` as the carrying
        // CapTpDelivered cert. Without this check, the AIR's
        // PI-bound `(recipient_pk, introducer_pk)` could carry forged
        // values while the cert's keys (verified above) carry the real
        // ones — the per-effect proof would then bind values that
        // never matched the cryptographic origin.
        for effect in &action.effects {
            if let Effect::ValidateHandoff {
                cert_hash: _,
                recipient_pk: effect_recipient,
                introducer_pk: effect_introducer,
            } = effect
            {
                if effect_recipient != &handoff_cert.recipient_pk {
                    return Err((
                        TurnError::InvalidAuthorization {
                            reason: "captp-delivered: Effect::ValidateHandoff.recipient_pk does \
                                     not match cert.recipient_pk"
                                .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                if effect_introducer != introducer_pk {
                    return Err((
                        TurnError::InvalidAuthorization {
                            reason: "captp-delivered: Effect::ValidateHandoff.introducer_pk does \
                                     not match cert.introducer"
                                .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        Ok(())
    }

    /// Verify a `WitnessedPredicate`-backed authorization
    /// (`Authorization::Custom`).
    ///
    /// Flow (AUTHORIZATION-CUSTOM-DESIGN §2):
    /// 1. **Cell consistency check.** If the target cell declares
    ///    `AuthRequired::Custom { vk_hash }` for any action it needs to
    ///    authorize, the predicate's kind MUST match
    ///    `WitnessedPredicateKind::Custom { vk_hash }` with the same
    ///    `vk_hash`.
    /// 2. **Registry lookup.** Resolve `predicate.kind` in
    ///    `self.witnessed_registry`. On miss → `AuthModeNotRegistered`.
    ///    No silent fallback.
    /// 3. **Input binding.** When `predicate.input_ref ==
    ///    InputRef::SigningMessage`, supply
    ///    `compute_partial_signing_message(action, position,
    ///    federation_id, turn_nonce)` — the same federation+nonce
    ///    binding the `Signature` path uses. Other `input_ref` shapes
    ///    are unsupported in auth context: the design specifies
    ///    SigningMessage as THE auth input.
    /// 4. **Proof bytes.** Resolved from
    ///    `action.witness_blobs[predicate.proof_witness_index]`.
    /// 5. **Verifier call.** On reject → `InvalidAuthorization`.
    ///
    /// Replay carries forward identically to the `Signature` path: the
    /// canonical signing message is recomputed from on-chain Turn
    /// fields, so receipts re-verify deterministically.
    pub(super) fn verify_custom_authorization(
        &self,
        action: &Action,
        target_cell: &Cell,
        predicate: &dregg_cell::WitnessedPredicate,
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        // Step 1: cell-side AuthRequired::Custom consistency check.
        // If any of the cell's permission slots demand a specific
        // Custom vk_hash, the predicate's kind must agree.
        let required_vk: Option<[u8; 32]> = {
            let candidates = [
                &target_cell.permissions.send,
                &target_cell.permissions.receive,
                &target_cell.permissions.set_state,
                &target_cell.permissions.set_permissions,
                &target_cell.permissions.set_verification_key,
                &target_cell.permissions.increment_nonce,
                &target_cell.permissions.delegate,
                &target_cell.permissions.access,
            ];
            candidates.iter().find_map(|req| match req {
                AuthRequired::Custom { vk_hash } => Some(*vk_hash),
                _ => None,
            })
        };
        if let Some(required) = required_vk {
            match predicate.kind {
                WitnessedPredicateKind::Custom { vk_hash } if vk_hash == required => {}
                _ => {
                    return Err((
                        TurnError::PermissionDenied {
                            cell: action.target,
                            action: "Custom".to_string(),
                            required: AuthRequired::Custom { vk_hash: required },
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        // Step 2: registry lookup. Failing closed: if the executor has
        // no registry, or the kind isn't in it, reject.
        let registry = self.witnessed_registry.as_ref().ok_or_else(|| {
            (
                TurnError::AuthModeNotRegistered {
                    kind: predicate_kind_name(predicate.kind),
                    vk_hash: predicate_kind_vk_hash(predicate.kind),
                },
                path.to_vec(),
            )
        })?;
        if registry.get(predicate.kind).is_none() {
            return Err((
                TurnError::AuthModeNotRegistered {
                    kind: predicate_kind_name(predicate.kind),
                    vk_hash: predicate_kind_vk_hash(predicate.kind),
                },
                path.to_vec(),
            ));
        }

        // Step 3: build the canonical signing message bytes.
        //
        // We use `compute_custom_signing_message` rather than the
        // Signature path's `compute_partial_signing_message` because
        // the latter hashes `action.hash()`, which itself hashes
        // `action.witness_blobs` — and `witness_blobs` contains the
        // very proof bytes the predicate's verifier is checking. That
        // would be circular at proof-generation time (the cclerk would
        // need the proof bytes to compute the message that the proof
        // commits to).
        //
        // `compute_custom_signing_message` binds:
        //   * federation_id  — T6 cross-federation replay defense
        //   * turn_nonce     — T11 stale-proof defense
        //   * position       — multi-action turn placement binding
        //   * target / method / args / effects-hashes / preconditions
        //                    — T2 forge-effects defense
        //   * predicate's *structural* shape (kind/commitment/input_ref/
        //     proof_witness_index) but NOT the proof bytes in
        //     witness_blobs.
        //
        // This is the design's "federation_id + nonce + action hash"
        // intent (AUTHORIZATION-CUSTOM-DESIGN §2 step 4), correctly
        // unfolded to break the witness-blob circularity.
        let position = path.first().copied().unwrap_or(0);
        let signing_message = Self::compute_custom_signing_message(
            action,
            predicate,
            position,
            &self.local_federation_id,
            turn_nonce,
        );

        // Step 4: resolve proof bytes from witness_blobs by index.
        let proof_blob = action
            .witness_blobs
            .get(predicate.proof_witness_index)
            .ok_or_else(|| {
                (
                    TurnError::InvalidAuthorization {
                        reason: format!(
                            "Authorization::Custom proof_witness_index {} out of bounds \
                             (witness_blobs.len()={})",
                            predicate.proof_witness_index,
                            action.witness_blobs.len()
                        ),
                    },
                    path.to_vec(),
                )
            })?;

        // Step 5: dispatch. We support InputRef::SigningMessage as the
        // canonical input shape for auth; other shapes are rejected at
        // this surface (slot-caveat / precondition surfaces have their
        // own input resolution).
        let input = match &predicate.input_ref {
            InputRef::SigningMessage => PredicateInput::SigningMessage(&signing_message),
            other => {
                return Err((
                    TurnError::InvalidAuthorization {
                        reason: format!(
                            "Authorization::Custom requires InputRef::SigningMessage, got {other:?}"
                        ),
                    },
                    path.to_vec(),
                ));
            }
        };

        registry
            .verify(predicate, &input, &proof_blob.bytes)
            .map_err(|e| match e {
                WitnessedPredicateError::KindNotRegistered { kind } => (
                    TurnError::AuthModeNotRegistered {
                        kind: predicate_kind_name(kind),
                        vk_hash: predicate_kind_vk_hash(kind),
                    },
                    path.to_vec(),
                ),
                other => (
                    TurnError::InvalidAuthorization {
                        reason: format!("Custom auth predicate rejected: {other}"),
                    },
                    path.to_vec(),
                ),
            })?;

        Ok(())
    }

    /// Check a single auth requirement against an action's authorization.
    pub(super) fn check_single_auth_requirement(
        &self,
        action: &Action,
        target_cell: &Cell,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        auth_required: &AuthRequired,
        action_name: &str,
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        match auth_required {
            AuthRequired::None => Ok(()),
            AuthRequired::Impossible => Err((
                TurnError::PermissionDenied {
                    cell: action.target,
                    action: action_name.to_string(),
                    required: AuthRequired::Impossible,
                },
                path.to_vec(),
            )),
            AuthRequired::Signature => match &action.authorization {
                Authorization::Signature(r, s) => {
                    self.verify_ed25519_signature(action, target_cell, r, s, path, turn_nonce)
                }
                // Stealth one-time signatures satisfy a Signature
                // requirement; the relation was already verified in
                // `verify_authorization` (fail-closed) before falling
                // through here. Re-verify to keep this arm self-contained
                // and defend against any future caller that reaches it
                // without the early check.
                Authorization::Stealth { .. } => {
                    self.verify_stealth_authorization(action, target_cell, path, turn_nonce)
                }
                Authorization::Breadstuff(token) => {
                    let effects_mask = action
                        .effects
                        .iter()
                        .fold(0u32, |acc, e| acc | e.effect_kind_mask());
                    self.check_breadstuff(
                        ledger,
                        actor_cell_id,
                        token,
                        action_name,
                        auth_required,
                        path,
                        action.target,
                        effects_mask,
                    )
                }
                _ => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Signature,
                    },
                    path.to_vec(),
                )),
            },
            // NOTE on revocation checking for Proof auth:
            // ZK proofs are anonymous — the verifier cannot determine WHICH capability
            // the prover used, so per-capability revocation cannot be enforced at
            // verification time. Revocation for ZK-authorized actions must be proven
            // at proof-generation time (the circuit must include a non-revocation check
            // as part of its public inputs). This is an inherent limitation of the
            // ZK auth model and is by design.
            AuthRequired::Proof => match &action.authorization {
                Authorization::Proof {
                    proof_bytes,
                    bound_action,
                    bound_resource,
                } => self.verify_zk_proof(
                    target_cell,
                    proof_bytes,
                    bound_action,
                    bound_resource,
                    path,
                ),
                _ => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Proof,
                    },
                    path.to_vec(),
                )),
            },
            AuthRequired::Custom { vk_hash } => {
                // The cell requires app-defined Custom auth with this
                // specific vk_hash. Because `Authorization::Custom`
                // short-circuits in `verify_authorization`, reaching
                // here means the action did NOT supply Custom auth —
                // reject.
                //
                // (The vk_hash match-up — predicate.kind's vk_hash ==
                // cell's required vk_hash — is enforced in
                // `verify_custom_authorization` when the Custom path
                // does run.)
                let _ = vk_hash;
                Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: auth_required.clone(),
                    },
                    path.to_vec(),
                ))
            }
            AuthRequired::Either => match &action.authorization {
                Authorization::Signature(r, s) => {
                    self.verify_ed25519_signature(action, target_cell, r, s, path, turn_nonce)
                }
                Authorization::Proof {
                    proof_bytes,
                    bound_action,
                    bound_resource,
                } => self.verify_zk_proof(
                    target_cell,
                    proof_bytes,
                    bound_action,
                    bound_resource,
                    path,
                ),
                Authorization::Breadstuff(token) => {
                    let effects_mask = action
                        .effects
                        .iter()
                        .fold(0u32, |acc, e| acc | e.effect_kind_mask());
                    self.check_breadstuff(
                        ledger,
                        actor_cell_id,
                        token,
                        action_name,
                        auth_required,
                        path,
                        action.target,
                        effects_mask,
                    )
                }
                Authorization::Bearer(proof) => self.verify_bearer_cap(proof, ledger, path),
                Authorization::Stealth { .. } => {
                    self.verify_stealth_authorization(action, target_cell, path, turn_nonce)
                }
                // Token is short-circuited in verify_authorization; if we
                // reach here the early-return was bypassed: treat as deny.
                Authorization::Token { .. } => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Either,
                    },
                    path.to_vec(),
                )),
                Authorization::Unchecked => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Either,
                    },
                    path.to_vec(),
                )),
                // CapTpDelivered is verified holistically in `verify_authorization`
                // and short-circuits before reaching this point. If we ever reach
                // here it means the early-return was bypassed: treat as deny.
                Authorization::CapTpDelivered { .. } => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Either,
                    },
                    path.to_vec(),
                )),
                // Authorization::Custom: defer to the witnessed-predicate
                // dispatch path. The `AuthRequired::Either` permission
                // accepts Custom only when the cell explicitly declares
                // it via `AuthRequired::Custom`; if a cell declared
                // `Either`, we treat Custom as a deny (the cell-program
                // / authorization path that wants Custom semantics
                // should declare `AuthRequired::Custom { vk_hash }`
                // directly).
                Authorization::Custom { .. } => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Either,
                    },
                    path.to_vec(),
                )),
                // OneOf is short-circuited in verify_authorization;
                // reaching here means a bug — treat as deny.
                Authorization::OneOf { .. } => Err((
                    TurnError::PermissionDenied {
                        cell: action.target,
                        action: action_name.to_string(),
                        required: AuthRequired::Either,
                    },
                    path.to_vec(),
                )),
            },
        }
    }

    /// Verify an Ed25519 signature against the target cell's public key.
    ///
    /// When the action uses `CommitmentMode::Partial`, the signing message is computed
    /// via `compute_partial_signing_message` (action hash + position + federation_id + nonce).
    /// This allows composed turns with partial signers to be verified correctly by the executor.
    pub(super) fn verify_ed25519_signature(
        &self,
        action: &Action,
        target_cell: &Cell,
        r: &[u8; 32],
        s: &[u8; 32],
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use crate::action::CommitmentMode;

        let message = match action.commitment_mode {
            CommitmentMode::Partial => {
                // For partial commitment, the signer committed to their action hash + position
                // + federation_id + turn_nonce.
                // The position is encoded in the path (root index).
                let position = path.first().copied().unwrap_or(0);
                Self::compute_partial_signing_message(
                    action,
                    position,
                    &self.local_federation_id,
                    turn_nonce,
                )
            }
            CommitmentMode::Full => {
                Self::compute_signing_message(action, &self.local_federation_id)
            }
        };

        let mut sig_bytes = [0u8; 64];
        sig_bytes[..32].copy_from_slice(r);
        sig_bytes[32..].copy_from_slice(s);

        let signature = Signature::from_bytes(&sig_bytes);

        let verifying_key = VerifyingKey::from_bytes(&target_cell.public_key()).map_err(|_| {
            (
                TurnError::InvalidAuthorization {
                    reason: "cell public key is not a valid Ed25519 point".to_string(),
                },
                path.to_vec(),
            )
        })?;

        verifying_key
            .verify_strict(&message, &signature)
            .map_err(|_| {
                (
                    TurnError::InvalidAuthorization {
                        reason: "Ed25519 signature verification failed".to_string(),
                    },
                    path.to_vec(),
                )
            })
    }

    /// Verify a ZK proof against the target cell's verification key.
    ///
    /// Uses the `bound_action` and `bound_resource` that were committed to at
    /// proving time (carried in the `Authorization::Proof` variant) rather than
    /// deriving from the action's method/target. This ensures the verifier checks
    /// against the same binding the prover created.
    pub(super) fn verify_zk_proof(
        &self,
        target_cell: &Cell,
        proof_bytes: &[u8],
        bound_action: &str,
        bound_resource: &str,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        if proof_bytes.is_empty() {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: "proof bytes are empty".to_string(),
                },
                path.to_vec(),
            ));
        }
        if proof_bytes.len() > 65536 {
            return Err((
                TurnError::InvalidAuthorization {
                    reason: format!("proof too large: {} bytes (max 65536)", proof_bytes.len()),
                },
                path.to_vec(),
            ));
        }

        let vk = target_cell.verification_key.as_ref().ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "cell requires proof but has no verification key".to_string(),
                },
                path.to_vec(),
            )
        })?;

        let verifier = self.proof_verifier.as_ref().ok_or_else(|| {
            (
                TurnError::InvalidAuthorization {
                    reason: "no proof verifier configured (fail-closed)".to_string(),
                },
                path.to_vec(),
            )
        })?;

        if verifier.verify(proof_bytes, bound_action, bound_resource, &vk.data) {
            Ok(())
        } else {
            Err((
                TurnError::InvalidAuthorization {
                    reason: "ZK proof verification failed".to_string(),
                },
                path.to_vec(),
            ))
        }
    }

    /// Check breadstuff (capability token) authorization.
    ///
    /// The breadstuff token must be held in the ACTOR's (parent cell's) capability
    /// list, not the target's. The actor presents a breadstuff token they hold as
    /// proof of their authority to act on the target cell. The matching capability
    /// must also reference the action's target cell (target-scoped).
    ///
    /// Beyond existence, this now enforces:
    /// - Expiry: the capability's `expires_at` must not have passed.
    /// - Revocation: if the capability's breadstuff matches a revocation channel, it
    ///   must not be tripped.
    /// - Facets: if the capability has `allowed_effects`, the action's effects must
    ///   be within the mask.
    pub(super) fn check_breadstuff(
        &self,
        ledger: &Ledger,
        actor_cell_id: &CellId,
        token: &[u8; 32],
        action_name: &str,
        auth_required: &AuthRequired,
        path: &[usize],
        target_id: CellId,
        effects_mask: dregg_cell::EffectMask,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        let actor_cell = ledger.get(actor_cell_id).ok_or_else(|| {
            (
                TurnError::CellNotFound { id: *actor_cell_id },
                path.to_vec(),
            )
        })?;

        // Find the SPECIFIC matching capability (not just any-match).
        let matching_cap = actor_cell
            .capabilities
            .iter()
            .find(|cap| cap.breadstuff.as_ref() == Some(token) && cap.target == target_id);

        let cap = matching_cap.ok_or_else(|| {
            (
                TurnError::PermissionDenied {
                    cell: target_id,
                    action: action_name.to_string(),
                    required: auth_required.clone(),
                },
                path.to_vec(),
            )
        })?;

        // Check expiry: if the capability has an expires_at, it must not have passed.
        if let Some(expires_at) = cap.expires_at {
            if self.block_height > expires_at {
                return Err((
                    TurnError::BreadstuffExpired {
                        actor: *actor_cell_id,
                        target: target_id,
                        expires_at,
                        current_height: self.block_height,
                    },
                    path.to_vec(),
                ));
            }
        }

        // Check facet (allowed_effects): if the capability restricts effects, the
        // action's combined effects mask must be within the allowed set.
        if let Some(mask) = cap.allowed_effects {
            if mask != 0 && effects_mask != 0 {
                // Any bit in effects_mask that is NOT in the cap's mask is a violation.
                if effects_mask & mask != effects_mask {
                    return Err((
                        TurnError::BreadstuffFacetViolation {
                            actor: *actor_cell_id,
                            target: target_id,
                            attempted_effects_mask: effects_mask,
                            allowed_mask: mask,
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        // Check revocation channel: if the breadstuff matches a registered revocation
        // channel, verify the channel hasn't been tripped.
        if let Some(ref channels) = self.revocation_channels {
            if let Err(_) = channels.check_exercise_permitted(
                token,
                self.block_height,
                self.block_height,
                self.max_introduction_lifetime,
            ) {
                // Only reject if this is actually a registered channel (not just any breadstuff).
                if channels.get(token).is_some() {
                    return Err((
                        TurnError::BreadstuffRevoked {
                            actor: *actor_cell_id,
                            target: target_id,
                            channel_id: *token,
                        },
                        path.to_vec(),
                    ));
                }
            }
        }

        Ok(())
    }

    /// Verify a bearer capability proof: the parallel authorization path for capabilities
    /// NOT in the actor's c-list but proven via delegation chain.
    pub fn verify_bearer_cap(
        &self,
        proof: &crate::action::BearerCapProof,
        ledger: &Ledger,
        path: &[usize],
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use crate::action::DelegationProofData;
        if self.block_height > proof.expires_at {
            return Err((
                TurnError::BearerCapExpired {
                    target: proof.target,
                    expires_at: proof.expires_at,
                    current_height: self.block_height,
                },
                path.to_vec(),
            ));
        }
        if let Some(channel_id) = &proof.revocation_channel {
            if let Some(ref channels) = self.revocation_channels {
                if channels
                    .check_exercise_permitted(
                        channel_id,
                        self.block_height,
                        self.block_height,
                        self.max_introduction_lifetime,
                    )
                    .is_err()
                {
                    return Err((
                        TurnError::BearerCapRevoked {
                            target: proof.target,
                            channel_id: *channel_id,
                        },
                        path.to_vec(),
                    ));
                }
            } else {
                return Err((
                    TurnError::BearerCapRevoked {
                        target: proof.target,
                        channel_id: *channel_id,
                    },
                    path.to_vec(),
                ));
            }
        }
        match &proof.delegation_proof {
            DelegationProofData::SignedDelegation {
                delegator_pk,
                signature,
                bearer_pk,
            } => {
                let message = Self::compute_bearer_delegation_message(
                    &proof.target,
                    &proof.permissions,
                    bearer_pk,
                    proof.expires_at,
                    &self.local_federation_id,
                );
                let vk = VerifyingKey::from_bytes(delegator_pk).map_err(|_| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: "invalid delegator public key".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                let sig = Signature::from_bytes(signature);
                vk.verify_strict(&message, &sig).map_err(|_| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: "delegation signature verification failed".to_string(),
                        },
                        path.to_vec(),
                    )
                })?;
                let delegator_cell = ledger
                    .iter()
                    .find(|(_, cell)| *cell.public_key() == *delegator_pk)
                    .map(|(_, cell)| cell);
                let delegator_cell = delegator_cell.ok_or_else(|| {
                    (
                        TurnError::BearerCapDelegatorLacksCapability {
                            delegator: CellId::from_bytes(*delegator_pk),
                            target: proof.target,
                        },
                        path.to_vec(),
                    )
                })?;
                if !Self::has_access_including_delegation_at(
                    delegator_cell,
                    &proof.target,
                    self.block_height,
                ) {
                    return Err((
                        TurnError::BearerCapDelegatorLacksCapability {
                            delegator: delegator_cell.id(),
                            target: proof.target,
                        },
                        path.to_vec(),
                    ));
                }
                let delegator_cap = delegator_cell
                    .capabilities
                    .capabilities_for(&proof.target)
                    .into_iter()
                    .find(|cap| cap.permissions != AuthRequired::Impossible);
                if let Some(cap) = delegator_cap {
                    if !proof.permissions.is_narrower_or_equal(&cap.permissions) {
                        return Err((
                            TurnError::BearerCapAmplification {
                                target: proof.target,
                                delegator_permissions: cap.permissions.clone(),
                                bearer_permissions: proof.permissions.clone(),
                            },
                            path.to_vec(),
                        ));
                    }

                    // Facet attenuation check: if the delegator's capability has a facet
                    // restriction, the bearer's facet (if any) must be a subset.
                    // If the bearer doesn't specify a facet, it inherits the delegator's.
                    // If the delegator has no facet, the bearer can specify any facet.
                    if let Some(delegator_mask) = cap.allowed_effects {
                        if delegator_mask != 0 {
                            if let Some(bearer_mask) = proof.allowed_effects {
                                // Bearer specifies a facet — it must be a subset of delegator's.
                                if !dregg_cell::is_facet_attenuation(delegator_mask, bearer_mask) {
                                    return Err((
                                        TurnError::BearerCapFacetAmplification {
                                            target: proof.target,
                                            delegator_mask,
                                            bearer_mask,
                                        },
                                        path.to_vec(),
                                    ));
                                }
                            }
                            // If bearer doesn't specify a facet (None), it inherits the
                            // delegator's mask. The effective facet is enforced at execution
                            // time via the returned Ok + caller checking proof.allowed_effects
                            // OR delegator_cap.allowed_effects.
                        }
                    }
                }
                Ok(())
            }
            DelegationProofData::StarkDelegation {
                proof_bytes,
                root_issuer_commitment,
            } => {
                use dregg_circuit::field::BabyBear;
                use dregg_circuit::stark;
                let stark_proof = stark::proof_from_bytes(proof_bytes).map_err(|e| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: format!("STARK proof deserialization failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                let mut public_inputs: Vec<BabyBear> = Vec::new();
                public_inputs.extend(Self::bytes32_to_babybear(root_issuer_commitment));
                public_inputs.extend(Self::bytes32_to_babybear(proof.target.as_bytes()));
                // Goal-2 hardening (anonymous delegation): bind the
                // *exercised scope* into the proof's public inputs so a
                // relay cannot reuse a valid proof for a wider grant.
                // The delegator/bearer pubkeys are deliberately NOT
                // bound (they stay hidden behind `root_issuer_commitment`
                // — that is the whole point of the anonymous path); only
                // the permission tier, the expiry, and the federation id
                // are bound, all of which are public on the turn anyway.
                let perm_tag: u32 = match &proof.permissions {
                    AuthRequired::None => 0,
                    AuthRequired::Signature => 1,
                    AuthRequired::Proof => 2,
                    AuthRequired::Either => 3,
                    AuthRequired::Impossible => 4,
                    AuthRequired::Custom { .. } => 5,
                };
                let scope_hash = {
                    let mut h = blake3::Hasher::new();
                    h.update(b"dregg-stark-delegation-scope-v1:");
                    h.update(&self.local_federation_id);
                    h.update(&perm_tag.to_le_bytes());
                    if let AuthRequired::Custom { vk_hash } = &proof.permissions {
                        h.update(vk_hash);
                    }
                    h.update(&proof.expires_at.to_le_bytes());
                    *h.finalize().as_bytes()
                };
                public_inputs.extend(Self::bytes32_to_babybear(&scope_hash));
                if stark_proof.public_inputs.len() < public_inputs.len() {
                    return Err((
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: format!(
                                "STARK proof has {} public inputs, expected at least {}",
                                stark_proof.public_inputs.len(),
                                public_inputs.len()
                            ),
                        },
                        path.to_vec(),
                    ));
                }
                for (i, expected) in public_inputs.iter().enumerate() {
                    if BabyBear(stark_proof.public_inputs[i]) != *expected {
                        return Err((
                            TurnError::BearerCapInvalidProof {
                                target: proof.target,
                                reason: format!("STARK public input mismatch at index {i}"),
                            },
                            path.to_vec(),
                        ));
                    }
                }
                let air = dregg_circuit::EffectVmAir::new(stark_proof.trace_len);
                stark::verify(&air, &stark_proof, &public_inputs).map_err(|e| {
                    (
                        TurnError::BearerCapInvalidProof {
                            target: proof.target,
                            reason: format!("STARK proof verification failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                Ok(())
            }
        }
    }

    /// Verify a [`Authorization::Stealth`] one-time-key authorization
    /// (anonymity-of-actor goal 1).
    ///
    /// The on-chain turn carries only `(one_time_pubkey P, ephemeral_pubkey
    /// R, blinding_scalar c, signature)`. The persistent spend public key
    /// `S` is the *target cell's* public key and never appears in the turn.
    /// We check the stealth-spend relation
    ///   `P == c·G + S`
    /// using Ed25519 point arithmetic (no Diffie-Hellman / view key needed
    /// at verify time — this mirrors `cell::stealth::derive_one_time_pubkey`,
    /// where `P = derive_stealth_scalar(shared)·G + S` and the signer holds
    /// `k = derive_stealth_scalar(shared) + s`). Then we verify `signature`
    /// under `P` over [`Authorization::stealth_signing_message`].
    ///
    /// ## Why this is sound
    /// Forging a valid signature under any `P = c·G + S` requires knowing the
    /// discrete log of `S` (the spend scalar `s`), because the one-time
    /// secret key is `k = c + s`. An adversary who only knows the public `S`
    /// cannot produce a valid signature. `c` is bound into `P` and into the
    /// signing message, so a relay cannot substitute a different `c`.
    ///
    /// ## Unlinkability
    /// `c` is `derive_stealth_scalar(H(r·V))` for a fresh ephemeral `r` per
    /// call, so `P`, `R`, and `c` look independently random across calls and
    /// reveal nothing tying two turns to the same `S` (the persistent
    /// identity) to a turn-stream observer.
    ///
    /// ## Replay
    /// The signing message binds `federation_id` + `turn_nonce` + position +
    /// `action.hash()`, so a stealth authorization for one (federation,
    /// nonce, action) does not re-verify against another. Same-turn
    /// resubmission is rejected by the per-agent receipt-chain / nonce gate.
    pub(super) fn verify_stealth_authorization(
        &self,
        action: &Action,
        target_cell: &Cell,
        path: &[usize],
        turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
        use curve25519_dalek::edwards::CompressedEdwardsY;
        use curve25519_dalek::scalar::Scalar;

        let (one_time_pubkey, ephemeral_pubkey, blinding_scalar, signature) =
            match &action.authorization {
                Authorization::Stealth {
                    one_time_pubkey,
                    ephemeral_pubkey,
                    blinding_scalar,
                    signature,
                } => (
                    one_time_pubkey,
                    ephemeral_pubkey,
                    blinding_scalar,
                    signature,
                ),
                _ => {
                    return Err((
                        TurnError::StealthAuthInvalid {
                            reason: "verify_stealth_authorization called on non-Stealth auth"
                                .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
            };

        // S = the target cell's persistent spend public key (Ed25519).
        let spend_pubkey = target_cell.public_key();
        let spend_point = CompressedEdwardsY(*spend_pubkey)
            .decompress()
            .ok_or_else(|| {
                (
                    TurnError::StealthAuthInvalid {
                        reason: "target cell public key is not a valid Ed25519 point".to_string(),
                    },
                    path.to_vec(),
                )
            })?;

        // Recompute P' = c·G + S and require it equals the carried one-time
        // pubkey. `Scalar::from_bytes_mod_order` matches the reduction
        // `cell::stealth` uses when deriving the one-time key, so an honest
        // prover's `c` reproduces the exact `P` they signed under.
        let c = Scalar::from_bytes_mod_order(*blinding_scalar);
        let expected_point = (&c * ED25519_BASEPOINT_TABLE) + spend_point;
        let expected_p = expected_point.compress().to_bytes();
        if &expected_p != one_time_pubkey {
            return Err((
                TurnError::StealthAuthInvalid {
                    reason: "one-time pubkey does not match c·G + S (stealth-spend relation \
                             failed): the signer does not control the cell's spend key"
                        .to_string(),
                },
                path.to_vec(),
            ));
        }

        // Verify the one-time signature under P over the bound message.
        let position = path.first().copied().unwrap_or(0);
        let message = Authorization::stealth_signing_message(
            &self.local_federation_id,
            &action.hash(),
            ephemeral_pubkey,
            blinding_scalar,
            position,
            turn_nonce,
        );
        let verifying_key = VerifyingKey::from_bytes(one_time_pubkey).map_err(|_| {
            (
                TurnError::StealthAuthInvalid {
                    reason: "one-time pubkey is not a valid Ed25519 verifying key".to_string(),
                },
                path.to_vec(),
            )
        })?;
        let sig = Signature::from_bytes(signature);
        verifying_key.verify_strict(&message, &sig).map_err(|_| {
            (
                TurnError::StealthAuthInvalid {
                    reason: "one-time signature verification failed".to_string(),
                },
                path.to_vec(),
            )
        })?;

        info!(
            kind = "authorization",
            auth_kind = "stealth",
            target = %action.target,
        );
        Ok(())
    }

    /// Build the deterministic [`dregg_token::AuthRequest`] that binds a
    /// presented token to THIS call (TOKEN-CAPABILITY-UNIFICATION.md step 4).
    ///
    /// The binding facts are:
    /// - `action`  = the action's method symbol (hex of the 32-byte symbol).
    /// - `service` = the target cell id (hex) — the *resource* being called.
    /// - `app_id`  = the local federation id (hex) — domain / cross-federation
    ///   replay defense.
    /// - `now`     = the current **block height** (NOT wall-clock), so any
    ///   temporal caveat in the token is evaluated against consensus height.
    ///   This is what makes verification deterministic and expiry
    ///   block-height-bound.
    ///
    /// Replaying the token against a different action/cell/federation
    /// produces different facts, so the token's caveats / Datalog no longer
    /// authorize → the verify call denies. This mirrors `Proof`'s
    /// bound_action/bound_resource and `CapTpDelivered`'s signing message.
    fn token_auth_request(&self, action: &Action) -> dregg_token::AuthRequest {
        let mut req = dregg_token::AuthRequest::default();
        req.action = Some(hex::encode(action.method));
        req.service = Some(hex::encode(action.target.as_bytes()));
        req.app_id = Some(hex::encode(self.local_federation_id));
        // Deterministic, consensus-bound "now": the block height. Temporal
        // caveats reference this, never wall-clock.
        req.now = Some(self.block_height as i64);
        req
    }

    /// Verify a first-class [`Authorization::Token`] biscuit / macaroon
    /// credential (goal 3, TOKEN-CAPABILITY-UNIFICATION.md P1+P3).
    ///
    /// Flow (deterministic, fail-closed):
    /// 1. **Decode** the encoded credential (UTF-8 of the `eb2_`/`em2_`
    ///    string). Format is self-describing via the prefix.
    /// 2. **Resolve the root key + trust anchor** from `key_ref`:
    ///    - `BiscuitIssuer { issuer_pubkey }`: the issuer MUST be a granting
    ///      authority the target cell trusts. The trust anchor (no executor
    ///      field, fully cell-derived) is: the issuer pubkey equals the
    ///      target cell's `public_key` (the cell is its own granting
    ///      authority — "I minted this credential against my own key"), or
    ///      the cell's verification-key bytes. An untrusted issuer is
    ///      rejected even if the token verifies cryptographically.
    ///    - `CellScopedMacaroon { cell }`: `cell` MUST equal the target cell;
    ///      the root secret is derived deterministically from the cell id via
    ///      a domain-separated KDF. Cross-cell macaroons (secret not held)
    ///      are rejected because their HMAC will not verify under the derived
    ///      key.
    /// 3. **Cryptographically verify + caveat/Datalog evaluate** the token
    ///    against the call-bound `AuthRequest` (`AuthToken::verify`). A
    ///    crypto failure → `TokenAuthInvalid`; a policy/caveat denial (the
    ///    capability-cover check — the token does not grant this
    ///    action/resource) → `TokenInsufficientCapability`. Expiry-by-height
    ///    surfaces as a denial too (the time fact is the block height).
    ///
    /// Discharges (third-party caveats) are passed through for the macaroon
    /// path; biscuit third-party blocks are carried inside the token itself.
    pub(super) fn verify_token_authorization(
        &self,
        action: &Action,
        target_cell: &Cell,
        encoded: &[u8],
        key_ref: &crate::action::TokenKeyRef,
        discharges: &[Vec<u8>],
        path: &[usize],
        _turn_nonce: u64,
    ) -> Result<(), (TurnError, Vec<usize>)> {
        use crate::action::TokenKeyRef;
        use dregg_token::TokenFormat;
        use dregg_token::traits::AuthToken;

        let token_str = std::str::from_utf8(encoded).map_err(|_| {
            (
                TurnError::TokenAuthInvalid {
                    reason: "encoded token is not valid UTF-8".to_string(),
                },
                path.to_vec(),
            )
        })?;

        let fmt = TokenFormat::detect(token_str).map_err(|e| {
            (
                TurnError::TokenAuthInvalid {
                    reason: format!("token format detection failed: {e}"),
                },
                path.to_vec(),
            )
        })?;

        let request = self.token_auth_request(action);

        // Build the concrete token, resolving + trust-checking the root key.
        let token: Box<dyn AuthToken> = match (fmt, key_ref) {
            (TokenFormat::Biscuit, TokenKeyRef::BiscuitIssuer { issuer_pubkey }) => {
                // Trust anchor: the issuer must be one the target cell
                // authorizes. Field-free anchor — the cell is its own
                // granting authority, or names the issuer via its VK bytes.
                let cell_pk: [u8; 32] = *target_cell.public_key();
                let vk_match = target_cell
                    .verification_key
                    .as_ref()
                    .map(|vk| vk.data.as_slice() == issuer_pubkey.as_slice())
                    .unwrap_or(false);
                if &cell_pk != issuer_pubkey && !vk_match {
                    return Err((
                        TurnError::TokenAuthInvalid {
                            reason: "biscuit issuer is not a granting authority the target \
                                     cell trusts (must equal the cell's public key or its \
                                     verification key)"
                                .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                let pk = dregg_token::biscuit_auth::PublicKey::from_bytes(
                    issuer_pubkey,
                    dregg_token::biscuit_auth::Algorithm::Ed25519,
                )
                .map_err(|e| {
                    (
                        TurnError::TokenAuthInvalid {
                            reason: format!("biscuit issuer pubkey invalid: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                let bt = dregg_token::BiscuitToken::from_encoded(token_str, pk).map_err(|e| {
                    (
                        TurnError::TokenAuthInvalid {
                            reason: format!("biscuit decode/signature-check failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                Box::new(bt)
            }
            (TokenFormat::Macaroon, TokenKeyRef::CellScopedMacaroon { cell }) => {
                // Cell-scoped macaroon: the verifier may only hold the secret
                // for the target cell. Reject cross-cell key refs outright.
                if cell != &action.target {
                    return Err((
                        TurnError::TokenAuthInvalid {
                            reason: "cell-scoped macaroon key_ref does not name the action's \
                                     target cell; a macaroon is only sound where the verifier \
                                     legitimately holds the cell's secret"
                                .to_string(),
                        },
                        path.to_vec(),
                    ));
                }
                let root_key = self.derive_cell_macaroon_secret(&action.target);
                // Discharge macaroons are raw serialized bytes (NOT UTF-8
                // strings — the macaroon backend `deserialize`s them).
                let mt = if discharges.is_empty() {
                    dregg_token::MacaroonToken::from_encoded(token_str, root_key)
                } else {
                    dregg_token::MacaroonToken::from_encoded_with_discharges(
                        token_str, root_key, discharges,
                    )
                }
                .map_err(|e| {
                    (
                        TurnError::TokenAuthInvalid {
                            reason: format!("macaroon decode failed: {e}"),
                        },
                        path.to_vec(),
                    )
                })?;
                Box::new(mt)
            }
            (TokenFormat::Biscuit, TokenKeyRef::CellScopedMacaroon { .. }) => {
                return Err((
                    TurnError::TokenAuthInvalid {
                        reason: "token is a biscuit but key_ref is CellScopedMacaroon".to_string(),
                    },
                    path.to_vec(),
                ));
            }
            (TokenFormat::Macaroon, TokenKeyRef::BiscuitIssuer { .. }) => {
                return Err((
                    TurnError::TokenAuthInvalid {
                        reason: "token is a macaroon but key_ref is BiscuitIssuer".to_string(),
                    },
                    path.to_vec(),
                ));
            }
        };

        // Cryptographic verify + caveat/Datalog evaluation bound to THIS
        // call. A denial here IS the capability-cover failure: the token did
        // not grant the requested (action, resource) under its caveats.
        match token.verify(&request) {
            Ok(_clearance) => Ok(()),
            Err(dregg_token::TokenError::Denied(msg)) => Err((
                TurnError::TokenInsufficientCapability {
                    cell: action.target,
                    action: hex::encode(action.method),
                    reason: format!("token caveats/Datalog do not authorize this call: {msg}"),
                },
                path.to_vec(),
            )),
            Err(dregg_token::TokenError::Expired) => Err((
                TurnError::TokenInsufficientCapability {
                    cell: action.target,
                    action: hex::encode(action.method),
                    reason: "token expired by block height".to_string(),
                },
                path.to_vec(),
            )),
            Err(e) => Err((
                TurnError::TokenAuthInvalid {
                    reason: format!("token verification failed: {e}"),
                },
                path.to_vec(),
            )),
        }
    }

    /// Derive the deterministic, cell-scoped macaroon root secret.
    ///
    /// HMAC macaroons require the verifier to hold the root secret, so this
    /// path is only sound where the federation legitimately owns the cell's
    /// secret. The secret is a domain-separated BLAKE3 KDF over the local
    /// federation id + the cell id, so it is:
    /// - deterministic (no wall-clock / randomness — consensus-safe),
    /// - cell-scoped (a different cell yields a different secret, so a
    ///   macaroon minted for cell A cannot verify against cell B),
    /// - federation-scoped (cross-federation replay produces a different
    ///   secret).
    ///
    /// NOTE: this binds the macaroon secret to the federation that runs the
    /// turn. A macaroon minted against this derivation is a *cell-local*
    /// credential, exactly as TOKEN-CAPABILITY-UNIFICATION.md requires (no
    /// shared HMAC secret ever crosses domains; cross-domain auth must use a
    /// biscuit).
    fn derive_cell_macaroon_secret(&self, cell: &CellId) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-cell-macaroon-secret-v1");
        hasher.update(&self.local_federation_id);
        hasher.update(cell.as_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Compute the delegation message signed by a delegator for a bearer capability.
    pub fn compute_bearer_delegation_message(
        target: &CellId,
        permissions: &AuthRequired,
        bearer_pk: &[u8; 32],
        expires_at: u64,
        federation_id: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-bearer-delegation-v1:");
        hasher.update(federation_id);
        hasher.update(target.as_bytes());
        let perm_byte = match permissions {
            AuthRequired::None => 0u8,
            AuthRequired::Signature => 1u8,
            AuthRequired::Proof => 2u8,
            AuthRequired::Either => 3u8,
            AuthRequired::Impossible => 4u8,
            AuthRequired::Custom { .. } => 5u8,
        };
        hasher.update(&[perm_byte]);
        if let AuthRequired::Custom { vk_hash } = permissions {
            hasher.update(vk_hash);
        }
        hasher.update(bearer_pk);
        hasher.update(&expires_at.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Compute the message that should be signed for an action.
    ///
    /// For actions with `CommitmentMode::Full`, this produces the standard signing
    /// message based on the action's content. For `CommitmentMode::Partial`, use
    /// [`compute_partial_signing_message`] which includes position, federation_id, and nonce.
    ///
    /// The `federation_id` binds the signature to a specific federation, preventing
    /// cross-federation replay where a valid signature from federation A could be
    /// submitted to federation B.
    pub fn compute_signing_message(action: &Action, federation_id: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: version-bumped to v2 when federation binding was added.
        hasher.update(b"dregg-action-sig-v2:");
        hasher.update(federation_id);
        hasher.update(action.target.as_bytes());
        hasher.update(&action.method);
        for arg in &action.args {
            hasher.update(arg);
        }
        for effect in &action.effects {
            hasher.update(&effect.hash());
        }
        hasher.update(&[action.may_delegate as u8]);
        // Include commitment_mode to prevent an attacker from changing the mode
        // (e.g., switching Full to Partial) and using the signature in a different context.
        hasher.update(&[action.commitment_mode as u8]);
        // Include balance_change to prevent malleability: without this, an attacker
        // could take a signed action and modify the balance_change field to drain funds.
        match action.balance_change {
            Some(delta) => {
                hasher.update(&[1u8]); // discriminant: Some
                hasher.update(&delta.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]); // discriminant: None
            }
        }
        // Include preconditions hash to prevent downgrade attacks where an attacker
        // removes preconditions (e.g., minimum balance guards) from a signed action.
        // Hash preconditions inline: use their serialized form for binding.
        let preconds_bytes = postcard::to_allocvec(&action.preconditions).unwrap_or_default();
        hasher.update(&preconds_bytes);
        *hasher.finalize().as_bytes()
    }

    /// Compute the signing message for an action in partial commitment mode.
    ///
    /// The signer commits to:
    /// - The action's own content hash (what they are doing)
    /// - Their position index in the forest (where they are)
    /// - The federation identity (prevents cross-federation replay)
    /// - The turn nonce (prevents replay within the same federation across turns)
    ///
    /// The forest root is NOT included because it creates a chicken-and-egg problem:
    /// the forest root is only computable after all fragments are assembled, but signers
    /// need to sign before assembly. Instead, the coordinator signs the full composed
    /// turn (including the forest root) via `coordinator_signature` on the composed Turn.
    ///
    /// This allows a party to sign their part without knowing about other actions,
    /// enabling multi-party composition (DEX fills, atomic swaps, etc.)
    pub fn compute_partial_signing_message(
        action: &Action,
        position: usize,
        federation_id: &[u8; 32],
        turn_nonce: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: version-bumped to v2 when federation/nonce binding was added.
        hasher.update(b"dregg-partial-sig-v2:");
        hasher.update(federation_id);
        hasher.update(&action.hash());
        hasher.update(&(position as u64).to_le_bytes());
        hasher.update(&turn_nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Compute the canonical signing message bytes for
    /// `Authorization::Custom`.
    ///
    /// Excludes `action.witness_blobs` (which contain the proof bytes
    /// the verifier is checking) to break the proof-generation
    /// circularity that would otherwise arise from
    /// `compute_partial_signing_message`. Includes:
    ///
    /// * Domain separator `"dregg-custom-sig-v1:"` (T-domain isolation).
    /// * `federation_id` (T6 cross-federation replay defense).
    /// * `turn_nonce` (T11 stale-proof defense).
    /// * `position` (multi-action turn binding).
    /// * Action target, method, args, effects (each via `effect.hash`),
    ///   may_delegate, commitment_mode, balance_change, preconditions
    ///   (T2 forge-effects defense — same fields the Signature
    ///   path's preimage covers).
    /// * The predicate's structural shape (kind / commitment /
    ///   input_ref / proof_witness_index) via postcard so a tampering
    ///   verifier can't substitute a different predicate against the
    ///   same proof.
    ///
    /// Returns the raw byte vector (not a 32-byte hash digest) because
    /// the predicate verifier consumes the full message — many app
    /// AIRs absorb the message into their public input series rather
    /// than hashing it.
    pub fn compute_custom_signing_message(
        action: &Action,
        predicate: &dregg_cell::WitnessedPredicate,
        position: usize,
        federation_id: &[u8; 32],
        turn_nonce: u64,
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(256);
        msg.extend_from_slice(b"dregg-custom-sig-v1:");
        msg.extend_from_slice(federation_id);
        msg.extend_from_slice(&turn_nonce.to_le_bytes());
        msg.extend_from_slice(&(position as u64).to_le_bytes());
        // Action body (mirrors compute_signing_message's preimage).
        msg.extend_from_slice(action.target.as_bytes());
        msg.extend_from_slice(&action.method);
        for arg in &action.args {
            msg.extend_from_slice(arg);
        }
        for effect in &action.effects {
            msg.extend_from_slice(&effect.hash());
        }
        msg.push(action.may_delegate as u8);
        msg.push(action.commitment_mode as u8);
        match action.balance_change {
            Some(delta) => {
                msg.push(1u8);
                msg.extend_from_slice(&delta.to_le_bytes());
            }
            None => msg.push(0u8),
        }
        let preconds_bytes = postcard::to_allocvec(&action.preconditions).unwrap_or_default();
        msg.extend_from_slice(&(preconds_bytes.len() as u32).to_le_bytes());
        msg.extend_from_slice(&preconds_bytes);
        // Predicate's structural shape (NOT the proof bytes).
        let pred_bytes = postcard::to_allocvec(predicate).unwrap_or_default();
        msg.extend_from_slice(&(pred_bytes.len() as u32).to_le_bytes());
        msg.extend_from_slice(&pred_bytes);
        msg
    }

    /// Determine ALL required permissions for an action based on its effects.
    pub(super) fn determine_required_permissions(
        &self,
        action: &Action,
    ) -> Vec<(dregg_cell::permissions::Action, &'static str)> {
        let mut result = Vec::new();
        let mut has_send = false;
        let mut has_set_state = false;
        let mut has_increment_nonce = false;
        let mut has_delegate = false;

        // A negative balance_change (withdrawal) requires Send permission.
        if let Some(delta) = action.balance_change {
            if delta < 0 && !has_send {
                result.push((dregg_cell::permissions::Action::Send, "Send"));
                has_send = true;
            }
        }

        for effect in &action.effects {
            match effect {
                Effect::Transfer { from, .. } if from == &action.target && !has_send => {
                    result.push((dregg_cell::permissions::Action::Send, "Send"));
                    has_send = true;
                }
                Effect::SetField { .. } if !has_set_state => {
                    result.push((dregg_cell::permissions::Action::SetState, "SetState"));
                    has_set_state = true;
                }
                Effect::IncrementNonce { .. } if !has_increment_nonce => {
                    result.push((
                        dregg_cell::permissions::Action::IncrementNonce,
                        "IncrementNonce",
                    ));
                    has_increment_nonce = true;
                }
                Effect::GrantCapability { .. } if !has_delegate => {
                    result.push((dregg_cell::permissions::Action::Delegate, "Delegate"));
                    has_delegate = true;
                }
                Effect::RevokeCapability { .. } if !has_delegate => {
                    result.push((dregg_cell::permissions::Action::Delegate, "Delegate"));
                    has_delegate = true;
                }
                Effect::SetPermissions { .. } => {
                    result.push((
                        dregg_cell::permissions::Action::SetPermissions,
                        "SetPermissions",
                    ));
                }
                Effect::SetVerificationKey { .. } => {
                    result.push((
                        dregg_cell::permissions::Action::SetVerificationKey,
                        "SetVerificationKey",
                    ));
                }
                // Locking funds in an escrow or obligation stake is equivalent to
                // sending value out — require Send permission on the source cell.
                Effect::CreateEscrow { .. }
                | Effect::CreateCommittedEscrow { .. }
                | Effect::CreateObligation { .. }
                    if !has_send =>
                {
                    result.push((dregg_cell::permissions::Action::Send, "Send"));
                    has_send = true;
                }
                // Settlement actions (release/refund/fulfill/slash) are checked for
                // creator/beneficiary authorization in the handler, but still require
                // at least Access permission to be mapped so that cells with
                // Access: None cannot be targeted.
                Effect::ReleaseEscrow { .. }
                | Effect::RefundEscrow { .. }
                | Effect::ReleaseCommittedEscrow { .. }
                | Effect::RefundCommittedEscrow { .. }
                | Effect::FulfillObligation { .. }
                | Effect::SlashObligation { .. } => {
                    result.push((dregg_cell::permissions::Action::Access, "Access"));
                }
                // Refusal mutates the target cell's audit slot + nonce
                // (CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3); it requires
                // SetState authority because it overwrites slot[4] with
                // a refusal-audit commitment.
                Effect::Refusal { .. } if !has_set_state => {
                    result.push((dregg_cell::permissions::Action::SetState, "SetState"));
                    has_set_state = true;
                }
                _ => {}
            }
        }

        result
    }

    /// Cav-Codex Block 1: walk an action and collect every cell whose
    /// state could be mutated by its effects. Used by `execute_tree` to
    /// snapshot pre-effect states so the cell-program evaluator can
    /// run on each touched cell's (old, new) pair after the action.
    ///
    /// The returned vec includes the action's `target` and every cell
    /// named explicitly in an `Effect::SetField { cell, .. }`,
    /// `Transfer { from, to }`, `GrantCapability { from, to }`,
    /// `RevokeCapability { cell }`, `IncrementNonce { cell }`,
    /// `EmitEvent { cell }`, `SetPermissions { cell }`,
    /// `SetVerificationKey { cell }`, `RevokeDelegation { child }`, or
    /// `MakeSovereign { cell }`. `ExerciseViaCapability` recursively
    /// expands its `inner_effects`. Note that some effects (Transfer,
    /// etc.) can name a cell that didn't exist before the effect; we
    /// snapshot whatever's there (lazy snapshot on `None`).
    pub(crate) fn collect_touched_cells(action: &Action) -> Vec<CellId> {
        let mut out: Vec<CellId> = vec![action.target];
        fn push(out: &mut Vec<CellId>, id: CellId) {
            if !out.contains(&id) {
                out.push(id);
            }
        }
        fn walk(out: &mut Vec<CellId>, effects: &[Effect]) {
            for e in effects {
                match e {
                    Effect::SetField { cell, .. }
                    | Effect::RevokeCapability { cell, .. }
                    | Effect::EmitEvent { cell, .. }
                    | Effect::IncrementNonce { cell }
                    | Effect::SetPermissions { cell, .. }
                    | Effect::SetVerificationKey { cell, .. }
                    | Effect::MakeSovereign { cell }
                    | Effect::CreateEscrow { cell, .. }
                    | Effect::Refusal { cell, .. } => push(out, *cell),
                    Effect::Transfer { from, to, .. } => {
                        push(out, *from);
                        push(out, *to);
                    }
                    Effect::GrantCapability { from, to, .. } => {
                        push(out, *from);
                        push(out, *to);
                    }
                    Effect::Introduce {
                        introducer,
                        recipient,
                        target,
                        ..
                    } => {
                        push(out, *introducer);
                        push(out, *recipient);
                        push(out, *target);
                    }
                    Effect::ExerciseViaCapability { inner_effects, .. } => {
                        walk(out, inner_effects);
                    }
                    Effect::RevokeDelegation { child } => push(out, *child),
                    _ => {
                        // CreateCell, CreateCellFromFactory, queue ops,
                        // note ops, bridge ops, captp ops: either create
                        // fresh state (no old to snapshot) OR mutate
                        // global executor-side data structures. Their
                        // cell-program coverage rides on the target
                        // cell's program (which we always snapshot).
                    }
                }
            }
        }
        walk(&mut out, &action.effects);
        out
    }
}

// =============================================================================
// Adversarial tests: stealth invocation + first-class token authorization.
//
// These exercise the three anonymity-of-actor goals at the
// `verify_authorization` surface (the canonical entry point):
//   1. Stealth (one-time-key) invocation — unlinkable, replay-rejected.
//   3. Authorization::Token (biscuit) — replay-rejected, insufficient-cap
//      rejected, expired-by-height rejected, tampered rejected.
// (Goal 2, StarkDelegation, is exercised via the existing bearer-cap tests
//  in `turn/src/tests.rs`; the hardening here only *adds* bound public
//  inputs, which those proofs must now also satisfy.)
// =============================================================================
#[cfg(test)]
mod anonymity_tests {
    use super::*;
    use crate::action::{Authorization, CommitmentMode, Effect, TokenKeyRef};
    use crate::executor::ComputronCosts;
    use crate::executor::TurnExecutor;
    use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
    use curve25519_dalek::scalar::Scalar;
    use dregg_cell::{Cell, Ledger, Preconditions};
    use ed25519_dalek::SigningKey;

    fn exec_at(block_height: u64) -> TurnExecutor {
        let mut e = TurnExecutor::new(ComputronCosts::zero());
        e.block_height = block_height;
        e.local_federation_id = [7u8; 32];
        e
    }

    fn vk_with_data(data: Vec<u8>) -> dregg_cell::VerificationKey {
        let hash = *blake3::hash(&data).as_bytes();
        dregg_cell::VerificationKey { hash, data }
    }

    /// Build an action targeting `target` with a single SetState effect
    /// (so the Signature requirement on `set_state` is exercised) plus the
    /// given authorization. `method` lets us vary the bound action.
    fn action_for(target: CellId, method: [u8; 32], authorization: Authorization) -> Action {
        Action {
            target,
            method,
            args: vec![],
            authorization,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: target,
                index: 0,
                value: [9u8; 32],
            }],
            may_delegate: crate::action::DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        }
    }

    // ── Stealth helpers ────────────────────────────────────────────────

    /// Produce a `(spend_pubkey S, spend_scalar s)` pair where `S = s·G` is a
    /// valid Ed25519 point. We derive `s` from an Ed25519 seed exactly the
    /// way `cell::stealth` does, so the relation P = c·G + S holds with the
    /// signing key k = c + s.
    fn spend_keypair(seed: u8) -> ([u8; 32], Scalar) {
        let sk = SigningKey::from_bytes(&[seed; 32]);
        let s = sk.to_scalar();
        let s_point = &s * ED25519_BASEPOINT_TABLE;
        (s_point.compress().to_bytes(), s)
    }

    /// Craft a valid `Authorization::Stealth` for `action_template` using a
    /// fresh blinding scalar `c` (derived from `c_seed`). Returns the auth
    /// AND mutates a clone of the action to carry it (since the signing
    /// message binds `action.hash()`, which excludes the signature).
    fn make_stealth_auth(
        federation_id: &[u8; 32],
        spend_scalar: &Scalar,
        c_seed: u8,
        target: CellId,
        method: [u8; 32],
        turn_nonce: u64,
        position: usize,
    ) -> Authorization {
        let c = Scalar::from_bytes_mod_order([c_seed; 32]);
        let p_point = (&c * ED25519_BASEPOINT_TABLE) + (spend_scalar * ED25519_BASEPOINT_TABLE);
        let one_time_pubkey = p_point.compress().to_bytes();
        // k = c + s (the one-time signing key, a raw scalar).
        let k = c + spend_scalar;
        let ephemeral_pubkey = [c_seed.wrapping_add(1); 32];
        let blinding_scalar = c.to_bytes();

        // Build the action carrying a placeholder signature to compute hash.
        let placeholder = Authorization::Stealth {
            one_time_pubkey,
            ephemeral_pubkey,
            blinding_scalar,
            signature: [0u8; 64],
        };
        let action = action_for(target, method, placeholder);
        let action_hash = action.hash();
        let msg = Authorization::stealth_signing_message(
            federation_id,
            &action_hash,
            &ephemeral_pubkey,
            &blinding_scalar,
            position,
            turn_nonce,
        );
        // Sign with k. We must sign as the one-time key whose public key is P.
        // ed25519_dalek::SigningKey::from_bytes treats the input as a *seed*,
        // not a scalar — so we cannot use it directly for a raw scalar key.
        // Instead use the hazmat raw-scalar signing.
        let sig = sign_with_scalar(&k, &one_time_pubkey, &msg);

        Authorization::Stealth {
            one_time_pubkey,
            ephemeral_pubkey,
            blinding_scalar,
            signature: sig,
        }
    }

    /// Sign a message with a raw Ed25519 scalar `k` whose public key is
    /// `pubkey = k·G`, using the dalek hazmat raw-key API. This matches the
    /// stealth construction where the one-time secret is a scalar, not a seed.
    fn sign_with_scalar(k: &Scalar, pubkey: &[u8; 32], msg: &[u8]) -> [u8; 64] {
        use ed25519_dalek::VerifyingKey;
        use ed25519_dalek::hazmat::{ExpandedSecretKey, raw_sign};
        use sha2::Sha512;
        // Build an ExpandedSecretKey from the scalar. The "hash prefix" (nonce
        // domain) can be any fixed value for a deterministic test; real
        // stealth signers derive it from the shared secret. We use a fixed
        // prefix derived from k for determinism.
        let mut prefix = [0u8; 32];
        prefix.copy_from_slice(&blake3::hash(&k.to_bytes()).as_bytes()[..32]);
        let esk = ExpandedSecretKey {
            scalar: *k,
            hash_prefix: prefix,
        };
        let vk = VerifyingKey::from_bytes(pubkey).expect("valid P");
        let sig = raw_sign::<Sha512>(&esk, msg, &vk);
        sig.to_bytes()
    }

    #[test]
    fn stealth_valid_authorizes_and_persistent_key_absent() {
        let fed = [7u8; 32];
        let (s_pub, s_scalar) = spend_keypair(11);
        let mut ledger = Ledger::new();
        let cell = Cell::new(s_pub, [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let target_cell = ledger.get(&cid).unwrap().clone();

        let method = [1u8; 32];
        let auth = make_stealth_auth(&fed, &s_scalar, 3, cid, method, 0, 0);
        // The persistent spend pubkey S must NOT appear anywhere in the auth.
        if let Authorization::Stealth {
            one_time_pubkey, ..
        } = &auth
        {
            assert_ne!(
                one_time_pubkey, &s_pub,
                "one-time key must differ from persistent spend key"
            );
        }
        let action = action_for(cid, method, auth);
        let exec = exec_at(0);
        exec.verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect("valid stealth auth should verify");
    }

    #[test]
    fn stealth_two_calls_unlinkable() {
        // Two stealth auths from the SAME spend key but fresh blinding scalars
        // must carry different one-time keys / blinding scalars (unlinkable).
        let fed = [7u8; 32];
        let (s_pub, s_scalar) = spend_keypair(12);
        let cid = Cell::new(s_pub, [0u8; 32]).id();
        let method = [2u8; 32];
        let a1 = make_stealth_auth(&fed, &s_scalar, 5, cid, method, 0, 0);
        let a2 = make_stealth_auth(&fed, &s_scalar, 6, cid, method, 0, 0);
        match (a1, a2) {
            (
                Authorization::Stealth {
                    one_time_pubkey: p1,
                    blinding_scalar: c1,
                    ..
                },
                Authorization::Stealth {
                    one_time_pubkey: p2,
                    blinding_scalar: c2,
                    ..
                },
            ) => {
                assert_ne!(p1, p2, "two calls must have unlinkable one-time keys");
                assert_ne!(c1, c2, "two calls must have distinct blinding scalars");
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn stealth_replay_across_turn_nonce_rejected() {
        // A stealth auth signed for turn_nonce 0 must NOT verify at nonce 1.
        let fed = [7u8; 32];
        let (s_pub, s_scalar) = spend_keypair(13);
        let mut ledger = Ledger::new();
        let cell = Cell::new(s_pub, [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let target_cell = ledger.get(&cid).unwrap().clone();
        let method = [3u8; 32];
        let auth = make_stealth_auth(&fed, &s_scalar, 7, cid, method, 0, 0);
        let action = action_for(cid, method, auth);
        let exec = exec_at(0);
        // Verifying at the SAME nonce/position works…
        exec.verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect("nonce 0 should verify");
        // …but replaying the same auth bytes at a DIFFERENT turn nonce fails
        // (the signing message binds the nonce).
        let err = exec
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 1)
            .expect_err("replay at nonce 1 must be rejected");
        assert!(
            matches!(err.0, TurnError::StealthAuthInvalid { .. }),
            "expected StealthAuthInvalid, got {:?}",
            err.0
        );
    }

    #[test]
    fn stealth_wrong_spend_key_rejected() {
        // An attacker who does NOT know the cell's spend scalar cannot forge:
        // signing with an unrelated scalar breaks the P == c·G + S relation
        // OR the signature under P.
        let fed = [7u8; 32];
        let (s_pub, _real_s) = spend_keypair(14);
        let (_attacker_pub, attacker_s) = spend_keypair(99);
        let mut ledger = Ledger::new();
        let cell = Cell::new(s_pub, [0u8; 32]); // cell registers the REAL S
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let target_cell = ledger.get(&cid).unwrap().clone();
        let method = [4u8; 32];
        // Attacker builds an auth with THEIR scalar; P = c·G + attacker·G ≠ c·G + S.
        let auth = make_stealth_auth(&fed, &attacker_s, 8, cid, method, 0, 0);
        let action = action_for(cid, method, auth);
        let exec = exec_at(0);
        let err = exec
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect_err("forged stealth auth must be rejected");
        assert!(
            matches!(err.0, TurnError::StealthAuthInvalid { .. }),
            "expected StealthAuthInvalid, got {:?}",
            err.0
        );
    }

    // ── Token (biscuit) helpers + tests ────────────────────────────────

    fn mint_biscuit_for(
        cell: CellId,
        method: [u8; 32],
        not_after: Option<i64>,
    ) -> (Vec<u8>, [u8; 32]) {
        use dregg_token::BiscuitToken;
        use dregg_token::biscuit_auth::KeyPair;
        use dregg_token::traits::{Attenuation, AuthToken};
        let kp = KeyPair::new();
        let issuer: [u8; 32] = kp
            .public()
            .to_bytes()
            .try_into()
            .expect("32-byte ed25519 pubkey");
        let svc = hex::encode(cell.as_bytes());
        let act = hex::encode(method);
        // Token grants service=cell-id with action set containing the method.
        let mut tok: Box<dyn AuthToken> = Box::new(
            BiscuitToken::mint_dregg(&kp, &[], &[(svc, act)], &[], &[], &[], None).unwrap(),
        );
        if let Some(na) = not_after {
            let att = Attenuation {
                not_after: Some(na),
                ..Default::default()
            };
            tok = tok.attenuate(&att).unwrap();
        }
        let encoded = tok.to_encoded().unwrap().into_bytes();
        (encoded, issuer)
    }

    #[test]
    fn token_biscuit_valid_authorizes() {
        let mut ledger = Ledger::new();
        let cell = Cell::new([21u8; 32], [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let mut target_cell = ledger.get(&cid).unwrap().clone();
        let method = [5u8; 32];
        let (encoded, issuer) = mint_biscuit_for(cid, method, None);
        // Trust anchor: make the issuer the cell's verification key.
        target_cell.verification_key = Some(vk_with_data(issuer.to_vec()));
        let auth = Authorization::Token {
            encoded,
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: issuer,
            },
            discharges: vec![],
        };
        let action = action_for(cid, method, auth);
        let exec = exec_at(100);
        exec.verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect("valid biscuit token should authorize");
    }

    #[test]
    fn token_biscuit_replay_against_different_action_rejected() {
        let mut ledger = Ledger::new();
        let cell = Cell::new([22u8; 32], [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let mut target_cell = ledger.get(&cid).unwrap().clone();
        let method = [6u8; 32];
        let (encoded, issuer) = mint_biscuit_for(cid, method, None);
        target_cell.verification_key = Some(vk_with_data(issuer.to_vec()));
        // Present the token bound to a DIFFERENT method — capability cover fails.
        let other_method = [0x99u8; 32];
        let auth = Authorization::Token {
            encoded,
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: issuer,
            },
            discharges: vec![],
        };
        let action = action_for(cid, other_method, auth);
        let exec = exec_at(100);
        let err = exec
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect_err("token replayed against a different action must be rejected");
        assert!(
            matches!(err.0, TurnError::TokenInsufficientCapability { .. }),
            "expected TokenInsufficientCapability, got {:?}",
            err.0
        );
    }

    #[test]
    fn token_biscuit_untrusted_issuer_rejected() {
        let mut ledger = Ledger::new();
        let cell = Cell::new([23u8; 32], [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let target_cell = ledger.get(&cid).unwrap().clone(); // no VK, pk != issuer
        let method = [7u8; 32];
        let (encoded, issuer) = mint_biscuit_for(cid, method, None);
        let auth = Authorization::Token {
            encoded,
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: issuer,
            },
            discharges: vec![],
        };
        let action = action_for(cid, method, auth);
        let exec = exec_at(100);
        let err = exec
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect_err("untrusted issuer must be rejected");
        assert!(
            matches!(err.0, TurnError::TokenAuthInvalid { .. }),
            "expected TokenAuthInvalid (untrusted issuer), got {:?}",
            err.0
        );
    }

    #[test]
    fn token_biscuit_expired_by_height_rejected() {
        let mut ledger = Ledger::new();
        let cell = Cell::new([24u8; 32], [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let mut target_cell = ledger.get(&cid).unwrap().clone();
        let method = [8u8; 32];
        // not_after = 5 (a block height); we verify at height 10 -> expired.
        let (encoded, issuer) = mint_biscuit_for(cid, method, Some(5));
        target_cell.verification_key = Some(vk_with_data(issuer.to_vec()));
        let auth = Authorization::Token {
            encoded,
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: issuer,
            },
            discharges: vec![],
        };
        let action = action_for(cid, method, auth);
        let exec = exec_at(10); // block height past not_after
        let err = exec
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect_err("token expired by block height must be rejected");
        assert!(
            matches!(err.0, TurnError::TokenInsufficientCapability { .. }),
            "expected TokenInsufficientCapability (expired), got {:?}",
            err.0
        );
        // And the SAME token verifies BEFORE expiry (height 3 < 5).
        let exec_ok = exec_at(3);
        exec_ok
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect("token should authorize before its height expiry");
    }

    #[test]
    fn token_biscuit_tampered_rejected() {
        let mut ledger = Ledger::new();
        let cell = Cell::new([25u8; 32], [0u8; 32]);
        let cid = cell.id();
        ledger.insert_cell(cell).unwrap();
        let mut target_cell = ledger.get(&cid).unwrap().clone();
        let method = [10u8; 32];
        let (mut encoded, issuer) = mint_biscuit_for(cid, method, None);
        target_cell.verification_key = Some(vk_with_data(issuer.to_vec()));
        // Flip a byte in the middle of the encoded token.
        let mid = encoded.len() / 2;
        encoded[mid] ^= 0xFF;
        let auth = Authorization::Token {
            encoded,
            key_ref: TokenKeyRef::BiscuitIssuer {
                issuer_pubkey: issuer,
            },
            discharges: vec![],
        };
        let action = action_for(cid, method, auth);
        let exec = exec_at(100);
        let err = exec
            .verify_authorization(&action, &target_cell, &ledger, &cid, &[0], 0)
            .expect_err("tampered token must be rejected");
        assert!(
            matches!(err.0, TurnError::TokenAuthInvalid { .. }),
            "expected TokenAuthInvalid (tampered), got {:?}",
            err.0
        );
    }
}
