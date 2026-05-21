use std::collections::BTreeMap;
use std::sync::Arc;

use crate::*;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
/// Tracks votes for a particular data type and helps form quorums
///
/// This is an implementation helper that tracks votes from different processes
/// and determines when a quorum (n-f votes) has been reached.
/// Used for implementing the collection of votes in the protocol.
pub struct QuorumTrack<
    T: Ord
        + CanonicalSerialize
        + CanonicalDeserialize
        + Valid
        + Serialize
        + for<'d> Deserialize<'d>
        + 'static,
> {
    /// Maps vote data to a map of (voter identity -> signed vote)
    /// Ensures we only count one vote per process and track when we reach a quorum
    #[serde(with = "serde_json_any_key::any_key_map")]
    pub votes: BTreeMap<T, BTreeMap<Identity, Arc<ThreshPartial<T>>>>,
}

/// Error when attempting to record a duplicate vote from the same process
#[derive(Debug, Serialize, Deserialize)]

pub struct Duplicate;

impl<
    T: Ord
        + Clone
        + CanonicalSerialize
        + CanonicalDeserialize
        + Valid
        + Serialize
        + for<'d> Deserialize<'d>
        + 'static,
> QuorumTrack<T>
{
    /// Records a new vote and returns the number of votes collected for this data
    ///
    /// This helps implement the quorum formation logic from the pseudocode:
    /// "A z-quorum for b is a set of n-f z-votes for b, each signed by a different process in Π"
    /// Returns Err(Duplicate) if this process has already voted for this data.
    pub fn record_vote(&mut self, vote: Arc<ThreshPartial<T>>) -> Result<usize, Duplicate> {
        let votes_now = self
            .votes
            .entry(vote.data.clone())
            .or_insert(BTreeMap::new());

        // Ensure each process only votes once (for safety)
        if votes_now.contains_key(&vote.author) {
            return Err(Duplicate);
        }

        // Record the vote and return the current count
        votes_now.insert(vote.author.clone(), vote);
        Ok(votes_now.len())
    }
}

impl<Tr: Transaction> MorpheusProcess<Tr> {
    pub fn try_vote(
        &mut self,
        z: u8,
        block: &BlockKey,
        // send this vote to only this process
        target: Option<Identity>,
        to_send: &mut Vec<(Message<Tr>, Option<Identity>)>,
    ) -> bool {
        tracing::debug!(target: "try_vote", z = z, block = ?block, target = ?target);
        let Some(author) = block.author.clone() else {
            tracing::warn!(target: "try_vote", "rejecting vote for genesis block");
            return false;
        };

        // Per paper Section 5: "voted_i(z, x, s, p_j)" - dedup key is (z-level, block type,
        // slot, author) WITHOUT view. This is correct: the paper guarantees that a correct
        // process never votes for conflicting blocks regardless of view, because the 1-QC
        // chain ensures consistency across views (see Theorem 6.2).
        if !self
            .voted_i
            .contains(&(z, block.type_, block.slot, author.clone()))
        {
            self.voted_i
                .insert((z, block.type_, block.slot, author.clone()));

            let voted = Arc::new(ThreshPartial::from_data(
                VoteData {
                    z,
                    for_which: block.clone(),
                },
                &self.kb,
            ));
            self.send_msg(to_send, (Message::NewVote(voted.clone()), target));
            true
        } else {
            false
        }
    }

    /// Returns false if the vote is a duplicate (sender already voted there)
    pub fn record_vote(
        &mut self,
        vote_data: &Arc<ThreshPartial<VoteData>>,
        to_send: &mut Vec<(Message<Tr>, Option<Identity>)>,
    ) -> bool {
        tracing::debug!(target: "record_vote", vote_data = ?vote_data.data);
        match self.vote_tracker.record_vote(vote_data.clone()) {
            Ok(num_votes) => {
                if num_votes >= (self.n - self.f) as usize {
                    // make the signature
                    let votes_now = self
                        .vote_tracker
                        .votes
                        .get(&vote_data.data)
                        .unwrap()
                        .values()
                        .map(|v| (v.author.0 as usize - 1, v.signature.clone()))
                        .collect::<Vec<_>>();
                    let agg = self.kb.hints_setup.aggregator();
                    let mut data = Vec::new();
                    vote_data.data.serialize_compressed(&mut data).unwrap();
                    let signed = hints::sign_aggregate(
                        &agg,
                        hints::F::from((self.n - self.f) as u64),
                        &votes_now,
                        &data,
                    )
                    .unwrap();
                    let quorum_formed = Arc::new(ThreshSigned {
                        data: vote_data.data.clone(),
                        signature: signed,
                    });

                    // 0-QCs for our own blocks need to be broadcast
                    if vote_data.data.z == 0
                        && vote_data.data.for_which.author.as_ref() == Some(&self.id)
                        && !self.zero_qcs_sent.contains(&vote_data.data.for_which)
                    {
                        self.zero_qcs_sent.insert(vote_data.data.for_which.clone());
                        crate::tracing_setup::qc_formed(
                            &self.id,
                            vote_data.data.z,
                            &vote_data.data,
                        );
                        self.send_msg(to_send, (Message::QC(quorum_formed.clone()), None));
                    }
                    self.record_qc(quorum_formed);
                }
                true
            }
            Err(Duplicate) => {
                tracing::error!(
                    target: "duplicate_vote",
                    vote_data = ?vote_data.data,
                    author = ?vote_data.author
                );
                false
            }
        }
    }

    /// Re-evaluate all pending votes based on current state
    pub fn reevaluate_pending_votes(&mut self, to_send: &mut Vec<(Message<Tr>, Option<Identity>)>) {
        // Only process votes for the current view
        let current_view = self.view_i;

        let mut all_pending = std::mem::replace(&mut self.pending_votes, BTreeMap::new());

        let pending = all_pending.entry(current_view).or_default();
        if !pending.dirty {
            self.pending_votes = all_pending;
            return;
        }

        // First check global conditions for the current view
        let contains_lead = self
            .index
            .contains_lead_by_view
            .get(&current_view)
            .copied()
            .unwrap_or(false);
        let unfinalized_lead_empty = self
            .index
            .unfinalized_lead_by_view
            .get(&current_view)
            .map_or(true, |set| set.is_empty());

        // Only process transaction block votes if we have leader blocks and no unfinalized leader blocks
        if contains_lead && unfinalized_lead_empty {
            // Process transaction block votes (1-votes and 2-votes)
            self.process_block_votes(
                1,
                &mut pending.tr_1,
                |this, block_key| this.is_eligible_for_tr_1_vote(block_key),
                Some("1-voted for a transaction block"),
                to_send,
            );

            self.process_block_votes(
                2,
                &mut pending.tr_2,
                |this, block_key| this.is_eligible_for_tr_2_vote(block_key),
                Some("2-voted for a transaction block"),
                to_send,
            );
        }

        // Process leader block votes if we're still in high throughput phase
        if self.phase_i.get(&current_view).unwrap_or(&Phase::High) == &Phase::High {
            self.process_block_votes(
                1,
                &mut pending.lead_1,
                |_, block_key| block_key.view == current_view,
                None,
                to_send,
            );

            self.process_block_votes(
                2,
                &mut pending.lead_2,
                |_, block_key| block_key.view == current_view,
                None,
                to_send,
            );
        }

        pending.dirty = false;
        self.pending_votes = all_pending;
    }

    /// Generic method to process pending votes for blocks
    ///
    /// This handles both transaction and leader blocks for both 1-votes and 2-votes
    fn process_block_votes<F>(
        &mut self,
        vote_level: u8,
        pending_votes: &mut BTreeMap<BlockKey, bool>,
        eligibility_check: F,
        phase_transition_reason: Option<&str>,
        to_send: &mut Vec<(Message<Tr>, Option<Identity>)>,
    ) where
        F: Fn(&Self, &BlockKey) -> bool,
    {
        let mut processed_keys = Vec::new();

        for block_key in pending_votes.keys().cloned() {
            if eligibility_check(self, &block_key) {
                if self.try_vote(vote_level, &block_key, None, to_send) {
                    if block_key.type_ == BlockType::Tr && phase_transition_reason.is_some() {
                        // If we voted for a transaction block, transition to low throughput phase
                        crate::tracing_setup::protocol_transition(
                            &self.id,
                            "throughput phase",
                            &Phase::High,
                            &Phase::Low,
                            phase_transition_reason,
                        );
                        self.set_phase(Phase::Low);
                    }
                    processed_keys.push(block_key);
                } else {
                    panic!(
                        "Already {}-voted {:?}, pending votes desync bug",
                        vote_level, block_key
                    );
                }
            }
        }

        pending_votes.retain(|key, _| !processed_keys.contains(&key));
    }
}
