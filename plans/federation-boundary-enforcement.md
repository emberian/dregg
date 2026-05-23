# Federation Boundary Enforcement

## Problem Statement

The wire protocol has NO authentication of connecting peers. Anyone who can reach
the TCP port connects, sends Hello, and is immediately in the "Active" state.
There is no proof-of-membership, no challenge-response, and no role classification.

This means:
- The blocklace (turns, cell state, swiss tables) is readable by any connector
- State replication (gossip push/pull) has no boundary
- Cross-federation CapTP sessions are indistinguishable from internal member gossip
- A non-member connecting over TCP gets full access to replicated state

## Design

### 1. PeerRole Enum

```rust
/// The authenticated role of a connected peer.
///
/// Determines what messages they may receive and what state is
/// replicated to them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeerRole {
    /// Full federation member -- gets all state, participates in consensus.
    /// Authenticated via Ed25519 challenge-response against constitution.
    Member { participant_key: [u8; 32] },
    /// External CapTP peer -- gets only CapTP messages, no state replication.
    CapTpPeer { federation_id: FederationId, session: CapSession },
    /// Light client -- gets only proofs and public commitments.
    LightClient,
    /// Unauthenticated -- limited to health check, public info, token presentation.
    Anonymous,
}
```

### 2. Challenge-Response Handshake

After the Hello/Welcome exchange, the server initiates a challenge:

```
Server -> Client: PeerChallenge { nonce: [u8; 32] }
Client -> Server: PeerResponse { 
    participant_key: [u8; 32], 
    signature: Signature,       // sign(nonce || server_node_id)
    constitution_version: u64,  // which constitution they claim membership in
}
Server: verify(participant_key, signature, nonce || self.node_id)
         AND constitution.is_participant(participant_key)
Server -> Client: PeerAuthenticated { role: PeerRole, granted_topics: Vec<String> }
```

If the client does NOT authenticate (e.g., it's an external presenter or light
client), it remains `Anonymous` and is restricted to:
- PresentToken (prove they hold a valid credential)
- RequestAttestedRoot (public information)
- RequestNonMembership (public non-membership proofs)
- Ping/Pong

### 3. ConnectionAuth Tracking

```rust
pub struct ConnectionAuth {
    /// The peer's authenticated role.
    pub role: PeerRole,
    /// When authentication was completed.
    pub authenticated_at: Instant,
    /// Whether this peer has completed the challenge-response.
    pub handshake_complete: bool,
}
```

Each connection carries a `ConnectionAuth` that is initialized as `Anonymous`
and upgraded if the peer completes the challenge-response.

### 4. Message Filtering by Role

| Message Type            | Anonymous | LightClient | CapTpPeer | Member |
|------------------------|-----------|-------------|-----------|--------|
| PresentToken           | Y         | Y           | Y         | Y      |
| RequestAttestedRoot    | Y         | Y           | Y         | Y      |
| RequestNonMembership   | Y         | Y           | Y         | Y      |
| Ping/Pong              | Y         | Y           | Y         | Y      |
| CapHello/CapGoodbye    | N         | N           | Y         | Y      |
| EnlivenSturdyRef       | N         | N           | Y         | Y      |
| PipelinedMsg           | N         | N           | Y         | Y      |
| PresentHandoff         | N         | N           | Y         | Y      |
| DropRemoteRef          | N         | N           | Y         | Y      |
| SubmitRevocation       | N         | N           | N         | Y      |
| (future) GossipPush    | N         | N           | N         | Y      |
| (future) StateSyncReq  | N         | N           | N         | Y      |

### 5. State Replication Boundary

- **SwissTable**: NEVER sent to non-members
- **Cell state**: only sent to Members, or via proven CapTP enliven
- **Blocklace blocks**: Members only; external parties get commitments/proofs
- **Turn data**: Members only; externals see only effects_hash (public input)

### 6. Implementation Plan

Phase 1 (this change):
- Add `PeerRole` enum
- Add `ConnectionAuth` struct 
- Add `PeerChallenge` / `PeerResponse` / `PeerAuthenticated` wire messages
- Implement challenge-response in `handle_connection_generic`
- Filter messages by role in `process_message`
- New error code: `PEER_AUTH_REQUIRED`

Phase 2 (future):
- Integrate with `ConstitutionManager` for live membership changes
- CapTP peer promotion (Anonymous -> CapTpPeer via CapHello with proof)
- Rate limiting per role
- Connection demotion on constitution change (member evicted -> disconnect)

## Security Properties

1. **No state leakage to non-members**: A TCP connector without a valid Ed25519
   key in the constitution gets only public information.
2. **Forward secrecy of role**: Even if an attacker captures a signed challenge,
   the nonce ensures it cannot be replayed.
3. **Constitution-bound**: Authentication is checked against the CURRENT
   constitution, not a stale copy. Member eviction invalidates future connections.
4. **Fail-closed**: If challenge-response fails or times out, the connection
   stays Anonymous (restricted).
