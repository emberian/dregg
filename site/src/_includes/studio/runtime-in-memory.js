/**
 * InMemoryRuntime — JS driver around the wasm PyanaRuntime handle.
 *
 * Owns one wasm runtime handle. Exposes a Runtime-shaped API (see STUDIO.md
 * § 3). All getters return Preact signals so inspectors auto-re-render when
 * the underlying state changes.
 *
 * State invalidation is push-based on mutation: every mutating call bumps an
 * internal version signal that all observed-object signals depend on. There
 * is no diff; the signals refetch on read. Coarse but correct for v0.
 *
 * Subscription/event API is not yet wired up; mutating calls fire on the
 * `_events` EventTarget if any visualizer wants to listen directly.
 */

const CAPS = Object.freeze({
  read: true,
  mutate: true,
  debug: true,
  timeTravel: false, // sim runtime is always at head; time-travel later
});

export async function createInMemoryRuntime({ wasm, signals }) {
  const { signal, computed } = signals;

  // §4.6 SDK integration COMPLETED (STARBRIDGE-FOLLOWUP-05): instantiate typed PyanaRuntime
  // from @pyana/sdk. All public mutations + high-level calls (create*, execute*,
  // peer*, federation*, intent*) now go through typed SDK surface (eliminates
  // raw `(wasm as any).foo()` class of bugs for starbridge-apps + Studio).
  // Getters for signal-driven inspectors use direct canonical wasm passthrough
  // (SDK runtime.ts does the identical (wasm as any) internally; no JS reimpl,
  // per substrate rule). Hybrid is required for sync computed() reactivity;
  // high-level app/turn-builder paths are fully typed.
  // When served, `/pkg/@pyana/sdk/index.mjs` is the bundled ESM from sdk-ts/.
  let sdkRuntime = null;
  try {
    const sdkMod = await import('/pkg/@pyana/sdk/index.mjs');
    if (sdkMod && sdkMod.PyanaRuntime) {
      sdkRuntime = new sdkMod.PyanaRuntime(wasm);
      console.log('[runtime-in-memory] §4.6 SDK wired (FOLLOWUP-05 complete): using @pyana/sdk PyanaRuntime for all mutators + typed surface');
    }
  } catch (e) {
    console.warn('[runtime-in-memory] §4.6 SDK not available (no /pkg/@pyana/sdk or import fail), falling back to raw wasm (visible gap):', e?.message || e);
  }

  const handle = wasm.create_runtime();

  // Coarse version counter; bumped on any mutation. All cached signals depend
  // on this — reading them after a mutation triggers re-fetch.
  const version = signal(0);
  const cursor = signal(0); // block height; sim runtimes always at head for now
  const events = new EventTarget();

  function fire(type, detail) {
    events.dispatchEvent(new CustomEvent(type, { detail }));
  }
  function bump() { version.value = version.value + 1; }

  // --- Observed-object signals (cached per id) ---
  const cellCache = new Map();
  function getCell(id) {
    if (!cellCache.has(id)) {
      cellCache.set(id, computed(() => {
        version.value; // dep
        try { return wasm.get_cell_state(handle, id); }
        catch { return null; }
      }));
    }
    return cellCache.get(id);
  }

  const listCellsSignal = computed(() => {
    version.value; // dep
    return wasm.get_all_cells(handle) || [];
  });
  function listCells() { return listCellsSignal; }

  // --- Receipts -------------------------------------------------------------
  // The wasm runtime exposes only `get_receipt_chain(handle)` returning the
  // *entire* receipt chain. We cache the full chain as one signal and derive
  // per-receipt lookups from it. listReceipts(agentIdx) is currently global
  // (the chain doesn't carry agent attribution); the agentIdx arg is reserved
  // for when a per-agent filter lands in wasm.
  const receiptChainSignal = computed(() => {
    version.value;
    try { return wasm.get_receipt_chain(handle) || []; }
    catch { return []; }
  });
  function listReceipts(_agentIdx) { return receiptChainSignal; }
  const receiptCache = new Map();
  function getReceipt(turnHash) {
    if (!receiptCache.has(turnHash)) {
      receiptCache.set(turnHash, computed(() => {
        const chain = receiptChainSignal.value;
        return chain.find(r => r.turn_hash === turnHash) || null;
      }));
    }
    return receiptCache.get(turnHash);
  }
  // <pyana-turn> uses the same source-of-truth: a "turn" in this runtime is
  // identified by its turn_hash and surfaces the matching receipt.
  function getTurn(turnHash) { return getReceipt(turnHash); }

  // --- Capabilities ---------------------------------------------------------
  // Capabilities are agent-indexed (no global ID in the sim). URI form:
  //   pyana://capability/<agent_idx>/<token_idx>
  const capTreeCache = new Map();
  function listCapabilities(agentIdx) {
    const key = String(agentIdx);
    if (!capTreeCache.has(key)) {
      capTreeCache.set(key, computed(() => {
        version.value;
        try { return wasm.get_capability_tree(handle, Number(agentIdx)) || null; }
        catch { return null; }
      }));
    }
    return capTreeCache.get(key);
  }
  function getCapability(agentIdx, slotOrIndex) {
    // We don't cache per-cap separately; this is a thin derivation over the
    // agent's tree signal. Returns a computed that finds by slot first, falling
    // back to position index.
    return computed(() => {
      const tree = listCapabilities(agentIdx).value;
      if (!tree || !tree.capabilities) return null;
      const slotNum = Number(slotOrIndex);
      const bySlot = tree.capabilities.find(c => Number(c.slot) === slotNum);
      if (bySlot) return { ...bySlot, agent_index: Number(agentIdx), agent_name: tree.agent_name, cell_id: tree.cell_id };
      const byIndex = tree.capabilities[slotNum];
      if (byIndex) return { ...byIndex, agent_index: Number(agentIdx), agent_name: tree.agent_name, cell_id: tree.cell_id };
      return null;
    });
  }

  // --- Intents --------------------------------------------------------------
  // wasm has no `get_intent(idx)` getter and no `list_intents`. The runtime
  // tracks intent creation in JS-side state populated by createIntent().
  // For a v0 we keep a JS-side ledger of `{intent_id, intent_index, ...input}`
  // returned by create_intent. Match results can be fetched on demand.
  const intentLedger = []; // [{ intent_id, intent_index, agent_index, kind, ... }]
  const intentLedgerSignal = signal(0); // bumped on push
  function listIntents() {
    return computed(() => {
      intentLedgerSignal.value;
      return intentLedger.slice();
    });
  }
  function getIntent(idOrIndex) {
    return computed(() => {
      intentLedgerSignal.value;
      // try as numeric index
      const asNum = Number(idOrIndex);
      if (!Number.isNaN(asNum) && intentLedger[asNum]) return intentLedger[asNum];
      // try by id
      const byId = intentLedger.find(i => i.intent_id === idOrIndex);
      return byId || null;
    });
  }
  function matchIntent(intentIndex, agentIndex) {
    try {
      return wasm.match_intent_for_agent(handle, Number(intentIndex), Number(agentIndex));
    } catch (e) {
      return { matched: false, kind: 'error', error: String(e?.message || e) };
    }
  }

  // --- Federations + Blocks -------------------------------------------------
  // Now wired. The wasm runtime constructs real `pyana_federation::Federation`
  // instances; the inspector reads through `get_federation_state` /
  // `get_federation_block` / `list_federation_blocks`, all of which return
  // shapes derived directly from the canonical RevocationBlock /
  // QuorumCertificate / NodeIdentity types. Blocks are addressed by
  // (fed_index, height); height 1 = first finalized block.
  const fedCache = new Map();
  function getFederation(fedIdx) {
    const key = String(fedIdx);
    if (!fedCache.has(key)) {
      fedCache.set(key, computed(() => {
        version.value;
        try { return wasm.get_federation_state(handle, Number(fedIdx)); }
        catch { return null; }
      }));
    }
    return fedCache.get(key);
  }
  // Blocks are addressed as `pyana://block/<fedIdx>/<height>` upstream, but
  // existing inspectors pass just the height-portion. To keep block lookup
  // self-contained, we default to fed_index=0 when callers pass a bare height;
  // callers that want a specific federation pass an object { fedIndex, height }.
  const blockCache = new Map();
  function getBlock(idOrSpec) {
    let fedIdx = 0;
    let height = 0;
    if (typeof idOrSpec === 'object' && idOrSpec !== null) {
      fedIdx = Number(idOrSpec.fedIndex || idOrSpec.fed_index || 0);
      height = Number(idOrSpec.height || 0);
    } else {
      height = Number(idOrSpec);
    }
    const key = `${fedIdx}/${height}`;
    if (!blockCache.has(key)) {
      blockCache.set(key, computed(() => {
        version.value;
        try {
          const block = wasm.get_federation_block(handle, fedIdx, BigInt(height));
          // Normalize null vs {}.
          if (!block || block === null) return null;
          return { ...block, fed_index: fedIdx };
        } catch { return null; }
      }));
    }
    return blockCache.get(key);
  }
  // Track federations created through this runtime so listBlocks() knows
  // which indices to scan. The wasm side has no `count_federations` getter
  // (federation handles are opaque indices into an internal Vec); we mirror
  // the count here. Other surfaces that create federations out-of-band
  // (none today) would need to bump this signal.
  const fedCountSignal = signal(0);
  const blocksListSignal = computed(() => {
    version.value;
    const count = fedCountSignal.value;
    const all = [];
    for (let i = 0; i < count; i++) {
      try {
        const list = wasm.list_federation_blocks(handle, i) || [];
        for (const b of list) all.push(b);
      } catch { /* skip federations the wasm side rejects */ }
    }
    return all;
  });
  function listBlocks() { return blocksListSignal; }

  // --- Wave 3: federation-list + factory + dfa stubs (use wasm bindings when present) ---
  const knownFedsSignal = computed(() => {
    version.value;
    try {
      return wasm.list_known_federations ? (wasm.list_known_federations(handle) || []) : [];
    } catch { return []; }
  });
  function listKnownFederations() { return knownFedsSignal; }

  function registerFederation(name, numNodes = 3) {
    try {
      // Adapt to canonical register_federation binding (pubkeys_json per plan §4.3/§5.7 + extension Task #28).
      // For sim/in-memory (Starbridge default), we only need count; dummies suffice (real pubkeys come from
      // extension cclerk / node paths). This eliminates the conflicting num_nodes overload dup.
      const n = Math.max(1, Number(numNodes) || 3);
      const dummyPubkeys = JSON.stringify(Array.from({ length: n }, () => '00'.repeat(32)));
      let res = wasm.register_federation ? wasm.register_federation(handle, name, dummyPubkeys) : { registered_index: -1, name };
      // Normalize shape for existing Starbridge callers (some expect fed_index).
      if (res && typeof res === 'object') {
        if (res.registered_index != null && res.fed_index == null) res.fed_index = res.registered_index;
      }
      bump();
      fire('federation-registered', res);
      return res;
    } catch (e) { return { error: String(e) }; }
  }

  function listDeployedFactories() {
    version.value;
    try { return wasm.list_deployed_factories ? (wasm.list_deployed_factories(handle) || []) : []; }
    catch { return []; }
  }

  function compileDfa(patternJson) {
    try { return wasm.compile_dfa ? wasm.compile_dfa(patternJson) : { note: 'pending' }; }
    catch (e) { return { error: String(e) }; }
  }

  // --- Mutations (now §4.6 SDK-wired where possible) ---
  // These are now async to accommodate SDK's typed async surface. Callers
  // (studio.html buttons, spikes, starbridge-apps) must await. Getters for
  // signals remain sync (internal driver).
  async function createAgent(name, initialBalance = 0) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.createAgent(name, initialBalance);
    } else {
      result = wasm.create_agent(handle, name, BigInt(initialBalance));
    }
    bump();
    fire('agent-created', result);
    return result;
  }
  async function createCell(ownerPkHex, initialBalance = 0) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.createCell(ownerPkHex, initialBalance);
    } else {
      result = wasm.create_cell(handle, ownerPkHex, BigInt(initialBalance));
    }
    bump();
    fire('cell-created', result);
    return result;
  }
  async function executeTurn(agentIndex, actions, fee = 0) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.executeTurn(agentIndex, actions, fee);
    } else {
      result = wasm.execute_turn(
        handle,
        agentIndex,
        JSON.stringify(actions),
        BigInt(fee),
      );
    }
    bump();
    fire('turn-executed', { agentIndex, actions, result });
    return result;
  }
  async function mintToken(agentIndex, resource, actions, expiry = 0) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.mintToken(agentIndex, resource, actions, expiry);
    } else {
      result = wasm.agent_mint_token(
        handle,
        agentIndex,
        resource,
        JSON.stringify(actions),
        BigInt(expiry),
      );
    }
    bump();
    fire('token-minted', { agentIndex, result });
    return result;
  }
  async function advanceHeight(blocks = 1) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.advanceHeight(blocks);
    } else {
      result = wasm.advance_height(handle, BigInt(blocks));
    }
    cursor.value = cursor.value + Number(blocks);
    bump();
    fire('height-advanced', { blocks, result });
    return result;
  }
  async function createFederation(name, numNodes = 4) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.createFederation(name, numNodes);
    } else {
      result = wasm.create_federation(handle, String(name), Number(numNodes) >>> 0);
    }
    fedCountSignal.value = fedCountSignal.value + 1;
    bump();
    fire('federation-created', result);
    return result;
  }
  async function createIntent(agentIndex, kind, actions, constraints, resourcePattern, expiry = 0) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.createIntent(agentIndex, kind, actions, constraints, resourcePattern, expiry);
    } else {
      result = wasm.create_intent(
        handle,
        Number(agentIndex),
        kind,
        JSON.stringify(actions || []),
        JSON.stringify(constraints || []),
        resourcePattern || '',
        BigInt(expiry),
      );
    }
    intentLedger.push({
      ...result,
      agent_index: Number(agentIndex),
      kind,
      actions: actions || [],
      constraints: constraints || [],
      resource_pattern: resourcePattern || null,
      expiry: Number(expiry),
    });
    intentLedgerSignal.value = intentLedgerSignal.value + 1;
    bump();
    fire('intent-created', result);
    return result;
  }
  // `propose_block(fed_index, events)` accepts an array of token-id strings
  // (each becomes a real `pyana_federation::RevocationEvent` signed by node 0).
  // Returns `{ block_hash, height, finalized }`; `finalized: false` means the
  // round didn't reach quorum (the canonical Federation enforces n - floor(n/3)
  // online votes — not any-N like the deleted sim).
  async function proposeBlock(fedIndex, events) {
    let result;
    const eventsJson = JSON.stringify(events || []);
    if (sdkRuntime) {
      result = await sdkRuntime.proposeBlock(fedIndex, events);
    } else {
      result = wasm.propose_block(handle, Number(fedIndex), eventsJson);
    }
    bump();
    fire('block-proposed', { fedIndex, events, result });
    return result;
  }
  // Drive one extra consensus round on an existing federation (consumes any
  // pending events). Returns the consensus round summary, or null if the
  // round didn't finalize.
  async function simulateConsensusRound(fedIndex) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.simulateConsensusRound(fedIndex);
    } else {
      result = wasm.simulate_consensus_round(handle, Number(fedIndex));
    }
    bump();
    fire('consensus-round', { fedIndex, result });
    return result;
  }

  // --- Turn trace -----------------------------------------------------------
  // Signal-cached per turn_hash (traces are immutable once committed).
  const turnTraceCache = new Map();
  function getTurnTrace(turnHash) {
    if (!turnTraceCache.has(turnHash)) {
      turnTraceCache.set(turnHash, computed(() => {
        // Trace is immutable after commit; version dep ensures we pick it up
        // once the turn lands in the receipt chain.
        version.value;
        try {
          const raw = wasm.get_turn_trace(handle, String(turnHash));
          return raw || { steps: [], computrons_total: 0, trace_gap_note: '' };
        } catch (e) {
          return { steps: [], computrons_total: 0, trace_gap_note: String(e?.message || e), _error: true };
        }
      }));
    }
    return turnTraceCache.get(turnHash);
  }

  // --- Observability trace events (Task #30) --------------------------------
  // Signal-cached; the live feed for <pyana-activity>. Bumps on any mutation
  // (via version) cause re-fetch of the JSON from wasm (canonical EventLog).
  // No JS reimplementation of pyana — pure passthrough + signal.
  const traceEventsSignal = computed(() => {
    version.value; // dep on mutations (executeTurn etc)
    try {
      const raw = wasm.get_trace_events_json(handle);
      return raw || { schema_version: 1, event_count: 0, events: [] };
    } catch (e) {
      return { schema_version: 1, event_count: 0, events: [], _error: String(e?.message || e) };
    }
  });
  function getTraceEvents() { return traceEventsSignal; }

  // --- Peer transition decode -----------------------------------------------
  // Non-cached; called per-paste. Bytes is a Uint8Array.
  function decodePeerTransition(bytes) {
    return wasm.decode_peer_transition(bytes);
  }

  // --- Peer exchange (sovereign-cell P2P) ---------------------------------
  // Thin signal-cached facade over the canonical `pyana_cell::PeerExchange`
  // surface exposed by the wasm crate. Mutations bump `version`; reads come
  // through cached computeds keyed on (agentIdx, peerCellId).
  const peerViewCache = new Map();
  function getPeerView(agentIdx, peerCellIdHex) {
    const key = `${agentIdx}/${peerCellIdHex}`;
    if (!peerViewCache.has(key)) {
      peerViewCache.set(key, computed(() => {
        version.value;
        try {
          return wasm.get_peer_view(handle, Number(agentIdx), String(peerCellIdHex));
        } catch (e) {
          return { error: String(e?.message || e) };
        }
      }));
    }
    return peerViewCache.get(key);
  }
  const peerListCache = new Map();
  function listPeers(agentIdx) {
    const key = String(agentIdx);
    if (!peerListCache.has(key)) {
      peerListCache.set(key, computed(() => {
        version.value;
        try { return wasm.list_peers(handle, Number(agentIdx)) || []; }
        catch { return []; }
      }));
    }
    return peerListCache.get(key);
  }
  function getPeerPubkey(agentIdx) {
    // One-shot read (no signal — the pubkey is immutable for the lifetime
    // of the agent; recompute on each call is fine and avoids stale caches).
    return wasm.get_peer_pubkey(handle, Number(agentIdx));
  }
  function getCellStateCommitment(cellIdHex) {
    try { return wasm.get_cell_state_commitment(handle, String(cellIdHex)); }
    catch { return null; }
  }
  async function registerPeer(agentIdx, peerCellIdHex, peerPubkeyHex, initialCommitmentHex) {
    let result;
    if (sdkRuntime) {
      result = await sdkRuntime.registerPeer(agentIdx, peerCellIdHex, peerPubkeyHex, initialCommitmentHex);
    } else {
      result = wasm.register_peer(
        handle,
        Number(agentIdx),
        String(peerCellIdHex),
        String(peerPubkeyHex),
        String(initialCommitmentHex),
      );
    }
    bump();
    fire('peer-registered', { agentIdx, peerCellIdHex, result });
    return result;
  }
  async function createPeerTransition(agentIdx, oldCommitHex, newCommitHex, effectsHashHex) {
    let bytes;
    if (sdkRuntime) {
      bytes = await sdkRuntime.createPeerTransition(agentIdx, oldCommitHex, newCommitHex, effectsHashHex);
    } else {
      // Returns Vec<u8> (postcard bytes) — the compact signed blob the JS
      // layer can base64-encode for paste UX.
      bytes = wasm.create_peer_transition(
        handle,
        Number(agentIdx),
        String(oldCommitHex),
        String(newCommitHex),
        String(effectsHashHex),
      );
    }
    bump();
    fire('peer-transition-created', { agentIdx, bytesLen: bytes?.length || 0 });
    return bytes;
  }
  async function verifyPeerTransition(agentIdx, transitionBytes, peerPubkeyHex) {
    let view;
    if (sdkRuntime) {
      view = await sdkRuntime.verifyPeerTransition(agentIdx, transitionBytes, peerPubkeyHex);
    } else {
      // Returns the updated PeerCellView shape on success; throws with a
      // typed-variant prefix (e.g. "CommitmentMismatch: ...") on failure.
      view = wasm.verify_peer_transition(
        handle,
        Number(agentIdx),
        transitionBytes,
        String(peerPubkeyHex),
      );
    }
    bump();
    fire('peer-transition-verified', { agentIdx, view });
    return view;
  }

  function destroy() {
    if (sdkRuntime) {
      sdkRuntime.destroy();
    } else {
      wasm.destroy_runtime(handle);
    }
  }

  // --- Wave 3 inspector support (notes / conditionals / rev channels) ---
  // Use wasm bindings added in bindings.rs; coarse version dep for reactivity.
  // Note: get_notes is per-agent; others global for the runtime.
  const notesCache = new Map(); // agentIdx -> signal
  function getNotes(agentIdx) {
    const key = String(agentIdx);
    if (!notesCache.has(key)) {
      notesCache.set(key, computed(() => {
        version.value;
        try { return wasm.get_notes(handle, Number(agentIdx)) || []; }
        catch { return []; }
      }));
    }
    return notesCache.get(key);
  }
  const conditionalsSignal = computed(() => {
    version.value;
    try { return wasm.get_pending_conditionals(handle) || []; }
    catch { return []; }
  });
  function listPendingConditionals() { return conditionalsSignal; }
  const revChannelsSignal = computed(() => {
    version.value;
    try { return wasm.list_revocation_channels(handle) || []; }
    catch { return []; }
  });
  function listRevocationChannels() { return revChannelsSignal; }

  return {
    caps: CAPS,
    source: { kind: 'sim', label: 'in-browser sim' },
    version,
    cursor,
    events,

    getCell,
    listCells,
    getReceipt,
    getTurn,
    listReceipts,
    getCapability,
    listCapabilities,
    getIntent,
    listIntents,
    matchIntent,
    getFederation,
    getBlock,
    listBlocks,
    listKnownFederations,
    registerFederation,
    listDeployedFactories,
    compileDfa,
    getTurnTrace,
    getTraceEvents,
    decodePeerTransition,

    // Peer exchange
    getPeerView,
    listPeers,
    getPeerPubkey,
    getCellStateCommitment,
    registerPeer,
    createPeerTransition,
    verifyPeerTransition,

    getNotes,
    listPendingConditionals,
    listRevocationChannels,

    createAgent,
    createCell,
    executeTurn,
    mintToken,
    advanceHeight,
    createFederation,
    createIntent,
    proposeBlock,
    simulateConsensusRound,

    destroy,

    // Escape hatch for spikes/tests: direct wasm + handle access (internal).
    // §4.6 SDK wiring COMPLETE (FOLLOWUP-05): _sdk is the @pyana/sdk PyanaRuntime
    // (all mutators + peer/intent/fed/turn paths are typed). Getters in signals
    // use canonical wasm (SDK does same under the hood; no reimpl, visible
    // only for reactivity driver). starbridge-apps/shared/turn-builders use
    // runtime: PyanaRuntime where passed.
    _wasm: wasm,
    _handle: handle,
    _sdk: sdkRuntime,
  };
}
