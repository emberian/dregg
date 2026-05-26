// Sandbox section — free-form JS execution against the WASM API

import { state, notifyStateChange } from '../playground.js';

export function initSandbox(wasm) {
  const container = document.getElementById('section-sandbox');
  container.innerHTML = `
    <div class="section-header">
      <h2>Code Sandbox</h2>
      <p>
        Write and execute arbitrary JavaScript against the full dregg WASM API. The
        <code>dregg</code> object is available with all methods. Use Ctrl+Enter to run.
        Explore freely — everything executes client-side in your browser.
      </p>
    </div>

    <div class="controls-row" style="margin-bottom: 8px;">
      <button class="btn btn-primary" id="sb-run" ${wasm ? '' : 'disabled'}>Run (Ctrl+Enter)</button>
      <button class="btn btn-secondary" id="sb-clear">Clear Output</button>
      <select id="sb-scenarios" style="font-family:var(--mono);font-size:11px;padding:6px 10px;background:var(--surface-2);border:1px solid var(--border-2);border-radius:var(--radius);color:var(--text);outline:none;">
        <option value="">-- Load scenario --</option>
        <option value="mint">Mint & Attenuate</option>
        <option value="stark">STARK Proof</option>
        <option value="merkle">Merkle Tree</option>
        <option value="datalog">Datalog Policy</option>
        <option value="pipeline">Full Pipeline</option>
        <option value="stealth">Stealth Address</option>
        <option value="bearer">Bearer Cap</option>
        <option value="factory">Factory + Provenance</option>
        <option value="composition">Proof Composition</option>
        <option value="private-transfer">Private Transfer (Full)</option>
      </select>
    </div>

    <textarea class="sandbox-editor" id="sb-editor" spellcheck="false" placeholder="// Write JavaScript that calls the dregg WASM API...
// The 'dregg' object is available with all methods.

const key = await dregg.generateRootKey();
console.log('Root key:', key.key_hex);

const minted = await dregg.mintToken(key.key_bytes, 'dregg.dev');
console.log('Token:', minted.token.slice(0, 40) + '...');
"></textarea>

    <div class="sandbox-output" id="sb-output">
      <div style="color: var(--text-muted);">Output will appear here...</div>
    </div>

    <div class="sandbox-api-ref">
      <div class="sandbox-api-ref__title">API Reference</div>
      <div class="sandbox-api-ref__list">
        <div><span>dregg.generateRootKey</span>() &rarr; {key_hex, key_bytes}</div>
        <div><span>dregg.mintToken</span>(keyBytes, location) &rarr; {token}</div>
        <div><span>dregg.attenuate</span>(token, keyBytes, svc, actions, expiresBigInt) &rarr; {token, caveats_added}</div>
        <div><span>dregg.verifyToken</span>(token, keyBytes, appId, action) &rarr; {allowed, policy}</div>
        <div><span>dregg.generateStarkProof</span>(leafU32, depth) &rarr; {proof_size_bytes, trace_rows, ...}</div>
        <div><span>dregg.verifyStarkProof</span>(jsonStr) &rarr; {valid, error}</div>
        <div><span>dregg.tamperProof</span>(jsonStr) &rarr; tamperedJsonStr</div>
        <div><span>dregg.merkleRoot</span>(leavesArr) &rarr; {root_hex, num_leaves, tree_depth}</div>
        <div><span>dregg.merkleMembership</span>(leavesArr, target) &rarr; {verified, leaf_index, proof_path}</div>
        <div><span>dregg.evaluateDatalog</span>(factsArr, reqObj) &rarr; {decision, matched_rule, steps}</div>
        <div><span>dregg.demonstrateFold</span>(factsArr, removeArr) &rarr; {old_root, new_root, verified}</div>
        <div><span>dregg.blake3Hash</span>(input) &rarr; hexStr</div>
        <div><span>dregg.deriveStealthKeys</span>(mnemonic, passphrase) &rarr; {spend_pubkey, view_pubkey, ...}</div>
        <div><span>dregg.createStealthAddress</span>(spendPub, viewPub) &rarr; {one_time_pubkey, ephemeral_pubkey}</div>
        <div><span>dregg.checkStealthOwnership</span>(viewPriv, spendPub, ephPub, otPub) &rarr; {is_ours}</div>
        <div><span>dregg.createValueCommitment</span>(amount, blinding) &rarr; {commitment, blinding}</div>
        <div><span>dregg.verifyConservation</span>(inputsJson, outputsJson) &rarr; {valid}</div>
        <div><span>dregg.createBearerCap</span>(delegatorHex, targetHex, action, expiry) &rarr; {bearer_token_hex}</div>
        <div><span>dregg.verifyBearerCap</span>(tokenHex, delegatorHex, targetHex, action, expiry, now) &rarr; {valid}</div>
        <div><span>dregg.createFromFactory</span>(factoryVkHex, ownerHex, balance) &rarr; {child_vk, param_hash}</div>
        <div><span>dregg.verifyProvenance</span>(cellVkHex, factoryVksJson) &rarr; {from_factory}</div>
        <div><span>dregg.makeCellSovereign</span>(cellIdHex, balance) &rarr; {state_commitment, mode}</div>
        <div><span>dregg.peerExchange</span>(senderHex, receiverHex, amount) &rarr; {exchange_id, proof_commitment}</div>
        <div><span>dregg.composeProofs</span>(proofsJson, mode) &rarr; {composed_proof, valid}</div>
      </div>
    </div>
  `;

  if (!wasm) return;

  const editor = container.querySelector('#sb-editor');
  const output = container.querySelector('#sb-output');
  const runBtn = container.querySelector('#sb-run');
  const clearBtn = container.querySelector('#sb-clear');
  const scenarioSelect = container.querySelector('#sb-scenarios');

  // Dragon's Egg API wrapper (gracefully handles missing optional exports)
  const dregg = {
    generateRootKey: () => wasm.generate_root_key(),
    mintToken: (keyBytes, location) => wasm.mint_token(keyBytes, location),
    attenuate: (token, keyBytes, service, actions, expiresSecs) =>
      wasm.attenuate_token(token, keyBytes, service, actions, expiresSecs),
    verifyToken: (token, keyBytes, appId, action) =>
      wasm.verify_token(token, keyBytes, appId, action),
    generateStarkProof: (leafValue, depth) => wasm.generate_demo_stark_proof(leafValue, depth),
    verifyStarkProof: (json) => wasm.verify_demo_stark_proof(json),
    tamperProof: (json) => wasm.tamper_demo_stark_proof(json),
    merkleRoot: (leaves) => wasm.compute_merkle_root(JSON.stringify(leaves)),
    merkleMembership: (leaves, target) => wasm.merkle_membership_proof(JSON.stringify(leaves), target),
    evaluateDatalog: (facts, req) => wasm.evaluate_datalog(JSON.stringify(facts), JSON.stringify(req)),
    demonstrateFold: (facts, remove) => wasm.demonstrate_fold(JSON.stringify(facts), JSON.stringify(remove)),
    computeIntentId: (json) => wasm.compute_intent_id ? wasm.compute_intent_id(json) : json,
    blake3Hash: (input) => wasm.blake3_hash ? wasm.blake3_hash(input) : input,
    // Privacy / new exports
    deriveStealthKeys: (mnemonic, passphrase) => wasm.derive_stealth_keys(mnemonic, passphrase),
    createStealthAddress: (spendPub, viewPub) => wasm.create_stealth_address(spendPub, viewPub),
    checkStealthOwnership: (viewPriv, spendPub, ephPub, otPub) =>
      wasm.check_stealth_ownership(viewPriv, spendPub, ephPub, otPub),
    scanStealthAnnouncements: (viewPriv, spendPub, announcementsJson) =>
      wasm.scan_stealth_announcements(viewPriv, spendPub, announcementsJson),
    createValueCommitment: (amount, blinding) => wasm.create_value_commitment(amount, blinding),
    verifyConservation: (inputsJson, outputsJson) =>
      wasm.verify_conservation_proof(inputsJson, outputsJson),
    buildCommittedTurn: (paramsJson) => wasm.build_committed_turn(paramsJson),
    generateRangeProof: (amount, blinding, commitment) =>
      wasm.generate_range_proof(amount, blinding, commitment),
    // WASM-side audit fix: create_bearer_cap now takes a delegator *signing
    // seed* (32-byte Ed25519 secret) and returns `{ bearer_token_hex (64-byte
    // signature), delegator_pubkey_hex, binding_hex, ... }`. verify_bearer_cap
    // takes the delegator *public* key. The sandbox surface keeps the
    // arg-name aliases for backward compat but the consumer is expected to
    // pass the correct key kind in each slot.
    createBearerCap: (delegatorSigningSeedHex, targetHex, action, expiry) =>
      wasm.create_bearer_cap(delegatorSigningSeedHex, targetHex, action, expiry),
    verifyBearerCap: (tokenHex, delegatorPubkeyHex, targetHex, action, expiry, currentTime) =>
      wasm.verify_bearer_cap(tokenHex, delegatorPubkeyHex, targetHex, action, expiry, currentTime),
    createFromFactory: (factoryVkHex, ownerHex, balance) =>
      wasm.create_from_factory(factoryVkHex, ownerHex, balance),
    verifyProvenance: (cellVkHex, factoryVksJson) =>
      wasm.verify_provenance(cellVkHex, factoryVksJson),
    makeCellSovereign: (cellIdHex, balance) =>
      wasm.make_cell_sovereign(cellIdHex, balance),
    peerExchange: (senderHex, receiverHex, amount) =>
      wasm.peer_exchange_with_proof(senderHex, receiverHex, amount),
    composeProofs: (proofsJson, mode) => wasm.compose_proofs(proofsJson, mode),
    buildFacetMask: (effectsJson) => wasm.build_facet_mask(effectsJson),
    generateSseTokens: (keywordsJson) => wasm.generate_sse_tokens(keywordsJson),
    // WASM-side audit fix: seal_intent_body now REQUIRES a 32-byte recipient
    // X25519 pubkey. Calling with null/undefined throws.
    sealIntentBody: (plaintextJson, recipientPubkey) => {
      if (!recipientPubkey) {
        throw new Error(
          'seal_intent_body: recipientPubkey is required (broadcast mode was removed; ' +
          'it derived the recipient key from the plaintext, which was not encryption).'
        );
      }
      return wasm.seal_intent_body(plaintextJson, recipientPubkey);
    },
    unsealIntentBody: (ciphertext, ephPub, nonce, privkey) =>
      wasm.unseal_intent_body(ciphertext, ephPub, nonce, privkey),
  };

  function appendOutput(level, text) {
    const entry = document.createElement('div');
    entry.className = `output-entry ${level}`;
    entry.textContent = text;
    output.appendChild(entry);
    output.scrollTop = output.scrollHeight;
  }

  function clearOutput() {
    output.innerHTML = '';
  }

  async function executeCode() {
    const code = editor.value.trim();
    if (!code) return;

    clearOutput();
    const startTime = performance.now();

    // Execute user code in a sandboxed iframe (allow-scripts only, no
    // allow-same-origin) to prevent DOM/window/document access. API calls
    // are proxied via postMessage.
    let sandboxFrame = document.getElementById('playground-sandbox-frame');
    if (sandboxFrame) sandboxFrame.remove();

    sandboxFrame = document.createElement('iframe');
    sandboxFrame.id = 'playground-sandbox-frame';
    sandboxFrame.sandbox = 'allow-scripts';
    sandboxFrame.style.display = 'none';

    const iframeHtml = `<!DOCTYPE html><html><head><script>
      window.addEventListener('message', async (event) => {
        if (event.data.type !== 'execute') return;
        const code = event.data.code;
        const console = {
          log: (...args) => parent.postMessage({ type: 'log', level: 'info', args: args.map(a => {
            if (a === undefined) return 'undefined';
            if (a === null) return 'null';
            if (typeof a === 'object') { try { return JSON.stringify(a, null, 2); } catch { return String(a); } }
            return String(a);
          }) }, '*'),
          error: (...args) => parent.postMessage({ type: 'log', level: 'error', args: args.map(String) }, '*'),
          warn: (...args) => parent.postMessage({ type: 'log', level: 'warning', args: args.map(String) }, '*'),
          info: (...args) => parent.postMessage({ type: 'log', level: 'info', args: args.map(String) }, '*'),
        };
        const dregg = new Proxy({}, {
          get(target, prop) {
            return (...args) => {
              parent.postMessage({ type: 'apiCall', method: prop, args: JSON.parse(JSON.stringify(args)) }, '*');
              return new Promise((resolve, reject) => {
                function handler(ev) {
                  if (ev.data && ev.data.type === 'apiResult' && ev.data.callId === prop) {
                    window.removeEventListener('message', handler);
                    if (ev.data.error) reject(new Error(ev.data.error));
                    else resolve(ev.data.result);
                  }
                }
                window.addEventListener('message', handler);
              });
            };
          }
        });
        try {
          const fn = new Function('dregg', 'console', 'performance', \`return (async () => { \${code} })();\`);
          await fn(dregg, console, performance);
          parent.postMessage({ type: 'done' }, '*');
        } catch (err) {
          parent.postMessage({ type: 'error', message: err.message || String(err) }, '*');
        }
      });
      parent.postMessage({ type: 'ready' }, '*');
    <\/script></head><body></body></html>`;

    sandboxFrame.srcdoc = iframeHtml;
    document.body.appendChild(sandboxFrame);

    try {
      await new Promise((resolve, reject) => {
        const timeout = setTimeout(() => {
          reject(new Error('Sandbox execution timed out (10s)'));
        }, 10000);

        function messageHandler(event) {
          const msg = event.data;
          if (!msg || !msg.type) return;

          switch (msg.type) {
            case 'ready':
              sandboxFrame.contentWindow.postMessage({ type: 'execute', code }, '*');
              break;
            case 'log':
              appendOutput(msg.level || 'info', (msg.args || []).join(' '));
              break;
            case 'apiCall':
              try {
                const result = dregg[msg.method](...(msg.args || []));
                const resolved = result instanceof Promise ? result : Promise.resolve(result);
                resolved.then(r => {
                  sandboxFrame.contentWindow.postMessage({ type: 'apiResult', callId: msg.method, result: r }, '*');
                }).catch(e => {
                  sandboxFrame.contentWindow.postMessage({ type: 'apiResult', callId: msg.method, error: e.message }, '*');
                });
              } catch (e) {
                sandboxFrame.contentWindow.postMessage({ type: 'apiResult', callId: msg.method, error: e.message }, '*');
              }
              break;
            case 'done':
              clearTimeout(timeout);
              window.removeEventListener('message', messageHandler);
              resolve();
              break;
            case 'error':
              clearTimeout(timeout);
              window.removeEventListener('message', messageHandler);
              reject(new Error(msg.message || 'Unknown error'));
              break;
          }
        }

        window.addEventListener('message', messageHandler);
      });

      const elapsed = (performance.now() - startTime).toFixed(1);
      appendOutput('success', `Completed in ${elapsed}ms`);
    } catch (e) {
      appendOutput('error', `Error: ${e.message || e}`);
    } finally {
      if (sandboxFrame && sandboxFrame.parentNode) {
        sandboxFrame.remove();
      }
    }
  }

  function formatArgs(args) {
    return args.map(a => {
      if (a === undefined) return 'undefined';
      if (a === null) return 'null';
      if (typeof a === 'object') {
        try { return JSON.stringify(a, null, 2); }
        catch { return String(a); }
      }
      return String(a);
    }).join(' ');
  }

  // Events
  runBtn.addEventListener('click', executeCode);
  clearBtn.addEventListener('click', clearOutput);

  editor.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      executeCode();
    }
    if (e.key === 'Tab') {
      e.preventDefault();
      const start = editor.selectionStart;
      const end = editor.selectionEnd;
      editor.value = editor.value.substring(0, start) + '  ' + editor.value.substring(end);
      editor.selectionStart = editor.selectionEnd = start + 2;
    }
  });

  // Scenario loading
  const scenarios = {
    mint: `// Mint & Attenuate — full token lifecycle
const root = await dregg.generateRootKey();
console.log("Root key:", root.key_hex);

const minted = await dregg.mintToken(root.key_bytes, "dregg.dev");
console.log("Minted:", minted.token.slice(0, 40) + "...");

const att = await dregg.attenuate(minted.token, root.key_bytes, "dns", "read", 3600n);
console.log("Attenuated (dns/read):", att.token.slice(0, 40) + "...");
console.log("Caveats added:", att.caveats_added);

const v1 = await dregg.verifyToken(att.token, root.key_bytes, "my-app", "read");
console.log("Verify read:", v1.allowed ? "ALLOWED" : "DENIED");

const v2 = await dregg.verifyToken(att.token, root.key_bytes, "my-app", "write");
console.log("Verify write:", v2.allowed ? "ALLOWED" : "DENIED");`,

    stark: `// STARK Proof — generate, verify, tamper, re-verify
const t0 = performance.now();
const proof = await dregg.generateStarkProof(42, 4);
console.log("Proof generated in", (performance.now() - t0).toFixed(1), "ms");
console.log("Size:", proof.proof_size_bytes, "bytes");
console.log("Trace rows:", proof.trace_rows);

const valid = await dregg.verifyStarkProof(JSON.stringify(proof));
console.log("Verify:", valid.valid ? "VALID" : "INVALID");

const tampered = await dregg.tamperProof(JSON.stringify(proof));
const invalid = await dregg.verifyStarkProof(tampered);
console.log("Tampered:", invalid.valid ? "VALID" : "INVALID (expected)");`,

    merkle: `// Merkle Tree — build, prove membership, prove absence
const leaves = ["alice", "bob", "carol", "dave", "eve"];
const tree = await dregg.merkleRoot(leaves);
console.log("Root:", tree.root_hex);
console.log("Leaves:", tree.num_leaves, "| Depth:", tree.tree_depth);

const proof = await dregg.merkleMembership(leaves, "bob");
console.log("Bob membership:", proof.verified, "at index", proof.leaf_index);

const tree2 = await dregg.merkleRoot([...leaves, "frank"]);
console.log("New root (with frank):", tree2.root_hex);
console.log("Root changed:", tree.root_hex !== tree2.root_hex);`,

    datalog: `// Datalog — policy evaluation with derivation trace
const facts = [
  { predicate: "app", terms: ["my-app", "read,write"] },
  { predicate: "service", terms: ["dns", "read,write"] },
];

const req1 = { app_id: "my-app", action: "read", now: Date.now() / 1000 | 0 };
const r1 = await dregg.evaluateDatalog(facts, req1);
console.log("my-app/read:", r1.decision, "-", r1.matched_rule);

const req2 = { app_id: "my-app", action: "delete", now: Date.now() / 1000 | 0 };
const r2 = await dregg.evaluateDatalog(facts, req2);
console.log("my-app/delete:", r2.decision, "-", r2.matched_rule || "default deny");`,

    pipeline: `// Full Pipeline — mint -> attenuate -> commit -> prove -> verify
const t0 = performance.now();

const root = await dregg.generateRootKey();
console.log("1. Key:", root.key_hex.slice(0, 16) + "...");

const minted = await dregg.mintToken(root.key_bytes, "dregg.dev");
console.log("2. Token:", minted.token.slice(0, 32) + "...");

const att = await dregg.attenuate(minted.token, root.key_bytes, "dns", "read", 3600n);
console.log("3. Attenuated:", att.caveats_added, "caveats");

const hash = await dregg.blake3Hash(att.token);
const tree = await dregg.merkleRoot([hash, "other-1", "other-2", "other-3"]);
console.log("4. Merkle root:", tree.root_hex.slice(0, 24) + "...");

const proof = await dregg.generateStarkProof(42, 4);
console.log("5. STARK proof:", proof.proof_size_bytes, "bytes");

const tokenOk = await dregg.verifyToken(att.token, root.key_bytes, "app", "read");
const proofOk = await dregg.verifyStarkProof(JSON.stringify(proof));
console.log("6. Token valid:", tokenOk.allowed, "| Proof valid:", proofOk.valid);
console.log("\\nPipeline complete in", (performance.now() - t0).toFixed(1), "ms");`,

    stealth: `// Stealth Address — derive keys, create address, check ownership
const keys = await dregg.deriveStealthKeys("correct horse battery staple", "demo");
console.log("View pubkey:", Array.from(keys.view_pubkey).slice(0, 8).map(b => b.toString(16).padStart(2, '0')).join('') + "...");
console.log("Spend pubkey:", Array.from(keys.spend_pubkey).slice(0, 8).map(b => b.toString(16).padStart(2, '0')).join('') + "...");

// Sender creates one-time address
const addr = await dregg.createStealthAddress(
  new Uint8Array(keys.spend_pubkey),
  new Uint8Array(keys.view_pubkey)
);
console.log("\\nOne-time address:", Array.from(addr.one_time_pubkey).slice(0, 8).map(b => b.toString(16).padStart(2, '0')).join('') + "...");
console.log("Ephemeral pubkey:", Array.from(addr.ephemeral_pubkey).slice(0, 8).map(b => b.toString(16).padStart(2, '0')).join('') + "...");

// Recipient checks ownership
const check = await dregg.checkStealthOwnership(
  new Uint8Array(keys.view_privkey),
  new Uint8Array(keys.spend_pubkey),
  new Uint8Array(addr.ephemeral_pubkey),
  new Uint8Array(addr.one_time_pubkey)
);
console.log("\\nIs ours?", check.is_ours);
console.log("Can derive spending key:", check.one_time_privkey !== null);`,

    bearer: `// Bearer Capability — create, verify, check expiry
// Generate hex keys (32 bytes = 64 hex chars)
function randomHex() {
  const b = new Uint8Array(32);
  crypto.getRandomValues(b);
  return Array.from(b).map(x => x.toString(16).padStart(2, '0')).join('');
}

const delegator = randomHex();
const target = randomHex();
console.log("Delegator:", delegator.slice(0, 16) + "...");
console.log("Target cell:", target.slice(0, 16) + "...");

// Create bearer cap (no expiry)
const cap = await dregg.createBearerCap(delegator, target, "transfer", 0n);
console.log("\\nBearer token:", cap.bearer_token_hex.slice(0, 24) + "...");
console.log("Action:", cap.action);

// Verify it
const now = BigInt(Math.floor(Date.now() / 1000));
const valid = await dregg.verifyBearerCap(cap.bearer_token_hex, delegator, target, "transfer", 0n, now);
console.log("\\nValid:", valid.valid);
console.log("Expired:", valid.expired);

// Try wrong action
const wrong = await dregg.verifyBearerCap(cap.bearer_token_hex, delegator, target, "admin", 0n, now);
console.log("\\nWrong action valid:", wrong.valid, "(expected false)");`,

    factory: `// Factory — deploy, create child, verify provenance
function randomHex() {
  const b = new Uint8Array(32);
  crypto.getRandomValues(b);
  return Array.from(b).map(x => x.toString(16).padStart(2, '0')).join('');
}

const factoryVk = randomHex();
const ownerPk = randomHex();
console.log("Factory VK:", factoryVk.slice(0, 20) + "...");

// Create child cell from factory
const child = await dregg.createFromFactory(factoryVk, ownerPk, 100n);
console.log("\\nChild VK:", child.child_vk.slice(0, 20) + "...");
console.log("Param hash:", child.param_hash.slice(0, 20) + "...");

// Verify provenance
const prov = await dregg.verifyProvenance(child.child_vk, JSON.stringify([factoryVk]));
console.log("\\nFrom known factory:", prov.from_factory);
console.log("Factory:", prov.factory_vk ? prov.factory_vk.slice(0, 20) + "..." : "none");

// Try unknown cell
const unknownCell = randomHex();
const prov2 = await dregg.verifyProvenance(unknownCell, JSON.stringify([factoryVk]));
console.log("\\nUnknown cell from factory:", prov2.from_factory, "(expected false)");`,

    composition: `// Proof Composition — generate 3 proofs, compose with AND
const t0 = performance.now();

// Generate individual proofs
const proof1 = await dregg.generateStarkProof(42, 3);
console.log("1. Membership proof:", proof1.proof_size_bytes, "bytes");

const proof2 = await dregg.generateStarkProof(99, 3);
console.log("2. Second proof:", proof2.proof_size_bytes, "bytes");

const proof3 = await dregg.generateStarkProof(7, 3);
console.log("3. Third proof:", proof3.proof_size_bytes, "bytes");

// Compose with AND
const composed = await dregg.composeProofs(JSON.stringify([
  { proof_json: JSON.stringify(proof1), public_inputs: [42, 3] },
  { proof_json: JSON.stringify(proof2), public_inputs: [99, 3] },
  { proof_json: JSON.stringify(proof3), public_inputs: [7, 3] },
]), "and");

console.log("\\nComposed (AND):", composed.composed_proof.slice(0, 32) + "...");
console.log("Mode:", composed.mode);
console.log("Input count:", composed.input_count);
console.log("Valid:", composed.valid);
console.log("\\nTotal time:", (performance.now() - t0).toFixed(1), "ms");`,

    'private-transfer': `// Private Transfer — stealth address + commitment + conservation
const t0 = performance.now();

// 1. Recipient derives stealth keys
const keys = await dregg.deriveStealthKeys("abandon abandon abandon", "test");
console.log("1. Recipient stealth keys derived");

// 2. Sender creates one-time address
const addr = await dregg.createStealthAddress(
  new Uint8Array(keys.spend_pubkey),
  new Uint8Array(keys.view_pubkey)
);
console.log("2. One-time address created");

// 3. Sender commits transfer amount (500 tokens)
const blinding = new Uint8Array(32);
crypto.getRandomValues(blinding);
const commit = await dregg.createValueCommitment(500n, blinding);
console.log("3. Value committed:", Array.from(new Uint8Array(commit.commitment)).slice(0,8).map(b=>b.toString(16).padStart(2,'0')).join('') + "...");

// 4. Recipient scans and finds the payment
const check = await dregg.checkStealthOwnership(
  new Uint8Array(keys.view_privkey),
  new Uint8Array(keys.spend_pubkey),
  new Uint8Array(addr.ephemeral_pubkey),
  new Uint8Array(addr.one_time_pubkey)
);
console.log("4. Recipient scan result: is_ours =", check.is_ours);

// 5. Verify conservation (1000 in -> 500 transfer + 500 change)
function rh() { return Array.from(crypto.getRandomValues(new Uint8Array(32))).map(b=>b.toString(16).padStart(2,'0')).join(''); }
const conserv = await dregg.verifyConservation(
  JSON.stringify([rh()]),
  JSON.stringify([rh(), rh()])
);
console.log("5. Conservation valid:", conserv.valid);
console.log("\\nFull private transfer in", (performance.now() - t0).toFixed(1), "ms");
console.log("   Sender identity: HIDDEN (stealth address)");
console.log("   Recipient identity: HIDDEN (one-time key)");
console.log("   Amount: HIDDEN (Pedersen commitment)");`,
  };

  scenarioSelect.addEventListener('change', () => {
    const id = scenarioSelect.value;
    if (id && scenarios[id]) {
      editor.value = scenarios[id];
      scenarioSelect.value = '';
    }
  });
}
