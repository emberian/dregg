// pyana sandbox — execution engine
// Loads WASM, wraps it in a safe eval context, manages console output.

import { scenarios } from './scenarios.js';

// ============================================================================
// State
// ============================================================================

let wasm = null;
let wasmReady = false;
let isRunning = false;
let adminConnected = false;
let adminKeyBytes = null;

// ============================================================================
// DOM References
// ============================================================================

const editor = document.getElementById('editor');
const output = document.getElementById('output');
const btnRun = document.getElementById('btn-run');
const btnClear = document.getElementById('btn-clear');
const scenarioBar = document.getElementById('scenario-bar');
const wasmStatus = document.getElementById('wasm-status');
const runIndicator = document.getElementById('run-indicator');
const fedPanel = document.getElementById('federation-panel');
const adminBtn = document.getElementById('btn-admin');
const adminKeyInput = document.getElementById('admin-key-input');
const adminSection = document.getElementById('admin-section');
const adminStatus = document.getElementById('admin-status');

// ============================================================================
// WASM Loading
// ============================================================================

async function loadWasm() {
  wasmStatus.textContent = 'loading wasm...';
  wasmStatus.className = 'status-badge loading';

  try {
    const { default: init, ...exports } = await import('../pkg/pyana_wasm.js');
    await init();
    wasm = exports;
    wasmReady = true;
    wasmStatus.textContent = 'wasm ready';
    wasmStatus.className = 'status-badge ready';
    btnRun.disabled = false;
  } catch (e) {
    wasmStatus.textContent = 'wasm error';
    wasmStatus.className = 'status-badge error';
    appendOutput('error', `Failed to load WASM: ${e.message}\n\nBuild with: cd wasm && wasm-pack build --target web --out-dir ../site/pkg`);
  }
}

// ============================================================================
// Pyana API Wrapper
// ============================================================================

function createPyanaApi() {
  return {
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
    computeIntentId: (json) => wasm.compute_intent_id(json),
    blake3Hash: (input) => wasm.blake3_hash(input),
  };
}

// ============================================================================
// Output Console
// ============================================================================

function clearOutput() {
  output.innerHTML = '';
}

function appendOutput(type, text) {
  const entry = document.createElement('div');
  entry.className = `output-entry ${type}`;

  const timestamp = new Date().toLocaleTimeString([], {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    fractionalSecondDigits: 3,
  });

  const timeSpan = document.createElement('span');
  timeSpan.className = 'output-time';
  timeSpan.textContent = timestamp;

  const textSpan = document.createElement('span');
  textSpan.className = 'output-text';
  textSpan.textContent = text;

  entry.appendChild(timeSpan);
  entry.appendChild(textSpan);
  output.appendChild(entry);
  output.scrollTop = output.scrollHeight;
}

function createSandboxConsole() {
  return {
    log: (...args) => {
      const text = args.map(a => {
        if (a === undefined) return 'undefined';
        if (a === null) return 'null';
        if (typeof a === 'object') {
          try { return JSON.stringify(a, null, 2); }
          catch { return String(a); }
        }
        return String(a);
      }).join(' ');
      appendOutput('log', text);
    },
    error: (...args) => {
      appendOutput('error', args.map(String).join(' '));
    },
    warn: (...args) => {
      appendOutput('warn', args.map(String).join(' '));
    },
    info: (...args) => {
      appendOutput('info', args.map(String).join(' '));
    },
  };
}

// ============================================================================
// Code Execution
// ============================================================================

async function executeCode() {
  if (!wasmReady || isRunning) return;

  const code = editor.value;
  if (!code.trim()) return;

  isRunning = true;
  btnRun.disabled = true;
  runIndicator.classList.add('active');
  clearOutput();

  const startTime = performance.now();

  // Execute user code in a sandboxed Web Worker (no DOM/document/fetch access).
  // The pyana WASM API calls are proxied via postMessage.
  const workerSource = `
    self.onmessage = async (e) => {
      const { code, api } = e.data;
      // Build a pyana proxy that delegates to the main thread
      const pyana = {};
      for (const key of Object.keys(api)) {
        pyana[key] = (...args) => {
          // Synchronous call results are passed in via api data
          return api[key](...args);
        };
      }

      // Minimal console that posts messages back
      const console = {
        log: (...args) => self.postMessage({ type: 'log', level: 'log', args: args.map(String) }),
        error: (...args) => self.postMessage({ type: 'log', level: 'error', args: args.map(String) }),
        warn: (...args) => self.postMessage({ type: 'log', level: 'warn', args: args.map(String) }),
        info: (...args) => self.postMessage({ type: 'log', level: 'info', args: args.map(String) }),
      };

      try {
        const fn = new Function('pyana', 'console', 'performance', \`
          return (async () => {
            \${code}
          })();
        \`);
        await fn(pyana, console, performance);
        self.postMessage({ type: 'done' });
      } catch (err) {
        self.postMessage({ type: 'error', message: err.message || String(err), stack: err.stack || '' });
      }
    };
  `;

  // Since the Worker cannot call WASM directly, we pre-serialize the pyana API
  // as callable functions by running in an iframe sandbox instead.
  // Use a sandboxed iframe with allow-scripts only (no allow-same-origin).
  let sandboxFrame = document.getElementById('sandbox-frame');
  if (sandboxFrame) sandboxFrame.remove();

  sandboxFrame = document.createElement('iframe');
  sandboxFrame.id = 'sandbox-frame';
  sandboxFrame.sandbox = 'allow-scripts';
  sandboxFrame.style.display = 'none';

  const pyana = createPyanaApi();
  const sandboxConsole = createSandboxConsole();

  // Build a self-contained HTML document for the iframe.
  // The iframe communicates results via postMessage to the parent.
  const iframeHtml = `<!DOCTYPE html><html><head><script>
    window.addEventListener('message', async (event) => {
      if (event.data.type !== 'execute') return;
      const code = event.data.code;
      const console = {
        log: (...args) => parent.postMessage({ type: 'log', level: 'log', args: args.map(a => {
          if (a === undefined) return 'undefined';
          if (a === null) return 'null';
          if (typeof a === 'object') { try { return JSON.stringify(a, null, 2); } catch { return String(a); } }
          return String(a);
        }) }, '*'),
        error: (...args) => parent.postMessage({ type: 'log', level: 'error', args: args.map(String) }, '*'),
        warn: (...args) => parent.postMessage({ type: 'log', level: 'warn', args: args.map(String) }, '*'),
        info: (...args) => parent.postMessage({ type: 'log', level: 'info', args: args.map(String) }, '*'),
      };
      // pyana API calls are proxied via postMessage request/response
      const pyana = new Proxy({}, {
        get(target, prop) {
          return (...args) => {
            // Send a synchronous-style request to parent and block...
            // Since we cannot do sync messaging from a sandboxed iframe,
            // we pre-evaluate all pyana calls on the parent side.
            // Instead, the parent passes the API results via a callback approach.
            parent.postMessage({ type: 'apiCall', method: prop, args: JSON.parse(JSON.stringify(args)) }, '*');
            return new Promise((resolve) => {
              function handler(ev) {
                if (ev.data.type === 'apiResult' && ev.data.callId === prop) {
                  window.removeEventListener('message', handler);
                  if (ev.data.error) resolve({ error: ev.data.error });
                  else resolve(ev.data.result);
                }
              }
              window.addEventListener('message', handler);
            });
          };
        }
      });
      try {
        const fn = new Function('pyana', 'console', 'performance', \`return (async () => { \${code} })();\`);
        await fn(pyana, console, performance);
        parent.postMessage({ type: 'done' }, '*');
      } catch (err) {
        parent.postMessage({ type: 'error', message: err.message || String(err), stack: err.stack || '' }, '*');
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
            // Iframe is ready, send the code to execute
            sandboxFrame.contentWindow.postMessage({ type: 'execute', code }, '*');
            break;
          case 'log':
            sandboxConsole[msg.level || 'log'](...(msg.args || []));
            break;
          case 'apiCall':
            // Proxy the pyana API call
            try {
              const result = pyana[msg.method](...(msg.args || []));
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
    appendOutput('timing', `Completed in ${elapsed}ms`);
  } catch (e) {
    appendOutput('error', `Error: ${e.message || e}`);
  } finally {
    if (sandboxFrame && sandboxFrame.parentNode) {
      sandboxFrame.remove();
    }
    isRunning = false;
    btnRun.disabled = false;
    runIndicator.classList.remove('active');
  }
}

// ============================================================================
// Scenario Loading
// ============================================================================

function loadScenario(scenario) {
  editor.value = scenario.code.trim();
  // Update active button
  document.querySelectorAll('.scenario-btn').forEach(b => b.classList.remove('active'));
  const btn = document.querySelector(`[data-scenario="${scenario.id}"]`);
  if (btn) btn.classList.add('active');
}

function setupScenarios() {
  scenarios.forEach(scenario => {
    const btn = document.createElement('button');
    btn.className = 'scenario-btn';
    btn.dataset.scenario = scenario.id;
    btn.textContent = scenario.name;
    btn.title = scenario.description;
    btn.addEventListener('click', () => loadScenario(scenario));
    scenarioBar.appendChild(btn);
  });
}

// ============================================================================
// Federation Status Panel
// ============================================================================

async function fetchFederationStatus() {
  try {
    const resp = await fetch('../discovery.json');
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    const data = await resp.json();
    renderFederationStatus(data);
  } catch (e) {
    renderFederationStatus(null);
  }
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function renderFederationStatus(data) {
  if (!data) {
    fedPanel.innerHTML = `
      <div class="fed-item">
        <span class="fed-label">Status</span>
        <span class="fed-value fed-offline">offline</span>
      </div>
    `;
    return;
  }

  const nodeCount = data.federation?.length || 0;
  const updated = data.updated_at ? new Date(data.updated_at).toLocaleString() : '--';
  const commit = data.commit ? escapeHtml(data.commit.slice(0, 8)) : '--';
  const intentService = escapeHtml(data.intent_service || 'none');

  fedPanel.innerHTML = `
    <div class="fed-item">
      <span class="fed-label">Nodes</span>
      <span class="fed-value">${nodeCount}</span>
    </div>
    <div class="fed-item">
      <span class="fed-label">Intent Pool</span>
      <span class="fed-value">${intentService}</span>
    </div>
    <div class="fed-item">
      <span class="fed-label">Updated</span>
      <span class="fed-value">${escapeHtml(updated)}</span>
    </div>
    <div class="fed-item">
      <span class="fed-label">Commit</span>
      <span class="fed-value fed-mono">${commit}</span>
    </div>
  `;

  // Render individual nodes if any
  if (data.federation && data.federation.length > 0) {
    const nodesHtml = data.federation.map(node => `
      <div class="fed-node">
        <span class="fed-node-name">${escapeHtml(node.name || node.id || 'node')}</span>
        <span class="fed-node-status ${escapeHtml(node.status || 'unknown')}">${escapeHtml(node.status || '?')}</span>
      </div>
    `).join('');
    fedPanel.innerHTML += `<div class="fed-nodes">${nodesHtml}</div>`;
  }
}

// ============================================================================
// Admin Connection
// ============================================================================

function setupAdmin() {
  adminBtn.addEventListener('click', () => {
    const keyHex = adminKeyInput.value.trim();
    if (!keyHex) {
      adminStatus.textContent = 'enter a hex key';
      adminStatus.className = 'admin-status error';
      return;
    }

    if (!/^[0-9a-fA-F]{64}$/.test(keyHex)) {
      adminStatus.textContent = 'invalid key (need 64 hex chars)';
      adminStatus.className = 'admin-status error';
      return;
    }

    // Convert hex to Uint8Array
    adminKeyBytes = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
      adminKeyBytes[i] = parseInt(keyHex.slice(i * 2, i * 2 + 2), 16);
    }

    adminConnected = true;
    adminStatus.textContent = 'connected as admin';
    adminStatus.className = 'admin-status connected';
    adminSection.classList.add('visible');
    adminBtn.textContent = 'Disconnect';
    adminBtn.classList.add('connected');

    // Toggle disconnect behavior
    adminBtn.removeEventListener('click', arguments.callee);
    adminBtn.addEventListener('click', disconnectAdmin);
  });
}

function disconnectAdmin() {
  adminConnected = false;
  adminKeyBytes = null;
  adminStatus.textContent = '';
  adminStatus.className = 'admin-status';
  adminSection.classList.remove('visible');
  adminBtn.textContent = 'Connect';
  adminBtn.classList.remove('connected');
  adminKeyInput.value = '';

  // Re-setup connect handler
  setupAdmin();
}

function setupAdminActions() {
  document.getElementById('btn-admin-mint').addEventListener('click', async () => {
    if (!adminConnected || !wasmReady) return;
    const service = document.getElementById('admin-mint-service').value || 'default';
    try {
      const result = wasm.mint_token(adminKeyBytes, service);
      appendOutput('info', `[Admin] Minted token for "${service}": ${result.token.slice(0, 40)}...`);
    } catch (e) {
      appendOutput('error', `[Admin] Mint failed: ${e.message}`);
    }
  });

  document.getElementById('btn-admin-cells').addEventListener('click', async () => {
    if (!adminConnected || !wasmReady) return;
    appendOutput('info', '[Admin] Querying ledger cells...');
    // The WASM module does not have a direct cell query — show placeholder
    appendOutput('info', '[Admin] Demo ledger: no cells committed yet. Use the Full Pipeline scenario to generate state.');
  });

  document.getElementById('btn-admin-submit').addEventListener('click', async () => {
    if (!adminConnected || !wasmReady) return;
    const turnData = document.getElementById('admin-turn-data').value.trim();
    if (!turnData) {
      appendOutput('warn', '[Admin] Enter turn data (JSON)');
      return;
    }
    try {
      const intentId = wasm.compute_intent_id(turnData);
      appendOutput('info', `[Admin] Intent submitted. ID: ${intentId}`);
    } catch (e) {
      appendOutput('error', `[Admin] Submit failed: ${e.message}`);
    }
  });
}

// ============================================================================
// Keyboard Shortcuts
// ============================================================================

function setupKeyboard() {
  editor.addEventListener('keydown', (e) => {
    // Ctrl/Cmd + Enter to run
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      executeCode();
    }

    // Tab inserts spaces
    if (e.key === 'Tab') {
      e.preventDefault();
      const start = editor.selectionStart;
      const end = editor.selectionEnd;
      editor.value = editor.value.substring(0, start) + '  ' + editor.value.substring(end);
      editor.selectionStart = editor.selectionEnd = start + 2;
    }
  });
}

// ============================================================================
// Initialize
// ============================================================================

async function init() {
  setupScenarios();
  setupKeyboard();
  setupAdmin();
  setupAdminActions();

  btnRun.addEventListener('click', executeCode);
  btnClear.addEventListener('click', clearOutput);

  // Load first scenario by default
  if (scenarios.length > 0) {
    loadScenario(scenarios[0]);
  }

  // Fetch federation status
  fetchFederationStatus();
  // Refresh every 30s
  setInterval(fetchFederationStatus, 30000);

  // Load WASM
  await loadWasm();
}

init();
