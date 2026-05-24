// Settings page script for Pyana Wallet node configuration.

const NODE_CONFIG_KEY = 'pyana_node_config';
const DEFAULT_NODE_URL = 'https://devnet.pyana.fg-goose.online';
const DEFAULT_NODE_WSS_URL = 'wss://devnet.pyana.fg-goose.online/ws';
const DEFAULT_NODE_WS_URL = 'ws://localhost:8420/ws';

const nodeUrlInput = document.getElementById('nodeUrl');
const wssUrlInput = document.getElementById('wssUrl');
const wsUrlInput = document.getElementById('wsUrl');
const devnetKeyInput = document.getElementById('devnetKey');
const saveBtn = document.getElementById('saveBtn');
const resetBtn = document.getElementById('resetBtn');
const testBtn = document.getElementById('testBtn');
const statusMsg = document.getElementById('statusMsg');

function showStatus(message, type) {
  statusMsg.textContent = message;
  statusMsg.className = 'status-msg ' + type;
  if (type === 'success') {
    setTimeout(() => { statusMsg.className = 'status-msg'; }, 4000);
  }
}

async function loadSettings() {
  const stored = await chrome.storage.local.get(NODE_CONFIG_KEY);
  const config = stored[NODE_CONFIG_KEY] || {};
  nodeUrlInput.value = config.nodeUrl || DEFAULT_NODE_URL;
  wssUrlInput.value = config.wssUrl || DEFAULT_NODE_WSS_URL;
  wsUrlInput.value = config.wsUrl || DEFAULT_NODE_WS_URL;
  devnetKeyInput.value = config.devnetKey || '';
}

saveBtn.addEventListener('click', async () => {
  const config = {
    nodeUrl: nodeUrlInput.value.trim() || DEFAULT_NODE_URL,
    wssUrl: wssUrlInput.value.trim() || DEFAULT_NODE_WSS_URL,
    wsUrl: wsUrlInput.value.trim() || DEFAULT_NODE_WS_URL,
    devnetKey: devnetKeyInput.value.trim(),
  };

  // Validate URLs.
  try {
    new URL(config.nodeUrl);
  } catch (_) {
    showStatus('Invalid Node URL format.', 'error');
    return;
  }
  try {
    new URL(config.wssUrl);
  } catch (_) {
    showStatus('Invalid WebSocket URL format.', 'error');
    return;
  }

  // P1-4: confirm with the user if the node hostname is changing.
  // The node URL is where every turn / balance / capability secret goes,
  // so switching it without user consent is equivalent to wallet compromise.
  try {
    const stored = await chrome.storage.local.get(NODE_CONFIG_KEY);
    const oldConfig = stored[NODE_CONFIG_KEY] || {};
    const oldHost = oldConfig.nodeUrl ? new URL(oldConfig.nodeUrl).host : new URL(DEFAULT_NODE_URL).host;
    const newHost = new URL(config.nodeUrl).host;
    if (oldHost !== newHost) {
      const proceed = window.confirm(
        'Changing node host\n\n' +
        'From: ' + oldHost + '\n' +
        'To:   ' + newHost + '\n\n' +
        'All capability secrets, turn submissions, and balance queries will be sent to the new host. ' +
        'Only change this if you trust the new host. Continue?'
      );
      if (!proceed) {
        showStatus('Save cancelled.', 'info');
        return;
      }
    }
  } catch (_e) {
    // If we can't read the old config, fall through and let the user confirm via save.
  }

  // Save via background message (triggers WebSocket reconnect).
  try {
    const response = await chrome.runtime.sendMessage({
      type: 'pyana:setNodeConfig',
      id: 'settings_save',
      config,
    });
    if (response && response.result && response.result.success) {
      showStatus('Settings saved. WebSocket will reconnect to new endpoint.', 'success');
    } else {
      showStatus('Failed to save: ' + (response?.error || 'Unknown error'), 'error');
    }
  } catch (e) {
    // Fallback: save directly to storage if background is unavailable.
    await chrome.storage.local.set({ [NODE_CONFIG_KEY]: config });
    showStatus('Settings saved to storage (background unreachable).', 'info');
  }
});

resetBtn.addEventListener('click', async () => {
  nodeUrlInput.value = DEFAULT_NODE_URL;
  wssUrlInput.value = DEFAULT_NODE_WSS_URL;
  wsUrlInput.value = DEFAULT_NODE_WS_URL;
  devnetKeyInput.value = '';
  showStatus('Fields reset to defaults. Click Save to apply.', 'info');
});

testBtn.addEventListener('click', async () => {
  const nodeUrl = nodeUrlInput.value.trim() || DEFAULT_NODE_URL;
  const devnetKey = devnetKeyInput.value.trim();
  showStatus('Testing connection...', 'info');

  try {
    const headers = { 'Accept': 'application/json' };
    if (devnetKey) {
      headers['X-Devnet-Key'] = devnetKey;
    }
    const resp = await fetch(nodeUrl.replace(/\/$/, '') + '/status', {
      headers,
      signal: AbortSignal.timeout(5000),
    });
    if (resp.ok) {
      const data = await resp.json();
      const info = [];
      if (data.version) info.push('v' + data.version);
      if (data.node_id) info.push('node: ' + data.node_id.slice(0, 12) + '...');
      if (data.height != null) info.push('height: ' + data.height);
      showStatus('Connected successfully. ' + info.join(', '), 'success');
    } else {
      const errText = await resp.text().catch(() => '');
      showStatus(`Node responded with HTTP ${resp.status}: ${errText.slice(0, 100)}`, 'error');
    }
  } catch (e) {
    if (e.name === 'TimeoutError' || e.name === 'AbortError') {
      showStatus('Connection timed out. Is the node running?', 'error');
    } else {
      showStatus('Connection failed: ' + e.message, 'error');
    }
  }
});

// Load settings on page open.
loadSettings();
