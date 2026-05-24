// Inboxes — send a message to a recipient pubkey, show the ciphertext,
// attempt decrypt with wrong key (fails) vs correct key (succeeds).
//
// Encryption: ECDH(P-256) → HKDF-SHA256 → AES-GCM. The Rust side uses
// X25519 + ChaCha20-Poly1305; WebCrypto exposes P-256 ECDH + AES-GCM
// natively, which is cryptographically equivalent in role for this demo.
// We use the browser's WebCrypto so there's zero third-party JS.

import { mountSection, hex, randomBytes, shortHex } from './_newworld.js';
import { renderInboxLifecycleSvg } from '../visualizers/inbox-lifecycle.js';

async function generateKeypair() {
  return crypto.subtle.generateKey(
    { name: 'ECDH', namedCurve: 'P-256' },
    true,
    ['deriveBits']
  );
}

async function exportPub(pubKey) {
  const raw = await crypto.subtle.exportKey('raw', pubKey);
  return new Uint8Array(raw);
}

async function deriveAesKey(myPriv, theirPubBytes) {
  const theirPub = await crypto.subtle.importKey(
    'raw', theirPubBytes,
    { name: 'ECDH', namedCurve: 'P-256' },
    false, []
  );
  const sharedBits = await crypto.subtle.deriveBits(
    { name: 'ECDH', public: theirPub },
    myPriv, 256
  );
  // HKDF-SHA256 → 32-byte AES-GCM key
  const ikm = await crypto.subtle.importKey('raw', sharedBits, 'HKDF', false, ['deriveKey']);
  return crypto.subtle.deriveKey(
    { name: 'HKDF', hash: 'SHA-256', salt: new Uint8Array(), info: new TextEncoder().encode('pyana-inbox') },
    ikm,
    { name: 'AES-GCM', length: 256 },
    false,
    ['encrypt', 'decrypt']
  );
}

async function encryptTo(myPriv, theirPub, plaintext) {
  const key = await deriveAesKey(myPriv, theirPub);
  const iv = randomBytes(12);
  const ct = await crypto.subtle.encrypt(
    { name: 'AES-GCM', iv }, key, new TextEncoder().encode(plaintext)
  );
  return { iv, ciphertext: new Uint8Array(ct) };
}

async function decryptFrom(myPriv, theirPub, iv, ct) {
  const key = await deriveAesKey(myPriv, theirPub);
  const pt = await crypto.subtle.decrypt(
    { name: 'AES-GCM', iv }, key, ct
  );
  return new TextDecoder().decode(pt);
}

export function initInboxes(_wasm) {
  mountSection('inboxes', (api) => {
    const { html, signal } = api;

    const senderKeys = signal(null);
    const recipientKeys = signal(null);
    const attackerKeys = signal(null);
    const messages = signal([]);   // { iv, ct, state, preview, error? }
    const plaintext = signal('hello from sender — this never appears in cleartext on the wire');
    const log = signal([]);

    function pushLog(msg, kind = 'info') {
      log.value = [...log.value, { msg, kind, t: Date.now() }].slice(-30);
    }

    async function setup() {
      const [s, r, a] = await Promise.all([generateKeypair(), generateKeypair(), generateKeypair()]);
      senderKeys.value = { kp: s, pub: await exportPub(s.publicKey) };
      recipientKeys.value = { kp: r, pub: await exportPub(r.publicKey) };
      attackerKeys.value = { kp: a, pub: await exportPub(a.publicKey) };
      pushLog('generated 3 keypairs (sender, recipient, attacker)', 'ok');
    }
    setup();

    async function send() {
      const sender = senderKeys.value, recip = recipientKeys.value;
      if (!sender || !recip) return;
      const { iv, ciphertext } = await encryptTo(sender.kp.privateKey, recip.pub, plaintext.value);
      messages.value = [...messages.value, {
        iv: hex(iv),
        ct: hex(ciphertext),
        state: 'pending',
        preview: shortHex(hex(ciphertext)),
        senderPub: hex(sender.pub),
      }];
      pushLog(`sent ciphertext ${shortHex(hex(ciphertext))} (${ciphertext.length}B)`, 'ok');
    }

    async function attemptDecrypt(i, attacker) {
      const m = messages.value[i];
      if (!m) return;
      const pub = senderKeys.value.pub;
      const ivBytes = new Uint8Array(m.iv.match(/.{2}/g).map(b => parseInt(b, 16)));
      const ctBytes = new Uint8Array(m.ct.match(/.{2}/g).map(b => parseInt(b, 16)));
      const who = attacker ? attackerKeys.value : recipientKeys.value;
      try {
        const pt = await decryptFrom(who.kp.privateKey, pub, ivBytes, ctBytes);
        messages.value = messages.value.map((mm, j) => j === i ? { ...mm, state: 'decrypted', preview: pt } : mm);
        pushLog(`${attacker ? 'ATTACKER' : 'recipient'} decrypted #${i + 1} → "${pt}"`, attacker ? 'warn' : 'ok');
      } catch (e) {
        messages.value = messages.value.map((mm, j) => j === i ? { ...mm, state: 'failed', error: String(e.message || e) } : mm);
        pushLog(`${attacker ? 'attacker' : 'recipient'} decrypt of #${i + 1} REJECTED — AEAD auth failure`, 'err');
      }
    }

    function clear() { messages.value = []; }

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Inbox demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Encrypted inbox</h3>
          <p class="vizzer__sub">P-256 ECDH + HKDF-SHA256 + AES-GCM (WebCrypto)</p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${clear}>clear</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          <div class="grid-2">
            <label class="field">message
              <textarea rows="2" value=${plaintext.value} onInput=${e => plaintext.value = e.target.value}></textarea>
            </label>
            <div style="display:flex;flex-direction:column;gap:6px;font-family:var(--font-mono);font-size:11px;">
              <div>sender pub: <span class="hex">${senderKeys.value ? shortHex(hex(senderKeys.value.pub)) : '...'}</span></div>
              <div>recipient pub: <span class="hex">${recipientKeys.value ? shortHex(hex(recipientKeys.value.pub)) : '...'}</span></div>
              <div>attacker pub: <span class="hex">${attackerKeys.value ? shortHex(hex(attackerKeys.value.pub)) : '...'}</span></div>
            </div>
          </div>
          <div>
            <button class="inline" onClick=${send} disabled=${!senderKeys.value || !recipientKeys.value}>send (encrypt → push)</button>
          </div>

          ${renderInboxLifecycleSvg(html, messages.value)}

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">queued messages</h3>
            <div style="display:flex;flex-direction:column;gap:6px;">
              ${messages.value.length === 0 ? html`<div style="color:var(--fg-muted);font-family:var(--font-mono);font-size:11px;">none.</div>` : null}
              ${messages.value.map((m, i) => html`
                <div key=${i} style="border:1px solid var(--line);border-radius:var(--r2);padding:8px;display:flex;flex-direction:column;gap:6px;font-family:var(--font-mono);font-size:11px;">
                  <div style="display:flex;gap:8px;align-items:center;">
                    <span class="chip" data-state=${m.state === 'decrypted' ? 'ok' : m.state === 'failed' ? 'err' : 'warn'}>${m.state}</span>
                    <span style="color:var(--fg-dim);">iv: <span class="hex">${shortHex(m.iv)}</span></span>
                    <span style="color:var(--fg-dim);">ct: <span class="hex" title=${m.ct}>${shortHex(m.ct)}</span></span>
                  </div>
                  <div style="color:var(--fg);">${m.state === 'decrypted' ? `plaintext: "${m.preview}"` : m.state === 'failed' ? `error: ${m.error}` : 'opaque ciphertext'}</div>
                  ${m.state === 'pending' ? html`
                    <div style="display:flex;gap:6px;">
                      <button class="inline" onClick=${() => attemptDecrypt(i, false)}>decrypt as recipient</button>
                      <button class="inline" data-tone="danger" onClick=${() => attemptDecrypt(i, true)}>decrypt as attacker</button>
                    </div>
                  ` : null}
                </div>
              `)}
            </div>
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${log.value.length === 0 ? html`<div style="color:var(--fg-muted);">no events.</div>` : null}
              ${log.value.slice().reverse().map((e, i) => html`<div key=${i} class="log__entry" data-kind=${e.kind}>${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Inboxes',
    lede: 'Each recipient publishes a pubkey; senders push AEAD-encrypted messages. Wrong-key attempts hit AEAD authentication failure; correct-key decrypt succeeds.',
    fallback: 'Interactive encrypted-inbox demo using ECDH + AES-GCM.',
  });
}
