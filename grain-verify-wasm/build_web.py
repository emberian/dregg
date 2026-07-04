#!/usr/bin/env python3
"""Assemble the self-contained, CSP-safe renter verifier page.

Reads the wasm-pack `--target web` output in `pkg/` and the sample fixtures in
`web/fixtures/`, and inlines EVERYTHING (wasm as base64, the wasm-bindgen glue
module verbatim, the fixtures as base64) into ONE `web/grain-verify.html` with no
external network of any kind. A renter opens the file, pastes their attestation +
pinned signer, and clicks Verify — the real grain-verify verifier runs in-page.

Run `./build-web.sh` (which builds the wasm first, then calls this).
"""
import base64
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent
PKG = ROOT / "pkg"
FIX = ROOT / "web" / "fixtures"
OUT = ROOT / "web" / "grain-verify.html"

glue = (PKG / "grain_verify_wasm.js").read_text()
wasm_b64 = base64.b64encode((PKG / "grain_verify_wasm_bg.wasm").read_bytes()).decode()


def fx(name: str) -> str:
    p = FIX / name
    return base64.b64encode(p.read_bytes()).decode() if p.exists() else ""


fixtures = {k: fx(f"{k}.json") for k in ("pass", "tampered", "renter", "pins")}

# The glue is an ES module. We keep it verbatim (its `export`s are harmless
# inside our own module) and call `initSync({module: bytes})` after it — that
# path compiles the inlined bytes with NO fetch / NO import.meta.url, so nothing
# touches the network.
HTML = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Grain Verifier — verify your hosted agent, in your browser</title>
<style>
  :root {
    --bg: #f6f7f9; --panel: #ffffff; --ink: #1a1d21; --muted: #5b636d;
    --line: #e2e5ea; --accent: #3a6ea5; --pass: #1a7f47; --pass-bg: #e7f5ec;
    --fail: #b0234a; --fail-bg: #fdecf0; --code-bg: #f0f2f5;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #14161a; --panel: #1c1f25; --ink: #e8eaed; --muted: #9aa2ad;
      --line: #2a2e36; --accent: #7fa8d4; --pass: #6cd39a; --pass-bg: #14301f;
      --fail: #ff8fab; --fail-bg: #34121c; --code-bg: #12141a;
    }
  }
  :root[data-theme="dark"] {
    --bg: #14161a; --panel: #1c1f25; --ink: #e8eaed; --muted: #9aa2ad;
    --line: #2a2e36; --accent: #7fa8d4; --pass: #6cd39a; --pass-bg: #14301f;
    --fail: #ff8fab; --fail-bg: #34121c; --code-bg: #12141a;
  }
  :root[data-theme="light"] {
    --bg: #f6f7f9; --panel: #ffffff; --ink: #1a1d21; --muted: #5b636d;
    --line: #e2e5ea; --accent: #3a6ea5; --pass: #1a7f47; --pass-bg: #e7f5ec;
    --fail: #b0234a; --fail-bg: #fdecf0; --code-bg: #f0f2f5;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0; background: var(--bg); color: var(--ink);
    font: 15px/1.55 -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
  }
  .wrap { max-width: 820px; margin: 0 auto; padding: 32px 20px 80px; }
  h1 { font-size: 1.5rem; margin: 0 0 4px; letter-spacing: -0.01em; }
  .sub { color: var(--muted); margin: 0 0 24px; }
  .panel {
    background: var(--panel); border: 1px solid var(--line); border-radius: 12px;
    padding: 18px 20px; margin: 0 0 18px;
  }
  .panel h2 { font-size: 0.95rem; margin: 0 0 10px; text-transform: uppercase;
    letter-spacing: 0.04em; color: var(--muted); }
  label { display: block; font-weight: 600; margin: 12px 0 4px; font-size: 0.9rem; }
  .hint { color: var(--muted); font-weight: 400; font-size: 0.82rem; }
  textarea, input {
    width: 100%; background: var(--code-bg); color: var(--ink);
    border: 1px solid var(--line); border-radius: 8px; padding: 10px 12px;
    font-family: ui-monospace, "SF Mono", Menlo, monospace; font-size: 0.82rem;
  }
  textarea { min-height: 150px; resize: vertical; }
  .row { display: flex; gap: 12px; flex-wrap: wrap; }
  .row > div { flex: 1 1 260px; }
  .btns { display: flex; gap: 10px; flex-wrap: wrap; margin-top: 16px; align-items: center; }
  button {
    background: var(--accent); color: #fff; border: 0; border-radius: 8px;
    padding: 10px 18px; font-size: 0.9rem; font-weight: 600; cursor: pointer;
  }
  button.ghost { background: transparent; color: var(--accent);
    border: 1px solid var(--line); }
  button:disabled { opacity: 0.5; cursor: not-allowed; }
  .samples { color: var(--muted); font-size: 0.82rem; margin-right: 4px; }
  #verdict { display: none; }
  #verdict.show { display: block; }
  .card { border-radius: 12px; padding: 18px 20px; border: 1px solid var(--line); }
  .card.pass { background: var(--pass-bg); border-color: var(--pass); }
  .card.fail { background: var(--fail-bg); border-color: var(--fail); }
  .badge { font-weight: 700; font-size: 1.05rem; }
  .card.pass .badge { color: var(--pass); }
  .card.fail .badge { color: var(--fail); }
  .grid { display: grid; grid-template-columns: auto 1fr; gap: 4px 16px;
    margin-top: 12px; font-size: 0.88rem; }
  .grid dt { color: var(--muted); }
  .grid dd { margin: 0; font-family: ui-monospace, Menlo, monospace;
    word-break: break-all; }
  .mode { font-size: 0.8rem; color: var(--muted); margin-top: 8px; }
  details { margin-top: 14px; }
  summary { cursor: pointer; color: var(--muted); font-size: 0.85rem; }
  .boundary { font-size: 0.8rem; color: var(--muted); white-space: pre-wrap;
    font-family: ui-monospace, Menlo, monospace; line-height: 1.45;
    background: var(--code-bg); border-radius: 8px; padding: 12px; overflow-x: auto; }
  ul.checks { margin: 8px 0 0; padding-left: 20px; }
  ul.checks li { margin: 3px 0; }
  code { background: var(--code-bg); padding: 1px 5px; border-radius: 4px;
    font-size: 0.85em; }
  .foot { color: var(--muted); font-size: 0.8rem; margin-top: 28px; }
  a { color: var(--accent); }
</style>
</head>
<body>
<div class="wrap">
  <h1>Grain Verifier</h1>
  <p class="sub">Re-witness what your hosted agent did — in this browser tab,
     offline, re-running nothing — with the honest boundary of every check
     stated on this page.</p>

  <div class="panel">
    <h2>What this checks — and what it doesn't</h2>
    <p style="margin:0 0 6px">This runs the real <code>grain-verify</code> verifier
       (compiled to WebAssembly) over the attestation a host hands back — the
       landed ladder R0 → R1 → R2, each optional rung composing with the ones
       below it. A <strong>PASS</strong>, given the signer key you pinned
       out-of-band, means:</p>
    <ul class="checks">
      <li><strong>R0 tamper-evidence</strong> — every receipt is signed, ordered and
          chain-linked under one signer; nothing spliced, reordered or hidden;
          the agent stayed under its budget ceiling at <em>every</em> step and the
          headroom bound is exact. (The host still holds the receipt key — this
          rung alone does not bind a host that forges a self-consistent chain.)</li>
      <li><strong>R1 anti-rewrite + anti-truncation</strong> (when you supply your
          renter pubkey + genesis nonce) — the host neither rewrote nor truncated
          the history relative to a checkpoint you countersigned. This slice is
          host-independent: the host does not hold your key.</li>
      <li><strong>R2 kernel-turn links</strong> (when you supply the executor's
          committed-turn manifest) — every admitted receipt is a view over a
          genuine committed kernel turn, so the meter was enforced host-side by
          the executor's own caveat. (Still trusts the executor host that
          produced the manifest.)</li>
    </ul>
    <p style="margin:10px 0 0" class="hint">It does <strong>not</strong> yet prove
       <em>execution integrity</em> — that each receipted turn was a genuine kernel
       transition — nor <em>completeness</em> ("it did nothing else"). That is R3,
       the whole-history STARK leg, not yet welded (see the honest boundary at the
       bottom). This is the landed R0/R1/R2 ladder, not yet full unfoolability.</p>
  </div>

  <div class="panel">
    <h2>Verify an attestation</h2>
    <label>Attestation JSON <span class="hint">— the artifact the host handed back</span></label>
    <textarea id="att" placeholder="Paste the GrainAttestation JSON here…"></textarea>

    <label>Pinned signer <span class="hint">— the receipt-chain signer key you pinned out-of-band (64 hex chars)</span></label>
    <input id="signer" placeholder="e.g. d1298eba…60fa3b0f" spellcheck="false">

    <div class="row">
      <div>
        <label>Renter pubkey <span class="hint">(optional, R1)</span></label>
        <input id="rpub" placeholder="your ed25519 pubkey (hex)" spellcheck="false">
      </div>
      <div>
        <label>Genesis nonce <span class="hint">(optional, R1)</span></label>
        <input id="nonce" placeholder="the nonce you chose at rent (hex)" spellcheck="false">
      </div>
    </div>

    <label>Committed-turn manifest <span class="hint">(optional, R2) — the JSON
       array of 64-hex turn hashes the executor host committed for this session;
       with it, every receipt must be a view over a committed kernel turn</span></label>
    <textarea id="turns" style="min-height:70px"
       placeholder='["ab12…", "cd34…"] — from the executor host'></textarea>

    <div class="btns">
      <button id="go" disabled>Verify</button>
      <span class="samples">load sample:</span>
      <button class="ghost" data-sample="pass">genuine (PASS)</button>
      <button class="ghost" data-sample="tampered">tampered (FAIL)</button>
      <button class="ghost" data-sample="renter">renter-anchored (PASS)</button>
    </div>
    <p id="status" class="hint" style="margin-top:10px">loading verifier…</p>
  </div>

  <div id="verdict"></div>

  <div class="panel">
    <h2>Honest boundary — what is NOT yet proven</h2>
    <pre class="boundary" id="boundary">…</pre>
  </div>

  <p class="foot">Self-contained: the WebAssembly verifier, its glue, and the
     sample fixtures are all inlined — this page makes no network requests.
     docs/THE-GRAIN.md face #1 (Unfoolable), rungs R0/R1/R2 (R3 is the gap above).
     The samples exercise R0/R1; a kernel-linked (R2) check needs a real
     committed-turn manifest from the executor host. Source:
     <code>grain-verify-wasm</code>.</p>
</div>

<script type="module">
// ── inlined artifacts ───────────────────────────────────────────────────────
const WASM_B64 = "__WASM_B64__";
const FIXTURES = __FIXTURES_JSON__;

function b64ToBytes(b64) {
  const bin = atob(b64);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return bytes;
}
function b64ToText(b64) { return new TextDecoder().decode(b64ToBytes(b64)); }

// ── the wasm-bindgen glue module (verbatim) ─────────────────────────────────
__GLUE__

// ── boot: init from the inlined bytes (no fetch, no import.meta.url) ─────────
initSync({ module: b64ToBytes(WASM_B64) });

const $ = (id) => document.getElementById(id);
$("status").textContent = "verifier ready.";
$("go").disabled = false;
try { $("boundary").textContent = whole_history_gap(); } catch (e) {}

// ── sample loaders ──────────────────────────────────────────────────────────
const pins = FIXTURES.pins ? JSON.parse(b64ToText(FIXTURES.pins)) : {};
for (const btn of document.querySelectorAll("[data-sample]")) {
  btn.addEventListener("click", () => {
    const which = btn.dataset.sample;
    $("att").value = FIXTURES[which] ? b64ToText(FIXTURES[which]) : "";
    if (which === "renter") {
      $("signer").value = pins.renter ? pins.renter.signer : "";
      $("rpub").value = pins.renter ? pins.renter.renter_pubkey : "";
      $("nonce").value = pins.renter ? pins.renter.genesis_nonce : "";
    } else {
      $("signer").value = pins.pass_and_tampered_signer || "";
      $("rpub").value = "";
      $("nonce").value = "";
    }
    $("turns").value = "";
    $("verdict").className = "";
  });
}

// ── verify ──────────────────────────────────────────────────────────────────
function esc(s) { return String(s).replace(/[&<>]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;'}[c])); }

$("go").addEventListener("click", () => {
  const att = $("att").value.trim();
  const signer = $("signer").value.trim();
  const rpub = $("rpub").value.trim() || undefined;
  const nonce = $("nonce").value.trim() || undefined;
  const turns = $("turns").value.trim() || undefined;
  let r;
  try {
    r = verify_attestation(att, signer, rpub, nonce, turns);
  } catch (e) {
    r = { ok: false, mode: "error", error: "verifier threw: " + e };
  }
  renderVerdict(r);
});

function renderVerdict(r) {
  const box = $("verdict");
  box.className = "show";
  if (r.ok) {
    box.innerHTML = `<div class="card pass">
      <div class="badge">✓ PASS — re-witnessed, untampered under the pinned signer</div>
      <p style="margin:8px 0 0">${esc(r.summary || "")}</p>
      <dl class="grid">
        <dt>agent</dt><dd>${esc(r.agent)}</dd>
        <dt>actions</dt><dd>${esc(r.actions)} (signed + ordered)</dd>
        <dt>consumed / budget</dt><dd>${esc(r.consumed)} / ${esc(r.budget)}</dd>
        <dt>headroom</dt><dd>${esc(r.headroom)} (budget − consumed)</dd>
        <dt>signer</dt><dd>${esc(r.signer_hex)}</dd>
        <dt>chain tip</dt><dd>${esc(r.tip_hex || "<none>")}</dd>${
        r.r2_linked != null
          ? `\n        <dt>kernel-linked</dt><dd>${esc(r.r2_linked)} receipt(s) are views over committed turns (R2)</dd>`
          : ""}
      </dl>
      <p class="mode">check: ${esc(r.mode)}${
        r.renter_anchored
          ? " — R1 anti-rewrite + anti-truncation verified"
          : ""}</p>
    </div>`;
  } else {
    box.innerHTML = `<div class="card fail">
      <div class="badge">✗ FAIL — refused</div>
      <p style="margin:8px 0 0">${esc(r.error || "verification failed")}</p>
      <p class="mode">check: ${esc(r.mode || "tamper-evidence (R0)")}</p>
    </div>`;
  }
  box.scrollIntoView({ behavior: "smooth", block: "nearest" });
}
</script>
</body>
</html>
"""

import json as _json

html = (
    HTML.replace("__WASM_B64__", wasm_b64)
    .replace("__FIXTURES_JSON__", _json.dumps(fixtures))
    .replace("__GLUE__", glue)
)
OUT.write_text(html)
print(f"wrote {OUT} ({len(html) // 1024} KiB, self-contained)", file=sys.stderr)
