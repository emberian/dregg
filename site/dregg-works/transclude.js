/* ============================================================================
 * dregg — transclusion for the open web.
 *
 * Drop this one self-contained script onto ANY web page and it turns marked
 * elements into VERIFIED transcluded quotes: the displayed bytes are checked, in
 * the visitor's own browser, against the on-chain commitment of the source cell
 * they claim to quote. The serving host is never trusted; the quoting page is
 * never believed. This is the span-level generalization of the whole-page
 * ./verify-badge.js (same trust story, same standalone blake3).
 *
 * WHAT IT DOES (entirely client-side), per marked element:
 *   1. parses the source ref        -> dregg://<cell>  (+ optional byte range)
 *   2. fetches the source DOCUMENT's bytes from an untrusted host (`cite` /
 *      `data-src`)                  -> blake3(bytes)   (the served body)
 *   3. fetches the cell's slot-0 commitment from a node API the VISITOR can
 *      point anywhere:  GET <node>/api/cell/<cell> -> json.fields[0]
 *   4. compares. ONLY on a match does it slice the quoted byte range out of the
 *      verified bytes and paint the span as a verified transclusion, with its
 *      citation (source ref, range, hash, node link) attached.
 *
 * THE HONEST FALLBACK (the load-bearing part):
 *   - hash mismatch      -> REFUSED chrome. The fetched bytes are NEVER shown;
 *                           the author's own fallback text stays, darkened and
 *                           labeled. A forged quote cannot be opened.
 *   - node/fetch failure -> UNVERIFIED chrome. The fallback text stays darkened
 *                           with the named reason. A failed check is never a
 *                           pass — this script never upgrades a placeholder it
 *                           could not verify.
 *   - no JS / script blocked -> the element renders exactly as the author wrote
 *                           it, carrying no verified styling at all (this
 *                           script owns ALL "verified" chrome; absent script,
 *                           absent claim).
 *
 * WHY THE QUOTE IS UNFORGEABLE (and what a backlink means here):
 *   The cell id is content-addressed and the slot-0 commitment is on-chain, so
 *   the quoting page cannot invent a source: either blake3(served bytes) equals
 *   the commitment the federation attested, or the span refuses. The FORWARD
 *   direction (this script) pins WHAT was quoted; the REVERSE direction — "who
 *   quotes this cell", each observation pinned to a receipt + content
 *   commitment — is the Backlinks registry demonstrated live at /transclusion/
 *   (wasm/src/bindings_transclusion.rs `transclusion_backlinks`). Two halves of
 *   Nelson's two-way link, both facts, neither an index anyone hand-maintains.
 *
 * HOW TO MARK AN ELEMENT (blockquote, span, div — anything):
 *   <blockquote data-dregg="dregg://<64-hex cell id>#b=120-240"
 *               cite="https://any-host.example/charter.html"
 *               data-node="https://<a-node>">
 *     fallback text — shown darkened until (unless) the bytes verify
 *   </blockquote>
 *
 *   - data-dregg      the source ref. `#b=<start>-<end>` selects a byte range
 *                     of the committed document (absent = the whole document).
 *                     Split form also accepted: data-dregg-cell="<64-hex>"
 *                     [data-start=".." data-end=".."].
 *   - cite / data-src where the source document's bytes are served (any host —
 *                     untrusted; data-src wins over cite when both are set).
 *   - data-node       node API base for the commitment lookup (per element).
 *   Page-wide node default: <script src=".../transclude.js" data-node="...">,
 *   <meta name="dregg:node" content="...">, or window.__DREGG__.node — else
 *   DEFAULT_NODE below (the public devnet node, sdk/src/endpoints.rs
 *   `defaults::DEVNET`; if the devnet domain moves, move both).
 *
 * Verified quotes are painted as TEXT (textContent), never as markup: the
 * source's bytes are its own; they do not get to script the quoting page.
 *
 * No build step, no dependencies, no external resources. The blake3 below is
 * the same standalone implementation as ./verify-badge.js, verified
 * byte-for-byte against @noble/hashes across all input lengths (multi-chunk
 * included) and the empty-string test vector.
 * ============================================================================ */
(function () {
  "use strict";

  /* ---------- standalone BLAKE3 (one-shot, 32-byte output) ---------- */
  var IV = new Uint32Array([
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
  ]);
  var MSG = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];
  var CHUNK_START = 1, CHUNK_END = 2, PARENT = 4, ROOT = 8;
  function rotr(x, n) { return ((x >>> n) | (x << (32 - n))) >>> 0; }

  function compress(cv, block, ctrLo, ctrHi, blockLen, flags) {
    var s = new Uint32Array(16);
    for (var i = 0; i < 8; i++) s[i] = cv[i];
    s[8] = IV[0]; s[9] = IV[1]; s[10] = IV[2]; s[11] = IV[3];
    s[12] = ctrLo >>> 0; s[13] = ctrHi >>> 0; s[14] = blockLen >>> 0; s[15] = flags >>> 0;
    var m = block;
    function g(a, b, c, d, mx, my) {
      s[a] = (s[a] + s[b] + mx) >>> 0; s[d] = rotr(s[d] ^ s[a], 16);
      s[c] = (s[c] + s[d]) >>> 0;       s[b] = rotr(s[b] ^ s[c], 12);
      s[a] = (s[a] + s[b] + my) >>> 0; s[d] = rotr(s[d] ^ s[a], 8);
      s[c] = (s[c] + s[d]) >>> 0;       s[b] = rotr(s[b] ^ s[c], 7);
    }
    for (var r = 0; r < 7; r++) {
      g(0, 4, 8, 12, m[0], m[1]);  g(1, 5, 9, 13, m[2], m[3]);
      g(2, 6, 10, 14, m[4], m[5]); g(3, 7, 11, 15, m[6], m[7]);
      g(0, 5, 10, 15, m[8], m[9]); g(1, 6, 11, 12, m[10], m[11]);
      g(2, 7, 8, 13, m[12], m[13]); g(3, 4, 9, 14, m[14], m[15]);
      if (r < 6) { var p = new Uint32Array(16); for (var k = 0; k < 16; k++) p[k] = m[MSG[k]]; m = p; }
    }
    for (var j = 0; j < 8; j++) { s[j] = (s[j] ^ s[j + 8]) >>> 0; s[j + 8] = (s[j + 8] ^ cv[j]) >>> 0; }
    return s;
  }
  function wordsOf(bytes, off, len) {
    var w = new Uint32Array(16);
    for (var i = 0; i < len; i++) w[i >> 2] |= bytes[off + i] << ((i & 3) * 8);
    return w;
  }
  function outputBytes(state) {
    var o = new Uint8Array(32);
    for (var i = 0; i < 8; i++) {
      o[i * 4] = state[i] & 255; o[i * 4 + 1] = (state[i] >>> 8) & 255;
      o[i * 4 + 2] = (state[i] >>> 16) & 255; o[i * 4 + 3] = (state[i] >>> 24) & 255;
    }
    return o;
  }
  function hashChunk(input, off, len, ctr, root) {
    var cv = IV.slice(0, 8);
    var nBlocks = Math.max(1, Math.ceil(len / 64));
    for (var b = 0; b < nBlocks; b++) {
      var bOff = off + b * 64, bLen = Math.min(64, len - b * 64), flags = 0;
      if (b === 0) flags |= CHUNK_START;
      if (b === nBlocks - 1) { flags |= CHUNK_END; if (root) flags |= ROOT; }
      var out = compress(cv, wordsOf(input, bOff, Math.max(0, bLen)),
        ctr & 0xffffffff, Math.floor(ctr / 0x100000000), bLen, flags);
      if (b === nBlocks - 1 && root) return outputBytes(out);
      cv = out.slice(0, 8);
    }
    return cv;
  }
  function parentOut(left, right, root) {
    var block = new Uint32Array(16);
    for (var i = 0; i < 8; i++) { block[i] = left[i]; block[i + 8] = right[i]; }
    var out = compress(IV.slice(0, 8), block, 0, 0, 64, PARENT | (root ? ROOT : 0));
    return root ? outputBytes(out) : out.slice(0, 8);
  }
  function pow2Below(n) { var p = 1; while (p * 2 < n) p *= 2; return p; }
  function hashTree(input, off, len, ctr, root) {
    if (len <= 1024) return hashChunk(input, off, len, ctr, root);
    var nChunks = Math.ceil(len / 1024);
    var leftChunks = pow2Below(nChunks), leftLen = leftChunks * 1024;
    var left = hashTree(input, off, leftLen, ctr, false);
    var right = hashTree(input, off + leftLen, len - leftLen, ctr + leftChunks, false);
    return parentOut(left, right, root);
  }
  function blake3hex(bytes) {
    var out = hashTree(bytes, 0, bytes.length, 0, true), s = "";
    for (var i = 0; i < 32; i++) s += (out[i] < 16 ? "0" : "") + out[i].toString(16);
    return s;
  }

  /* ---------- config: the page-wide default node ---------- */
  // The default cell-lookup node: the public devnet API host from the central
  // endpoints config (sdk/src/endpoints.rs `defaults::DEVNET`). Overridable per
  // element (data-node) and page-wide (script data-node / meta dregg:node /
  // window.__DREGG__.node) — the default only applies when none are set.
  var DEFAULT_NODE = "https://devnet.dregg.fg-goose.online";
  function pageNode() {
    var cfg = (window.__DREGG__ && typeof window.__DREGG__ === "object") ? window.__DREGG__ : {};
    var self = document.currentScript || (function () {
      var ss = document.getElementsByTagName("script");
      for (var i = ss.length - 1; i >= 0; i--) if (/transclude\.js/.test(ss[i].src)) return ss[i];
      return null;
    })();
    function meta(n) { var m = document.querySelector('meta[name="dregg:' + n + '"]'); return m && m.content; }
    var scriptNode = self && self.dataset ? self.dataset.node : null;
    return (scriptNode || meta("node") || cfg.node || DEFAULT_NODE).trim().replace(/\/+$/, "");
  }

  /* ---------- parsing the source ref off an element ---------- */
  // Accepts data-dregg="dregg://<64hex>[#b=<start>-<end>]" or the split form
  // data-dregg-cell="<64hex>" [data-start data-end]. Returns null when the
  // element carries no well-formed ref (rendered as "unconfigured", not a pass).
  function parseRef(el) {
    var cell = null, start = null, end = null;
    var uri = el.getAttribute("data-dregg");
    if (uri) {
      var m = /^dregg:\/\/([0-9a-fA-F]{64})(?:#b=(\d+)-(\d+))?$/.exec(uri.trim());
      if (!m) return null;
      cell = m[1].toLowerCase();
      if (m[2] != null) { start = parseInt(m[2], 10); end = parseInt(m[3], 10); }
    } else {
      var c = (el.getAttribute("data-dregg-cell") || "").trim().toLowerCase().replace(/^0x/, "");
      if (!/^[0-9a-f]{64}$/.test(c)) return null;
      cell = c;
      var ds = el.getAttribute("data-start"), de = el.getAttribute("data-end");
      if (ds != null && de != null) { start = parseInt(ds, 10); end = parseInt(de, 10); }
    }
    if (start != null && !(start >= 0 && end > start)) return null;
    return { cell: cell, start: start, end: end };
  }

  /* ---------- the chrome (self-contained styles, dt- prefix) ---------- */
  function injectStyle() {
    if (document.getElementById("dt-style")) return;
    var css =
      '.dt-q{border-left:3px solid #3a4a41;padding:0.4em 0.9em;margin:0.6em 0;' +
      'transition:filter .25s,opacity .25s,border-color .25s}' +
      '.dt-q.dt-pending,.dt-q.dt-unverified{filter:grayscale(1) brightness(.62)}' +
      '.dt-q.dt-pending>.dt-body,.dt-q.dt-unverified>.dt-body{font-style:italic;opacity:.8}' +
      '.dt-q.dt-verified{border-left-color:#7aab6f;filter:none}' +
      '.dt-q.dt-refused{border-left-color:#d9663f;filter:grayscale(.4) brightness(.75)}' +
      '.dt-q.dt-refused>.dt-body{text-decoration:line-through;opacity:.7}' +
      '.dt-cite{display:block;margin-top:.45em;' +
      'font:11px/1.5 "SF Mono","Cascadia Code","JetBrains Mono",ui-monospace,Menlo,monospace;' +
      'color:#7a7265;word-break:break-all;user-select:text}' +
      '.dt-cite a{color:#7aab6f;text-decoration:none}.dt-cite a:hover{color:#c49245}' +
      '.dt-cite .dt-ok{color:#7aab6f;font-weight:700}' +
      '.dt-cite .dt-bad{color:#d9663f;font-weight:700}' +
      '.dt-cite .dt-dim{color:#c49245;font-weight:700}';
    var st = document.createElement("style");
    st.id = "dt-style"; st.textContent = css;
    document.head.appendChild(st);
  }

  function citeEl(el) {
    var c = el.querySelector(":scope > .dt-cite");
    if (!c) { c = document.createElement("span"); c.className = "dt-cite"; el.appendChild(c); }
    return c;
  }

  // Wrap the element's original children in a .dt-body span once, so the
  // author's fallback text survives every state and the citation line can sit
  // beneath it without clobbering anything.
  function bodyEl(el) {
    var b = el.querySelector(":scope > .dt-body");
    if (!b) {
      b = document.createElement("span");
      b.className = "dt-body";
      while (el.firstChild) b.appendChild(el.firstChild);
      el.appendChild(b);
    }
    return b;
  }

  function shortHex(h) { return String(h || "").slice(0, 8) + "…"; }
  function rangeLabel(ref) {
    return ref.start == null ? "bytes 0..end" : "bytes " + ref.start + ".." + ref.end;
  }

  /* ---------- state painters (only dt-verified ever shows fetched bytes) ---------- */
  function paintPending(el) {
    el.classList.add("dt-q", "dt-pending");
    bodyEl(el); // wrap the fallback text
    citeEl(el).textContent = "verifying transclusion…";
  }
  function paintVerified(el, ref, text, servedHash, node) {
    var body = bodyEl(el);
    body.textContent = text; // TEXT, never markup — the source does not script this page
    el.classList.remove("dt-pending", "dt-unverified", "dt-refused");
    el.classList.add("dt-verified");
    var c = citeEl(el);
    c.innerHTML = "";
    var ok = document.createElement("span");
    ok.className = "dt-ok"; ok.textContent = "✓ verified transclusion";
    var a = document.createElement("a");
    a.href = node + "/api/cell/" + ref.cell; a.target = "_blank"; a.rel = "noopener";
    a.textContent = "dregg://" + shortHex(ref.cell);
    c.appendChild(ok);
    c.appendChild(document.createTextNode(" · "));
    c.appendChild(a);
    c.appendChild(document.createTextNode(
      " · " + rangeLabel(ref) + " · blake3 " + shortHex(servedHash) +
      " · matched the on-chain commitment in your browser"));
  }
  function paintRefused(el, ref, servedHash, committedHash) {
    // The forged bytes are NEVER shown: the author's fallback stays, struck.
    el.classList.remove("dt-pending", "dt-verified", "dt-unverified");
    el.classList.add("dt-refused");
    var c = citeEl(el);
    c.innerHTML = "";
    var bad = document.createElement("span");
    bad.className = "dt-bad"; bad.textContent = "✕ REFUSED — ContentHashMismatch";
    c.appendChild(bad);
    c.appendChild(document.createTextNode(
      " · served blake3 " + shortHex(servedHash) + " ≠ committed " + shortHex(committedHash) +
      " (cell " + shortHex(ref.cell) + ") · the host served bytes the publisher never committed; " +
      "they were not rendered."));
  }
  function paintUnverified(el, reason) {
    el.classList.remove("dt-pending", "dt-verified", "dt-refused");
    el.classList.add("dt-q", "dt-unverified");
    bodyEl(el);
    var c = citeEl(el);
    c.innerHTML = "";
    var dim = document.createElement("span");
    dim.className = "dt-dim"; dim.textContent = "unverified";
    c.appendChild(dim);
    c.appendChild(document.createTextNode(
      " · " + String(reason) + " · a failed check is never a pass — treat this quote as a claim."));
  }

  /* ---------- the per-element check ---------- */
  function verifyOne(el, node) {
    var ref = parseRef(el);
    injectStyle();
    if (!ref) {
      paintUnverified(el, "no well-formed data-dregg ref (want dregg://<64-hex>[#b=start-end])");
      return Promise.resolve();
    }
    paintPending(el);
    var src = el.getAttribute("data-src") || el.getAttribute("cite");
    if (!src) {
      paintUnverified(el, "no source bytes named (set cite= or data-src= to the committed document's URL)");
      return Promise.resolve();
    }
    var elNode = (el.getAttribute("data-node") || node).replace(/\/+$/, "");
    return Promise.all([
      fetch(src, { cache: "no-store" }).then(function (r) {
        if (!r.ok) throw new Error("source fetch " + r.status);
        return r.arrayBuffer();
      }),
      fetch(elNode + "/api/cell/" + ref.cell, { cache: "no-store" }).then(function (r) {
        if (!r.ok) throw new Error("node " + r.status);
        return r.json();
      }),
    ]).then(function (res) {
      var bytes = new Uint8Array(res[0]);
      var served = blake3hex(bytes);
      var detail = res[1] || {};
      if (!detail.found) throw new Error("cell not found on node");
      var committed = ((detail.fields && detail.fields[0]) || "").toLowerCase();
      if (!committed) throw new Error("cell has no slot-0 content commitment");
      if (served !== committed) {
        paintRefused(el, ref, served, committed);
        return;
      }
      // VERIFIED: only now do the bytes become content. Slice the quoted range
      // out of the verified document and paint it, with the citation attached.
      var lo = ref.start == null ? 0 : Math.min(ref.start, bytes.length);
      var hi = ref.end == null ? bytes.length : Math.min(ref.end, bytes.length);
      var text = new TextDecoder("utf-8").decode(bytes.subarray(lo, hi));
      paintVerified(el, ref, text, served, elNode);
    }).catch(function (err) {
      paintUnverified(el, String(err && err.message || err));
    });
  }

  /* ---------- scan + a rescan hook for dynamically added quotes ---------- */
  function run() {
    var node = pageNode();
    var els = document.querySelectorAll("[data-dregg],[data-dregg-cell]");
    for (var i = 0; i < els.length; i++) verifyOne(els[i], node);
  }
  window.dreggTransclude = { rescan: run, version: 1 };

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", run);
  else run();
})();
