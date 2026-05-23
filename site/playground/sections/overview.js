// Overview section — introduction and architecture diagram

import { navigateTo } from '../playground.js';

export function initOverview() {
  const container = document.getElementById('section-overview');
  container.innerHTML = `
    <div class="section-header">
      <h2>Welcome to the Pyana Playground</h2>
      <p>
        Pyana is a distributed object-capability runtime that combines macaroon-style tokens,
        STARK proofs, Merkle commitments, and Datalog policy evaluation into a single coherent
        authorization system. Everything you see here runs entirely in your browser via WebAssembly
        — no server, no backend, no trust assumptions.
      </p>
      <span class="next-hint" data-next="tokens">Start the tour: mint your first token &#8594;</span>
    </div>

    <div class="overview-arch">
      <pre>
                                  +--------------------------+
                                  |    pyana runtime (WASM)  |
                                  +--------------------------+
                                             |
                 +---------------------------+---------------------------+
                 |               |               |               |       |
          +------+------+ +-----+-----+ +------+------+ +------+------+ |
          |   Tokens    | |   Proofs  | |   Merkle    | |   Datalog   | |
          | (macaroon)  | |  (STARK)  | | (BLAKE3 4x) | |  (policy)   | |
          +------+------+ +-----+-----+ +------+------+ +------+------+ |
                 |               |               |               |       |
                 +-------------- + ---- + -------+---- + --------+       |
                                 |      |              |                  |
                          +------+------+------+------+------+           |
                          |         Notes & Nullifiers       |           |
                          |  (private value transfer, UTXO)  |           |
                          +----------------------------------+           |
                                                                         |
                          +----------------------------------+           |
                          |     Capabilities & Delegation    +-----------+
                          |  (attenuation chains, revocation)|
                          +----------------------------------+
                                         |
                          +----------------------------------+
                          |     Cross-Federation Bridge      |
                          | (conditional turns, note bridge) |
                          +----------------------------------+</pre>
    </div>

    <div class="overview-extension-note" style="background:var(--accent-soft);border:1px solid var(--accent);border-radius:6px;padding:12px 16px;margin-bottom:24px;">
      <strong style="color:var(--accent-bright);">Pyana Wallet Extension</strong>
      <span style="color:var(--fg-dim);margin-left:8px;">
        Install the browser extension to manage capabilities and generate STARK proofs from any web page.
        <a href="../extension/" style="color:var(--accent-bright);text-decoration:underline;">Install now</a>
      </span>
    </div>

    <div class="overview-capabilities">
      <div class="overview-cap" data-nav="tokens">
        <div class="overview-cap__title">Tokens</div>
        <div class="overview-cap__desc">Mint root macaroons, attenuate with caveats, verify against policy. HMAC-based, constant-time.</div>
      </div>
      <div class="overview-cap" data-nav="proofs">
        <div class="overview-cap__title">STARK Proofs</div>
        <div class="overview-cap__desc">Generate real zero-knowledge proofs over BabyBear (p=2^31-2^27+1). FRI commitment, transparent setup.</div>
      </div>
      <div class="overview-cap" data-nav="merkle">
        <div class="overview-cap__title">Merkle Trees</div>
        <div class="overview-cap__desc">4-ary BLAKE3 Merkle trees. Membership proofs, absence proofs, incremental updates.</div>
      </div>
      <div class="overview-cap" data-nav="datalog">
        <div class="overview-cap__title">Datalog Policy</div>
        <div class="overview-cap__desc">Evaluate authorization with declarative rules. Full derivation trace, step-by-step reasoning.</div>
      </div>
      <div class="overview-cap" data-nav="notes">
        <div class="overview-cap__title">Private Notes</div>
        <div class="overview-cap__desc">UTXO-style private value transfer. Commitments hide amounts, nullifiers prevent double-spend.</div>
      </div>
      <div class="overview-cap" data-nav="capabilities">
        <div class="overview-cap__title">Capabilities</div>
        <div class="overview-cap__desc">Delegation chains with cryptographic attenuation. Grant, narrow, revoke — monotonically reducing scope.</div>
      </div>
      <div class="overview-cap" data-nav="crossfed">
        <div class="overview-cap__title">Cross-Federation</div>
        <div class="overview-cap__desc">Bridge notes and tokens across federation boundaries with conditional turns and intent matching.</div>
      </div>
      <div class="overview-cap" data-nav="sovereign">
        <div class="overview-cap__title">Sovereign Cells</div>
        <div class="overview-cap__desc">Opt a cell out of consensus. Peer-to-peer exchange with STARK proofs of state validity.</div>
      </div>
      <div class="overview-cap" data-nav="bearer">
        <div class="overview-cap__title">Bearer Caps</div>
        <div class="overview-cap__desc">Proof-carrying authorization. Transfer caps off-chain, exercise instantly. No state update needed.</div>
      </div>
      <div class="overview-cap" data-nav="factories">
        <div class="overview-cap__title">Cell Factories</div>
        <div class="overview-cap__desc">Deploy templates, create cells with verified provenance. Whitelisting and compliance patterns.</div>
      </div>
      <div class="overview-cap" data-nav="private-transfers">
        <div class="overview-cap__title">Private Transfers</div>
        <div class="overview-cap__desc">Stealth addresses + Pedersen commitments. Full sender/recipient/amount privacy with conservation proof.</div>
      </div>
      <div class="overview-cap" data-nav="composition">
        <div class="overview-cap__title">Proof Composition</div>
        <div class="overview-cap__desc">Compose multiple proofs (AND/OR/Chain/Aggregate) into a single verifiable commitment.</div>
      </div>
      <div class="overview-cap" data-nav="gallery">
        <div class="overview-cap__title">Gallery</div>
        <div class="overview-cap__desc">Sealed-bid auctions and AMM swaps. Real-world scenarios composing multiple primitives end-to-end.</div>
      </div>
      <div class="overview-cap" data-nav="sandbox">
        <div class="overview-cap__title">Code Sandbox</div>
        <div class="overview-cap__desc">Write arbitrary JavaScript against the full pyana WASM API. Experiment freely.</div>
      </div>
    </div>
  `;

  // Navigation from overview cards
  container.querySelectorAll('[data-nav]').forEach(el => {
    el.style.cursor = 'pointer';
    el.addEventListener('click', () => navigateTo(el.dataset.nav));
  });

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('tokens'));
}
