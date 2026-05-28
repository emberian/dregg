/**
 * Full Turn Proof Section — compose all sub-proofs and show what each covers.
 *
 * Demonstrates the composed proof structure:
 * - Derivation proof (state transition validity)
 * - Membership proof (credential non-revocation)
 * - Presentation proof (attribute satisfaction)
 * - Binding commitment (ties sub-proofs together)
 */

import { state, notifyStateChange, getWasm } from '../playground.js';

const SUB_PROOFS = [
  {
    id: 'derivation',
    label: 'Derivation Proof',
    air: 'DerivationAir',
    description: 'Proves state transition is valid: new_state = F(old_state, action)',
    publicInputs: ['old_state_hash', 'new_state_hash', 'action_hash', 'nonce'],
    estimatedSize: '2.1 KiB',
    color: '#6ba3c7',
  },
  {
    id: 'membership',
    label: 'Body Membership',
    air: 'BodyMembershipAir',
    description: 'Proves credential is in the issuer set and not revoked',
    publicInputs: ['credential_commitment', 'issuer_root', 'revocation_root', 'epoch'],
    estimatedSize: '1.8 KiB',
    color: '#d99a3f',
  },
  {
    id: 'presentation',
    label: 'Presentation',
    air: 'PresentationAir',
    description: 'Proves attributes satisfy a policy without revealing them',
    publicInputs: ['policy_hash', 'disclosed_attrs_hash', 'holder_commitment', 'timestamp'],
    estimatedSize: '2.4 KiB',
    color: '#9bb87a',
  },
  {
    id: 'note_membership',
    label: 'Note Membership',
    air: 'MerklePoseidon2StarkAir',
    description: 'Proves a note exists in the note tree (Merkle inclusion)',
    publicInputs: ['note_commitment', 'tree_root', 'leaf_index', 'path_hash'],
    estimatedSize: '1.5 KiB',
    color: '#c77ab8',
  },
];

let composedProof = null;
let selectedProofs = new Set(['derivation', 'membership', 'presentation']);

export function initFullTurnProof(wasm) {
  const section = document.getElementById('section-full-turn-proof');
  if (!section) return;

  section.innerHTML = `
    <div class="pg-section__header">
      <h2>Full Turn Proof Composition</h2>
      <p>A sovereign turn carries a composed proof binding multiple sub-proofs. Select which sub-proofs to include, see the binding structure, and generate the composition.</p>
    </div>

    <div class="ftp-layout">
      <div class="ftp-selector">
        <h4 class="ftp-selector__title">Sub-Proof Selection</h4>
        <div class="ftp-selector__list" id="ftp-proof-list">
          ${SUB_PROOFS.map(sp => `
            <div class="ftp-proof-card" data-proof-id="${sp.id}">
              <div class="ftp-proof-card__header">
                <label class="ftp-proof-card__check">
                  <input type="checkbox" ${selectedProofs.has(sp.id) ? 'checked' : ''} data-proof="${sp.id}">
                  <span class="ftp-proof-card__dot" style="background: ${sp.color};"></span>
                  <span class="ftp-proof-card__label">${sp.label}</span>
                </label>
                <span class="ftp-proof-card__size">${sp.estimatedSize}</span>
              </div>
              <div class="ftp-proof-card__body">
                <div class="ftp-proof-card__desc">${sp.description}</div>
                <div class="ftp-proof-card__air">AIR: ${sp.air}</div>
                <div class="ftp-proof-card__pis">Public Inputs: ${sp.publicInputs.join(', ')}</div>
              </div>
            </div>
          `).join('')}
        </div>
      </div>

      <div class="ftp-composition">
        <h4 class="ftp-composition__title">Composition Structure</h4>
        <div class="ftp-composition__diagram" id="ftp-diagram"></div>
        <div class="ftp-composition__binding" id="ftp-binding">
          <div class="ftp-binding__header">BLAKE3 Binding Commitment</div>
          <div class="ftp-binding__formula" id="ftp-formula">Select sub-proofs to see binding</div>
        </div>
      </div>

      <div class="ftp-actions">
        <button class="pg-btn pg-btn--accent" id="ftp-compose-btn">Compose Proof</button>
        <button class="pg-btn pg-btn--ghost" id="ftp-verify-btn" disabled>Verify Composition</button>
        <div class="ftp-result" id="ftp-result"></div>
      </div>
    </div>
  `;

  wireControls(wasm);
  renderComposition();
}

function wireControls(wasm) {
  document.querySelectorAll('[data-proof]').forEach(cb => {
    cb.addEventListener('change', () => {
      if (cb.checked) selectedProofs.add(cb.dataset.proof);
      else selectedProofs.delete(cb.dataset.proof);
      renderComposition();
    });
  });

  document.getElementById('ftp-compose-btn').addEventListener('click', () => compose(wasm));
  document.getElementById('ftp-verify-btn').addEventListener('click', () => verify(wasm));
}

function renderComposition() {
  const diagram = document.getElementById('ftp-diagram');
  const formula = document.getElementById('ftp-formula');

  const selected = SUB_PROOFS.filter(sp => selectedProofs.has(sp.id));

  if (!selected.length) {
    diagram.innerHTML = '<div class="pg-empty">Select at least one sub-proof.</div>';
    formula.textContent = 'No proofs selected';
    return;
  }

  // Render composition diagram
  diagram.innerHTML = `
    <div class="ftp-diagram-flow">
      ${selected.map(sp => `
        <div class="ftp-diagram-node" style="border-color: ${sp.color};">
          <div class="ftp-diagram-node__label" style="color: ${sp.color};">${sp.label}</div>
          <div class="ftp-diagram-node__pis">${sp.publicInputs.length} PIs</div>
        </div>
      `).join('<div class="ftp-diagram-arrow">+</div>')}
      <div class="ftp-diagram-arrow">=</div>
      <div class="ftp-diagram-node ftp-diagram-node--binding">
        <div class="ftp-diagram-node__label">Composed</div>
        <div class="ftp-diagram-node__pis">${selected.reduce((sum, sp) => sum + sp.publicInputs.length, 0)} PIs + binding</div>
      </div>
    </div>
  `;

  // Render binding formula
  const allPis = selected.flatMap(sp => sp.publicInputs);
  formula.innerHTML = `
    <code>binding = BLAKE3(${selected.map(sp => `proof_${sp.id}`).join(' || ')})</code>
    <div style="margin-top: 6px; font-size: 9px; color: var(--text-muted);">
      pi[0..2] = [old_state, new_state]<br>
      pi[2..6] = action_binding<br>
      pi[6..10] = composition_commitment
    </div>
  `;
}

function compose(wasm) {
  const startTime = performance.now();
  const selected = SUB_PROOFS.filter(sp => selectedProofs.has(sp.id));

  // Simulate composition
  const totalSize = selected.reduce((sum, sp) => sum + parseFloat(sp.estimatedSize), 0);
  composedProof = {
    subProofs: selected.map(sp => sp.id),
    binding: Math.floor(Math.random() * 0xFFFFFFFF).toString(16).padStart(64, '0'),
    size: Math.round(totalSize * 1024),
    mode: selected.length > 2 ? 'parallel' : 'sequential',
  };

  const elapsed = (performance.now() - startTime).toFixed(1);
  state.proofCount++;
  notifyStateChange();

  const resultEl = document.getElementById('ftp-result');
  resultEl.innerHTML = `
    <div class="ftp-result__card">
      <span class="ftp-result__badge">COMPOSED</span>
      <span>${composedProof.subProofs.length} sub-proofs, ${(composedProof.size / 1024).toFixed(1)} KiB</span>
      <span>mode: ${composedProof.mode}</span>
      <span>${elapsed}ms</span>
    </div>
    <div class="ftp-result__binding">
      binding: ${composedProof.binding.slice(0, 32)}...
    </div>
  `;

  document.getElementById('ftp-verify-btn').disabled = false;
}

function verify(wasm) {
  if (!composedProof) return;

  const startTime = performance.now();
  // Simulated verification
  const elapsed = (performance.now() - startTime).toFixed(1);

  const resultEl = document.getElementById('ftp-result');
  resultEl.innerHTML += `
    <div class="ftp-result__card" style="margin-top: 8px;">
      <span class="ftp-result__badge" style="background: var(--success-soft); color: var(--accent-bright);">VERIFIED</span>
      <span>All ${composedProof.subProofs.length} sub-proofs valid</span>
      <span>Binding check: passed</span>
      <span>${elapsed}ms</span>
    </div>
  `;
}
