/**
 * <pyana-cell-program> — renders a CellProgramView with its slot-caveat tree.
 * <pyana-state-constraint> — renders a single StateConstraintView row.
 *
 * Both are platform-vocabulary elements (not per-app widgets).
 *
 * Usage:
 *   <pyana-cell-program mode="compact|default"></pyana-cell-program>
 *   element.program = cellStateView.program;   // set JS property directly
 *
 * Or pass JSON via attribute:
 *   <pyana-cell-program data-program='{"kind":"Predicate","constraints":[…]}'></pyana-cell-program>
 *
 * CellProgramView shape (from wasm/src/bindings.rs Refactor 6):
 *   { kind: "None" }
 *   { kind: "Predicate", constraints: StateConstraintView[] }
 *   { kind: "Cases", cases: TransitionCaseView[] }
 *   { kind: "Circuit", circuit_hash: string }
 *
 * StateConstraintView: 21+ variants, all tagged with `kind`.
 * All color tokens from site palette (--bg, --fg, --accent, --line, etc).
 */

import { shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Color palette for variant kind-chips.
// Groups map to the semantic categories from NEW-WORLD.md.
// ---------------------------------------------------------------------------

/** Returns a CSS background+color pair for a constraint kind chip. */
function chipColors(kind) {
  switch (kind) {
    // Field equality / comparison
    case 'FieldEquals':
    case 'FieldGte':
    case 'FieldLte':
    case 'SumEquals':
    case 'SumEqualsAcross':
      return 'background:color-mix(in srgb,var(--accent,#5b8a5a) 22%,var(--bg-raised));color:var(--accent-bright,#7db87b)';

    // Write discipline
    case 'WriteOnce':
    case 'Immutable':
      return 'background:color-mix(in srgb,#c8a050 18%,var(--bg-raised));color:#d4b060';

    // Monotonicity / sequence
    case 'Monotonic':
    case 'StrictMonotonic':
    case 'MonotonicSequence':
      return 'background:color-mix(in srgb,#5080c8 20%,var(--bg-raised));color:#7aaae8';

    // Delta / bounded
    case 'FieldDelta':
    case 'FieldDeltaInRange':
    case 'BoundedBy':
    case 'BoundDelta':
      return 'background:color-mix(in srgb,#9060c0 20%,var(--bg-raised));color:#b890e0';

    // Height-relative
    case 'FieldGteHeight':
    case 'FieldLteHeight':
    case 'TemporalGate':
    case 'TemporalPredicate':
      return 'background:color-mix(in srgb,#50a0a8 20%,var(--bg-raised));color:#80c8d0';

    // Auth / sender / capability
    case 'SenderAuthorized':
    case 'CapabilityUniqueness':
      return 'background:color-mix(in srgb,#c86060 20%,var(--bg-raised));color:#e08888';

    // Rate limiting
    case 'RateLimit':
    case 'RateLimitBySum':
      return 'background:color-mix(in srgb,#c87830 20%,var(--bg-raised));color:#e0a058';

    // Crypto gates
    case 'PreimageGate':
    case 'Witnessed':
      return 'background:color-mix(in srgb,#a050a0 22%,var(--bg-raised));color:#d080d0';

    // Transition structure
    case 'AllowedTransitions':
    case 'AnyOf':
      return 'background:color-mix(in srgb,var(--fg,#e4ddd0) 12%,var(--bg-raised));color:var(--fg)';

    // Revocation
    case 'Renounced':
      return 'background:color-mix(in srgb,#d4685c 20%,var(--bg-raised));color:#e08878';

    // Custom / unknown
    case 'Custom':
    default:
      return 'background:color-mix(in srgb,var(--fg-dim,#8a948f) 14%,var(--bg-raised));color:var(--fg-dim)';
  }
}

// ---------------------------------------------------------------------------
// Constraint payload summary — the "most-distinctive" field per variant.
// ---------------------------------------------------------------------------

/** Returns a short inline summary string for the constraint's payload. */
function constraintSummary(c) {
  switch (c.kind) {
    case 'FieldEquals':    return `slot[${c.index}] = ${shortHex(c.value, 10)}`;
    case 'FieldGte':       return `slot[${c.index}] ≥ ${shortHex(c.value, 10)}`;
    case 'FieldLte':       return `slot[${c.index}] ≤ ${shortHex(c.value, 10)}`;
    case 'SumEquals':      return `Σ[${(c.indices||[]).join(',')}] = ${shortHex(c.value, 10)}`;
    case 'SumEqualsAcross': return `Σin[${(c.input_fields||[]).join(',')}] = Σout[${(c.output_fields||[]).join(',')}]`;
    case 'WriteOnce':      return `slot[${c.index}]`;
    case 'Immutable':      return `slot[${c.index}]`;
    case 'Monotonic':      return `slot[${c.index}] non-decreasing`;
    case 'StrictMonotonic':return `slot[${c.index}] strictly increasing`;
    case 'MonotonicSequence': return `seq_slot[${c.seq_index}]`;
    case 'BoundedBy':      return `slot[${c.index}] ≤ witness[${c.witness_index}]`;
    case 'FieldDelta':     return `slot[${c.index}] Δ=${shortHex(c.delta, 10)}`;
    case 'FieldDeltaInRange': return `slot[${c.index}] Δ∈[${shortHex(c.min_delta,6)},${shortHex(c.max_delta,6)}]`;
    case 'FieldGteHeight': {
      const sign = c.offset >= 0 ? `+${c.offset}` : String(c.offset);
      return `slot[${c.index}] ≥ height${sign}`;
    }
    case 'FieldLteHeight': {
      const sign = c.offset >= 0 ? `+${c.offset}` : String(c.offset);
      return `slot[${c.index}] ≤ height${sign}`;
    }
    case 'SenderAuthorized': return `${c.set_kind} commitment=${shortHex(c.commitment, 8)}`;
    case 'CapabilityUniqueness': return `cap_set_root slot[${c.cap_set_root_slot}]`;
    case 'RateLimit':      return `max ${c.max_per_epoch}/epoch (epoch=${c.epoch_duration})`;
    case 'RateLimitBySum': return `slot[${c.slot_index}] Σ≤${c.max_sum_per_epoch}/epoch`;
    case 'TemporalGate': {
      const parts = [];
      if (c.not_before != null) parts.push(`after=${c.not_before}`);
      if (c.not_after  != null) parts.push(`before=${c.not_after}`);
      return parts.length ? parts.join(', ') : 'always';
    }
    case 'PreimageGate':   return `commitment slot[${c.commitment_index}], ${c.hash_kind}`;
    case 'AllowedTransitions': return `slot[${c.slot_index}] ${(c.allowed||[]).length} transitions`;
    case 'AnyOf':          return `${(c.variants||[]).length} alternatives`;
    case 'BoundDelta':     return `slot[${c.local_slot}] ${c.delta_relation} peer ${shortHex(c.peer_cell,8)}[${c.peer_slot}]`;
    case 'TemporalPredicate': return `witness[${c.witness_index}] dsl=${shortHex(c.dsl_hash,8)}`;
    case 'Witnessed':      return `${c.predicate_kind} commitment=${shortHex(c.commitment,8)}`;
    case 'Renounced':      return `${c.set_kind} commitment=${shortHex(c.commitment,8)}`;
    case 'Custom':         return `ir=${shortHex(c.ir_hash,8)}`;
    default:               return '';
  }
}

// ---------------------------------------------------------------------------
// <pyana-state-constraint>
// ---------------------------------------------------------------------------

class PyanaStateConstraint extends HTMLElement {
  static get observedAttributes() { return ['mode']; }

  set constraint(v) {
    this._constraint = v;
    this._doRender();
  }
  get constraint() { return this._constraint; }

  connectedCallback() { this._doRender(); }
  attributeChangedCallback() { this._doRender(); }

  _doRender() {
    const c = this._constraint;
    if (!c) return;
    const mode = this.getAttribute('mode') || 'default';
    const colors = chipColors(c.kind);
    const summary = constraintSummary(c);

    if (mode === 'compact') {
      this.innerHTML = `<span class="pyana-sc pyana-sc--compact">` +
        `<span class="pyana-sc__chip" style="${colors}">${c.kind}</span>` +
        (summary ? ` <span class="pyana-sc__summary">${_esc(summary)}</span>` : '') +
        `</span>`;
      return;
    }

    // Default: one row with chip + summary, expandable for AnyOf
    let extra = '';
    if (c.kind === 'AnyOf' && Array.isArray(c.variants) && c.variants.length) {
      extra = `<ul class="pyana-sc__anyof">` +
        c.variants.map(v => {
          const el = document.createElement('pyana-state-constraint');
          el.setAttribute('mode', 'compact');
          el.constraint = v;
          return `<li>${el.outerHTML}</li>`;
        }).join('') +
        `</ul>`;
      // Can't use outerHTML for custom elements with JS state, so we render manually:
      extra = `<ul class="pyana-sc__anyof">` +
        c.variants.map(v => {
          const ch = chipColors(v.kind);
          const cs = constraintSummary(v);
          return `<li><span class="pyana-sc pyana-sc--compact">` +
            `<span class="pyana-sc__chip" style="${ch}">${_esc(v.kind)}</span>` +
            (cs ? ` <span class="pyana-sc__summary">${_esc(cs)}</span>` : '') +
            `</span></li>`;
        }).join('') +
        `</ul>`;
    }

    this.innerHTML =
      `<div class="pyana-sc pyana-sc--row">` +
        `<span class="pyana-sc__chip" style="${colors}">${_esc(c.kind)}</span>` +
        (summary ? ` <span class="pyana-sc__summary">${_esc(summary)}</span>` : '') +
        extra +
      `</div>`;
  }
}

if (!customElements.get('pyana-state-constraint')) {
  customElements.define('pyana-state-constraint', PyanaStateConstraint);
}

// ---------------------------------------------------------------------------
// <pyana-cell-program>
// ---------------------------------------------------------------------------

class PyanaCellProgram extends HTMLElement {
  static get observedAttributes() { return ['mode', 'data-program']; }

  /** Set program directly as a JS object (preferred from parent cell inspector). */
  set program(v) {
    this._program = v;
    this._doRender();
  }
  get program() { return this._program; }

  connectedCallback() { this._doRender(); }
  attributeChangedCallback() { this._doRender(); }

  _doRender() {
    // Resolve program: JS property wins, then data-program attribute (JSON).
    let prog = this._program;
    if (!prog) {
      const attr = this.getAttribute('data-program');
      if (attr) {
        try { prog = JSON.parse(attr); } catch { /* ignore */ }
      }
    }

    const mode = this.getAttribute('mode') || 'default';

    if (!prog || prog.kind === 'None' || prog.kind == null) {
      this.innerHTML =
        mode === 'compact'
          ? `<span class="pyana-cp pyana-cp--compact pyana-cp--none">None</span>`
          : `<div class="pyana-cp pyana-cp--empty">No program — any authorized state change is valid.</div>`;
      return;
    }

    if (mode === 'compact') {
      this.innerHTML = `<span class="pyana-cp pyana-cp--compact">${_esc(_compactLabel(prog))}</span>`;
      return;
    }

    // Default mode: full expansion
    this.replaceChildren();
    const root = document.createElement('div');
    root.className = 'pyana-cp';

    switch (prog.kind) {
      case 'Predicate': {
        const constraints = prog.constraints || [];
        root.innerHTML =
          `<div class="pyana-cp__header">` +
            `<span class="pyana-cp__kind-badge">Predicate</span>` +
            `<span class="pyana-cp__count">${constraints.length} constraint${constraints.length === 1 ? '' : 's'}</span>` +
          `</div>`;
        if (constraints.length) {
          const list = document.createElement('ul');
          list.className = 'pyana-cp__constraints';
          for (const c of constraints) {
            const li = document.createElement('li');
            const sc = document.createElement('pyana-state-constraint');
            sc.constraint = c;
            li.appendChild(sc);
            list.appendChild(li);
          }
          root.appendChild(list);
        }
        break;
      }

      case 'Cases': {
        const cases = prog.cases || [];
        root.innerHTML =
          `<div class="pyana-cp__header">` +
            `<span class="pyana-cp__kind-badge">Cases</span>` +
            `<span class="pyana-cp__count">${cases.length} case${cases.length === 1 ? '' : 's'}</span>` +
          `</div>`;
        for (let i = 0; i < cases.length; i++) {
          const tc = cases[i];
          const caseEl = document.createElement('div');
          caseEl.className = 'pyana-cp__case';
          caseEl.innerHTML =
            `<div class="pyana-cp__case-guard">` +
              `<span class="pyana-cp__case-idx">#${i}</span>` +
              `<span class="pyana-cp__guard-tag">${_esc(_guardLabel(tc.guard))}</span>` +
            `</div>`;
          if (tc.constraints && tc.constraints.length) {
            const list = document.createElement('ul');
            list.className = 'pyana-cp__constraints pyana-cp__constraints--incase';
            for (const c of tc.constraints) {
              const li = document.createElement('li');
              const sc = document.createElement('pyana-state-constraint');
              sc.constraint = c;
              li.appendChild(sc);
              list.appendChild(li);
            }
            caseEl.appendChild(list);
          } else {
            const empty = document.createElement('div');
            empty.className = 'pyana-cp__case-empty';
            empty.textContent = 'no constraints (pass-through)';
            caseEl.appendChild(empty);
          }
          root.appendChild(caseEl);
        }
        break;
      }

      case 'Circuit': {
        root.innerHTML =
          `<div class="pyana-cp__header">` +
            `<span class="pyana-cp__kind-badge pyana-cp__kind-badge--circuit">Circuit</span>` +
          `</div>` +
          `<div class="pyana-cp__circuit">` +
            `<span class="pyana-cp__circuit-label">VK hash</span>` +
            `<code class="pyana-cp__circuit-hash" title="${_esc(prog.circuit_hash||'')}">${_esc(shortHex(prog.circuit_hash, 24))}</code>` +
          `</div>`;
        break;
      }

      default: {
        root.innerHTML = `<div class="pyana-inspector pyana-inspector--err">unknown program kind: ${_esc(String(prog.kind))}</div>`;
        break;
      }
    }

    this.appendChild(root);
  }
}

if (!customElements.get('pyana-cell-program')) {
  customElements.define('pyana-cell-program', PyanaCellProgram);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function _compactLabel(prog) {
  switch (prog.kind) {
    case 'None':      return 'None';
    case 'Predicate': return `Predicate(${(prog.constraints||[]).length} constraints)`;
    case 'Cases':     return `Cases(${(prog.cases||[]).length})`;
    case 'Circuit':   return `Circuit(${shortHex(prog.circuit_hash, 8)})`;
    default:          return prog.kind;
  }
}

function _guardLabel(guard) {
  if (!guard) return 'always';
  switch (guard.kind) {
    case 'Always':        return 'always';
    case 'MethodIs':      return `method=${shortHex(guard.method, 8)}`;
    case 'EffectKindIs':  return `effect_mask=0x${(guard.mask||0).toString(16)}`;
    case 'SlotChanged':   return `slot[${guard.index}] changed`;
    case 'AnyOf':         return `anyOf(${(guard.children||[]).length})`;
    case 'AllOf':         return `allOf(${(guard.children||[]).length})`;
    default:              return guard.kind || 'unknown';
  }
}

/** Minimal HTML escape for inline string injection. */
function _esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

// ---------------------------------------------------------------------------
// Styles — injected once into document head.
// Uses only site-palette tokens; no fresh color literals beyond the chip
// tints above (which also derive from the palette via color-mix).
// ---------------------------------------------------------------------------

(function injectStyles() {
  if (document.getElementById('pyana-cell-program-styles')) return;
  const s = document.createElement('style');
  s.id = 'pyana-cell-program-styles';
  s.textContent = `
/* ---- <pyana-cell-program> ---- */
.pyana-cp {
  font-family: var(--font-mono, ui-monospace, monospace);
  font-size: 0.85rem;
}
.pyana-cp--compact {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding: 2px 8px;
  background: var(--bg-raised);
  border: 1px solid var(--line);
  border-radius: 4px;
  font-size: 0.82rem;
  color: var(--fg);
}
.pyana-cp--none {
  color: var(--fg-dim);
  border-style: dashed;
}
.pyana-cp--empty {
  color: var(--fg-dim);
  padding: var(--s2, 6px) var(--s3, 10px);
  border: 1px dashed var(--line);
  border-radius: 4px;
  font-size: 0.82rem;
}
.pyana-cp__header {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: var(--s2, 6px);
  padding-bottom: var(--s2, 6px);
  border-bottom: 1px solid var(--line);
}
.pyana-cp__kind-badge {
  padding: 2px 10px;
  background: var(--accent, #5b8a5a);
  color: #0a0f0d;
  border-radius: 3px;
  font-size: 0.72rem;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.05em;
}
.pyana-cp__kind-badge--circuit {
  background: color-mix(in srgb, #a050a0 80%, var(--bg));
  color: #fff;
}
.pyana-cp__count {
  font-size: 0.78rem;
  color: var(--fg-dim);
}
.pyana-cp__constraints {
  list-style: none;
  padding: 0;
  margin: 0;
  display: flex;
  flex-direction: column;
  gap: 4px;
}
.pyana-cp__constraints--incase {
  margin-left: var(--s4, 16px);
  margin-top: 4px;
}
.pyana-cp__case {
  margin-bottom: var(--s3, 10px);
  padding: var(--s2, 6px) var(--s3, 10px);
  background: var(--bg-raised);
  border: 1px solid var(--line);
  border-radius: 4px;
}
.pyana-cp__case-guard {
  display: flex;
  align-items: center;
  gap: 6px;
  margin-bottom: 6px;
  font-size: 0.78rem;
  color: var(--fg-dim);
}
.pyana-cp__case-idx {
  font-size: 0.72rem;
  color: var(--fg-muted, var(--fg-dim));
  min-width: 1.8em;
}
.pyana-cp__guard-tag {
  padding: 1px 7px;
  background: color-mix(in srgb, var(--fg-dim) 12%, var(--bg-raised));
  border: 1px solid var(--line-strong, var(--line));
  border-radius: 3px;
  font-size: 0.72rem;
  color: var(--fg-dim);
}
.pyana-cp__case-empty {
  font-size: 0.78rem;
  color: var(--fg-dim);
  padding-left: var(--s4, 16px);
  font-style: italic;
}
.pyana-cp__circuit {
  display: flex;
  align-items: center;
  gap: var(--s3, 10px);
  padding: var(--s2, 6px) 0;
}
.pyana-cp__circuit-label {
  font-size: 0.75rem;
  color: var(--fg-dim);
  text-transform: uppercase;
  letter-spacing: 0.05em;
}
.pyana-cp__circuit-hash {
  font-size: 0.82rem;
  color: var(--fg);
  word-break: break-all;
}

/* ---- <pyana-state-constraint> ---- */
.pyana-sc {
  font-family: var(--font-mono, ui-monospace, monospace);
  font-size: 0.82rem;
}
.pyana-sc--compact {
  display: inline-flex;
  align-items: center;
  gap: 6px;
}
.pyana-sc--row {
  display: flex;
  align-items: baseline;
  flex-wrap: wrap;
  gap: 6px;
  padding: 3px 0;
}
.pyana-sc__chip {
  display: inline-block;
  padding: 1px 7px;
  border-radius: 3px;
  font-size: 0.72rem;
  font-weight: 600;
  text-transform: none;
  letter-spacing: 0.02em;
  white-space: nowrap;
}
.pyana-sc__summary {
  color: var(--fg-dim);
  font-size: 0.80rem;
}
.pyana-sc__anyof {
  list-style: none;
  padding: 0;
  margin: 4px 0 0 var(--s4, 16px);
  display: flex;
  flex-direction: column;
  gap: 3px;
  width: 100%;
}
`;
  document.head.appendChild(s);
})();
