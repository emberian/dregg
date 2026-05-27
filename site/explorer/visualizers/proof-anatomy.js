/**
 * Proof Anatomy Visualizer — exploded view of a STARK proof.
 *
 * Parses hex-encoded proofs and shows:
 * - AIR name, trace dimensions, query count
 * - FRI layers with folding structure
 * - Merkle commitment tree
 * - Individual query openings
 * - Proof size breakdown
 *
 * Interface: init(container), update({ hex }), destroy()
 */

export const name = 'proof-anatomy';

let _container = null;

export function init(container) {
  _container = container;
}

export function update(data) {
  if (!_container) return;
  if (data.hex) {
    const parsed = parseProof(data.hex);
    render(parsed);
  }
}

export function destroy() {
  if (_container) _container.innerHTML = '';
  _container = null;
}

function parseProof(hex) {
  // Remove 0x prefix if present
  const cleanHex = hex.startsWith('0x') ? hex.slice(2) : hex;
  const bytes = cleanHex.length / 2;

  // Parse the proof structure based on dregg's STARK proof format
  // Header: [magic(4)] [version(1)] [air_id(1)] [trace_len(4)] [num_cols(2)] [num_queries(2)] [fri_layers(1)]
  // This is a best-effort parse — real proofs follow the serialization from circuit/src/stark.rs

  const result = {
    raw_size: bytes,
    valid: false,
    header: null,
    commitments: [],
    queries: [],
    fri_layers: [],
    metadata: {},
  };

  if (bytes < 14) {
    result.error = 'Too short to be a valid proof (minimum 14 bytes for header)';
    return result;
  }

  try {
    // Parse header
    const magic = cleanHex.slice(0, 8);
    const version = parseInt(cleanHex.slice(8, 10), 16);
    const airId = parseInt(cleanHex.slice(10, 12), 16);
    const traceLen = parseInt(cleanHex.slice(12, 20), 16);
    const numCols = parseInt(cleanHex.slice(20, 24), 16);
    const numQueries = parseInt(cleanHex.slice(24, 28), 16);
    const friLayerCount = parseInt(cleanHex.slice(28, 30), 16);

    // Map AIR IDs to names
    const airNames = {
      0x01: 'DerivationAir',
      0x02: 'FoldAir',
      0x03: 'MultiStepAir',
      0x04: 'BodyMembershipAir',
      0x05: 'PresentationAir',
      0x06: 'Plonky3VerifierAir',
      0x07: 'ChunkedDerivationAir',
      0x10: 'IvcAir',
    };

    result.header = {
      magic: magic === '64726567' ? 'dreg (valid)' : `unknown (${magic})`,
      version,
      air_id: airId,
      air_name: airNames[airId] || `Unknown(0x${airId.toString(16)})`,
      trace_len: traceLen,
      num_cols: numCols,
      num_queries: numQueries,
      fri_layer_count: friLayerCount,
    };

    // Estimate proof components (sizes in bytes)
    const commitmentSize = 32; // Poseidon2 hash
    const queryOpeningSize = numCols * 4 + 32; // field elements + Merkle path
    const friLayerSize = traceLen / 2; // rough estimate

    result.commitments = Array.from({ length: Math.min(3, Math.floor((bytes - 15) / commitmentSize)) }, (_, i) => ({
      index: i,
      type: ['trace', 'constraint', 'quotient'][i] || `layer-${i}`,
      hash: cleanHex.slice(30 + i * 64, 30 + (i + 1) * 64) || '(truncated)',
      offset: 15 + i * commitmentSize,
    }));

    result.queries = Array.from({ length: Math.min(numQueries, 8) }, (_, i) => ({
      index: i,
      estimated_size: queryOpeningSize,
    }));

    result.fri_layers = Array.from({ length: friLayerCount }, (_, i) => ({
      index: i,
      domain_size: traceLen >> (i + 1),
      folding_factor: 2,
    }));

    // Size breakdown
    const headerSize = 15;
    const commitmentsTotal = result.commitments.length * commitmentSize;
    const queriesTotal = numQueries * queryOpeningSize;
    const friTotal = bytes - headerSize - commitmentsTotal - queriesTotal;

    result.metadata = {
      header_bytes: headerSize,
      commitments_bytes: commitmentsTotal,
      queries_bytes: Math.max(0, queriesTotal),
      fri_bytes: Math.max(0, friTotal),
      total_bytes: bytes,
    };

    result.valid = magic === '64726567';
    if (!result.valid) {
      // Still parse as best-effort even if magic doesn't match
      result.valid = true;
      result.header.magic = `(unrecognized magic: ${magic}) — parsing as generic STARK`;
    }

  } catch (e) {
    result.error = `Parse error: ${e.message}`;
  }

  return result;
}

function render(parsed) {
  if (!_container) return;

  if (parsed.error) {
    _container.innerHTML = `
      <div style="padding: 12px; font-family: var(--mono); font-size: 11px; color: var(--danger);">
        Parse Error: ${parsed.error}
      </div>`;
    return;
  }

  const h = parsed.header;
  const m = parsed.metadata;

  _container.innerHTML = `
    <div class="proof-anatomy-view">
      <div class="proof-anatomy__section">
        <div class="proof-anatomy__section-title">HEADER</div>
        <div class="proof-anatomy__grid">
          <span class="proof-anatomy__key">Magic</span><span class="proof-anatomy__val">${h.magic}</span>
          <span class="proof-anatomy__key">Version</span><span class="proof-anatomy__val">${h.version}</span>
          <span class="proof-anatomy__key">AIR</span><span class="proof-anatomy__val" style="color: var(--accent-bright);">${h.air_name}</span>
          <span class="proof-anatomy__key">Trace Length</span><span class="proof-anatomy__val">${h.trace_len.toLocaleString()} rows</span>
          <span class="proof-anatomy__key">Columns</span><span class="proof-anatomy__val">${h.num_cols}</span>
          <span class="proof-anatomy__key">Queries</span><span class="proof-anatomy__val">${h.num_queries}</span>
          <span class="proof-anatomy__key">FRI Layers</span><span class="proof-anatomy__val">${h.fri_layer_count}</span>
        </div>
      </div>

      <div class="proof-anatomy__section">
        <div class="proof-anatomy__section-title">COMMITMENTS (${parsed.commitments.length})</div>
        ${parsed.commitments.map(c => `
          <div class="proof-anatomy__commitment">
            <span class="proof-anatomy__commit-type">${c.type}</span>
            <span class="proof-anatomy__commit-hash">${c.hash.slice(0, 32)}${c.hash.length > 32 ? '...' : ''}</span>
          </div>
        `).join('')}
      </div>

      <div class="proof-anatomy__section">
        <div class="proof-anatomy__section-title">FRI LAYERS (${parsed.fri_layers.length})</div>
        <div class="proof-anatomy__fri-layers">
          ${parsed.fri_layers.map(l => `
            <div class="proof-anatomy__fri-layer">
              <span>Layer ${l.index}</span>
              <span>domain: ${l.domain_size.toLocaleString()}</span>
              <span>fold: ${l.folding_factor}x</span>
            </div>
          `).join('')}
        </div>
      </div>

      <div class="proof-anatomy__section">
        <div class="proof-anatomy__section-title">SIZE BREAKDOWN</div>
        <div class="proof-anatomy__size-bar">
          ${renderSizeBar(m)}
        </div>
        <div class="proof-anatomy__grid" style="margin-top: 8px;">
          <span class="proof-anatomy__key">Header</span><span class="proof-anatomy__val">${m.header_bytes} bytes</span>
          <span class="proof-anatomy__key">Commitments</span><span class="proof-anatomy__val">${m.commitments_bytes} bytes</span>
          <span class="proof-anatomy__key">Query Openings</span><span class="proof-anatomy__val">${m.queries_bytes} bytes</span>
          <span class="proof-anatomy__key">FRI Data</span><span class="proof-anatomy__val">${m.fri_bytes} bytes</span>
          <span class="proof-anatomy__key">Total</span><span class="proof-anatomy__val" style="color: var(--accent-bright);">${m.total_bytes.toLocaleString()} bytes (${(m.total_bytes / 1024).toFixed(1)} KiB)</span>
        </div>
      </div>
    </div>
  `;
}

function renderSizeBar(m) {
  const total = m.total_bytes || 1;
  const segments = [
    { label: 'header', size: m.header_bytes, color: 'var(--info)' },
    { label: 'commits', size: m.commitments_bytes, color: 'var(--accent)' },
    { label: 'queries', size: m.queries_bytes, color: 'var(--lantern)' },
    { label: 'FRI', size: m.fri_bytes, color: 'var(--danger)' },
  ];

  return `<div style="display: flex; height: 8px; border-radius: 4px; overflow: hidden; background: var(--surface-3);">
    ${segments.map(s => {
      const pct = Math.max(0, (s.size / total) * 100);
      return pct > 0 ? `<div style="width: ${pct}%; background: ${s.color};" title="${s.label}: ${s.size}B"></div>` : '';
    }).join('')}
  </div>`;
}
