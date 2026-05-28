// CI Results section — fetches and displays demo results from CI
// Ported from site/demos/index.html inline script

import { navigateTo } from '../playground.js';

export function initCiResults() {
  const container = document.getElementById('section-ci-results');
  container.innerHTML = `
    <div class="section-header">
      <h2>CI Results</h2>
      <p>
        Real STARK proofs, real Datalog evaluation traces, real timing data.
        This is the actual system running — documentation by execution.
        Generated automatically on every push to <code>main</code>.
      </p>
    </div>

    <div class="ci-meta" id="ci-meta"></div>

    <div class="controls-row" style="margin-bottom: 16px;">
      <div class="control-group" style="flex:1; max-width: 400px;">
        <label>Filter</label>
        <input type="text" id="ci-filter" placeholder="Filter by demo name..." spellcheck="false">
      </div>
      <div class="control-group">
        <label>Show</label>
        <select id="ci-show-filter">
          <option value="all">All</option>
          <option value="pass">Passed only</option>
          <option value="fail">Failed only</option>
        </select>
      </div>
    </div>

    <div class="ci-summary" id="ci-summary"></div>
    <div id="ci-container">
      <div class="ci-loading" id="ci-loading">Loading results...</div>
    </div>
  `;

  const metaEl = container.querySelector('#ci-meta');
  const summaryEl = container.querySelector('#ci-summary');
  const containerEl = container.querySelector('#ci-container');
  const filterInput = container.querySelector('#ci-filter');
  const showFilter = container.querySelector('#ci-show-filter');

  let allResults = [];

  function stripAnsi(str) {
    return str.replace(/\x1b\[[0-9;]*[a-zA-Z]/g, '');
  }

  function formatDuration(ms) {
    if (ms < 1000) return ms + 'ms';
    if (ms < 60000) return (ms / 1000).toFixed(1) + 's';
    return (ms / 60000).toFixed(1) + 'min';
  }

  function formatTimestamp(ts) {
    const d = new Date(ts);
    return d.toLocaleDateString('en-US', {
      year: 'numeric', month: 'short', day: 'numeric',
      hour: '2-digit', minute: '2-digit', timeZoneName: 'short'
    });
  }

  function escapeHtml(str) {
    return str
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  function renderResults(data) {
    allResults = data.results || [];

    // Metadata
    const shortSha = data.commit ? data.commit.substring(0, 8) : '?';
    metaEl.innerHTML = `
      <span class="ci-meta-item">Commit: <a href="https://github.com/emberian/dregg/commit/${data.commit || ''}">${shortSha}</a></span>
      <span class="ci-meta-item">Generated: ${data.timestamp ? formatTimestamp(data.timestamp) : 'unknown'}</span>
    `;

    // Summary stats
    const total = allResults.length;
    const passed = allResults.filter(r => r.exit_code === 0).length;
    const failed = total - passed;
    const totalDuration = allResults.reduce((sum, r) => sum + (r.duration_ms || 0), 0);
    summaryEl.innerHTML = `
      <span class="ci-stat">${total} demos</span>
      <span class="ci-stat ci-stat--pass">${passed} passed</span>
      ${failed > 0 ? `<span class="ci-stat ci-stat--fail">${failed} failed</span>` : ''}
      <span class="ci-stat">Total: ${formatDuration(totalDuration)}</span>
    `;

    applyFilters();
  }

  function applyFilters() {
    const query = filterInput.value.toLowerCase();
    const showMode = showFilter.value;

    // Sort: failures first, then alphabetical
    const sorted = [...allResults].sort((a, b) => {
      if (a.exit_code !== 0 && b.exit_code === 0) return -1;
      if (a.exit_code === 0 && b.exit_code !== 0) return 1;
      return a.name.localeCompare(b.name);
    });

    const filtered = sorted.filter(result => {
      if (query && !result.name.toLowerCase().includes(query)) return false;
      if (showMode === 'pass' && result.exit_code !== 0) return false;
      if (showMode === 'fail' && result.exit_code === 0) return false;
      return true;
    });

    if (filtered.length === 0) {
      containerEl.innerHTML = '<div class="ci-loading">No results match the filter.</div>';
      return;
    }

    containerEl.innerHTML = filtered.map(result => {
      const passed = result.exit_code === 0;
      const badgeClass = passed ? 'ci-badge--pass' : 'ci-badge--fail';
      const badgeText = passed ? 'pass' : 'exit ' + result.exit_code;
      const cleanOutput = stripAnsi(result.output || '(no output)');

      return `
        <details class="ci-card" data-name="${escapeHtml(result.name)}">
          <summary class="ci-card__header">
            <span class="ci-card__chevron">&#x25b6;</span>
            <span class="ci-card__name">${escapeHtml(result.name)}</span>
            <span class="ci-badge ${badgeClass}">${badgeText}</span>
            <span class="ci-card__duration">${formatDuration(result.duration_ms || 0)}</span>
          </summary>
          <div class="ci-card__body">
            <pre class="ci-card__output">${escapeHtml(cleanOutput)}</pre>
          </div>
        </details>
      `;
    }).join('');
  }

  filterInput.addEventListener('input', applyFilters);
  showFilter.addEventListener('change', applyFilters);

  // Fetch results
  fetch('../../demos/results.json')
    .then(r => {
      if (!r.ok) throw new Error('HTTP ' + r.status);
      return r.json();
    })
    .then(renderResults)
    .catch(err => {
      containerEl.innerHTML = `<div class="ci-loading ci-loading--error">
        Could not load results. Run the demos workflow to generate results.json. (${escapeHtml(err.message)})
      </div>`;
    });
}
