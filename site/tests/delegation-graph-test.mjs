/**
 * Playwright ad-hoc test for <pyana-delegation-graph> inspector.
 *
 * Run with:
 *   node tests/delegation-graph-test.mjs
 *
 * Requires a dev server already running on http://localhost:4818
 * (e.g. `npx serve . -l 4818` from the site/ directory, or the normal
 * `make dev` target).
 *
 * Tests:
 *  1. Default mode: 3 agents created with caps granted between them →
 *     SVG element is present and contains expected node count.
 *  2. Edge arrows rendered: SVG contains .pdg-edge groups matching expected
 *     delegation count.
 *  3. Click a node → pyana:navigate CustomEvent fires with correct URI.
 *  4. Compact mode renders text summary and thumbnail SVG.
 *  5. No JS errors throughout.
 */
import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = 'http://localhost:4818';

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));

  console.log('[test] Navigating to studio...');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Wait for pyana:ready (wasm + Preact signals loaded)
  await page.waitForFunction(() => !!window.pyana, { timeout: 15000 });
  console.log('[test] pyana:ready fired.');

  // Wait for the runtime to be attached to <pyana-app id="app">
  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime;
  }, { timeout: 10000 });
  console.log('[test] runtime attached.');

  // Inject delegation-graph.js (it's not in the studio barrel yet after a cold
  // load; this mirrors how proof-inspector-test.mjs injects its inspector).
  // Actually after our barrel edit it IS imported via inspectors.js — but we
  // add it here idempotently in case the static bundle pre-dates our edit.
  await page.addScriptTag({ url: `${BASE}/_includes/studio/inspectors/delegation-graph.js` });
  console.log('[test] delegation-graph.js injected.');

  // ─── Setup: create 3 agents and grant some caps ───────────────────────────
  // We drive the runtime directly from page.evaluate so we don't depend on
  // studio.html button layout staying stable.

  const setupResult = await page.evaluate(() => {
    const runtime = document.getElementById('app').runtime;
    // Genesis agent (alice) gets a large balance; bob and carol start at 0.
    // Each non-genesis agent creation costs GENESIS_MINT_FEE (2000) from alice.
    // With 3 agents: alice spends 2000 × 2 = 4000 in fees, so 10000 is plenty.
    const alice = runtime.createAgent('alice', 10000);
    const bob   = runtime.createAgent('bob',   0);
    const carol = runtime.createAgent('carol', 0);

    // Use runtime._wasm.grant_capability directly — this is the canonical path
    // for adding edges to the delegation graph without needing signed turns.
    // Signature (S): bob gets a cap pointing at alice's cell
    runtime._wasm.grant_capability(runtime._handle,
      alice.agent_index, bob.agent_index, alice.cell_id, 'Signature');
    // Proof (P): carol gets a cap pointing at alice's cell
    runtime._wasm.grant_capability(runtime._handle,
      alice.agent_index, carol.agent_index, alice.cell_id, 'Proof');
    // None (N): carol gets a cap pointing at bob's cell
    runtime._wasm.grant_capability(runtime._handle,
      bob.agent_index, carol.agent_index, bob.cell_id, 'None');
    // Either (E): bob gets a cap pointing at carol's cell
    runtime._wasm.grant_capability(runtime._handle,
      carol.agent_index, bob.agent_index, carol.cell_id, 'Either');

    return {
      aliceIdx:  alice.agent_index,
      bobIdx:    bob.agent_index,
      carolIdx:  carol.agent_index,
      aliceCell: alice.cell_id,
      bobCell:   bob.cell_id,
      carolCell: carol.cell_id,
    };
  });
  console.log('[test] agents created:', setupResult);

  // ─── Get the raw delegation graph to know expected counts ─────────────────
  const graphShape = await page.evaluate(() => {
    const rt = document.getElementById('app').runtime;
    const g = rt._wasm.get_delegation_graph(rt._handle);
    return { nodeCount: g.nodes.length, edgeCount: g.edges.length };
  });
  console.log(`[test] graph shape: ${graphShape.nodeCount} nodes, ${graphShape.edgeCount} edges`);

  if (graphShape.nodeCount < 3) {
    throw new Error(`TEST FAILED: expected ≥3 nodes, got ${graphShape.nodeCount}`);
  }

  // ─── Test 1: Default mode — mount element, wait for SVG ───────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-delegation-graph');
    el.setAttribute('id', 'test-pdg-default');
    // Wrap in a pyana-app so InspectorBase#findRuntime works
    const app = document.getElementById('app');
    app.appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pdg-default');
    return el && el.querySelector('svg') !== null;
  }, { timeout: 8000 });
  console.log('[test 1] SVG rendered.');

  // Count .pdg-node groups
  const nodeGroupCount = await page.evaluate(() => {
    const el = document.getElementById('test-pdg-default');
    return el.querySelectorAll('.pdg-node').length;
  });
  console.log(`[test 1] .pdg-node groups: ${nodeGroupCount}`);
  if (nodeGroupCount !== graphShape.nodeCount) {
    throw new Error(`TEST FAILED: expected ${graphShape.nodeCount} node groups, got ${nodeGroupCount}`);
  }
  console.log('[test 1] PASS: SVG contains correct node count.');

  // ─── Test 2: Edge groups ───────────────────────────────────────────────────
  const edgeGroupCount = await page.evaluate(() => {
    const el = document.getElementById('test-pdg-default');
    return el.querySelectorAll('.pdg-edge').length;
  });
  console.log(`[test 2] .pdg-edge groups: ${edgeGroupCount}`);
  // We granted 4 caps via grant_capability.
  const minExpectedEdges = 4;
  if (edgeGroupCount < minExpectedEdges) {
    throw new Error(`TEST FAILED: expected ≥${minExpectedEdges} edge groups, got ${edgeGroupCount}`);
  }
  console.log('[test 2] PASS: SVG contains expected edge groups.');

  // ─── Test 3: Click node → pyana:navigate event ────────────────────────────
  const navigateDetail = await page.evaluate(async () => {
    return new Promise((resolve) => {
      const el = document.getElementById('test-pdg-default');
      el.addEventListener('pyana:navigate', (e) => resolve(e.detail), { once: true });
      // Find first .pdg-node circle and dispatch a click on it
      const nodeGroup = el.querySelector('.pdg-node');
      if (nodeGroup) nodeGroup.dispatchEvent(new MouseEvent('click', { bubbles: true }));
      // Timeout fallback
      setTimeout(() => resolve(null), 2000);
    });
  });

  console.log('[test 3] navigate event detail:', navigateDetail);
  if (!navigateDetail || !navigateDetail.uri || !navigateDetail.uri.startsWith('pyana://cell/')) {
    throw new Error(`TEST FAILED: pyana:navigate did not fire with expected URI. Got: ${JSON.stringify(navigateDetail)}`);
  }
  console.log('[test 3] PASS: click dispatches pyana:navigate with pyana://cell/... URI.');

  // ─── Test 4: Compact mode ─────────────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-delegation-graph');
    el.setAttribute('id', 'test-pdg-compact');
    el.setAttribute('mode', 'compact');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-pdg-compact');
    return el && el.children.length > 0;
  }, { timeout: 5000 });

  const compactText = await page.evaluate(() => {
    return document.getElementById('test-pdg-compact').innerText;
  });
  const hasCompactSVG = await page.evaluate(() => {
    return !!document.getElementById('test-pdg-compact').querySelector('svg');
  });
  console.log(`[test 4] compact text: "${compactText}"`);
  console.log(`[test 4] compact has thumbnail SVG: ${hasCompactSVG}`);

  if (!compactText.includes('cell')) {
    throw new Error(`TEST FAILED: compact mode text doesn't mention "cell": "${compactText}"`);
  }
  if (!hasCompactSVG) {
    throw new Error('TEST FAILED: compact mode missing thumbnail SVG');
  }
  console.log('[test 4] PASS: compact mode shows summary text + thumbnail SVG.');

  // ─── Screenshot (for visual inspection) ───────────────────────────────────
  const screenshotPath = '/tmp/delegation-graph-test.png';
  await page.screenshot({ path: screenshotPath, fullPage: false });
  console.log(`[test] screenshot saved to ${screenshotPath}`);

  // ─── Check for JS errors ──────────────────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM') &&
    !e.includes('import statement outside a module') // addScriptTag injects as classic script
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors during run:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message);
  process.exit(1);
});
