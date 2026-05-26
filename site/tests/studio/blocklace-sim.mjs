/**
 * Playwright test for <pyana-blocklace-sim> inspector.
 *
 * Run with:
 *   node tests/studio/blocklace-sim.mjs
 *
 * Requires the site served on port 8080:
 *   npx serve . -l 8080   (from /Users/ember/dev/breadstuffs/site)
 *
 * Tests:
 *  1. Component mounts and renders SVG after tick()
 *  2. tick(n) advances simulation by exactly n ticks
 *  3. tau ordering is non-empty after enough ticks
 *  4. SVG circle elements are present
 *  5. Equivocator injection: red blocks appear with equivocator-index set
 *  6. Compact mode renders summary text
 *  7. reset() clears all blocks
 *  8. getState() returns correct shape
 *  9. node-count attribute respected (5 nodes → 5 column headers)
 * 10. No unexpected JS errors
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

const BASE = 'http://localhost:8080';
const INSPECTOR_URL = `${BASE}/_includes/studio/inspectors/blocklace-sim.js`;

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => {
    if (msg.type() === 'error') errors.push(`[console.error] ${msg.text()}`);
  });

  // Navigate to a minimal HTML page (studio serves static files; use /studio as base).
  console.log('[test] Navigating to /studio …');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Inject the blocklace-sim inspector as a module.
  await page.addScriptTag({ url: INSPECTOR_URL, type: 'module' });

  // Wait for the custom element to register.
  await page.waitForFunction(() => !!customElements.get('pyana-blocklace-sim'), { timeout: 10000 });
  console.log('[test] <pyana-blocklace-sim> registered.');

  // Mount the element directly in the document body (outside pyana-app; it's self-contained).
  await page.evaluate(() => {
    const el = document.createElement('pyana-blocklace-sim');
    el.setAttribute('node-count', '4');
    el.setAttribute('id', 'test-sim');
    document.body.appendChild(el);
  });

  // Wait for the component to render its internal DOM.
  await page.waitForFunction(() => {
    const el = document.getElementById('test-sim');
    return el && el.children.length > 0;
  }, { timeout: 5000 });
  console.log('[test] component rendered.');

  // ─── Test 1: tick(5) produces 5 ticks ─────────────────────────────────────
  const tickResult = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    const newBlocks = el.tick(5);
    return { ticks: el.getState().ticks, newBlocksLen: newBlocks.length };
  });
  if (tickResult.ticks !== 5) throw new Error(`TEST 1 FAILED: expected 5 ticks, got ${tickResult.ticks}`);
  if (tickResult.newBlocksLen < 5) throw new Error(`TEST 1 FAILED: tick(5) returned ${tickResult.newBlocksLen} blocks`);
  console.log(`[test 1] PASS: tick(5) → ticks=5, ${tickResult.newBlocksLen} new blocks`);

  // ─── Test 2: SVG is rendered ───────────────────────────────────────────────
  const svgExists = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    return !!el.querySelector('svg');
  });
  if (!svgExists) throw new Error('TEST 2 FAILED: no SVG element found');
  console.log('[test 2] PASS: SVG rendered.');

  // ─── Test 3: SVG has circle elements ──────────────────────────────────────
  const circleCount = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    return el.querySelectorAll('svg circle').length;
  });
  if (circleCount < 5) throw new Error(`TEST 3 FAILED: expected >= 5 circles, got ${circleCount}`);
  console.log(`[test 3] PASS: ${circleCount} circle elements in SVG.`);

  // ─── Test 4: tau ordering non-empty after enough ticks ────────────────────
  // With 4 nodes and 2f+1 = 3, finality happens quickly. Tick a bunch more.
  await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    el.tick(20);
  });
  const tauLen = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    return el.getState().tauOrder.length;
  });
  if (tauLen === 0) throw new Error('TEST 4 FAILED: tauOrder is empty after 25 ticks');
  console.log(`[test 4] PASS: tauOrder has ${tauLen} entry/entries after 25 ticks.`);

  // ─── Test 5: tau order displayed in the DOM ────────────────────────────────
  const tauDomText = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    const tauEl = el.querySelector('#pbs-tau');
    return tauEl ? tauEl.textContent.trim() : '';
  });
  if (!tauDomText || tauDomText === '(none yet)') throw new Error(`TEST 5 FAILED: tau DOM text is "${tauDomText}"`);
  console.log(`[test 5] PASS: tau DOM: "${tauDomText.slice(0, 60)}…"`);

  // ─── Test 6: getState() returns correct shape ─────────────────────────────
  const state = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    return el.getState();
  });
  if (!Array.isArray(state.blocks)) throw new Error('TEST 6 FAILED: state.blocks not an array');
  if (!Array.isArray(state.tauOrder)) throw new Error('TEST 6 FAILED: state.tauOrder not an array');
  if (typeof state.ticks !== 'number') throw new Error('TEST 6 FAILED: state.ticks not a number');
  if (typeof state.wave !== 'number') throw new Error('TEST 6 FAILED: state.wave not a number');
  if (typeof state.equivocations !== 'number') throw new Error('TEST 6 FAILED: state.equivocations not a number');
  console.log(`[test 6] PASS: getState shape correct — ${state.blocks.length} blocks, ticks=${state.ticks}`);

  // ─── Test 7: reset() clears state ─────────────────────────────────────────
  await page.evaluate(() => {
    document.getElementById('test-sim').reset();
  });
  const afterReset = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    return el.getState();
  });
  if (afterReset.blocks.length !== 0) throw new Error(`TEST 7 FAILED: after reset blocks=${afterReset.blocks.length}`);
  if (afterReset.ticks !== 0) throw new Error(`TEST 7 FAILED: after reset ticks=${afterReset.ticks}`);
  console.log('[test 7] PASS: reset() cleared state.');

  // ─── Test 8: equivocator-index triggers equivocation events ───────────────
  await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    el.setAttribute('equivocator-index', '0');
    // Tick many times to reliably hit the ~20% equivocator trigger
    el.tick(60);
  });
  const equivState = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    const s = el.getState();
    const redBlocks = s.blocks.filter(b => b.isEquivocator);
    return { equivocations: s.equivocations, redBlockCount: redBlocks.length };
  });
  // With 60 ticks and ~20% chance for node 0 (chosen ~25% of time) = ~3 expected
  // We just check >0 is very likely; accept flakiness only if truly unlucky.
  if (equivState.equivocations === 0) {
    console.warn(`[test 8] WARN: equivocations=0 after 60 ticks — statistically unlikely but possible. Retrying with 100 more ticks.`);
    await page.evaluate(() => document.getElementById('test-sim').tick(100));
    const retry = await page.evaluate(() => document.getElementById('test-sim').getState().equivocations);
    if (retry === 0) throw new Error('TEST 8 FAILED: no equivocations after 160 ticks with equivocator-index=0');
    console.log(`[test 8] PASS (retry): equivocations=${retry}`);
  } else {
    console.log(`[test 8] PASS: equivocations=${equivState.equivocations}, equivocator blocks=${equivState.redBlockCount}`);
  }

  // Check red diamond polygon in SVG
  const hasPolygon = await page.evaluate(() => {
    const el = document.getElementById('test-sim');
    return el.querySelectorAll('svg polygon').length > 0;
  });
  if (!hasPolygon) throw new Error('TEST 8b FAILED: no polygon (equivocator diamond) in SVG');
  console.log('[test 8b] PASS: equivocator diamond polygons visible in SVG.');

  // ─── Test 9: compact mode renders summary ─────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-blocklace-sim');
    el.setAttribute('node-count', '3');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-sim-compact');
    document.body.appendChild(el);
    el.tick(5);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-sim-compact');
    return el && el.children.length > 0;
  }, { timeout: 3000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-sim-compact');
    return el ? el.textContent.trim() : '';
  });
  if (!compactText.includes('nodes')) throw new Error(`TEST 9 FAILED: compact text lacks "nodes": "${compactText}"`);
  if (!compactText.includes('ticks')) throw new Error(`TEST 9 FAILED: compact text lacks "ticks": "${compactText}"`);
  console.log(`[test 9] PASS: compact mode: "${compactText.slice(0, 80)}"`);

  // ─── Test 10: node-count=5 gives 5 column headers in SVG ─────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-blocklace-sim');
    el.setAttribute('node-count', '5');
    el.setAttribute('id', 'test-sim-5nodes');
    document.body.appendChild(el);
    el.tick(3);
  });

  const textCount = await page.evaluate(() => {
    const el = document.getElementById('test-sim-5nodes');
    // Node headers are <text> elements with "N0", "N1", ... "N4"
    return el.querySelectorAll('svg text').length;
  });
  if (textCount < 5) throw new Error(`TEST 10 FAILED: expected >= 5 SVG text nodes for 5 columns, got ${textCount}`);
  console.log(`[test 10] PASS: ${textCount} SVG text elements for 5-node sim.`);

  // ─── Check for unexpected JS errors ───────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM') &&
    !e.includes('net::ERR_') &&
    !e.includes('pyana') // runtime errors from studio.html are not our concern
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message || err);
  process.exit(1);
});
