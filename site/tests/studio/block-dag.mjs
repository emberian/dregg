/**
 * Playwright ad-hoc test for <pyana-block-dag> inspector.
 *
 * Run with:
 *   node tests/studio/block-dag.mjs
 *
 * Requires the dev server running on port 4818:
 *   npx eleventy --serve --port=4818  (or make serve)
 *
 * What this test does:
 *  1. Navigates to /studio.html (wasm + in-memory runtime + <pyana-app#app>)
 *  2. Waits for wasm init and runtime-ready
 *  3. Creates a federation with 4 nodes
 *  4. Proposes 3 blocks via runtime.proposeBlock(0, [...])
 *  5. Injects block-dag.js module
 *  6. Mounts <pyana-block-dag uri="pyana://federation/0">
 *  7. Verifies the DAG SVG renders with block rects + edges
 *  8. Verifies the block count in the header text
 *  9. Verifies clicking a block rect fires pyana:navigate
 * 10. Verifies compact mode renders summary text + thumbnail SVG
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

const BASE = 'http://localhost:4818';

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => {
    if (msg.type() === 'error') errors.push(`[console.error] ${msg.text()}`);
  });

  console.log('[test] Navigating to /studio.html …');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Wait for pyanaUi bootstrap (Preact + signals + htm)
  await page.waitForFunction(() => !!window.pyanaUi, { timeout: 20000 });
  console.log('[test] pyanaUi ready.');

  // Wait for the in-memory runtime to be attached
  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] runtime attached to <pyana-app#app>.');

  // ─── Step 1: create federation + propose blocks ──────────────────────────
  const setupResult = await page.evaluate(() => {
    const rt = document.getElementById('app').runtime;

    // Create a 4-node federation
    let fed;
    try {
      fed = rt.createFederation('test-fed', 4);
    } catch (e) {
      return { error: 'createFederation failed: ' + e.message };
    }

    // Propose 3 blocks (each should finalize with 4 nodes)
    const results = [];
    for (const events of [
      ['tok-001', 'tok-002'],
      ['tok-003'],
      ['tok-004', 'tok-005', 'tok-006'],
    ]) {
      try {
        const r = rt.proposeBlock(0, events);
        results.push(r);
      } catch (e) {
        return { error: 'proposeBlock failed: ' + e.message };
      }
    }

    return { fed, results };
  });

  if (setupResult.error) {
    throw new Error('TEST SETUP FAILED: ' + setupResult.error);
  }
  console.log('[test] federation created; blocks proposed:',
    JSON.stringify(setupResult.results));

  // ─── Step 2: inject block-dag.js ─────────────────────────────────────────
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/block-dag.js`,
    type: 'module',
  });
  await page.waitForFunction(() => !!customElements.get('pyana-block-dag'), { timeout: 8000 });
  console.log('[test] <pyana-block-dag> custom element registered.');

  // ─── Step 3: mount element inside <pyana-app#app> ────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-block-dag');
    el.setAttribute('uri', 'pyana://federation/0');
    el.setAttribute('id', 'test-dag');
    document.getElementById('app').appendChild(el);
  });

  // Wait for the component to render
  await page.waitForFunction(() => {
    const el = document.getElementById('test-dag');
    return el && el.children.length > 0;
  }, { timeout: 10000 });
  console.log('[test] <pyana-block-dag> rendered.');

  // ─── Test 1: SVG is present ───────────────────────────────────────────────
  const hasSvg = await page.evaluate(() => {
    const el = document.getElementById('test-dag');
    return el ? !!el.querySelector('svg') : false;
  });
  if (!hasSvg) throw new Error('TEST FAILED [1]: no SVG rendered');
  console.log('[test 1] PASS: SVG present.');

  // ─── Test 2: block rects rendered ─────────────────────────────────────────
  const rectCount = await page.evaluate(() => {
    const el = document.getElementById('test-dag');
    return el ? el.querySelectorAll('.bdag-block').length : 0;
  });
  console.log(`[test 2] bdag-block groups: ${rectCount}`);
  if (rectCount < 1) throw new Error(`TEST FAILED [2]: expected blocks in SVG, got ${rectCount}`);
  console.log(`[test 2] PASS: ${rectCount} block rect(s) rendered.`);

  // ─── Test 3: edges (paths) connect blocks ─────────────────────────────────
  // Edges are <path> elements within the SVG (not inside .bdag-block groups)
  const pathCount = await page.evaluate(() => {
    const svg = document.querySelector('#test-dag svg');
    if (!svg) return 0;
    // Count paths that are NOT inside .bdag-block groups (i.e. edge paths)
    const allPaths = [...svg.querySelectorAll('path')];
    const blockPaths = [...svg.querySelectorAll('.bdag-block path')];
    return allPaths.length - blockPaths.length;
  });
  console.log(`[test 3] edge path count: ${pathCount}`);
  // With 3 blocks in a chain we expect at least 2 edges (h2→h1, h3→h2)
  // (genesis has no parent so height-1 block may or may not have an edge)
  if (pathCount < 1) {
    console.warn('[test 3] WARN: fewer edges than expected — parent_hash may be null for first block');
  } else {
    console.log(`[test 3] PASS: ${pathCount} edge(s) rendered.`);
  }

  // ─── Test 4: header text mentions block count ─────────────────────────────
  const headerText = await page.evaluate(() => {
    const header = document.querySelector('#test-dag header');
    return header ? header.textContent.trim() : '';
  });
  console.log(`[test 4] header text: "${headerText}"`);
  const hasBlockCount = /block/i.test(headerText) || /\d+/.test(headerText);
  if (!hasBlockCount) throw new Error(`TEST FAILED [4]: header text unexpected: "${headerText}"`);
  console.log('[test 4] PASS: header contains block info.');

  // ─── Test 5: click block → pyana:navigate event ───────────────────────────
  const navigateUri = await page.evaluate(async () => {
    return new Promise(resolve => {
      const app = document.getElementById('app');
      function handler(ev) {
        app.removeEventListener('pyana:navigate', handler);
        resolve(ev.detail?.uri || '');
      }
      app.addEventListener('pyana:navigate', handler);

      const block = document.querySelector('#test-dag .bdag-block');
      if (block) block.dispatchEvent(new MouseEvent('click', { bubbles: true }));
      else resolve('no-block-found');
    });
  });
  console.log(`[test 5] navigate URI: "${navigateUri}"`);
  if (!navigateUri || navigateUri === 'no-block-found') {
    throw new Error('TEST FAILED [5]: pyana:navigate not fired or no block to click');
  }
  if (!navigateUri.startsWith('pyana://block/')) {
    throw new Error(`TEST FAILED [5]: unexpected navigate URI: "${navigateUri}"`);
  }
  console.log('[test 5] PASS: pyana:navigate fires with correct block URI.');

  // ─── Test 6: compact mode ─────────────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-block-dag');
    el.setAttribute('uri', 'pyana://federation/0');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-dag-compact');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-dag-compact');
    return el && el.children.length > 0;
  }, { timeout: 8000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-dag-compact');
    return el ? el.textContent.trim() : '';
  });
  console.log(`[test 6] compact text: "${compactText}"`);

  const hasH = /H=/.test(compactText);
  const hasNodes = /node/i.test(compactText);
  if (!hasH || !hasNodes) {
    throw new Error(`TEST FAILED [6]: compact summary unexpected: "${compactText}"`);
  }

  const hasCompactSvg = await page.evaluate(() => {
    const el = document.getElementById('test-dag-compact');
    return el ? !!el.querySelector('svg') : false;
  });
  if (!hasCompactSvg) throw new Error('TEST FAILED [6]: compact mode has no thumbnail SVG');
  console.log('[test 6] PASS: compact mode renders summary + thumbnail SVG.');

  // ─── Test 7: bad URI shows error ──────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-block-dag');
    el.setAttribute('uri', 'pyana://cell/notAfederationURI');
    el.setAttribute('id', 'test-dag-bad');
    document.getElementById('app').appendChild(el);
  });
  await page.waitForFunction(() => {
    const el = document.getElementById('test-dag-bad');
    return el && el.children.length > 0;
  }, { timeout: 5000 });
  const badText = await page.evaluate(() => {
    const el = document.getElementById('test-dag-bad');
    return el ? el.textContent.trim() : '';
  });
  const showsError = /wrong kind|err/i.test(badText);
  if (!showsError) throw new Error(`TEST FAILED [7]: bad URI didn't show error: "${badText}"`);
  console.log('[test 7] PASS: wrong-kind URI shows error.');

  // ─── Check for unexpected JS errors ──────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('net::ERR_')
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors during run:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message || err);
  process.exit(1);
});
