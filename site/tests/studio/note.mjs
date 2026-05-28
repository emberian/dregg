/**
 * Playwright test for <dregg-note> inspector + get_notes (#45).
 *
 * Run with:
 *   node tests/studio/note.mjs
 *
 * Requires the site served on port 8080 (serving the built dist/):
 *   npx serve dist -l 8080   (from /Users/ember/dev/breadstuffs/site)
 *
 * Tests:
 *  1. get_notes is empty for a fresh agent (honest empty, not fabricated).
 *  2. After create_note, get_notes returns the real minted note
 *     (commitment / value / asset_type from canonical dregg_cell::Note).
 *  3. <dregg-note uri="dregg://note/<commitment>"> resolves the real note
 *     (renders value + unspent status), not the "note not found" notice.
 *  4. After spend_note, get_notes marks the note spent with a real nullifier.
 *  5. list_deployed_factories surfaces the real default factory metadata.
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

const BASE = 'http://localhost:8080';

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => {
    if (msg.type() === 'error') errors.push(`[console.error] ${msg.text()}`);
  });

  console.log('[test] Navigating to /studio …');
  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  await page.waitForFunction(() => !!(window.dreggUi || window.dregg), { timeout: 20000 });
  await page.waitForFunction(() => {
    const app = document.getElementById('app');
    return app && app.runtime && app.runtime._wasm && app.runtime._handle != null;
  }, { timeout: 20000 });
  console.log('[test] runtime attached.');

  // ── Step 1: Create alice. Genesis (idx 0) needs to exist first; createAgent
  // here is the first agent so it's genesis. We need a second so notes belong to
  // a non-genesis too — but create_note works for any agent including genesis.
  const setup = await page.evaluate(async () => {
    const rt = document.getElementById('app').runtime;
    const alice = await rt.createAgent('alice', 5000n);
    if (!alice || alice.agent_index == null) {
      return { error: 'createAgent failed: ' + JSON.stringify(alice) };
    }
    return { agent_index: alice.agent_index };
  });
  if (setup.error) throw new Error('SETUP FAILED: ' + setup.error);
  const agentIdx = setup.agent_index;
  console.log(`[test] alice created: agent_index=${agentIdx}`);

  // ── Test 1: get_notes empty for fresh agent ──────────────────────────────
  const emptyNotes = await page.evaluate((idx) => {
    const rt = document.getElementById('app').runtime;
    return rt._wasm.get_notes(rt._handle, idx);
  }, agentIdx);
  if (!Array.isArray(emptyNotes) || emptyNotes.length !== 0) {
    throw new Error(`TEST 1 FAILED: expected empty notes, got ${JSON.stringify(emptyNotes)}`);
  }
  console.log('[test 1] PASS: get_notes empty for fresh agent.');

  // ── Test 2: create_note → get_notes returns the real note ────────────────
  const created = await page.evaluate((idx) => {
    const rt = document.getElementById('app').runtime;
    const res = rt._wasm.create_note(rt._handle, idx, 250n, 7n);
    const notes = rt._wasm.get_notes(rt._handle, idx);
    // Normalize BigInt → Number for structured-clone back to Node.
    const norm = notes.map(n => ({ ...n, value: Number(n.value), asset_type: Number(n.asset_type) }));
    return { res, notes: norm };
  }, agentIdx);
  const commitment = created.res?.commitment;
  if (!commitment || commitment.length !== 64) {
    throw new Error(`TEST 2 FAILED: create_note gave no commitment: ${JSON.stringify(created.res)}`);
  }
  if (created.notes.length !== 1) {
    throw new Error(`TEST 2 FAILED: expected 1 note, got ${JSON.stringify(created.notes)}`);
  }
  const note = created.notes[0];
  if (note.commitment !== commitment || note.value !== 250 || note.asset_type !== 7 || note.spent !== false) {
    throw new Error(`TEST 2 FAILED: note mismatch: ${JSON.stringify(note)} vs commitment ${commitment}`);
  }
  console.log(`[test 2] PASS: get_notes returns real minted note (value=250 asset=7, commitment=${commitment.slice(0,12)}…).`);

  // ── Test 3: <dregg-note> URI resolves the real note ──────────────────────
  await page.evaluate(({ idx, uri }) => {
    const el = document.createElement('dregg-note');
    el.setAttribute('uri', uri);
    el.setAttribute('agent-index', String(idx));
    el.setAttribute('id', 'test-note');
    document.getElementById('app').appendChild(el);
  }, { idx: agentIdx, uri: `dregg://note/${commitment}` });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-note');
    return el && el.querySelector('.dregg-inspector--note') !== null;
  }, { timeout: 8000 });

  const noteRender = await page.evaluate(() => {
    const el = document.getElementById('test-note');
    return el ? el.innerText : '';
  });
  if (/note not found/i.test(noteRender)) {
    throw new Error(`TEST 3 FAILED: <dregg-note> shows "not found" instead of real note. Render:\n${noteRender}`);
  }
  if (!noteRender.includes('250')) {
    throw new Error(`TEST 3 FAILED: <dregg-note> did not render the note value 250. Render:\n${noteRender}`);
  }
  if (!/unspent/i.test(noteRender)) {
    throw new Error(`TEST 3 FAILED: <dregg-note> did not show unspent status. Render:\n${noteRender}`);
  }
  console.log('[test 3] PASS: <dregg-note> URI resolves real note (value 250, unspent).');

  // ── Test 4: spend_note → note marked spent with real nullifier ───────────
  const spent = await page.evaluate((idx) => {
    const rt = document.getElementById('app').runtime;
    const res = rt._wasm.spend_note(rt._handle, idx, 250n, 7n);
    const notes = rt._wasm.get_notes(rt._handle, idx);
    const norm = notes.map(n => ({ ...n, value: Number(n.value), asset_type: Number(n.asset_type) }));
    return { res, notes: norm };
  }, agentIdx);
  if (spent.notes.length !== 1) {
    throw new Error(`TEST 4 FAILED: expected still 1 note (deduped), got ${JSON.stringify(spent.notes)}`);
  }
  const sn = spent.notes[0];
  if (sn.spent !== true || !sn.nullifier || sn.nullifier.length !== 64) {
    throw new Error(`TEST 4 FAILED: note not marked spent with real nullifier: ${JSON.stringify(sn)}`);
  }
  if (sn.nullifier !== spent.res?.nullifier) {
    throw new Error(`TEST 4 FAILED: get_notes nullifier != spend_note nullifier: ${sn.nullifier} vs ${spent.res?.nullifier}`);
  }
  console.log(`[test 4] PASS: spend_note marks note spent with real nullifier=${sn.nullifier.slice(0,12)}….`);

  // ── Test 5: list_deployed_factories surfaces real default factory ────────
  const factories = await page.evaluate(() => {
    const rt = document.getElementById('app').runtime;
    return rt._wasm.list_deployed_factories(rt._handle);
  });
  if (!Array.isArray(factories) || factories.length < 1) {
    throw new Error(`TEST 5 FAILED: no factories listed: ${JSON.stringify(factories)}`);
  }
  const def = factories.find(f => f.is_default);
  if (!def || !def.vk || def.vk.length !== 64 || typeof def.default_mode !== 'string') {
    throw new Error(`TEST 5 FAILED: default factory metadata not real: ${JSON.stringify(factories)}`);
  }
  console.log(`[test 5] PASS: list_deployed_factories surfaces real default factory (mode=${def.default_mode}, vk=${def.vk.slice(0,12)}…).`);

  // ── JS error check ───────────────────────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM not available') &&
    !e.includes('net::ERR_') &&
    !e.includes('favicon')
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
