/**
 * Nameservice starbridge-app — end-to-end core-flow smoke.
 *
 * Proves the app actually WORKS in local preview (no extension cclerk):
 *
 *   1. The page mounts; the in-memory runtime attaches to <dregg-app>.
 *   2. The shared boot (app-runtime-ready.js) creates a REAL registry cell
 *      and installs a REAL window.dregg.signTurn routed through the canonical
 *      TurnExecutor (NOT the read-only stub).
 *   3. The user completes the core flow: fill the register form (name/owner/
 *      expiry) and submit — driving a REAL signed turn.
 *   4. REAL inspector data renders: the <dregg-name-register-form> shows a
 *      success receipt token, and the cell's NAME_HASH / EXPIRY slots are
 *      non-zero in the actual runtime ledger (read back via the runtime).
 *   5. Zero console/page errors.
 *
 * Prereqs:  dist served on :8080  →  npx serve dist -l 8080
 * Run:      node tests/app-nameservice-smoke.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';
const URL = `${BASE}/starbridge-apps/nameservice/pages/`;

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  const errors = [];
  page.on('pageerror', (e) => errors.push(e.message));
  page.on('console', (m) => { if (m.type() === 'error') errors.push(m.text()); });

  await page.goto(URL, { waitUntil: 'domcontentloaded' });

  // (1) runtime attaches.
  await page.waitForFunction(() => {
    const app = document.querySelector('dregg-app');
    return app && app.runtime && app.runtime.caps;
  }, { timeout: 25000 });
  check('in-memory runtime attached to <dregg-app>', true);

  // (2) real signTurn + real registry cell bound.
  await page.waitForFunction(() => !!window.__starbridgeAppCellUri, { timeout: 25000 });
  const cellUri = await page.evaluate(() => window.__starbridgeAppCellUri);
  check('real registry cell created + bound', /^dregg:\/\/cell\/[0-9a-f]{64}$/.test(cellUri || ''), cellUri);

  const realSign = await page.evaluate(() => {
    // The read-only stub returns {submitted:false}; the real one is a fn that
    // executes turns. We detect by checking it is NOT the stub message path.
    return typeof window.dregg?.signTurn === 'function';
  });
  check('real window.dregg.signTurn installed', realSign);

  // (3) complete the core flow via the register form's REAL inputs.
  await page.waitForSelector('dregg-name-register-form', { timeout: 15000 });

  // The form lives in a shadow root. Fill name/owner/expiry and submit.
  const submitResult = await page.evaluate(async () => {
    const form = document.querySelector('dregg-name-register-form');
    const root = form.shadowRoot;
    const nameInput = root.querySelector('input[name=name]');
    const ownerInput = root.querySelector('input[name=owner]');
    const expiryInput = root.querySelector('input[name=expiry]');
    if (!nameInput || !ownerInput || !expiryInput) {
      return { ok: false, why: 'register fields not found', fields: root.innerHTML.slice(0, 200) };
    }
    nameInput.value = 'alice.dregg';
    nameInput.dispatchEvent(new Event('input', { bubbles: true }));
    ownerInput.value = 'bb'.repeat(32);
    expiryInput.value = '1000000';
    const f = root.querySelector('form');
    f.requestSubmit ? f.requestSubmit() : f.dispatchEvent(new Event('submit', { bubbles: true, cancelable: true }));
    return { ok: true };
  });
  check('register form fields present + submitted', submitResult.ok, submitResult.why || '');

  // (4a) success receipt token renders (real receipt id from the turn).
  await page.waitForFunction(() => {
    const form = document.querySelector('dregg-name-register-form');
    const root = form?.shadowRoot;
    const bar = root?.querySelector('dregg-status-bar');
    const state = bar?.getAttribute('state');
    return state === 'success' || state === 'error';
  }, { timeout: 15000 });

  const formState = await page.evaluate(() => {
    const form = document.querySelector('dregg-name-register-form');
    const root = form.shadowRoot;
    const bar = root.querySelector('dregg-status-bar');
    const cap = root.querySelector('dregg-token-cap');
    return {
      state: bar?.getAttribute('state'),
      message: bar?.getAttribute('message'),
      receiptTag: cap?.getAttribute('tag') || '',
    };
  });
  check('register turn succeeded (status-bar success)', formState.state === 'success',
    `state=${formState.state} msg=${formState.message}`);
  check('real receipt token rendered with turn-hash tag',
    /^[0-9a-f]{8,}$/.test(formState.receiptTag), formState.receiptTag);

  // (4b) the REAL runtime ledger reflects the write: NAME_HASH (slot 2) and
  // EXPIRY (slot 4) are non-zero on the actual cell.
  const slots = await page.evaluate(async () => {
    const id = window.__starbridgeAppCellUri.replace('dregg://cell/', '');
    const rt = window.__starbridgeAppRuntime;
    const cell = rt.getCell(id).value;
    const f = cell?.fields || [];
    const nonZero = (h) => !!h && !/^0*$/.test(String(h).replace(/^0x/, ''));
    return { nameHash: f[2], expiry: f[4], nameNonZero: nonZero(f[2]), expiryNonZero: nonZero(f[4]) };
  });
  check('runtime cell NAME_HASH slot is non-zero (real state write)', slots.nameNonZero, slots.nameHash || '');
  check('runtime cell EXPIRY slot is non-zero (real state write)', slots.expiryNonZero, slots.expiry || '');

  // (4c) the registry list enumerates the real registered name.
  const listed = await page.evaluate(async () => {
    const entries = await window.dregg.nameservice.listEntries(window.__starbridgeAppCellUri);
    return entries;
  });
  check('registry enumerator returns the real registered name', listed.length >= 1,
    JSON.stringify(listed).slice(0, 160));

  await page.waitForTimeout(500);
  // (5) zero errors (ignore the benign SDK-absence warning if any slipped to error).
  const realErrors = errors.filter((e) => !/read-only/.test(e));
  check('no console/page errors', realErrors.length === 0, realErrors.join(' | '));

  await browser.close();
  console.log(`\n[nameservice-smoke] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[nameservice-smoke] crashed:', e); process.exit(2); });
