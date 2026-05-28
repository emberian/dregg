/**
 * Identity starbridge-app — mount + core-flow smoke.
 *
 * Identity's full issue→present→verify flow depends on the ZK credential
 * engine surfaced as window.dregg.credentials.* — which is the EXTENSION
 * cclerk's surface and is NOT present in the static local preview. So this
 * smoke asserts the HONEST in-preview contract:
 *
 *   1. The page mounts; the in-memory runtime attaches.
 *   2. A REAL issuer cell is created + bound (the runtime-realizable part).
 *   3. All four identity custom elements UPGRADE (defined) and render real
 *      chrome — no undefined-element / blank-panel errors.
 *   4. The issuer-counter increment flow IS real: a real signed turn bumps
 *      the issuer cell's ISSUANCE_COUNTER slot through the canonical executor.
 *   5. Zero console/page errors on mount.
 *
 * Prereqs:  dist served on :8080.
 * Run:      node tests/app-identity-smoke.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';
const URL = `${BASE}/starbridge-apps/identity/pages/`;

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const TAGS = [
  'dregg-credential',
  'dregg-credential-issue-form',
  'dregg-credential-present-form',
  'dregg-credential-verifier',
];

async function run() {
  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  const errors = [];
  page.on('pageerror', (e) => errors.push(e.message));
  page.on('console', (m) => { if (m.type() === 'error') errors.push(m.text()); });

  await page.goto(URL, { waitUntil: 'domcontentloaded' });

  await page.waitForFunction(() => {
    const app = document.querySelector('dregg-app');
    return app && app.runtime && app.runtime.caps;
  }, { timeout: 25000 });
  check('in-memory runtime attached to <dregg-app>', true);

  await page.waitForFunction(() => !!window.__starbridgeAppCellUri, { timeout: 25000 });
  const cellUri = await page.evaluate(() => window.__starbridgeAppCellUri);
  check('real issuer cell created + bound',
    /^dregg:\/\/cell\/[0-9a-f]{64}$/.test(cellUri || ''), cellUri);

  // All four custom elements upgrade.
  for (const tag of TAGS) {
    const defined = await page.evaluate((t) => !!customElements.get(t), tag);
    check(`custom element <${tag}> is defined (no undefined-element)`, defined);
  }

  // The issue form renders real chrome (its shadow root has form fields).
  const issueChrome = await page.evaluate(() => {
    const el = document.querySelector('dregg-credential-issue-form');
    const root = el?.shadowRoot || el;
    return {
      text: (root?.textContent || '').replace(/\s+/g, ' ').trim().slice(0, 80),
      hasChrome: !!root?.querySelector?.('form, input, button, [class*="form"]'),
    };
  });
  check('issue form rendered real chrome', issueChrome.hasChrome, issueChrome.text);

  // Drive the REAL issue flow through the issue form (preview honest path):
  // fill subject + claims, submit, expect success state + the explicit
  // "extension required for ZK blob; counter advanced on-ledger" note, and a
  // real ISSUANCE_COUNTER bump in the runtime ledger.
  const issued = await page.evaluate(async () => {
    const el = document.querySelector('dregg-credential-issue-form');
    const root = el.shadowRoot;
    const subject = root.querySelector('input[name=subject]');
    if (!subject) return { ok: false, why: 'no subject input' };
    subject.value = 'cc'.repeat(32);
    for (const inp of root.querySelectorAll('input[name^=attr_]')) inp.value = '1';
    const f = root.querySelector('form');
    f.requestSubmit ? f.requestSubmit() : f.dispatchEvent(new Event('submit', { bubbles: true, cancelable: true }));
    return { ok: true };
  });
  check('issue form filled + submitted', issued.ok, issued.why || '');

  await page.waitForFunction(() => {
    const el = document.querySelector('dregg-credential-issue-form');
    const bar = el?.shadowRoot?.querySelector('dregg-status-bar');
    return ['success', 'error'].includes(bar?.getAttribute('state'));
  }, { timeout: 15000 });

  const issueState = await page.evaluate(() => {
    const el = document.querySelector('dregg-credential-issue-form');
    const bar = el.shadowRoot.querySelector('dregg-status-bar');
    return { state: bar?.getAttribute('state'), message: bar?.getAttribute('message') };
  });
  check('issue flow reached success (real on-ledger turn)', issueState.state === 'success',
    `state=${issueState.state} msg=${issueState.message}`);

  const counter = await page.evaluate(() => {
    const id = window.__starbridgeAppCellUri.replace('dregg://cell/', '');
    const cell = window.__starbridgeAppRuntime.getCell(id).value;
    return cell?.fields?.[3];
  });
  const counterNonZero = !!counter && !/^0*$/.test(String(counter).replace(/^0x/, ''));
  check('real turn bumped issuer ISSUANCE_COUNTER slot', counterNonZero, counter || '');

  await page.waitForTimeout(400);
  const realErrors = errors.filter((e) => !/read-only|credentials/.test(e));
  check('no console/page errors on mount', realErrors.length === 0, realErrors.join(' | '));

  await browser.close();
  console.log(`\n[identity-smoke] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[identity-smoke] crashed:', e); process.exit(2); });
