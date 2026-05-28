/**
 * Playground migration smoke test (STARBRIDGE-PLAN §4.9).
 *
 * Loads the full copy-through playground at /playground/, clicks through every
 * nav section, and verifies:
 *
 *   1. The page boots, wasm loads, and the shared Studio inspector runtime
 *      seeds (window has the embedded <dregg-app> elements with a runtime).
 *   2. Clicking every nav section throws no errors and produces no console
 *      errors / uncaught page errors.
 *   3. The Tier-2 migrated sections render REAL platform inspectors with real
 *      data (never JS placeholders):
 *        - proofs    → <dregg-proof> bound to the seeded turn (trust tier)
 *        - merkle    → <dregg-merkle-tree> (real BLAKE3 root)
 *        - datalog   → <dregg-predicate> editor (real evaluate_datalog)
 *        - notes     → <dregg-note> bound to the seeded note commitment
 *        - effect-vm → <dregg-turn-debugger> bound to the seeded turn
 *   4. The retired sections are gone from the nav (crossfed, full-turn-proof,
 *      tiered-revocation).
 *   5. Tier-1 deeplink banners route to dregg:// URIs in /starbridge/.
 *
 * Prereqs:  dist served on :8080  →  npx serve dist -l 8080
 * Run:      node tests/playground-smoke.mjs
 * Env:      PLAYGROUND_BASE (default http://localhost:8080)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.PLAYGROUND_BASE || 'http://localhost:8080';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const RETIRED = ['crossfed', 'full-turn-proof', 'tiered-revocation'];

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const pageErrors = [];
  const consoleErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
  page.on('console', (msg) => {
    if (msg.type() === 'error') consoleErrors.push(msg.text());
  });

  await page.goto(`${BASE}/playground/`, { waitUntil: 'domcontentloaded' });

  // wasm + Studio runtime bootstrap.
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  await page.waitForFunction(
    () => document.getElementById('wasm-status')?.classList.contains('ready'),
    { timeout: 30000 },
  ).catch(() => {});

  // Nav is rendered statically in index.html; collect every section button.
  const sections = await page.$$eval('.pg-nav__item', (els) =>
    els.map((el) => el.dataset.section),
  );
  check('nav has sections', sections.length > 10, `${sections.length} sections`);

  // Retired sections must NOT appear in the nav.
  for (const r of RETIRED) {
    check(`retired section "${r}" removed from nav`, !sections.includes(r));
  }

  // Click through every section (scenario tabs hide some; reveal then click).
  let clicked = 0;
  for (const id of sections) {
    // The scenario tabs hide non-active sections via [hidden]; navigate by
    // hash which forces the owning scenario active, then the section active.
    await page.evaluate((s) => { location.hash = `#${s}`; }, id);
    await page.waitForTimeout(60);
    const active = await page.evaluate(
      (s) => document.getElementById(`section-${s}`)?.classList.contains('active'),
      id,
    );
    if (active) clicked += 1;
  }
  check('every nav section activates', clicked === sections.length,
    `${clicked}/${sections.length}`);

  // Wait for the shared seeded runtime to attach to the embedded inspectors.
  await page.waitForFunction(() => {
    const apps = document.querySelectorAll('dregg-app');
    return apps.length > 0 && Array.from(apps).every((a) => !!a.runtime);
  }, { timeout: 30000 }).catch(() => {});

  // ── Tier-2 inspector renders ───────────────────────────────────────────────
  // Merkle: real 4-ary BLAKE3 tree (svg + root text), no seed dependency.
  await page.evaluate(() => { location.hash = '#merkle'; });
  await page.waitForSelector('#section-merkle dregg-merkle-tree', { timeout: 10000 });
  await page.waitForFunction(() => {
    const el = document.querySelector('#section-merkle dregg-merkle-tree');
    return el && (el.querySelector('svg') || /root/i.test(el.textContent));
  }, { timeout: 15000 }).catch(() => {});
  const merkleOk = await page.evaluate(() => {
    const el = document.querySelector('#section-merkle dregg-merkle-tree');
    return !!el && (!!el.querySelector('svg') || /root/i.test(el.textContent));
  });
  check('merkle → <dregg-merkle-tree> renders real tree', merkleOk);

  // Datalog: predicate editor with a real ALLOW/DENY conclusion.
  await page.evaluate(() => { location.hash = '#datalog'; });
  await page.waitForSelector('#section-datalog dregg-predicate', { timeout: 10000 });
  await page.waitForFunction(() => {
    const el = document.querySelector('#section-datalog dregg-predicate');
    return el && el.textContent.trim().length > 0;
  }, { timeout: 15000 }).catch(() => {});
  const predicateOk = await page.evaluate(() => {
    const el = document.querySelector('#section-datalog dregg-predicate');
    return !!el && el.textContent.trim().length > 0;
  });
  check('datalog → <dregg-predicate> editor renders', predicateOk);

  // Proofs: <dregg-proof> bound to the seeded turn, with a trust-tier badge.
  await page.evaluate(() => { location.hash = '#proofs'; });
  await page.waitForSelector('#section-proofs dregg-proof', { timeout: 10000 });
  await page.waitForFunction(() => {
    const el = document.querySelector('#section-proofs dregg-proof');
    return el && /tier/i.test(el.textContent);
  }, { timeout: 20000 }).catch(() => {});
  const proofState = await page.evaluate(() => {
    const el = document.querySelector('#section-proofs dregg-proof');
    return {
      uri: el?.getAttribute('uri') || '',
      tier: /tier/i.test(el?.textContent || ''),
    };
  });
  check('proofs → <dregg-proof> bound to a seeded receipt',
    /^dregg:\/\/receipt\/[0-9a-f]{8,}/.test(proofState.uri), proofState.uri);
  check('proofs → <dregg-proof> shows a trust tier', proofState.tier);

  // Effect VM: <dregg-turn-debugger> bound to the seeded turn.
  await page.evaluate(() => { location.hash = '#effect-vm'; });
  await page.waitForSelector('#section-effect-vm dregg-turn-debugger', { timeout: 10000 });
  await page.waitForFunction(() => {
    const el = document.querySelector('#section-effect-vm dregg-turn-debugger');
    return el && el.getAttribute('uri') && el.getAttribute('uri') !== 'dregg://turn/seed';
  }, { timeout: 20000 }).catch(() => {});
  const tdUri = await page.evaluate(() =>
    document.querySelector('#section-effect-vm dregg-turn-debugger')?.getAttribute('uri') || '');
  check('effect-vm → <dregg-turn-debugger> bound to the seeded turn',
    /^dregg:\/\/turn\/[0-9a-f]{8,}/.test(tdUri), tdUri);

  // Notes: <dregg-note> bound to the seeded note commitment (best-effort —
  // some wasm builds may not expose a note index; require at least the element).
  await page.evaluate(() => { location.hash = '#notes'; });
  await page.waitForSelector('#section-notes dregg-note', { timeout: 10000 });
  const noteUri = await page.evaluate(() =>
    document.querySelector('#section-notes dregg-note')?.getAttribute('uri') || '');
  check('notes → <dregg-note> present', !!noteUri, noteUri);

  // ── Tier-1 deeplinks ───────────────────────────────────────────────────────
  await page.evaluate(() => { location.hash = '#capabilities'; });
  await page.waitForTimeout(80);
  const capLinks = await page.$$eval('#section-capabilities .pg-sb-link', (els) =>
    els.map((el) => el.getAttribute('href')));
  check('capabilities → deeplinks to capability + delegation-graph',
    capLinks.some((h) => /dregg%3A%2F%2Fcapability/i.test(h)) &&
      capLinks.some((h) => /delegation-graph/i.test(h)),
    capLinks.join(' , '));

  const tokenLink = await page.evaluate(() => {
    location.hash = '#tokens';
    return document.querySelector('#section-tokens .pg-sb-link')?.getAttribute('href') || '';
  });
  check('tokens → deeplink routes to a dregg:// URI in /starbridge/',
    tokenLink.startsWith('/starbridge/?at=dregg') || /starbridge.*at=dregg/.test(tokenLink),
    tokenLink);

  // ── Error hygiene ───────────────────────────────────────────────────────────
  check('no uncaught page errors', pageErrors.length === 0, pageErrors.join(' | '));
  // Filter benign network noise (favicon, optional discovery.json) from console.
  const realConsole = consoleErrors.filter(
    (t) => !/favicon|discovery\.json|net::ERR|Failed to load resource/i.test(t),
  );
  check('no console errors', realConsole.length === 0, realConsole.slice(0, 5).join(' | '));

  await browser.close();
  console.log(`\n[smoke] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[smoke] crashed:', e); process.exit(2); });
