/**
 * Subscription starbridge-app — REAL multi-agent grant flow smoke.
 *
 * Proves the subscription publisher/consumer grant flow is REAL in-browser
 * (no extension cclerk), driving the canonical TurnExecutor:
 *
 *   1. The page mounts; the in-memory runtime attaches to <dregg-app>.
 *   2. window.dregg.appFlows.subscription() runs:
 *        - mints a dedicated topic cell + installs the canonical
 *          `subscription_program` cell-program on it (multi-method Cases,
 *          MonotonicSequence head/tail, Immutable capacity/owner);
 *        - creates THREE distinct agents (owner, publisher, consumer) — real
 *          separate cipherclerks;
 *        - owner GRANTS the publisher + consumer (real grant_publisher /
 *          grant_consumer turns: SetField + EmitEvent);
 *        - the PUBLISHER (a different agent) publishes (head 0→1);
 *        - the CONSUMER (a third agent) consumes (tail 0→1).
 *   3. Every turn commits; the final on-ledger topic-cell state shows the real
 *      head=1, tail=1, non-zero publishers/consumers/message roots.
 *   4. Zero console/page errors.
 *
 * Prereqs:  dist served on :8080  →  npx serve dist -l 8080
 * Run:      node tests/app-subscription-flow.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';
const URL = `${BASE}/starbridge-apps/subscription/pages/`;

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const nonZero = (h) => !!h && !/^0*$/.test(String(h).replace(/^0x/, ''));
const u64BE = (h) => {
  const s = String(h || '').replace(/^0x/, '');
  return s.length === 64 ? Number(BigInt('0x' + s)) : NaN;
};

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

  // (1b) the multi-agent flow module loaded.
  await page.waitForFunction(() => typeof window.dregg?.appFlows?.subscription === 'function',
    { timeout: 25000 });
  check('window.dregg.appFlows.subscription installed', true);

  // (2) run the REAL multi-agent grant flow.
  const result = await page.evaluate(async () => {
    try {
      return await window.dregg.appFlows.subscription();
    } catch (e) {
      return { ok: false, error: String(e?.message || e) };
    }
  });

  check('subscription flow ran without throwing', result.ok === true, result.error || '');
  if (!result.ok) { await browser.close(); console.log('\n[subscription-flow] ABORTED'); process.exit(1); }

  // (3) distinct agents drove the turns.
  const a = result.agents || {};
  check('three distinct agents (owner/publisher/consumer)',
    a.ownerIdx !== a.publisherIdx && a.publisherIdx !== a.consumerIdx && a.ownerIdx !== a.consumerIdx,
    JSON.stringify(a));

  // (4) every step committed.
  const steps = result.log || [];
  const byStep = Object.fromEntries(steps.filter((s) => s.result).map((s) => [s.step, s.result]));
  for (const step of ['grant_publisher', 'grant_consumer', 'publish', 'consume']) {
    const res = byStep[step];
    check(`${step} turn committed (real signed turn)`,
      res && res.status === 'committed' && /^[0-9a-f]{16,}$/.test(res.turn_hash || ''),
      res ? `status=${res.status} hash=${(res.turn_hash || '').slice(0, 12)}` : 'missing');
  }

  // (5) final on-ledger state: real head=1, tail=1, non-zero roots.
  const st = result.state || {};
  check('topic cell seq_head == 1 (publisher advanced head)', u64BE(st.seq_head) === 1, st.seq_head);
  check('topic cell seq_tail == 1 (consumer advanced tail)', u64BE(st.seq_tail) === 1, st.seq_tail);
  check('topic cell publishers_root non-zero (owner granted publisher)',
    nonZero(st.publishers_root), st.publishers_root);
  check('topic cell consumers_root non-zero (owner granted consumer)',
    nonZero(st.consumers_root), st.consumers_root);
  check('topic cell message_root non-zero (publish folded a message)',
    nonZero(st.message_root), st.message_root);
  check('topic cell latest_payload_hash non-zero', nonZero(st.latest_payload_hash), st.latest_payload_hash);

  // (5b) read back through the runtime independently to confirm it's real ledger state.
  const live = await page.evaluate(async (cellId) => {
    const rt = window.__starbridgeAppRuntime;
    return { head: rt.readCellField(cellId, 0), tail: rt.readCellField(cellId, 1) };
  }, result.topicCell);
  check('independent runtime read confirms head=1', u64BE(live.head) === 1, live.head);
  check('independent runtime read confirms tail=1', u64BE(live.tail) === 1, live.tail);

  await page.waitForTimeout(300);
  // (6) zero errors.
  const realErrors = errors.filter((e) => !/read-only/.test(e));
  check('no console/page errors', realErrors.length === 0, realErrors.join(' | '));

  await browser.close();
  console.log(`\n[subscription-flow] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[subscription-flow] crashed:', e); process.exit(2); });
