/**
 * Governed-namespace starbridge-app — REAL propose/vote/threshold-sig-commit
 * flow smoke.
 *
 * Proves the governance flow is REAL in-browser (no extension cclerk), driving
 * the canonical TurnExecutor with a real Authorization::Custom threshold sig:
 *
 *   1. The page mounts; the in-memory runtime attaches to <dregg-app>.
 *   2. window.dregg.appFlows.governedNamespace() runs:
 *        - mints a namespace cell + installs the canonical `governance_program`
 *          (Cases: Immutable committee/threshold, Monotonic version/window,
 *          MonotonicSequence(version) on commit);
 *        - creates a 2-of-3 committee of distinct cipherclerks;
 *        - registers a REAL Ed25519 threshold verifier under GOVERNANCE_VK;
 *        - committee member 0 PROPOSES a route-table update (pending root + window);
 *        - members 0 + 1 VOTE (tally advances);
 *        - COMMIT via a REAL Authorization::Custom turn: members 0+1 each sign
 *          the exact canonical custom signing message; the registered verifier
 *          validates the 2-of-3 threshold; only then does the atomic swap
 *          (route_table_root := proposed, version 0→1) commit.
 *   3. The commit committed (real threshold-sig discharge), version==1,
 *      route_table_root == the canonical proposed commitment, pending cleared.
 *   4. Zero console/page errors.
 *
 * Prereqs:  dist served on :8080  →  npx serve dist -l 8080
 * Run:      node tests/app-governed-namespace-flow.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';
const URL = `${BASE}/starbridge-apps/governed-namespace/pages/`;

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const nonZero = (h) => !!h && !/^0*$/.test(String(h).replace(/^0x/, ''));
const isZero = (h) => !!h && /^0*$/.test(String(h).replace(/^0x/, ''));
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

  await page.waitForFunction(() => typeof window.dregg?.appFlows?.governedNamespace === 'function',
    { timeout: 25000 });
  check('window.dregg.appFlows.governedNamespace installed', true);

  // (2) run the REAL propose → vote → threshold-sig commit flow.
  const result = await page.evaluate(async () => {
    try {
      return await window.dregg.appFlows.governedNamespace();
    } catch (e) {
      return { ok: false, error: String(e?.message || e) };
    }
  });

  check('governance flow ran without throwing', result.ok === true, result.error || '');
  if (!result.ok) { await browser.close(); console.log('\n[governed-namespace-flow] ABORTED'); process.exit(1); }

  // (3) distinct 3-member committee.
  const pks = result.committeePubkeys || [];
  check('3 distinct committee members', new Set(pks).size === 3, JSON.stringify(pks.map((p) => p.slice(0, 8))));

  const steps = result.log || [];
  const byStep = Object.fromEntries(steps.filter((s) => s.result).map((s) => [s.step, s.result]));

  // (4) propose + votes committed.
  check('propose turn committed', byStep.propose && byStep.propose.status === 'committed',
    byStep.propose ? byStep.propose.status : 'missing');
  check('vote-0 turn committed', byStep['vote-0'] && byStep['vote-0'].status === 'committed',
    byStep['vote-0'] ? byStep['vote-0'].status : 'missing');
  check('vote-1 turn committed', byStep['vote-1'] && byStep['vote-1'].status === 'committed',
    byStep['vote-1'] ? byStep['vote-1'].status : 'missing');

  // (5) THE COMMIT: real Authorization::Custom threshold-sig turn committed.
  const commit = byStep.commit;
  check('commit_table_update committed via REAL threshold-sig Authorization::Custom',
    commit && commit.status === 'committed' && /^[0-9a-f]{16,}$/.test(commit.turn_hash || ''),
    commit ? `status=${commit.status} err=${commit.error || ''}` : 'missing');
  check('flow reports commitCommitted === true', result.commitCommitted === true);

  // (6) final on-ledger state reflects the atomic swap.
  const st = result.state || {};
  check('namespace cell version == 1 (MonotonicSequence accepted +1)', u64BE(st.version) === 1, st.version);
  check('namespace cell route_table_root == canonical proposed commitment',
    st.route_table_root && st.route_table_root === result.proposedRoot,
    `state=${(st.route_table_root || '').slice(0, 12)} proposed=${(result.proposedRoot || '').slice(0, 12)}`);
  check('namespace cell threshold slot non-zero (immutable committee config)',
    nonZero(st.threshold), st.threshold);
  check('namespace cell governance_committee_root non-zero (immutable)',
    nonZero(st.governance_committee_root), st.governance_committee_root);
  check('namespace cell pending_proposal_root cleared by commit',
    isZero(st.pending_proposal_root), st.pending_proposal_root);

  // (7) independent runtime read confirms version=1.
  const live = await page.evaluate(async (cellId) => {
    const rt = window.__starbridgeAppRuntime;
    return { version: rt.readCellField(cellId, 1), root: rt.readCellField(cellId, 0) };
  }, result.nsCell);
  check('independent runtime read confirms version=1', u64BE(live.version) === 1, live.version);

  await page.waitForTimeout(300);
  // (8) zero errors.
  const realErrors = errors.filter((e) => !/read-only/.test(e));
  check('no console/page errors', realErrors.length === 0, realErrors.join(' | '));

  await browser.close();
  console.log(`\n[governed-namespace-flow] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[governed-namespace-flow] crashed:', e); process.exit(2); });
