/**
 * Playwright ad-hoc test for <pyana-cell-program> and <pyana-state-constraint>.
 *
 * Run from site/ root:
 *   node tests/cell-program-test.mjs
 *
 * Requires http://localhost:4818 to be serving the built site.
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

  // Wait for pyana:ready (wasm + inspector bundle loaded)
  await page.waitForFunction(() => !!window.pyana, { timeout: 15000 });
  console.log('[test] pyana:ready fired.');

  // Inject cell-program.js as an ES module (it uses `import` for _base.js)
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/cell-program.js`,
    type: 'module',
  });
  console.log('[test] cell-program.js injected.');

  // Wait for custom element registration (module evaluation is async)
  await page.waitForFunction(() =>
    !!customElements.get('pyana-cell-program') &&
    !!customElements.get('pyana-state-constraint'),
    { timeout: 10000 }
  );
  console.log('[test] custom elements registered.');

  // ─── Test 1: compact mode — None ────────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-cp-none');
    document.body.appendChild(el);
    el.program = { kind: 'None' };
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-none');
    return el && el.innerHTML.trim().length > 0;
  }, { timeout: 5000 });

  const noneText = await page.$eval('#test-cp-none', el => el.innerText.trim());
  console.log('[test 1] None compact:', noneText);
  if (!noneText.includes('None')) throw new Error('TEST FAILED: None compact should show "None"');
  console.log('[test 1] PASS: None compact renders correctly.');

  // ─── Test 2: compact mode — Predicate with 3 constraints ────────────────────
  const predProgram = {
    kind: 'Predicate',
    constraints: [
      { kind: 'FieldEquals', index: 0, value: 'deadbeef00000000000000000000000000000000000000000000000000000000' },
      { kind: 'WriteOnce',   index: 1 },
      { kind: 'RateLimit',   max_per_epoch: 5, epoch_duration: 100 },
    ],
  };

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-cp-pred-compact');
    document.body.appendChild(el);
    el.program = prog;
  }, predProgram);

  const predCompactText = await page.$eval('#test-cp-pred-compact', el => el.innerText.trim());
  console.log('[test 2] Predicate compact:', predCompactText);
  if (!predCompactText.includes('Predicate')) throw new Error('TEST FAILED: Predicate compact should show "Predicate"');
  if (!predCompactText.includes('3')) throw new Error('TEST FAILED: Predicate compact should show count 3');
  console.log('[test 2] PASS: Predicate(3) compact renders.');

  // ─── Test 3: default mode — Predicate, each constraint rendered ─────────────
  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'default');
    el.setAttribute('id', 'test-cp-pred-default');
    document.body.appendChild(el);
    el.program = prog;
  }, predProgram);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-pred-default');
    return el && el.querySelectorAll('pyana-state-constraint').length >= 3;
  }, { timeout: 5000 });

  const scCount = await page.$eval('#test-cp-pred-default', el =>
    el.querySelectorAll('pyana-state-constraint').length
  );
  console.log('[test 3] Constraint elements rendered:', scCount);
  if (scCount < 3) throw new Error(`TEST FAILED: expected 3 pyana-state-constraint, got ${scCount}`);

  // Verify chips are present
  const chipCount = await page.$eval('#test-cp-pred-default', el =>
    el.querySelectorAll('.pyana-sc__chip').length
  );
  console.log('[test 3] Chips rendered:', chipCount);
  if (chipCount < 3) throw new Error(`TEST FAILED: expected ≥3 chips, got ${chipCount}`);

  // Check that FieldEquals chip text is correct
  const chipTexts = await page.$$eval('#test-cp-pred-default .pyana-sc__chip', chips =>
    chips.map(c => c.textContent.trim())
  );
  console.log('[test 3] Chip labels:', chipTexts);
  if (!chipTexts.includes('FieldEquals')) throw new Error('TEST FAILED: FieldEquals chip missing');
  if (!chipTexts.includes('WriteOnce'))   throw new Error('TEST FAILED: WriteOnce chip missing');
  if (!chipTexts.includes('RateLimit'))   throw new Error('TEST FAILED: RateLimit chip missing');
  console.log('[test 3] PASS: Predicate default renders 3 constraint rows with correct chips.');

  // ─── Test 4: default mode — comprehensive variant coverage ─────────────────
  const allVariantsProgram = {
    kind: 'Predicate',
    constraints: [
      { kind: 'FieldEquals',        index: 0, value: 'aaaa000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'FieldGte',           index: 1, value: 'bbbb000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'FieldLte',           index: 2, value: 'cccc000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'SumEquals',          indices: [0, 1], value: 'dddd000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'WriteOnce',          index: 3 },
      { kind: 'Immutable',          index: 4 },
      { kind: 'Monotonic',          index: 5 },
      { kind: 'StrictMonotonic',    index: 6 },
      { kind: 'MonotonicSequence',  seq_index: 7 },
      { kind: 'BoundedBy',          index: 0, witness_index: 1 },
      { kind: 'FieldDelta',         index: 0, delta: 'ffff000000000000000000000000000000000000000000000000000000000001' },
      { kind: 'FieldDeltaInRange',  index: 1, min_delta: '0000000000000001', max_delta: '0000000000000064' },
      { kind: 'FieldGteHeight',     index: 2, offset: 10 },
      { kind: 'FieldLteHeight',     index: 3, offset: -5 },
      { kind: 'SumEqualsAcross',    input_fields: [0, 1], output_fields: [2, 3] },
      { kind: 'SenderAuthorized',   set_kind: 'Merkle', commitment: 'beef000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'CapabilityUniqueness', cap_set_root_slot: 2 },
      { kind: 'RateLimit',          max_per_epoch: 10, epoch_duration: 60 },
      { kind: 'RateLimitBySum',     slot_index: 0, max_sum_per_epoch: 1000, epoch_duration: 60 },
      { kind: 'TemporalGate',       not_before: 1716480000, not_after: null },
      { kind: 'PreimageGate',       commitment_index: 1, hash_kind: 'Blake3' },
      { kind: 'AllowedTransitions', slot_index: 0, allowed: [['aaaa', 'bbbb'], ['cccc', 'dddd']] },
      { kind: 'AnyOf',              variants: [
          { kind: 'FieldEquals', index: 0, value: '0000000000000000000000000000000000000000000000000000000000000001' },
          { kind: 'Monotonic',   index: 1 },
        ]
      },
      { kind: 'BoundDelta',         local_slot: 0, peer_cell: 'cafe000000000000000000000000000000000000000000000000000000000000', peer_slot: 1, delta_relation: 'Lte' },
      { kind: 'TemporalPredicate',  witness_index: 2, dsl_hash: 'dead000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'Witnessed',          predicate_kind: 'Dfa', commitment: 'face000000000000000000000000000000000000000000000000000000000000', input_ref: 'Slot', proof_witness_index: 3 },
      { kind: 'Renounced',          set_kind: 'AllowList', commitment: 'bead000000000000000000000000000000000000000000000000000000000000' },
      { kind: 'Custom',             ir_hash: 'aabb000000000000000000000000000000000000000000000000000000000000', descriptor_debug: 'custom_constraint_v1' },
    ],
  };

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'default');
    el.setAttribute('id', 'test-cp-all-variants');
    document.body.appendChild(el);
    el.program = prog;
  }, allVariantsProgram);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-all-variants');
    return el && el.querySelectorAll('pyana-state-constraint').length >= 28;
  }, { timeout: 5000 });

  const allVariantChips = await page.$$eval('#test-cp-all-variants .pyana-sc__chip', chips =>
    chips.map(c => c.textContent.trim())
  );
  console.log('[test 4] All variant chips:', allVariantChips);

  const expectedVariants = [
    'FieldEquals', 'FieldGte', 'FieldLte', 'SumEquals', 'WriteOnce', 'Immutable',
    'Monotonic', 'StrictMonotonic', 'MonotonicSequence', 'BoundedBy',
    'FieldDelta', 'FieldDeltaInRange', 'FieldGteHeight', 'FieldLteHeight',
    'SumEqualsAcross', 'SenderAuthorized', 'CapabilityUniqueness',
    'RateLimit', 'RateLimitBySum', 'TemporalGate', 'PreimageGate',
    'AllowedTransitions', 'AnyOf', 'BoundDelta', 'TemporalPredicate',
    'Witnessed', 'Renounced', 'Custom',
  ];

  const missing = expectedVariants.filter(v => !allVariantChips.includes(v));
  if (missing.length > 0) {
    throw new Error(`TEST FAILED: Missing chips for variants: ${missing.join(', ')}`);
  }
  console.log('[test 4] PASS: All 28 variants render with chips.');

  // ─── Test 5: Cases program ──────────────────────────────────────────────────
  const casesProgram = {
    kind: 'Cases',
    cases: [
      {
        guard: { kind: 'Always' },
        constraints: [{ kind: 'WriteOnce', index: 0 }],
      },
      {
        guard: { kind: 'SlotChanged', index: 1 },
        constraints: [{ kind: 'Monotonic', index: 1 }, { kind: 'RateLimit', max_per_epoch: 3, epoch_duration: 10 }],
      },
      {
        guard: { kind: 'MethodIs', method: 'cafebabe00000000000000000000000000000000000000000000000000000000' },
        constraints: [],
      },
    ],
  };

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-cp-cases-compact');
    document.body.appendChild(el);
    el.program = prog;
  }, casesProgram);

  const casesCompact = await page.$eval('#test-cp-cases-compact', el => el.innerText.trim());
  console.log('[test 5a] Cases compact:', casesCompact);
  if (!casesCompact.includes('Cases')) throw new Error('TEST FAILED: Cases compact missing "Cases"');
  if (!casesCompact.includes('3'))     throw new Error('TEST FAILED: Cases compact missing count "3"');

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'default');
    el.setAttribute('id', 'test-cp-cases-default');
    document.body.appendChild(el);
    el.program = prog;
  }, casesProgram);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-cases-default');
    return el && el.querySelectorAll('.pyana-cp__case').length >= 3;
  }, { timeout: 5000 });

  const caseCount = await page.$eval('#test-cp-cases-default', el =>
    el.querySelectorAll('.pyana-cp__case').length
  );
  console.log('[test 5b] Case divs:', caseCount);
  if (caseCount < 3) throw new Error(`TEST FAILED: Expected 3 case divs, got ${caseCount}`);

  const guardTexts = await page.$$eval('#test-cp-cases-default .pyana-cp__guard-tag', els =>
    els.map(e => e.textContent.trim())
  );
  console.log('[test 5b] Guard labels:', guardTexts);
  if (!guardTexts.some(t => t.includes('always'))) throw new Error('TEST FAILED: "always" guard missing');
  if (!guardTexts.some(t => t.includes('slot[')))  throw new Error('TEST FAILED: SlotChanged guard missing');
  console.log('[test 5] PASS: Cases program renders case guards + nested constraints.');

  // ─── Test 6: Circuit program ────────────────────────────────────────────────
  const circuitProgram = {
    kind: 'Circuit',
    circuit_hash: 'aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899',
  };

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-cp-circuit-compact');
    document.body.appendChild(el);
    el.program = prog;
  }, circuitProgram);

  const circuitCompact = await page.$eval('#test-cp-circuit-compact', el => el.innerText.trim());
  console.log('[test 6a] Circuit compact:', circuitCompact);
  if (!circuitCompact.includes('Circuit')) throw new Error('TEST FAILED: Circuit compact missing "Circuit"');

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'default');
    el.setAttribute('id', 'test-cp-circuit-default');
    document.body.appendChild(el);
    el.program = prog;
  }, circuitProgram);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-circuit-default');
    return el && el.querySelector('.pyana-cp__circuit-hash');
  }, { timeout: 5000 });

  const circuitHashText = await page.$eval('#test-cp-circuit-default .pyana-cp__circuit-hash', el => el.textContent.trim());
  console.log('[test 6b] Circuit hash displayed:', circuitHashText);
  if (!circuitHashText.includes('aabbccdd')) throw new Error('TEST FAILED: Circuit hash not shown');
  console.log('[test 6] PASS: Circuit program renders VK hash.');

  // ─── Test 7: data-program attribute (JSON passthrough) ──────────────────────
  await page.evaluate(() => {
    const prog = { kind: 'Predicate', constraints: [{ kind: 'Immutable', index: 0 }] };
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'compact');
    el.setAttribute('data-program', JSON.stringify(prog));
    el.setAttribute('id', 'test-cp-attr');
    document.body.appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-attr');
    return el && el.innerHTML.trim().length > 0;
  }, { timeout: 5000 });

  const attrText = await page.$eval('#test-cp-attr', el => el.innerText.trim());
  console.log('[test 7] data-program attr:', attrText);
  if (!attrText.includes('Predicate')) throw new Error('TEST FAILED: data-program attr not parsed');
  console.log('[test 7] PASS: data-program attribute JSON passthrough works.');

  // ─── Test 8: AnyOf nested chip rendering ────────────────────────────────────
  const anyofProgram = {
    kind: 'Predicate',
    constraints: [
      { kind: 'AnyOf', variants: [
        { kind: 'FieldEquals', index: 0, value: '0000000000000000000000000000000000000000000000000000000000000001' },
        { kind: 'SenderAuthorized', set_kind: 'Merkle', commitment: 'cafe000000000000000000000000000000000000000000000000000000000000' },
        { kind: 'CapabilityUniqueness', cap_set_root_slot: 3 },
      ]},
    ],
  };

  await page.evaluate((prog) => {
    const el = document.createElement('pyana-cell-program');
    el.setAttribute('mode', 'default');
    el.setAttribute('id', 'test-cp-anyof');
    document.body.appendChild(el);
    el.program = prog;
  }, anyofProgram);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-cp-anyof');
    return el && el.querySelector('.pyana-sc__anyof');
  }, { timeout: 5000 });

  const anyofItems = await page.$eval('#test-cp-anyof .pyana-sc__anyof', ul =>
    ul.querySelectorAll('li').length
  );
  console.log('[test 8] AnyOf inline items:', anyofItems);
  if (anyofItems < 3) throw new Error(`TEST FAILED: AnyOf should show 3 alternatives, got ${anyofItems}`);
  console.log('[test 8] PASS: AnyOf renders nested alternatives inline.');

  // ─── Check for JS errors ─────────────────────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') && !e.includes('NetworkError') && !e.includes('WASM')
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors during test run:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message);
  process.exit(1);
});
