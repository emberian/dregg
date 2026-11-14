import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import vm from 'node:vm';

// Evaluate the actual rendering functions without booting either application.
function loadFunction(path, name, context) {
  const source = readFileSync(new URL('../../' + path, import.meta.url), 'utf8');
  const start = source.indexOf(`function ${name}(`);
  assert.ok(start >= 0);
  const end = source.indexOf('\n}', start) + 2;
  vm.runInContext(source.slice(start, end), context);
}

test('explorer distinguishes exemption, pending and unattested', () => {
  const context = vm.createContext({ esc: String });
  loadFunction('site/explorer/explorer.js', 'proofStatusPill', context);
  loadFunction('site/explorer/explorer.js', 'proofPill', context);
  const exempt = context.proofPill({ has_proof: false, proof_status: 'not_required' });
  assert.match(exempt, /signature attestation, not a validity proof/);
  assert.doesNotMatch(exempt, /proof attached|proof pending/);
  assert.match(context.proofPill({ has_proof: false, proof_status: 'unattested' }), /unattested/);
  assert.match(context.proofPill({ has_proof: true, proof_status: 'not_required' }), /proof attached/);
});

test('settlement badge shows signature-only status without claiming proven', () => {
  const classes = new Set();
  const el = { textContent: '', classList: { add: x => classes.add(x), remove: x => classes.delete(x) } };
  const context = vm.createContext({ $: () => el });
  loadFunction('drex-web/app.js', 'renderProofBadge', context);
  for (const receipt of [{ proofStatus: 'not_required' }, { proof_status: 'not_required' }]) {
    context.renderProofBadge({ receipt });
    assert.match(el.textContent, /signature attestation only.*no validity proof/);
    assert.doesNotMatch(el.textContent, /proven/);
    assert.ok(classes.has('show'));
  }
  context.renderProofBadge({ receipt: {} });
  assert.equal(el.textContent, '');
  assert.ok(!classes.has('show'));
});

test('second settlement UI labels exempt receipts as signature-only', () => {
  const html = (strings, ...values) => strings.reduce((s, part, i) => s + part + (values[i] ?? ''), '');
  const context = vm.createContext({ html });
  loadFunction('drex-web-v2/src/app.js', 'SettleResult', context);
  const rendered = context.SettleResult({ s: { accepted: true, proofStatus: 'not_required' } });
  assert.match(rendered, /Committed · signature only/);
  assert.match(rendered, /no validity proof/);
  assert.doesNotMatch(rendered, /Committed · proof pending|Settled ·/);
});
