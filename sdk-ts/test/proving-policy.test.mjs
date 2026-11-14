import { test } from 'node:test';
import assert from 'node:assert/strict';
import { NodeClient, Receipt } from '../dist/index.mjs';

const hash = '12'.repeat(32);

// Stub the transport, exercising the real public proof fetcher and receipt noun.
test('not_required never becomes a proof or an endless pending response', async () => {
  const client = new NodeClient('http://localhost');
  client.request = async () => ({ turn_hash: hash, proof_status: 'not_required', proof_hex: null });
  await assert.rejects(client.turnProof(hash), /signature|attestation only/);
  const receipt = new Receipt({ turnHash: hash, proofStatus: 'not_required', hasProofHint: false });
  assert.equal(receipt.proofStatus, 'not_required');
  assert.equal(receipt.hasProof(), false);
  assert.equal(receipt.proof(), undefined);
});

test('proof fetch refuses unknown disposition and malformed bytes', async () => {
  const client = new NodeClient('http://localhost');
  for (const response of [
    { proof_status: 'unattested', proof_hex: 'abcd' },
    { proof_status: 'proved', proof_hex: '' },
    { proof_status: 'proved', proof_hex: 'xyz' },
    { proof_status: 'future_status', proof_hex: 'abcd' },
  ]) {
    client.request = async () => ({ turn_hash: hash, ...response });
    await assert.rejects(client.turnProof(hash), /no.*proved artifact/);
  }
  client.request = async () => ({ turn_hash: hash, proof_status: 'proved', proof_hex: 'abcd' });
  assert.ok(await client.turnProof(hash)); // Artifact present; cryptographic verification is still required.
});

test('receipt lookup retains not_required explicitly', async () => {
  const client = new NodeClient('http://localhost');
  client.receipts = async () => [{ turn_hash: hash, proof_status: 'not_required', has_proof: false }];
  const receipt = await client.receiptForTurn(hash, 1, 0);
  assert.equal(receipt.proofStatus, 'not_required');
  assert.equal(receipt.hasProof(), false);
});

test('SSE retains coordination disposition without attaching a proof', { timeout: 5000 }, async () => {
  const { createServer } = await import('node:http');
  const server = createServer((_req, res) => {
    res.writeHead(200, { 'content-type': 'text/event-stream' });
    res.write(`event: receipt\nid: 0\ndata: ${JSON.stringify({
      chain_index: 0, turn_hash: hash, receipt_hash: hash,
      proof_status: 'not_required', has_proof: false, finality: 'final',
      receipt: { turn_hash: Array(32).fill(0x12) },
    })}\n\n`);
  });
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
  try {
    const client = new NodeClient(`http://127.0.0.1:${server.address().port}`);
    for await (const receipt of client.events().subscribe()) {
      assert.equal(receipt.proofStatus, 'not_required');
      assert.equal(receipt.hasProof(), false);
      break;
    }
  } finally {
    server.closeAllConnections();
    await new Promise((resolve) => server.close(resolve));
  }
});
