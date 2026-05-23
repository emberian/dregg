/**
 * Example interactions with a deployed PyanaFederation zkApp.
 *
 * Usage:
 *   DEPLOYER_KEY=<base58-private-key> \
 *   ZKAPP_ADDRESS=<base58-public-key> \
 *   MINA_ENDPOINT=https://api.minascan.io/node/devnet/v1/graphql \
 *   npx ts-node scripts/interact.ts <command> [args...]
 *
 * Commands:
 *   status                           - Show current on-chain state
 *   advance <old> <new> <height>     - Submit a state advance
 *   deposit <amount> <commitment>    - Deposit tokens
 *   withdraw <amount> <nullifier>    - Withdraw tokens
 */

import {
  Mina,
  PrivateKey,
  PublicKey,
  Field,
  UInt64,
  fetchAccount,
  Poseidon,
} from 'o1js';
import { PyanaFederation } from '../src/PyanaFederation';
import { BridgeRelay } from '../src/bridge-ops';

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

const MINA_ENDPOINT =
  process.env.MINA_ENDPOINT ??
  'https://api.minascan.io/node/devnet/v1/graphql';

const DEPLOYER_KEY = process.env.DEPLOYER_KEY;
const ZKAPP_ADDRESS = process.env.ZKAPP_ADDRESS;

function requireEnv(name: string): string {
  const val = process.env[name];
  if (!val) {
    console.error(`ERROR: ${name} environment variable is required`);
    process.exit(1);
  }
  return val;
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

async function showStatus(zkApp: PyanaFederation, address: PublicKey) {
  await fetchAccount({ publicKey: address });

  console.log('=== PyanaFederation Status ===\n');
  console.log(`  Address:        ${address.toBase58()}`);
  console.log(`  State Root:     ${zkApp.stateRoot.get().toString()}`);
  console.log(`  Proven Height:  ${zkApp.provenHeight.get().toString()}`);
  console.log(`  Federation ID:  ${zkApp.federationId.get().toString()}`);
  console.log(`  Total Locked:   ${zkApp.totalLocked.get().toString()} nanomina`);
  console.log(`  Nullifier Root: ${zkApp.nullifierRoot.get().toString()}`);
  console.log(`  Relay Auth:     ${zkApp.relayAuthority.get().toString()}`);
}

async function advanceState(
  relay: BridgeRelay,
  senderKey: PrivateKey,
  oldRoot: string,
  newRoot: string,
  height: string,
) {
  console.log('Submitting state advance...');
  console.log(`  Old root: ${oldRoot}`);
  console.log(`  New root: ${newRoot}`);
  console.log(`  Height:   ${height}`);

  const effectsHash = Poseidon.hash([Field(BigInt(newRoot)), Field(BigInt(height))]);

  const result = await relay.submitStateAdvance(
    senderKey,
    Field(BigInt(oldRoot)),
    Field(BigInt(newRoot)),
    Field(BigInt(height)),
    effectsHash,
  );

  if (result.success) {
    console.log(`  Success! TX: ${result.txHash}`);
  } else {
    console.error(`  Failed: ${result.error}`);
  }
}

async function deposit(
  relay: BridgeRelay,
  senderKey: PrivateKey,
  amount: string,
  commitment: string,
) {
  console.log('Processing deposit...');
  console.log(`  Amount:     ${amount} nanomina`);
  console.log(`  Commitment: ${commitment}`);

  const result = await relay.processDeposit(
    senderKey,
    UInt64.from(BigInt(amount)),
    Field(BigInt(commitment)),
  );

  if (result.success) {
    console.log(`  Success! TX: ${result.txHash}`);
  } else {
    console.error(`  Failed: ${result.error}`);
  }
}

async function withdraw(
  relay: BridgeRelay,
  senderKey: PrivateKey,
  amount: string,
  nullifier: string,
  zkApp: PyanaFederation,
  address: PublicKey,
) {
  console.log('Processing withdrawal...');
  console.log(`  Amount:    ${amount} nanomina`);
  console.log(`  Nullifier: ${nullifier}`);

  await fetchAccount({ publicKey: address });
  const currentRoot = zkApp.stateRoot.get();
  const recipient = senderKey.toPublicKey();

  const result = await relay.processWithdrawal(
    senderKey,
    UInt64.from(BigInt(amount)),
    Field(BigInt(nullifier)),
    currentRoot,
    recipient,
  );

  if (result.success) {
    console.log(`  Success! TX: ${result.txHash}`);
  } else {
    console.error(`  Failed: ${result.error}`);
  }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

async function main() {
  const command = process.argv[2];

  if (!command || command === 'help') {
    console.log('Usage: npx ts-node scripts/interact.ts <command> [args...]');
    console.log('');
    console.log('Commands:');
    console.log('  status                           - Show on-chain state');
    console.log('  advance <old> <new> <height>     - Submit state advance');
    console.log('  deposit <amount> <commitment>    - Deposit tokens');
    console.log('  withdraw <amount> <nullifier>    - Withdraw tokens');
    return;
  }

  // Connect to network
  const Network = Mina.Network(MINA_ENDPOINT);
  Mina.setActiveInstance(Network);

  const address = PublicKey.fromBase58(requireEnv('ZKAPP_ADDRESS'));
  const zkApp = new PyanaFederation(address);

  if (command === 'status') {
    await showStatus(zkApp, address);
    return;
  }

  // All other commands need a sender key
  const senderKey = PrivateKey.fromBase58(requireEnv('DEPLOYER_KEY'));

  // Compile for proving
  console.log('Compiling zkApp...');
  await PyanaFederation.compile();

  const relay = new BridgeRelay({
    zkAppAddress: address,
    minaEndpoint: MINA_ENDPOINT,
  });

  switch (command) {
    case 'advance': {
      const [oldRoot, newRoot, height] = process.argv.slice(3);
      if (!oldRoot || !newRoot || !height) {
        console.error('Usage: advance <oldRoot> <newRoot> <height>');
        process.exit(1);
      }
      await advanceState(relay, senderKey, oldRoot, newRoot, height);
      break;
    }
    case 'deposit': {
      const [amount, commitment] = process.argv.slice(3);
      if (!amount || !commitment) {
        console.error('Usage: deposit <amount> <commitment>');
        process.exit(1);
      }
      await deposit(relay, senderKey, amount, commitment);
      break;
    }
    case 'withdraw': {
      const [amount, nullifier] = process.argv.slice(3);
      if (!amount || !nullifier) {
        console.error('Usage: withdraw <amount> <nullifier>');
        process.exit(1);
      }
      await withdraw(relay, senderKey, amount, nullifier, zkApp, address);
      break;
    }
    default:
      console.error(`Unknown command: ${command}`);
      process.exit(1);
  }
}

main().catch((e) => {
  console.error('Error:', e);
  process.exit(1);
});
