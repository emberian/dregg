/**
 * Deploy the PyanaFederation zkApp to Mina testnet.
 *
 * Usage:
 *   DEPLOYER_KEY=<base58-private-key> \
 *   MINA_ENDPOINT=https://api.minascan.io/node/devnet/v1/graphql \
 *   GENESIS_ROOT=<field-decimal> \
 *   CONSTITUTION_HASH=<field-decimal> \
 *   npx ts-node scripts/deploy.ts
 *
 * The script will:
 * 1. Compile the zkApp (generates the verification key)
 * 2. Deploy the contract to a fresh address
 * 3. Initialize with the provided genesis state
 * 4. Print the zkApp address for relay configuration
 */

import {
  Mina,
  PrivateKey,
  Field,
  AccountUpdate,
  Poseidon,
  fetchAccount,
} from 'o1js';
import { PyanaFederation } from '../src/PyanaFederation';

// ---------------------------------------------------------------------------
// Configuration from environment
// ---------------------------------------------------------------------------

const MINA_ENDPOINT =
  process.env.MINA_ENDPOINT ??
  'https://api.minascan.io/node/devnet/v1/graphql';

const DEPLOYER_KEY = process.env.DEPLOYER_KEY;
if (!DEPLOYER_KEY) {
  console.error('ERROR: DEPLOYER_KEY environment variable is required');
  console.error('       Provide a base58-encoded Mina private key');
  process.exit(1);
}

const GENESIS_ROOT = process.env.GENESIS_ROOT
  ? Field(BigInt(process.env.GENESIS_ROOT))
  : Poseidon.hash([Field(0)]); // Default genesis

const CONSTITUTION_HASH = process.env.CONSTITUTION_HASH
  ? Field(BigInt(process.env.CONSTITUTION_HASH))
  : Poseidon.hash([Field(1), Field(2), Field(3)]); // Default constitution

// ---------------------------------------------------------------------------
// Main deployment
// ---------------------------------------------------------------------------

async function main() {
  console.log('=== PyanaFederation Deployment ===\n');

  // Connect to Mina network
  console.log(`Connecting to: ${MINA_ENDPOINT}`);
  const Network = Mina.Network(MINA_ENDPOINT);
  Mina.setActiveInstance(Network);

  // Set up deployer account
  const deployerKey = PrivateKey.fromBase58(DEPLOYER_KEY!);
  const deployerAccount = deployerKey.toPublicKey();
  console.log(`Deployer: ${deployerAccount.toBase58()}`);

  // Fetch deployer account to check balance
  console.log('Fetching deployer account...');
  await fetchAccount({ publicKey: deployerAccount });

  // Generate a new keypair for the zkApp
  const zkAppKey = PrivateKey.random();
  const zkAppAddress = zkAppKey.toPublicKey();
  console.log(`\nzkApp address: ${zkAppAddress.toBase58()}`);
  console.log(`zkApp private key: ${zkAppKey.toBase58()}`);
  console.log('\n  !!! SAVE THE PRIVATE KEY - YOU NEED IT FOR UPGRADES !!!\n');

  // Compile the zkApp
  console.log('Compiling PyanaFederation...');
  const startCompile = Date.now();
  const { verificationKey } = await PyanaFederation.compile();
  const compileTime = ((Date.now() - startCompile) / 1000).toFixed(1);
  console.log(`  Compiled in ${compileTime}s`);
  console.log(`  Verification key hash: ${verificationKey.hash.toString().slice(0, 20)}...`);

  // Compute relay authority hash (deployer is initial relay)
  const relayPubKeyHash = Poseidon.hash(deployerAccount.toFields());

  // Deploy transaction
  console.log('\nDeploying...');
  const deployTxn = await Mina.transaction(
    { sender: deployerAccount, fee: 300_000_000 }, // 0.3 MINA fee
    async () => {
      AccountUpdate.fundNewAccount(deployerAccount);
      await new PyanaFederation(zkAppAddress).deploy({ verificationKey });
    },
  );
  await deployTxn.prove();
  const deployResult = await deployTxn.sign([deployerKey, zkAppKey]).send();
  console.log(`  Deploy tx: ${deployResult.hash}`);
  console.log('  Waiting for inclusion...');
  await deployResult.wait();
  console.log('  Deployed!');

  // Initialize transaction
  console.log('\nInitializing...');
  console.log(`  Genesis root: ${GENESIS_ROOT.toString()}`);
  console.log(`  Constitution: ${CONSTITUTION_HASH.toString()}`);
  console.log(`  Relay authority: ${relayPubKeyHash.toString().slice(0, 20)}...`);

  const zkApp = new PyanaFederation(zkAppAddress);
  const initTxn = await Mina.transaction(
    { sender: deployerAccount, fee: 200_000_000 },
    async () => {
      await zkApp.initialize(GENESIS_ROOT, CONSTITUTION_HASH, relayPubKeyHash);
    },
  );
  await initTxn.prove();
  const initResult = await initTxn.sign([deployerKey]).send();
  console.log(`  Init tx: ${initResult.hash}`);
  console.log('  Waiting for inclusion...');
  await initResult.wait();
  console.log('  Initialized!');

  // Summary
  console.log('\n=== Deployment Complete ===');
  console.log(`  Network:     ${MINA_ENDPOINT}`);
  console.log(`  zkApp:       ${zkAppAddress.toBase58()}`);
  console.log(`  Federation:  ${CONSTITUTION_HASH.toString()}`);
  console.log(`  Genesis:     ${GENESIS_ROOT.toString()}`);
  console.log(`  Height:      1`);
  console.log('\nAdd to your relay config:');
  console.log(`  mina_zkapp_address = "${zkAppAddress.toBase58()}"`);
}

main().catch((e) => {
  console.error('Deployment failed:', e);
  process.exit(1);
});
