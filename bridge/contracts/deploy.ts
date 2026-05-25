// =============================================================================
// Pyana Bridge — Deployment and Interaction Script
// =============================================================================
//
// Based on patterns from:
//   - ~/midnight/midnight-docs/docs/guides/deploy-mn-app.mdx
//   - ~/midnight/midnight-js/testkit-js/testkit-js-e2e/test/contracts.it.test.ts
//   - @midnight-ntwrk/midnight-js-contracts API
//
// Package versions target the 4.0.x / 8.0.x generation (as of 2026 docs).
//
// Usage:
//   npx tsx deploy.ts deploy        — Deploy fresh bridge contract
//   npx tsx deploy.ts lock <amount> <pyanaAddr>  — Lock NIGHT for pyana
//   npx tsx deploy.ts unlock <attestation.json>  — Unlock with attestation
//   npx tsx deploy.ts status        — Query bridge state
//   npx tsx deploy.ts rotate <newKeyCommitment>  — Rotate federation key
//   npx tsx deploy.ts pause         — Pause bridge (governance)
//   npx tsx deploy.ts resume        — Resume bridge (governance)
//
// =============================================================================

import * as path from 'node:path';
import * as fs from 'node:fs';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { WebSocket } from 'ws';
import * as Rx from 'rxjs';
import { Buffer } from 'buffer';

// Midnight SDK imports
import {
  deployContract,
  findDeployedContract,
  type FinalizedDeployTxData,
} from '@midnight-ntwrk/midnight-js-contracts';
import { httpClientProofProvider } from '@midnight-ntwrk/midnight-js-http-client-proof-provider';
import { indexerPublicDataProvider } from '@midnight-ntwrk/midnight-js-indexer-public-data-provider';
import { levelPrivateStateProvider } from '@midnight-ntwrk/midnight-js-level-private-state-provider';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { setNetworkId, getNetworkId } from '@midnight-ntwrk/midnight-js-network-id';
import * as ledger from '@midnight-ntwrk/ledger-v8';
import { WalletFacade } from '@midnight-ntwrk/cipherclerk-sdk-facade';
import { DustWallet } from '@midnight-ntwrk/cipherclerk-sdk-dust-cclerk';
import { HDWallet, Roles } from '@midnight-ntwrk/cipherclerk-sdk-hd';
import { ShieldedWallet } from '@midnight-ntwrk/cipherclerk-sdk-shielded';
import {
  createKeystore,
  InMemoryTransactionHistoryStorage,
  PublicKey,
  UnshieldedWallet,
} from '@midnight-ntwrk/cipherclerk-sdk-unshielded-cclerk';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import { toHex } from '@midnight-ntwrk/midnight-js-utils';
import { unshieldedToken } from '@midnight-ntwrk/ledger-v8';

// @ts-expect-error Required for cipherclerk sync in Node.js
globalThis.WebSocket = WebSocket;

// =============================================================================
// Configuration
// =============================================================================

// Network configuration — adjust for your target network
setNetworkId('preprod');

const CONFIG = {
  indexer: 'https://indexer.preprod.midnight.network/api/v4/graphql',
  indexerWS: 'wss://indexer.preprod.midnight.network/api/v4/graphql/ws',
  node: 'https://rpc.preprod.midnight.network',
  proofServer: 'http://127.0.0.1:6300',
};

// Bridge deployment parameters
const BRIDGE_CONFIG = {
  // Minimum lock/unlock: 1 NIGHT (10^6 STARS)
  minAmount: 1_000_000n,
  // Maximum per-transaction: 10,000 NIGHT
  maxAmount: 10_000_000_000n,
  // Daily limit: 100,000 NIGHT
  dailyLimit: 100_000_000_000n,
  // Domain separator for this bridge instance
  domainSeparator: Buffer.from('pyana:midnight:bridge:v1\0\0\0\0\0\0\0\0', 'utf8'),
};

// =============================================================================
// Path Configuration
// =============================================================================

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const zkConfigPath = path.resolve(__dirname, 'managed', 'pyana-bridge');
const deploymentPath = path.resolve(__dirname, 'deployment.json');

// =============================================================================
// Contract Loading
// =============================================================================

interface BridgeLedger {
  bridgeState: number;
  totalLocked: bigint;
  federationKeyCommitment: Uint8Array;
  federationEpoch: bigint;
  previousKeyCommitment: Uint8Array;
  minAmount: bigint;
  maxAmount: bigint;
  dailyLimit: bigint;
  dailyUsed: bigint;
  dailyResetTimestamp: bigint;
  lockNonce: bigint;
  lastLockEvent: {
    amount: bigint;
    pyanaRecipient: Uint8Array;
    nonce: bigint;
    timestamp: bigint;
  };
  lastUnlockEvent: {
    amount: bigint;
    midnightRecipient: Uint8Array;
    nonce: bigint;
    epoch: bigint;
  };
}

interface BridgePrivateState {
  governanceSecretKey: Uint8Array;
  federationVerificationSecret: Uint8Array;
}

type BridgeContract = {
  impureCircuits: {
    lockForPyana: (ctx: any, amount: bigint, pyanaRecipient: Uint8Array) => any;
    unlockFromPyana: (
      ctx: any,
      amount: bigint,
      midnightRecipient: any,
      nonce: bigint,
      epoch: bigint,
      attestationProof: Uint8Array,
      pyanaBlockHash: Uint8Array,
    ) => any;
    rotateFederationKey: (ctx: any, newKeyCommitment: Uint8Array, newEpoch: bigint) => any;
    updateBridgeLimits: (ctx: any, min: bigint, max: bigint, daily: bigint) => any;
    pauseBridge: (ctx: any) => any;
    resumeBridge: (ctx: any) => any;
    emergencyShutdown: (ctx: any) => any;
    resetDailyUsage: (ctx: any, timestamp: bigint) => any;
  };
  pureCircuits: {
    getTotalLocked: (ctx: any) => bigint;
    getBridgeState: (ctx: any) => number;
    getFederationEpoch: (ctx: any) => bigint;
    getLimits: (ctx: any) => [bigint, bigint, bigint];
  };
};

async function loadContract() {
  const contractPath = path.join(zkConfigPath, 'contract', 'index.js');
  if (!fs.existsSync(contractPath)) {
    throw new Error(
      `Contract not compiled! Run: compact compile pyana_bridge.compact managed/pyana-bridge\n` +
        `Expected: ${contractPath}`,
    );
  }
  const PyanaContract = await import(pathToFileURL(contractPath).href);
  return PyanaContract;
}

// =============================================================================
// Cipherclerk Setup
// =============================================================================

function deriveKeys(seed: string) {
  const hdCclerk = HDWallet.fromSeed(Buffer.from(seed, 'hex'));
  if (hdCclerk.type !== 'seedOk') throw new Error('Invalid seed');

  const result = hdCclerk.hdCclerk
    .selectAccount(0)
    .selectRoles([Roles.Zswap, Roles.NightExternal, Roles.Dust])
    .deriveKeysAt(0);

  if (result.type !== 'keysDerived') throw new Error('Key derivation failed');
  hdCclerk.hdCclerk.clear();
  return result.keys;
}

async function createCipherclerk(seed: string) {
  const keys = deriveKeys(seed);
  const networkId = getNetworkId();

  const shieldedSecretKeys = ledger.ZswapSecretKeys.fromSeed(keys[Roles.Zswap]);
  const dustSecretKey = ledger.DustSecretKey.fromSeed(keys[Roles.Dust]);
  const unshieldedKeystore = createKeystore(keys[Roles.NightExternal], networkId);

  const cclerkConfig = {
    networkId,
    indexerClientConnection: {
      indexerHttpUrl: CONFIG.indexer,
      indexerWsUrl: CONFIG.indexerWS,
    },
    provingServerUrl: new URL(CONFIG.proofServer),
    relayURL: new URL(CONFIG.node.replace(/^http/, 'ws')),
  };

  const shieldedCclerk = ShieldedWallet(cclerkConfig).startWithSecretKeys(shieldedSecretKeys);

  const unshieldedCclerk = UnshieldedWallet({
    networkId,
    indexerClientConnection: cclerkConfig.indexerClientConnection,
    txHistoryStorage: new InMemoryTransactionHistoryStorage(),
  }).startWithPublicKey(PublicKey.fromKeyStore(unshieldedKeystore));

  const dustCclerk = DustWallet({
    ...cclerkConfig,
    costParameters: {
      additionalFeeOverhead: 300_000_000_000_000n,
      feeBlocksMargin: 5,
    },
  }).startWithSecretKey(dustSecretKey, ledger.LedgerParameters.initialParameters().dust);

  const cclerk = new WalletFacade(shieldedCclerk, unshieldedCclerk, dustCclerk);
  await cclerk.start(shieldedSecretKeys, dustSecretKey);

  return { cclerk, shieldedSecretKeys, dustSecretKey, unshieldedKeystore };
}

// =============================================================================
// Provider Setup
// =============================================================================

function signTransactionIntents(
  tx: { intents?: Map<number, any> },
  signFn: (payload: Uint8Array) => ledger.Signature,
  proofMarker: 'proof' | 'pre-proof',
): void {
  if (!tx.intents || tx.intents.size === 0) return;

  for (const segment of tx.intents.keys()) {
    const intent = tx.intents.get(segment);
    if (!intent) continue;

    const cloned = ledger.Intent.deserialize<
      ledger.SignatureEnabled,
      ledger.Proofish,
      ledger.PreBinding
    >('signature', proofMarker, 'pre-binding', intent.serialize());

    const sigData = cloned.signatureData(segment);
    const signature = signFn(sigData);

    if (cloned.fallibleUnshieldedOffer) {
      const sigs = cloned.fallibleUnshieldedOffer.inputs.map(
        (_: any, i: number) => cloned.fallibleUnshieldedOffer!.signatures.at(i) ?? signature,
      );
      cloned.fallibleUnshieldedOffer = cloned.fallibleUnshieldedOffer.addSignatures(sigs);
    }

    if (cloned.guaranteedUnshieldedOffer) {
      const sigs = cloned.guaranteedUnshieldedOffer.inputs.map(
        (_: any, i: number) => cloned.guaranteedUnshieldedOffer!.signatures.at(i) ?? signature,
      );
      cloned.guaranteedUnshieldedOffer = cloned.guaranteedUnshieldedOffer.addSignatures(sigs);
    }

    tx.intents.set(segment, cloned);
  }
}

async function createProviders(cclerkCtx: Awaited<ReturnType<typeof createCipherclerk>>) {
  const state = await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(Rx.filter((s) => s.isSynced)),
  );

  const cclerkProvider = {
    getCoinPublicKey: () => state.shielded.coinPublicKey.toHexString(),
    getEncryptionPublicKey: () => state.shielded.encryptionPublicKey.toHexString(),
    async balanceTx(tx: any, ttl?: Date) {
      const recipe = await cclerkCtx.cclerk.balanceUnboundTransaction(
        tx,
        {
          shieldedSecretKeys: cclerkCtx.shieldedSecretKeys,
          dustSecretKey: cclerkCtx.dustSecretKey,
        },
        { ttl: ttl ?? new Date(Date.now() + 30 * 60 * 1000) },
      );

      const signFn = (payload: Uint8Array) => cclerkCtx.unshieldedKeystore.signData(payload);

      signTransactionIntents(recipe.baseTransaction, signFn, 'proof');
      if (recipe.balancingTransaction) {
        signTransactionIntents(recipe.balancingTransaction, signFn, 'pre-proof');
      }

      return cclerkCtx.cclerk.finalizeRecipe(recipe);
    },
    submitTx: (tx: any) => cclerkCtx.cclerk.submitTransaction(tx) as any,
  };

  const zkConfigProvider = new NodeZkConfigProvider(zkConfigPath);

  return {
    privateStateProvider: levelPrivateStateProvider({
      privateStateStoreName: 'pyana-bridge-state',
      cclerkProvider,
    }),
    publicDataProvider: indexerPublicDataProvider(CONFIG.indexer, CONFIG.indexerWS),
    zkConfigProvider,
    proofProvider: httpClientProofProvider(CONFIG.proofServer, zkConfigProvider),
    cclerkProvider,
    midnightProvider: cclerkProvider,
  };
}

// =============================================================================
// Bridge Witness Implementations
// =============================================================================
//
// These are the TypeScript witness implementations that the Compact runtime
// calls when executing circuits. They provide access to private state.

function createWitnesses(privateState: BridgePrivateState) {
  return {
    governanceSecretKey: ({
      privateState: ps,
    }: {
      privateState: BridgePrivateState;
    }): [BridgePrivateState, Uint8Array] => {
      return [ps, ps.governanceSecretKey];
    },

    federationVerificationSecret: ({
      privateState: ps,
    }: {
      privateState: BridgePrivateState;
    }): [BridgePrivateState, Uint8Array] => {
      return [ps, ps.federationVerificationSecret];
    },
  };
}

// =============================================================================
// Deployment
// =============================================================================

async function deployBridge(seed: string, governanceKey: Uint8Array, federationCommitment: Uint8Array) {
  console.log('Loading compiled contract...');
  const PyanaContract = await loadContract();

  const privateState: BridgePrivateState = {
    governanceSecretKey: governanceKey,
    federationVerificationSecret: new Uint8Array(32), // Set by federation
  };

  const witnesses = createWitnesses(privateState);

  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  console.log('Creating cipherclerk...');
  const cclerkCtx = await createCipherclerk(seed);

  console.log('Syncing cipherclerk...');
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  console.log('Setting up providers...');
  const providers = await createProviders(cclerkCtx);

  console.log('Deploying bridge contract...');
  const deployTxData = await deployContract(providers, {
    compiledContract,
    // Constructor arguments
    initialState: {
      federationKeyCommitment: federationCommitment,
      governanceAuthority: governanceKey,
      domainSeparator: BRIDGE_CONFIG.domainSeparator,
      minAmount: BRIDGE_CONFIG.minAmount,
      maxAmount: BRIDGE_CONFIG.maxAmount,
      dailyLimit: BRIDGE_CONFIG.dailyLimit,
    },
    privateState,
  });

  const contractAddress = deployTxData.deployTxData.contractAddress;
  console.log(`Bridge deployed at: ${contractAddress}`);

  // Save deployment info
  const deployment = {
    contractAddress,
    network: getNetworkId(),
    deployedAt: new Date().toISOString(),
    config: {
      minAmount: BRIDGE_CONFIG.minAmount.toString(),
      maxAmount: BRIDGE_CONFIG.maxAmount.toString(),
      dailyLimit: BRIDGE_CONFIG.dailyLimit.toString(),
    },
  };

  fs.writeFileSync(deploymentPath, JSON.stringify(deployment, null, 2));
  console.log(`Deployment info saved to: ${deploymentPath}`);

  return deployTxData;
}

// =============================================================================
// Lock NIGHT for Pyana
// =============================================================================

async function lockForPyana(seed: string, amount: bigint, pyanaRecipient: Uint8Array) {
  const deployment = JSON.parse(fs.readFileSync(deploymentPath, 'utf-8'));
  const PyanaContract = await loadContract();

  const privateState: BridgePrivateState = {
    governanceSecretKey: new Uint8Array(32), // Not needed for lock
    federationVerificationSecret: new Uint8Array(32),
  };

  const witnesses = createWitnesses(privateState);
  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  const cclerkCtx = await createCipherclerk(seed);
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  const providers = await createProviders(cclerkCtx);

  console.log('Joining deployed contract...');
  const contract = await findDeployedContract(providers, {
    contractAddress: deployment.contractAddress,
    compiledContract,
    privateState,
  });

  console.log(`Locking ${amount} NIGHT for pyana recipient: ${toHex(pyanaRecipient)}`);
  const result = await contract.callTx.lockForPyana(amount, pyanaRecipient);

  console.log('Lock transaction submitted successfully');
  console.log(`Transaction: ${result}`);

  return result;
}

// =============================================================================
// Unlock from Pyana
// =============================================================================

interface AttestationFile {
  amount: string; // bigint as string
  midnightRecipient: string; // hex
  nonce: string; // bigint as string
  epoch: string; // bigint as string
  attestationProof: string; // hex
  pyanaBlockHash: string; // hex
  recipientType: 'user' | 'contract'; // determines Either variant
}

async function unlockFromPyana(seed: string, attestationPath: string) {
  const deployment = JSON.parse(fs.readFileSync(deploymentPath, 'utf-8'));
  const attestation: AttestationFile = JSON.parse(fs.readFileSync(attestationPath, 'utf-8'));
  const PyanaContract = await loadContract();

  const privateState: BridgePrivateState = {
    governanceSecretKey: new Uint8Array(32),
    federationVerificationSecret: new Uint8Array(32),
  };

  const witnesses = createWitnesses(privateState);
  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  const cclerkCtx = await createCipherclerk(seed);
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  const providers = await createProviders(cclerkCtx);

  const contract = await findDeployedContract(providers, {
    contractAddress: deployment.contractAddress,
    compiledContract,
    privateState,
  });

  const recipientBytes = Buffer.from(attestation.midnightRecipient, 'hex');

  // Construct the Either<ContractAddress, UserAddress> based on recipient type
  const midnightRecipient =
    attestation.recipientType === 'contract'
      ? { is_left: true, left: { bytes: recipientBytes }, right: { bytes: new Uint8Array(32) } }
      : { is_left: false, left: { bytes: new Uint8Array(32) }, right: { bytes: recipientBytes } };

  console.log(`Unlocking ${attestation.amount} NIGHT to ${attestation.midnightRecipient}`);

  const result = await contract.callTx.unlockFromPyana(
    BigInt(attestation.amount),
    midnightRecipient,
    BigInt(attestation.nonce),
    BigInt(attestation.epoch),
    Buffer.from(attestation.attestationProof, 'hex'),
    Buffer.from(attestation.pyanaBlockHash, 'hex'),
  );

  console.log('Unlock transaction submitted successfully');
  console.log(`Transaction: ${result}`);

  return result;
}

// =============================================================================
// Query Bridge Status
// =============================================================================

async function queryBridgeStatus(seed: string) {
  const deployment = JSON.parse(fs.readFileSync(deploymentPath, 'utf-8'));
  const PyanaContract = await loadContract();

  const privateState: BridgePrivateState = {
    governanceSecretKey: new Uint8Array(32),
    federationVerificationSecret: new Uint8Array(32),
  };

  const witnesses = createWitnesses(privateState);
  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  const cclerkCtx = await createCipherclerk(seed);
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  const providers = await createProviders(cclerkCtx);

  const contract = await findDeployedContract(providers, {
    contractAddress: deployment.contractAddress,
    compiledContract,
    privateState,
  });

  // Read public ledger state via the indexer
  // The compiled contract exposes ledger getters
  const state = contract.state;

  const bridgeStates = ['ACTIVE', 'PAUSED', 'EMERGENCY_SHUTDOWN'];

  console.log('\n=== Pyana Bridge Status ===');
  console.log(`Contract:         ${deployment.contractAddress}`);
  console.log(`Network:          ${deployment.network}`);
  console.log(`State:            ${bridgeStates[state.bridgeState] ?? 'UNKNOWN'}`);
  console.log(`Total Locked:     ${state.totalLocked} STARS`);
  console.log(`Federation Epoch: ${state.federationEpoch}`);
  console.log(`Min Amount:       ${state.minAmount} STARS`);
  console.log(`Max Amount:       ${state.maxAmount} STARS`);
  console.log(`Daily Limit:      ${state.dailyLimit} STARS`);
  console.log(`Daily Used:       ${state.dailyUsed} STARS`);
  console.log('===========================\n');

  if (state.lastLockEvent.amount > 0n) {
    console.log('Last Lock Event:');
    console.log(`  Amount:    ${state.lastLockEvent.amount}`);
    console.log(`  Recipient: ${toHex(state.lastLockEvent.pyanaRecipient)}`);
    console.log(`  Nonce:     ${state.lastLockEvent.nonce}`);
  }

  if (state.lastUnlockEvent.amount > 0n) {
    console.log('Last Unlock Event:');
    console.log(`  Amount:    ${state.lastUnlockEvent.amount}`);
    console.log(`  Recipient: ${toHex(state.lastUnlockEvent.midnightRecipient)}`);
    console.log(`  Nonce:     ${state.lastUnlockEvent.nonce}`);
    console.log(`  Epoch:     ${state.lastUnlockEvent.epoch}`);
  }
}

// =============================================================================
// Governance Operations
// =============================================================================

async function rotateFederationKey(seed: string, newKeyCommitment: Uint8Array) {
  const deployment = JSON.parse(fs.readFileSync(deploymentPath, 'utf-8'));
  const PyanaContract = await loadContract();

  // Governance key must be provided in private state
  const governanceKey = Buffer.from(
    process.env.PYANA_GOVERNANCE_KEY ?? '',
    'hex',
  );
  if (governanceKey.length !== 32) {
    throw new Error('Set PYANA_GOVERNANCE_KEY env var (64 hex chars)');
  }

  const privateState: BridgePrivateState = {
    governanceSecretKey: governanceKey,
    federationVerificationSecret: new Uint8Array(32),
  };

  const witnesses = createWitnesses(privateState);
  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  const cclerkCtx = await createCipherclerk(seed);
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  const providers = await createProviders(cclerkCtx);

  const contract = await findDeployedContract(providers, {
    contractAddress: deployment.contractAddress,
    compiledContract,
    privateState,
  });

  // Read current epoch to compute next
  const currentEpoch = contract.state.federationEpoch;
  const newEpoch = currentEpoch + 1n;

  console.log(`Rotating federation key to epoch ${newEpoch}...`);
  const result = await contract.callTx.rotateFederationKey(newKeyCommitment, newEpoch);

  console.log('Key rotation submitted successfully');
  return result;
}

async function pauseBridge(seed: string) {
  const deployment = JSON.parse(fs.readFileSync(deploymentPath, 'utf-8'));
  const PyanaContract = await loadContract();

  const governanceKey = Buffer.from(process.env.PYANA_GOVERNANCE_KEY ?? '', 'hex');
  if (governanceKey.length !== 32) {
    throw new Error('Set PYANA_GOVERNANCE_KEY env var (64 hex chars)');
  }

  const privateState: BridgePrivateState = {
    governanceSecretKey: governanceKey,
    federationVerificationSecret: new Uint8Array(32),
  };

  const witnesses = createWitnesses(privateState);
  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  const cclerkCtx = await createCipherclerk(seed);
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  const providers = await createProviders(cclerkCtx);

  const contract = await findDeployedContract(providers, {
    contractAddress: deployment.contractAddress,
    compiledContract,
    privateState,
  });

  console.log('Pausing bridge...');
  const result = await contract.callTx.pauseBridge();
  console.log('Bridge paused');
  return result;
}

async function resumeBridge(seed: string) {
  const deployment = JSON.parse(fs.readFileSync(deploymentPath, 'utf-8'));
  const PyanaContract = await loadContract();

  const governanceKey = Buffer.from(process.env.PYANA_GOVERNANCE_KEY ?? '', 'hex');
  if (governanceKey.length !== 32) {
    throw new Error('Set PYANA_GOVERNANCE_KEY env var (64 hex chars)');
  }

  const privateState: BridgePrivateState = {
    governanceSecretKey: governanceKey,
    federationVerificationSecret: new Uint8Array(32),
  };

  const witnesses = createWitnesses(privateState);
  const compiledContract = CompiledContract.make('pyana-bridge', PyanaContract.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(zkConfigPath),
  );

  const cclerkCtx = await createCipherclerk(seed);
  await Rx.firstValueFrom(
    cclerkCtx.cclerk.state().pipe(
      Rx.throttleTime(5000),
      Rx.filter((s) => s.isSynced),
    ),
  );

  const providers = await createProviders(cclerkCtx);

  const contract = await findDeployedContract(providers, {
    contractAddress: deployment.contractAddress,
    compiledContract,
    privateState,
  });

  console.log('Resuming bridge...');
  const result = await contract.callTx.resumeBridge();
  console.log('Bridge resumed');
  return result;
}

// =============================================================================
// CLI Entry Point
// =============================================================================

async function main() {
  const args = process.argv.slice(2);
  const command = args[0];

  // Cipherclerk seed from env (required for all operations)
  const seed = process.env.PYANA_CCLERK_SEED;
  if (!seed) {
    console.error('Error: Set PYANA_CCLERK_SEED env var (64 hex chars)');
    process.exit(1);
  }

  switch (command) {
    case 'deploy': {
      const governanceKey = Buffer.from(process.env.PYANA_GOVERNANCE_KEY ?? '', 'hex');
      const federationCommitment = Buffer.from(
        process.env.PYANA_FEDERATION_COMMITMENT ?? '',
        'hex',
      );
      if (governanceKey.length !== 32) {
        console.error('Set PYANA_GOVERNANCE_KEY env var (64 hex chars)');
        process.exit(1);
      }
      if (federationCommitment.length !== 32) {
        console.error('Set PYANA_FEDERATION_COMMITMENT env var (64 hex chars)');
        process.exit(1);
      }
      await deployBridge(seed, governanceKey, federationCommitment);
      break;
    }

    case 'lock': {
      const amount = BigInt(args[1] ?? '0');
      const pyanaAddr = Buffer.from(args[2] ?? '', 'hex');
      if (amount === 0n || pyanaAddr.length !== 32) {
        console.error('Usage: deploy.ts lock <amount_stars> <pyana_recipient_hex>');
        process.exit(1);
      }
      await lockForPyana(seed, amount, pyanaAddr);
      break;
    }

    case 'unlock': {
      const attestationFile = args[1];
      if (!attestationFile || !fs.existsSync(attestationFile)) {
        console.error('Usage: deploy.ts unlock <attestation.json>');
        process.exit(1);
      }
      await unlockFromPyana(seed, attestationFile);
      break;
    }

    case 'status': {
      await queryBridgeStatus(seed);
      break;
    }

    case 'rotate': {
      const newCommitment = Buffer.from(args[1] ?? '', 'hex');
      if (newCommitment.length !== 32) {
        console.error('Usage: deploy.ts rotate <new_key_commitment_hex>');
        process.exit(1);
      }
      await rotateFederationKey(seed, newCommitment);
      break;
    }

    case 'pause': {
      await pauseBridge(seed);
      break;
    }

    case 'resume': {
      await resumeBridge(seed);
      break;
    }

    default: {
      console.log(`
Pyana Bridge CLI

Usage:
  npx tsx deploy.ts <command> [args]

Commands:
  deploy                          Deploy fresh bridge contract
  lock <amount> <pyana_addr>      Lock NIGHT tokens for pyana transfer
  unlock <attestation.json>       Unlock NIGHT with federation attestation
  status                          Query bridge state
  rotate <new_commitment>         Rotate federation key (governance)
  pause                           Pause bridge operations (governance)
  resume                          Resume bridge operations (governance)

Environment Variables:
  PYANA_CCLERK_SEED              64-char hex cipherclerk seed (required)
  PYANA_GOVERNANCE_KEY           32-byte governance secret key (hex, for gov ops)
  PYANA_FEDERATION_COMMITMENT    32-byte federation key commitment (hex, for deploy)
      `);
      process.exit(1);
    }
  }
}

main().catch((err) => {
  console.error('Fatal error:', err);
  process.exit(1);
});
