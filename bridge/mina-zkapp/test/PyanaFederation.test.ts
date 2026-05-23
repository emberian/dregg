import {
  Field,
  Mina,
  PrivateKey,
  PublicKey,
  AccountUpdate,
  UInt64,
  Poseidon,
} from 'o1js';
import { PyanaFederation } from '../src/PyanaFederation';

describe('PyanaFederation', () => {
  let deployerKey: PrivateKey;
  let deployerAccount: PublicKey;
  let zkAppKey: PrivateKey;
  let zkAppAddress: PublicKey;
  let zkApp: PyanaFederation;

  // Test constants
  const genesisRoot = Poseidon.hash([Field(42), Field(1337)]);
  const constitutionHash = Poseidon.hash([Field(100), Field(200)]);
  const relayPubKeyHash = Poseidon.hash([Field(999)]);

  beforeAll(async () => {
    // Compile the zkApp (required for proving)
    await PyanaFederation.compile();
  });

  beforeEach(async () => {
    // Set up a fresh local blockchain for each test
    const Local = await Mina.LocalBlockchain({ proofsEnabled: false });
    Mina.setActiveInstance(Local);

    // Get test accounts from the local blockchain
    deployerKey = Local.testAccounts[0].key;
    deployerAccount = Local.testAccounts[0];

    // Generate a new keypair for the zkApp
    zkAppKey = PrivateKey.random();
    zkAppAddress = zkAppKey.toPublicKey();
    zkApp = new PyanaFederation(zkAppAddress);
  });

  async function deployAndInitialize() {
    // Deploy
    const deployTxn = await Mina.transaction(deployerAccount, async () => {
      AccountUpdate.fundNewAccount(deployerAccount);
      await zkApp.deploy({ verificationKey: undefined });
    });
    await deployTxn.sign([deployerKey, zkAppKey]).send();

    // Initialize
    const initTxn = await Mina.transaction(deployerAccount, async () => {
      await zkApp.initialize(genesisRoot, constitutionHash, relayPubKeyHash);
    });
    await initTxn.prove();
    await initTxn.sign([deployerKey]).send();
  }

  // -------------------------------------------------------------------------
  // Deployment and initialization
  // -------------------------------------------------------------------------

  describe('deployment', () => {
    it('should deploy successfully', async () => {
      const txn = await Mina.transaction(deployerAccount, async () => {
        AccountUpdate.fundNewAccount(deployerAccount);
        await zkApp.deploy({ verificationKey: undefined });
      });
      await txn.sign([deployerKey, zkAppKey]).send();

      // State should be zeroed before initialization
      const root = zkApp.stateRoot.get();
      expect(root).toEqual(Field(0));
    });

    it('should initialize with genesis state', async () => {
      await deployAndInitialize();

      expect(zkApp.stateRoot.get()).toEqual(genesisRoot);
      expect(zkApp.provenHeight.get()).toEqual(Field(1));
      expect(zkApp.federationId.get()).toEqual(constitutionHash);
      expect(zkApp.totalLocked.get()).toEqual(Field(0));
      expect(zkApp.relayAuthority.get()).toEqual(relayPubKeyHash);
    });

    it('should reject double initialization', async () => {
      await deployAndInitialize();

      // Try to initialize again
      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.initialize(
            Field(9999),
            Field(8888),
            Field(7777),
          );
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // State advancement
  // -------------------------------------------------------------------------

  describe('advanceState', () => {
    it('should advance state with valid transition', async () => {
      await deployAndInitialize();

      const newRoot = Poseidon.hash([Field(1), Field(2), Field(3)]);
      const newHeight = Field(2);
      const effectsHash = Poseidon.hash([Field(10)]);

      const txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.advanceState(genesisRoot, newRoot, newHeight, effectsHash);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Verify state updated
      expect(zkApp.stateRoot.get()).toEqual(newRoot);
      expect(zkApp.provenHeight.get()).toEqual(newHeight);
    });

    it('should reject state advance with wrong old root', async () => {
      await deployAndInitialize();

      const wrongOldRoot = Field(12345);
      const newRoot = Poseidon.hash([Field(5)]);

      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.advanceState(wrongOldRoot, newRoot, Field(2), Field(1));
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });

    it('should reject state advance with non-increasing height', async () => {
      await deployAndInitialize();

      const newRoot = Poseidon.hash([Field(7)]);

      // Height 0 is less than current height 1
      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.advanceState(genesisRoot, newRoot, Field(0), Field(1));
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });

    it('should reject no-op transition (same root)', async () => {
      await deployAndInitialize();

      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.advanceState(genesisRoot, genesisRoot, Field(2), Field(1));
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });

    it('should chain multiple state advances', async () => {
      await deployAndInitialize();

      const root2 = Poseidon.hash([Field(2)]);
      const root3 = Poseidon.hash([Field(3)]);
      const root4 = Poseidon.hash([Field(4)]);

      // Advance 1 -> 2
      let txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.advanceState(genesisRoot, root2, Field(2), Field(10));
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Advance 2 -> 3
      txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.advanceState(root2, root3, Field(3), Field(20));
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Advance 3 -> 4
      txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.advanceState(root3, root4, Field(4), Field(30));
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      expect(zkApp.stateRoot.get()).toEqual(root4);
      expect(zkApp.provenHeight.get()).toEqual(Field(4));
    });
  });

  // -------------------------------------------------------------------------
  // Deposits
  // -------------------------------------------------------------------------

  describe('deposit', () => {
    it('should accept a valid deposit', async () => {
      await deployAndInitialize();

      const amount = UInt64.from(1_000_000_000); // 1 MINA
      const noteCommitment = Poseidon.hash([Field(42), Field(100)]);

      const txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.deposit(amount, noteCommitment);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Total locked should increase
      expect(zkApp.totalLocked.get()).toEqual(amount.value);
    });

    it('should accumulate multiple deposits', async () => {
      await deployAndInitialize();

      const amount1 = UInt64.from(1_000_000_000);
      const amount2 = UInt64.from(2_000_000_000);
      const note1 = Poseidon.hash([Field(1)]);
      const note2 = Poseidon.hash([Field(2)]);

      let txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.deposit(amount1, note1);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.deposit(amount2, note2);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      const expected = amount1.add(amount2);
      expect(zkApp.totalLocked.get()).toEqual(expected.value);
    });

    it('should reject zero amount deposit', async () => {
      await deployAndInitialize();

      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.deposit(UInt64.from(0), Field(123));
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });

    it('should reject deposit with zero note commitment', async () => {
      await deployAndInitialize();

      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.deposit(UInt64.from(100), Field(0));
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // Withdrawals
  // -------------------------------------------------------------------------

  describe('withdraw', () => {
    it('should process a valid withdrawal', async () => {
      await deployAndInitialize();

      // First deposit
      const depositAmount = UInt64.from(5_000_000_000);
      const noteCommitment = Poseidon.hash([Field(50)]);

      let txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.deposit(depositAmount, noteCommitment);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Then withdraw a portion
      const withdrawAmount = UInt64.from(2_000_000_000);
      const nullifier = Poseidon.hash([Field(999)]);
      const recipient = PrivateKey.random().toPublicKey();

      txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.withdraw(
          withdrawAmount,
          nullifier,
          genesisRoot, // state root at spend
          recipient,
        );
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Total locked should decrease
      const expectedRemaining = depositAmount.sub(withdrawAmount);
      expect(zkApp.totalLocked.get()).toEqual(expectedRemaining.value);
    });

    it('should reject withdrawal exceeding locked balance', async () => {
      await deployAndInitialize();

      // Deposit 1 MINA
      const depositAmount = UInt64.from(1_000_000_000);
      let txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.deposit(depositAmount, Poseidon.hash([Field(1)]));
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      // Try to withdraw 2 MINA
      const withdrawAmount = UInt64.from(2_000_000_000);
      const recipient = PrivateKey.random().toPublicKey();

      await expect(async () => {
        txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.withdraw(
            withdrawAmount,
            Field(123),
            genesisRoot,
            recipient,
          );
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });

    it('should reject withdrawal with zero nullifier', async () => {
      await deployAndInitialize();

      // Deposit first
      let txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.deposit(UInt64.from(1_000_000_000), Poseidon.hash([Field(1)]));
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();

      const recipient = PrivateKey.random().toPublicKey();

      await expect(async () => {
        txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.withdraw(
            UInt64.from(500_000_000),
            Field(0), // zero nullifier
            genesisRoot,
            recipient,
          );
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // Membership verification
  // -------------------------------------------------------------------------

  describe('verifyMembership', () => {
    it('should verify membership against current root', async () => {
      await deployAndInitialize();

      const cellId = Field(42);
      const leafHash = Poseidon.hash([Field(42), Field(100)]);

      // Passing the correct current root should succeed
      const txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.verifyMembership(cellId, leafHash, genesisRoot);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();
    });

    it('should reject membership proof against wrong root', async () => {
      await deployAndInitialize();

      const wrongRoot = Field(99999);

      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.verifyMembership(Field(1), Field(2), wrongRoot);
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });
  });

  // -------------------------------------------------------------------------
  // Capability verification
  // -------------------------------------------------------------------------

  describe('verifyCapability', () => {
    it('should verify a capability attestation', async () => {
      await deployAndInitialize();

      const capHash = Poseidon.hash([Field(1), Field(2), Field(3)]);
      const holder = PrivateKey.random().toPublicKey();

      const txn = await Mina.transaction(deployerAccount, async () => {
        await zkApp.verifyCapability(capHash, holder, genesisRoot);
      });
      await txn.prove();
      await txn.sign([deployerKey]).send();
    });

    it('should reject capability against wrong state root', async () => {
      await deployAndInitialize();

      const capHash = Poseidon.hash([Field(1)]);
      const holder = PrivateKey.random().toPublicKey();
      const wrongRoot = Field(7777);

      await expect(async () => {
        const txn = await Mina.transaction(deployerAccount, async () => {
          await zkApp.verifyCapability(capHash, holder, wrongRoot);
        });
        await txn.prove();
        await txn.sign([deployerKey]).send();
      }).rejects.toThrow();
    });
  });
});
