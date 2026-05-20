// pyana playground — main entry point
// Loads WASM module and wires up the interactive UI.

import init, {
    mint_token,
    generate_root_key,
    attenuate_token,
    verify_token,
    generate_stark_proof,
    verify_stark_proof,
    tamper_stark_proof,
    compute_merkle_root,
    merkle_membership_proof,
    merkle_non_membership_proof,
    evaluate_datalog,
    demonstrate_fold,
} from './pkg/pyana_wasm.js';

// State
let currentRootKey = null; // Uint8Array

// ============================================================================
// Initialization
// ============================================================================

async function main() {
    try {
        await init();
        console.log('[pyana] WASM module loaded');
        setupTabs();
        setupTokens();
        setupStark();
        setupMerkle();
        setupDatalog();
        setupFold();
    } catch (e) {
        console.error('[pyana] Failed to initialize WASM:', e);
        document.body.innerHTML = `<div style="color:#f85149;padding:2rem;font-family:monospace">
            <h2>Failed to load WASM module</h2>
            <pre>${e.message || e}</pre>
            <p>Make sure you've built with: cd wasm && wasm-pack build --target web</p>
        </div>`;
    }
}

// ============================================================================
// Tab navigation
// ============================================================================

function setupTabs() {
    const tabs = document.querySelectorAll('.tab');
    tabs.forEach(tab => {
        tab.addEventListener('click', () => {
            tabs.forEach(t => t.classList.remove('active'));
            document.querySelectorAll('.panel').forEach(p => p.classList.remove('active'));
            tab.classList.add('active');
            document.getElementById(tab.dataset.panel).classList.add('active');
        });
    });
}

// ============================================================================
// Token Playground
// ============================================================================

function setupTokens() {
    document.getElementById('btn-gen-key').addEventListener('click', () => {
        const result = generate_root_key();
        currentRootKey = new Uint8Array(result.key_bytes);
        document.getElementById('mint-key').value = result.key_hex;
    });

    document.getElementById('btn-mint').addEventListener('click', () => {
        const keyHex = document.getElementById('mint-key').value.trim();
        const location = document.getElementById('mint-location').value.trim();

        if (keyHex.length !== 64) {
            showResult('mint-result', 'error', 'Root key must be 64 hex characters (32 bytes)');
            return;
        }

        const keyBytes = hexToBytes(keyHex);
        currentRootKey = keyBytes;

        try {
            const result = mint_token(keyBytes, location || 'pyana.dev');
            showResult('mint-result', 'success',
                `Token minted successfully!\n\nFormat: ${result.format}\nLocation: ${result.location}\n\nToken:\n${result.token}`);
            // Auto-fill attenuate and verify panels
            document.getElementById('att-token').value = result.token;
            document.getElementById('ver-token').value = result.token;
        } catch (e) {
            showResult('mint-result', 'error', `Mint failed: ${e.message || e}`);
        }
    });

    document.getElementById('btn-attenuate').addEventListener('click', () => {
        const tokenStr = document.getElementById('att-token').value.trim();
        const service = document.getElementById('att-service').value.trim();
        const actions = document.getElementById('att-actions').value.trim();
        const expires = parseInt(document.getElementById('att-expires').value) || 0;

        if (!tokenStr || !currentRootKey) {
            showResult('att-result', 'error', 'Mint a token first (need token + root key)');
            return;
        }

        try {
            const result = attenuate_token(tokenStr, currentRootKey, service, actions, BigInt(expires));
            showResult('att-result', 'success',
                `Attenuated!\n\nService: ${result.service}\nActions: ${result.actions}\nExpires: ${result.expires_secs}s\n\nToken:\n${result.token}`);
            // Update verify panel with attenuated token
            document.getElementById('ver-token').value = result.token;
        } catch (e) {
            showResult('att-result', 'error', `Attenuate failed: ${e.message || e}`);
        }
    });

    document.getElementById('btn-verify').addEventListener('click', () => {
        const tokenStr = document.getElementById('ver-token').value.trim();
        const appId = document.getElementById('ver-app').value.trim();
        const action = document.getElementById('ver-action').value.trim();

        if (!tokenStr || !currentRootKey) {
            showResult('ver-result', 'error', 'Mint a token first (need root key for verification)');
            return;
        }

        try {
            const result = verify_token(tokenStr, currentRootKey, appId, action);
            if (result.allowed) {
                showResult('ver-result', 'success',
                    `ALLOWED\n\nPolicy: ${result.policy || 'default'}`);
            } else {
                showResult('ver-result', 'error',
                    `DENIED\n\nReason: ${result.error || 'no matching policy'}`);
            }
        } catch (e) {
            showResult('ver-result', 'error', `Verify error: ${e.message || e}`);
        }
    });
}

// ============================================================================
// STARK Proof Viewer
// ============================================================================

let currentProofJson = null;

function setupStark() {
    document.getElementById('btn-stark-prove').addEventListener('click', () => {
        const leaf = parseInt(document.getElementById('stark-leaf').value) || 42;
        const depth = parseInt(document.getElementById('stark-depth').value) || 4;

        try {
            const result = generate_stark_proof(leaf, depth);
            currentProofJson = result.proof_json;
            document.getElementById('stark-proof-json').value = currentProofJson.slice(0, 500) + '...';

            showResult('stark-result', 'success',
                `Proof generated!\n\nLeaf: ${result.leaf_value}\nRoot: ${result.root_value}\nSize: ${formatBytes(result.proof_size_bytes)}\nTime: ${result.generation_time_ms.toFixed(1)}ms\nTrace rows: ${result.trace_rows}\nFRI layers: ${result.fri_layers}\nQueries: ${result.num_queries}`);

            // Update stats
            document.getElementById('stat-size').textContent = formatBytes(result.proof_size_bytes);
            document.getElementById('stat-prove-time').textContent = result.generation_time_ms.toFixed(1) + 'ms';
            document.getElementById('stat-rows').textContent = result.trace_rows;
            document.getElementById('stat-fri').textContent = result.fri_layers;
            document.getElementById('stat-queries').textContent = result.num_queries;
        } catch (e) {
            showResult('stark-result', 'error', `Prove failed: ${e.message || e}`);
        }
    });

    document.getElementById('btn-stark-verify').addEventListener('click', () => {
        if (!currentProofJson) {
            showResult('stark-verify-result', 'error', 'Generate a proof first');
            return;
        }

        try {
            const result = verify_stark_proof(currentProofJson);
            document.getElementById('stat-verify-time').textContent = result.verification_time_ms.toFixed(1) + 'ms';

            if (result.valid) {
                showResult('stark-verify-result', 'success',
                    `VALID\n\nVerification time: ${result.verification_time_ms.toFixed(1)}ms`);
            } else {
                showResult('stark-verify-result', 'error',
                    `INVALID\n\nError: ${result.error}\nVerification time: ${result.verification_time_ms.toFixed(1)}ms`);
            }
        } catch (e) {
            showResult('stark-verify-result', 'error', `Verify error: ${e.message || e}`);
        }
    });

    document.getElementById('btn-stark-tamper').addEventListener('click', () => {
        if (!currentProofJson) {
            showResult('stark-verify-result', 'error', 'Generate a proof first');
            return;
        }

        try {
            currentProofJson = tamper_stark_proof(currentProofJson);
            document.getElementById('stark-proof-json').value = '[TAMPERED] ' + currentProofJson.slice(0, 480) + '...';
            showResult('stark-verify-result', 'info',
                'Proof tampered! Bits flipped in trace values.\nClick Verify to confirm it fails.');
        } catch (e) {
            showResult('stark-verify-result', 'error', `Tamper error: ${e.message || e}`);
        }
    });
}

// ============================================================================
// Merkle Tree Visualizer
// ============================================================================

function setupMerkle() {
    document.getElementById('btn-merkle-root').addEventListener('click', () => {
        const leavesText = document.getElementById('merkle-leaves').value.trim();
        const leaves = leavesText.split('\n').map(s => s.trim()).filter(s => s.length > 0);

        if (leaves.length === 0) {
            showResult('merkle-root-result', 'error', 'Add at least one leaf');
            return;
        }

        try {
            const result = compute_merkle_root(JSON.stringify(leaves));
            showResult('merkle-root-result', 'success',
                `Root: ${result.root_hex}\n\nLeaves: ${result.num_leaves}\nHash: BLAKE3 4-ary`);
        } catch (e) {
            showResult('merkle-root-result', 'error', `Error: ${e.message || e}`);
        }
    });

    document.getElementById('btn-merkle-member').addEventListener('click', () => {
        const leavesText = document.getElementById('merkle-leaves').value.trim();
        const leaves = leavesText.split('\n').map(s => s.trim()).filter(s => s.length > 0);
        const target = document.getElementById('merkle-check-leaf').value.trim();

        if (!target) {
            showResult('merkle-member-result', 'error', 'Enter a leaf to check');
            return;
        }

        try {
            const result = merkle_membership_proof(JSON.stringify(leaves), target);
            if (result.is_member) {
                showResult('merkle-member-result', 'success',
                    `MEMBER\n\nLeaf: "${target}"\nProof depth: ${result.proof_path_len}\nRoot: ${result.root_hex}`);
            } else {
                showResult('merkle-member-result', 'error',
                    `NOT A MEMBER\n\nLeaf "${target}" is not in the tree.`);
            }
        } catch (e) {
            showResult('merkle-member-result', 'error', `Error: ${e.message || e}`);
        }
    });

    document.getElementById('btn-merkle-absent').addEventListener('click', () => {
        const leavesText = document.getElementById('merkle-leaves').value.trim();
        const leaves = leavesText.split('\n').map(s => s.trim()).filter(s => s.length > 0);
        const target = document.getElementById('merkle-absent-leaf').value.trim();

        if (!target) {
            showResult('merkle-absent-result', 'error', 'Enter a leaf to prove absent');
            return;
        }

        try {
            const result = merkle_non_membership_proof(JSON.stringify(leaves), target);
            if (result.proven_absent) {
                showResult('merkle-absent-result', 'success',
                    `PROVEN ABSENT\n\nLeaf "${target}" is verifiably NOT in the tree.\nRoot: ${result.root_hex}`);
            } else {
                showResult('merkle-absent-result', 'info',
                    `Could not generate non-membership proof.\nThe leaf might actually be in the tree.`);
            }
        } catch (e) {
            showResult('merkle-absent-result', 'error', `Error: ${e.message || e}`);
        }
    });
}

// ============================================================================
// Datalog Evaluator
// ============================================================================

function setupDatalog() {
    document.getElementById('btn-datalog-eval').addEventListener('click', () => {
        const factsStr = document.getElementById('datalog-facts').value.trim();
        const requestStr = document.getElementById('datalog-request').value.trim();

        try {
            const result = evaluate_datalog(factsStr, requestStr);
            const cls = result.conclusion === 'allow' ? 'success' : 'error';
            let text = `Conclusion: ${result.conclusion.toUpperCase()}`;
            if (result.policy_rule_id !== null && result.policy_rule_id !== undefined) {
                text += `\nPolicy Rule ID: ${result.policy_rule_id}`;
            }
            text += `\nDerivation Steps: ${result.num_derivation_steps}`;

            if (result.steps && result.steps.length > 0) {
                text += '\n\nDerivation trace:';
                result.steps.forEach((step, i) => {
                    text += `\n  ${i + 1}. rule[${step.rule_id}] => ${step.derived_predicate_hex.slice(0, 16)}... (${step.num_bindings} bindings)`;
                });
            }

            showResult('datalog-result', cls, text);
        } catch (e) {
            showResult('datalog-result', 'error', `Evaluation error: ${e.message || e}`);
        }
    });
}

// ============================================================================
// Fold Chain
// ============================================================================

function setupFold() {
    document.getElementById('btn-fold').addEventListener('click', () => {
        const factsText = document.getElementById('fold-facts').value.trim();
        const removeText = document.getElementById('fold-remove').value.trim();

        const facts = factsText.split('\n').map(s => s.trim()).filter(s => s.length > 0);
        const remove = removeText.split('\n').map(s => s.trim()).filter(s => s.length > 0);

        if (facts.length === 0) {
            showResult('fold-result', 'error', 'Add at least one fact');
            return;
        }

        try {
            const result = demonstrate_fold(JSON.stringify(facts), JSON.stringify(remove));
            const cls = result.verified ? 'success' : 'error';
            showResult('fold-result', cls,
                `Fold ${result.verified ? 'VERIFIED' : 'FAILED'}\n\nOld root: ${result.old_root_hex.slice(0, 32)}...\nNew root: ${result.new_root_hex.slice(0, 32)}...\n\nTotal facts: ${result.total_facts}\nRemoved: ${result.removed_facts}\nRemaining: ${result.remaining_facts}\n\nThe cryptographic delta proves that capabilities can only be narrowed, never expanded.`);
        } catch (e) {
            showResult('fold-result', 'error', `Fold error: ${e.message || e}`);
        }
    });
}

// ============================================================================
// Utilities
// ============================================================================

function showResult(id, type, text) {
    const el = document.getElementById(id);
    el.className = `result ${type}`;
    el.textContent = text;
}

function hexToBytes(hex) {
    const bytes = new Uint8Array(hex.length / 2);
    for (let i = 0; i < hex.length; i += 2) {
        bytes[i / 2] = parseInt(hex.substr(i, 2), 16);
    }
    return bytes;
}

function formatBytes(bytes) {
    if (bytes < 1024) return bytes + ' B';
    if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KiB';
    return (bytes / (1024 * 1024)).toFixed(1) + ' MiB';
}

// Boot
main();
