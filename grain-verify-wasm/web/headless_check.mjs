// Headless end-to-end check of the ACTUAL wasm artifact (not the native core):
// import the wasm-bindgen glue, init from the compiled bytes, and run
// verify_attestation over the sample fixtures + their pins. Asserts the wasm
// verdict matches what native grain-verify says (PASS on genuine, FAIL on
// tampered, PASS on renter-anchored). Run: `node web/headless_check.mjs`.
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const pkg = join(here, "..", "pkg");
const fix = join(here, "fixtures");

const mod = await import(join(pkg, "grain_verify_wasm.js"));
const wasmBytes = readFileSync(join(pkg, "grain_verify_wasm_bg.wasm"));
mod.initSync({ module: wasmBytes });

const readf = (n) => readFileSync(join(fix, n), "utf8");
const pins = JSON.parse(readf("pins.json"));

let failures = 0;
function expect(label, cond, detail) {
  if (cond) {
    console.log(`  ok   ${label}`);
  } else {
    console.log(`  FAIL ${label} :: ${detail}`);
    failures++;
  }
}

// genuine → PASS
{
  const r = mod.verify_attestation(readf("pass.json"), pins.pass_and_tampered_signer);
  expect("genuine attestation PASSES", r.ok === true, JSON.stringify(r));
  expect("  actions re-witnessed", r.actions === 5, `actions=${r.actions}`);
  expect("  consumed==5, budget==25", r.consumed === 5 && r.budget === 25,
    `consumed=${r.consumed} budget=${r.budget}`);
}

// tampered → FAIL
{
  const r = mod.verify_attestation(readf("tampered.json"), pins.pass_and_tampered_signer);
  expect("tampered attestation FAILS", r.ok === false, JSON.stringify(r));
  expect("  error mentions signature", /signature/i.test(r.error || ""), r.error);
}

// wrong pinned signer → FAIL
{
  const r = mod.verify_attestation(readf("pass.json"), "ab".repeat(32));
  expect("wrong pinned signer REFUSED", r.ok === false, JSON.stringify(r));
  expect("  error mentions authority", /authority/i.test(r.error || ""), r.error);
}

// renter-anchored → PASS
{
  const p = pins.renter;
  const r = mod.verify_attestation(readf("renter.json"), p.signer, p.renter_pubkey, p.genesis_nonce);
  expect("renter-anchored attestation PASSES", r.ok === true, JSON.stringify(r));
  expect("  renter_anchored flag set", r.renter_anchored === true, JSON.stringify(r));
  expect("  R1 teeth verified", r.anti_rewrite_anti_truncation === true, JSON.stringify(r));
}

// renter-anchored with WRONG nonce → FAIL
{
  const p = pins.renter;
  const r = mod.verify_attestation(readf("renter.json"), p.signer, p.renter_pubkey, "99".repeat(32));
  expect("renter anchor with wrong nonce FAILS", r.ok === false, JSON.stringify(r));
}

// R2 (kernel-linked) NEGATIVE: the samples are UNMINTED sessions — against any
// manifest the R2 tooth must refuse (no receipt carries a kernel-turn link).
{
  const r = mod.verify_attestation(readf("pass.json"), pins.pass_and_tampered_signer,
    undefined, undefined, "[]");
  expect("R2 mode refuses an unminted session", r.ok === false, JSON.stringify(r));
  expect("  error names the R2 tooth", /R2/.test(r.error || ""), r.error);
  expect("  mode names the rungs", r.mode === "kernel-linked (R0+R2)", r.mode);
}

// R2 malformed manifest → a clear input error, not a panic
{
  const r = mod.verify_attestation(readf("pass.json"), pins.pass_and_tampered_signer,
    undefined, undefined, "{nope");
  expect("R2 malformed manifest is a clear error", r.ok === false && /manifest/.test(r.error || ""),
    JSON.stringify(r));
}

// the honest boundary is surfaced
expect("whole_history_gap() non-empty", (mod.whole_history_gap() || "").length > 50, "empty");
expect("the gap names the landed rungs + the remaining ask",
  /R2/.test(mod.whole_history_gap()) && /REMAINING BREADSTUFFS ASK/.test(mod.whole_history_gap()),
  mod.whole_history_gap().slice(0, 120));

console.log(failures === 0 ? "\nALL WASM CHECKS PASSED" : `\n${failures} WASM CHECK(S) FAILED`);
process.exit(failures === 0 ? 0 : 1);
