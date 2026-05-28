import { test, expect } from '@playwright/test';
import { mockPlaygroundDiscovery, blockWebSockets } from '../mocks/api';

// The "blocklace-sim" section is now the real Federation Consensus view: it
// drives the wasm runtime (create_federation / propose_block /
// list_federation_blocks), not a JS Math.random simulator. We intentionally do
// NOT block wasm here — the section needs it. This spec asserts the real
// controls render; the deep behavior (real blocks, real prev_hash chaining,
// real QC) is exercised by the live playwright run in CI against a built pkg.
test.describe('Playground Consensus (real federation)', () => {
  test.beforeEach(async ({ page }) => {
    await mockPlaygroundDiscovery(page);
    await blockWebSockets(page);
    await page.goto('/playground/');
    await page.waitForSelector('.pg-nav__item.active');
    await page.click('[data-scenario="proving"]');
    await page.click('[data-section="blocklace-sim"]');
    await expect(page.locator('#section-blocklace-sim')).toHaveClass(/active/);
  });

  test('renders the real consensus controls', async ({ page }) => {
    await expect(page.locator('#bsim-node-count')).toBeVisible();
    await expect(page.locator('#bsim-propose')).toBeVisible();
    await expect(page.locator('#bsim-auto')).toBeVisible();
    await expect(page.locator('#bsim-reset')).toBeVisible();
    // Real committee stats (not a JS sim's wave/equivocation counters).
    await expect(page.locator('#bsim-quorum')).toBeVisible();
    await expect(page.locator('#bsim-faults')).toBeVisible();
    await expect(page.locator('#bsim-dag')).toBeVisible();
  });

  test('does not present itself as a simulation', async ({ page }) => {
    const text = (await page.locator('#section-blocklace-sim').textContent()) || '';
    // The section copy commits to real wasm, not a Math.random sim.
    expect(text.toLowerCase()).toContain('real');
    expect(text).not.toContain('Math.random');
  });
});
