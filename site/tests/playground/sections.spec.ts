import { test, expect } from '@playwright/test';
import { mockPlaygroundDiscovery, blockWebSockets, blockWasm } from '../mocks/api';

test.describe('Playground Sections', () => {
  test.beforeEach(async ({ page }) => {
    await mockPlaygroundDiscovery(page);
    await blockWebSockets(page);
    await blockWasm(page);
    await page.goto('/playground/');
    await page.waitForSelector('.pg-nav__item.active');
  });

  test('page loads without critical JS errors', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', err => errors.push(err.message));

    await page.goto('/playground/');
    await page.waitForSelector('.pg-nav__item.active');

    // Filter expected errors (WASM load failure, network)
    const realErrors = errors.filter(e =>
      !e.includes('WASM') &&
      !e.includes('fetch') &&
      !e.includes('NetworkError') &&
      !e.includes('Failed to fetch') &&
      !e.includes('WebSocket')
    );
    expect(realErrors).toHaveLength(0);
  });

  test('overview section is active by default', async ({ page }) => {
    await expect(page.locator('#section-overview')).toHaveClass(/active/);
  });

  test('nav items switch sections on click', async ({ page }) => {
    // Click tokens nav
    await page.click('[data-section="tokens"]');
    await expect(page.locator('#section-tokens')).toHaveClass(/active/);
    await expect(page.locator('#section-overview')).not.toHaveClass(/active/);

    // Click proofs nav
    await page.click('[data-section="proofs"]');
    await expect(page.locator('#section-proofs')).toHaveClass(/active/);
    await expect(page.locator('#section-tokens')).not.toHaveClass(/active/);
  });

  test('each major section loads without error', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', err => errors.push(err.message));

    const sections = [
      'overview', 'tokens', 'proofs', 'merkle', 'datalog',
      'notes', 'capabilities', 'crossfed', 'sovereign',
      'bearer', 'factories', 'effect-vm', 'blocklace-sim',
    ];

    for (const section of sections) {
      await page.click(`[data-section="${section}"]`);
      await expect(page.locator(`#section-${section}`)).toHaveClass(/active/);
    }

    const realErrors = errors.filter(e =>
      !e.includes('WASM') &&
      !e.includes('fetch') &&
      !e.includes('NetworkError') &&
      !e.includes('Failed to fetch') &&
      !e.includes('WebSocket')
    );
    expect(realErrors).toHaveLength(0);
  });

  test('WASM status shows error state when WASM unavailable', async ({ page }) => {
    // With WASM blocked, the status indicator should show error state
    const wasmStatus = page.locator('#wasm-status');
    // Wait for WASM loading to complete (error path)
    await page.waitForFunction(() => {
      const el = document.getElementById('wasm-status');
      return el && el.textContent !== 'loading...';
    }, { timeout: 5000 });

    await expect(wasmStatus).toHaveText('wasm error');
  });

  test('clicking nav updates URL hash', async ({ page }) => {
    await page.click('[data-section="merkle"]');
    await expect(page.locator('#section-merkle')).toHaveClass(/active/);

    // URL hash should reflect the navigated section
    const url = page.url();
    expect(url).toContain('#merkle');
  });

  test('system state panel shows initial values', async ({ page }) => {
    // State panel should be visible with initial zeroed state
    await expect(page.locator('#state-token-count')).toHaveText('0');
    await expect(page.locator('#state-nullifier-count')).toHaveText('0');
    await expect(page.locator('#state-receipt-count')).toHaveText('0');
    await expect(page.locator('#state-proof-count')).toHaveText('0');
  });

  test('reset button clears state', async ({ page }) => {
    // Click reset
    await page.click('#btn-reset-state');

    // All counters should be zero
    await expect(page.locator('#state-token-count')).toHaveText('0');
    await expect(page.locator('#state-nullifier-count')).toHaveText('0');
    await expect(page.locator('#state-receipt-count')).toHaveText('0');
    await expect(page.locator('#state-proof-count')).toHaveText('0');
  });
});
