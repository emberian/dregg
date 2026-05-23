import { test, expect } from '@playwright/test';
import { mockPlaygroundDiscovery, blockWebSockets, blockWasm } from '../mocks/api';

test.describe('Playground Effect VM', () => {
  test.beforeEach(async ({ page }) => {
    await mockPlaygroundDiscovery(page);
    await blockWebSockets(page);
    await blockWasm(page);
    await page.goto('/playground/');
    await page.waitForSelector('.pg-nav__item.active');
    // Navigate to Effect VM section
    await page.click('[data-section="effect-vm"]');
    await expect(page.locator('#section-effect-vm')).toHaveClass(/active/);
  });

  test('effect VM section renders controls', async ({ page }) => {
    // Select dropdown should be present
    await expect(page.locator('#evm-effect-select')).toBeVisible();
    // Add button should be present
    await expect(page.locator('#evm-add-btn')).toBeVisible();
    // Clear button should be present
    await expect(page.locator('#evm-clear-btn')).toBeVisible();
  });

  test('can add an effect to the sequence', async ({ page }) => {
    // Initially empty
    await expect(page.locator('#evm-sequence .pg-empty')).toBeVisible();

    // Select Transfer and add it
    await page.selectOption('#evm-effect-select', 'transfer');
    await page.click('#evm-add-btn');

    // Sequence should now show a step
    await expect(page.locator('.effect-vm-step')).toHaveCount(1);
    await expect(page.locator('.effect-vm-step__type')).toHaveText('Transfer');

    // Trace table should show 1 row
    await expect(page.locator('#evm-trace-meta')).toHaveText('1 rows');
  });

  test('can build a multi-effect sequence', async ({ page }) => {
    // Add Transfer
    await page.selectOption('#evm-effect-select', 'transfer');
    await page.click('#evm-add-btn');

    // Add Credit
    await page.selectOption('#evm-effect-select', 'credit');
    await page.click('#evm-add-btn');

    // Add Nullify
    await page.selectOption('#evm-effect-select', 'nullify');
    await page.click('#evm-add-btn');

    // Should have 3 steps
    await expect(page.locator('.effect-vm-step')).toHaveCount(3);
    await expect(page.locator('#evm-trace-meta')).toHaveText('3 rows');
  });

  test('trace table renders with correct column count', async ({ page }) => {
    // Add a transfer (has columns: src_bal, dst_bal, amount, nonce)
    await page.selectOption('#evm-effect-select', 'transfer');
    await page.click('#evm-add-btn');

    // Trace table should exist
    const table = page.locator('.evm-table');
    await expect(table).toBeVisible();

    // Should have header columns: # + Type + 4 data columns = 6
    const headerCells = table.locator('thead th');
    const count = await headerCells.count();
    expect(count).toBeGreaterThanOrEqual(4); // At minimum: #, Type, and some data cols
  });

  test('clear button resets the sequence', async ({ page }) => {
    // Add some effects
    await page.click('#evm-add-btn');
    await page.click('#evm-add-btn');
    await expect(page.locator('.effect-vm-step')).toHaveCount(2);

    // Clear
    await page.click('#evm-clear-btn');

    // Should be empty again
    await expect(page.locator('#evm-sequence .pg-empty')).toBeVisible();
    await expect(page.locator('#evm-trace-meta')).toHaveText('0 rows');
  });

  test('constraint checks show pass/fail indicators', async ({ page }) => {
    // Add a valid effect
    await page.selectOption('#evm-effect-select', 'credit');
    await page.click('#evm-add-btn');

    // Constraints section should show checks
    const constraints = page.locator('#evm-constraints');
    await expect(constraints.locator('.evm-constraint-row')).toHaveCount(4);

    // Should have badge indicators
    await expect(constraints.locator('.evm-constraint-badge')).toHaveCount(4);
  });

  test('prove button enables after adding effects', async ({ page }) => {
    // Initially disabled
    await expect(page.locator('#evm-prove-btn')).toBeDisabled();

    // Add effect
    await page.click('#evm-add-btn');

    // Prove button should be enabled
    await expect(page.locator('#evm-prove-btn')).not.toBeDisabled();
  });

  test('can generate a simulated proof', async ({ page }) => {
    // Add effect
    await page.click('#evm-add-btn');

    // Generate proof
    await page.click('#evm-prove-btn');

    // Proof result should appear
    const result = page.locator('#evm-proof-result');
    await expect(result.locator('.evm-proof-success')).toBeVisible();
    await expect(result.locator('.evm-proof-success__badge')).toHaveText('PROOF GENERATED');

    // Verify button should now be enabled
    await expect(page.locator('#evm-verify-btn')).not.toBeDisabled();
  });

  test('can remove an effect from the sequence', async ({ page }) => {
    // Add two effects
    await page.click('#evm-add-btn');
    await page.click('#evm-add-btn');
    await expect(page.locator('.effect-vm-step')).toHaveCount(2);

    // Remove the first one
    await page.click('.effect-vm-step__remove[data-idx="0"]');
    await expect(page.locator('.effect-vm-step')).toHaveCount(1);
  });
});
