import { test, expect } from '@playwright/test';
import { mockPlaygroundDiscovery, blockWebSockets, blockWasm } from '../mocks/api';

test.describe('Playground Blocklace Simulator', () => {
  test.beforeEach(async ({ page }) => {
    await mockPlaygroundDiscovery(page);
    await blockWebSockets(page);
    await blockWasm(page);
    await page.goto('/playground/');
    await page.waitForSelector('.pg-nav__item.active');
    // Navigate to Blocklace Sim section
    await page.click('[data-section="blocklace-sim"]');
    await expect(page.locator('#section-blocklace-sim')).toHaveClass(/active/);
  });

  test('simulator renders controls with configurable node count', async ({ page }) => {
    // Node count input should be present
    const nodeInput = page.locator('#bsim-node-count');
    await expect(nodeInput).toBeVisible();
    await expect(nodeInput).toHaveValue('3');

    // Block rate input
    await expect(page.locator('#bsim-rate')).toBeVisible();

    // Start/Stop/Step/Reset buttons
    await expect(page.locator('#bsim-start')).toBeVisible();
    await expect(page.locator('#bsim-stop')).toBeVisible();
    await expect(page.locator('#bsim-step')).toBeVisible();
    await expect(page.locator('#bsim-reset')).toBeVisible();
  });

  test('step button produces a block in the DAG', async ({ page }) => {
    // Initial state: no blocks
    await expect(page.locator('#bsim-block-count')).toHaveText('0');

    // Step once
    await page.click('#bsim-step');

    // Should have 1 block
    await expect(page.locator('#bsim-block-count')).toHaveText('1');

    // DAG should have SVG content
    const dag = page.locator('#bsim-dag');
    await expect(dag.locator('svg')).toBeVisible();
    // Should have at least one circle node
    await expect(dag.locator('svg circle')).toHaveCount(1);
  });

  test('multiple steps produce multiple blocks', async ({ page }) => {
    await page.click('#bsim-step');
    await page.click('#bsim-step');
    await page.click('#bsim-step');

    await expect(page.locator('#bsim-block-count')).toHaveText('3');

    // DAG should have 3 circle nodes (plus possible finality rings)
    const circles = page.locator('#bsim-dag svg circle');
    const count = await circles.count();
    expect(count).toBeGreaterThanOrEqual(3);
  });

  test('reset clears the simulation', async ({ page }) => {
    // Generate some blocks
    await page.click('#bsim-step');
    await page.click('#bsim-step');
    await expect(page.locator('#bsim-block-count')).toHaveText('2');

    // Reset
    await page.click('#bsim-reset');

    // Stats should be zeroed
    await expect(page.locator('#bsim-block-count')).toHaveText('0');
    await expect(page.locator('#bsim-final-count')).toHaveText('0');
    await expect(page.locator('#bsim-wave')).toHaveText('0');
    await expect(page.locator('#bsim-equivocations')).toHaveText('0');

    // DAG should show empty message
    await expect(page.locator('#bsim-dag .pg-empty')).toBeVisible();
  });

  test('configurable node count changes simulation', async ({ page }) => {
    // Change to 5 nodes
    await page.fill('#bsim-node-count', '5');

    // Step to create a block
    await page.click('#bsim-step');
    await expect(page.locator('#bsim-block-count')).toHaveText('1');

    // SVG should have "Node 4" text (0-indexed, 5th node)
    const dag = page.locator('#bsim-dag svg');
    await expect(dag).toBeVisible();
    // With 5 nodes, there should be 5 node labels
    const nodeLabels = dag.locator('text');
    await expect(nodeLabels).toHaveCount(5);
  });

  test('equivocation checkbox can be toggled', async ({ page }) => {
    const checkbox = page.locator('#bsim-equivocate');
    await expect(checkbox).not.toBeChecked();

    await checkbox.check();
    await expect(checkbox).toBeChecked();
  });

  test('event log shows entries after stepping', async ({ page }) => {
    await page.click('#bsim-step');

    // Log body should have at least one entry
    const logBody = page.locator('#bsim-log-body');
    await expect(logBody.locator('.bsim-log__entry')).toHaveCount(1);

    // Entry should mention block production
    const entry = logBody.locator('.bsim-log__entry').first();
    await expect(entry).toContainText('produced block');
  });

  test('start button begins automatic simulation', async ({ page }) => {
    await page.click('#bsim-start');

    // Start should be disabled, stop enabled
    await expect(page.locator('#bsim-start')).toBeDisabled();
    await expect(page.locator('#bsim-stop')).not.toBeDisabled();

    // Wait a bit for automatic blocks to be produced
    await page.waitForFunction(() => {
      const el = document.getElementById('bsim-block-count');
      return el && parseInt(el.textContent || '0') >= 2;
    }, { timeout: 5000 });

    // Stop the simulation
    await page.click('#bsim-stop');
    await expect(page.locator('#bsim-start')).not.toBeDisabled();
    await expect(page.locator('#bsim-stop')).toBeDisabled();
  });
});
