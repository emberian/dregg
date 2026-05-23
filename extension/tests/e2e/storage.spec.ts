import { test, expect } from '../fixtures/extension';
import { MockNode } from '../fixtures/node-mock';

let mockNode: MockNode;

test.beforeAll(async () => {
  mockNode = new MockNode({ port: 8420 });
  await mockNode.start();
});

test.afterAll(async () => {
  await mockNode.stop();
});

test.beforeEach(async () => {
  mockNode.reset();
});

test.describe('Storage tab UI', () => {
  test('storage tab shows quota information', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="storage"]').click();
    const bytesStored = popup.locator('#quotaBytesStored');
    await expect(bytesStored).toBeVisible();
    const bytesLimit = popup.locator('#quotaBytesLimit');
    await expect(bytesLimit).toBeVisible();
    const objectCount = popup.locator('#quotaObjectCount');
    await expect(objectCount).toBeVisible();
    const computrons = popup.locator('#quotaComputrons');
    await expect(computrons).toBeVisible();
  });

  test('quota bar is present', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="storage"]').click();
    const barFill = popup.locator('#quotaBarFill');
    await expect(barFill).toBeVisible();
  });

  test('refresh quota button is clickable', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="storage"]').click();
    const refreshBtn = popup.locator('#refreshQuotaBtn');
    await expect(refreshBtn).toBeVisible();
    await expect(refreshBtn).toHaveText('Refresh Quota');
    await refreshBtn.click();
    // After clicking, the quota should attempt to load.
    await popup.waitForTimeout(500);
    // Verify the button is still there (no crash).
    await expect(refreshBtn).toBeVisible();
  });

  test('switching to storage tab triggers quota load', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="storage"]').click();
    await popup.waitForTimeout(500);

    // If the node is configured and reachable, quota values should be populated.
    // If not, they show "--". Either way, the elements should have text.
    const bytesStored = popup.locator('#quotaBytesStored');
    const text = await bytesStored.textContent();
    expect(text).toBeDefined();
    expect(text!.length).toBeGreaterThan(0);
  });
});

test.describe('Storage quota display', () => {
  test('quota displays default values when node unreachable', async ({ popup }) => {
    // Stop the mock node to simulate unreachable state.
    await mockNode.stop();

    await popup.locator('.tab-btn[data-tab="storage"]').click();
    await popup.locator('#refreshQuotaBtn').click();
    await popup.waitForTimeout(1000);

    const bytesStored = popup.locator('#quotaBytesStored');
    const text = await bytesStored.textContent();
    // Should show "--" when node is unreachable.
    expect(text).toBe('--');

    // Restart for other tests.
    await mockNode.start();
  });
});
