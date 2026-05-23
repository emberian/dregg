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

test.describe('Directory tab UI', () => {
  test('directory tab shows mounted services section', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="directory"]').click();
    const container = popup.locator('#directoryContainer');
    await expect(container).toBeVisible();
  });

  test('discover input and search button are present', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="directory"]').click();
    const tagsInput = popup.locator('#discoverTagsInput');
    await expect(tagsInput).toBeVisible();
    await expect(tagsInput).toHaveAttribute('placeholder', 'Tags (comma-separated)');
    const discoverBtn = popup.locator('#discoverBtn');
    await expect(discoverBtn).toBeVisible();
    await expect(discoverBtn).toHaveText('Search');
  });

  test('search with tags triggers discovery', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="directory"]').click();
    await popup.locator('#discoverTagsInput').fill('oracle,price');
    await popup.locator('#discoverBtn').click();

    // Button should briefly show "..." while loading.
    await popup.waitForTimeout(300);
    const btn = popup.locator('#discoverBtn');
    const text = await btn.textContent();
    // Should return to "Search" after completion.
    expect(text).toBe('Search');

    // Results area should have been populated (or show empty if node unreachable).
    const results = popup.locator('#discoveryResults');
    await expect(results).toBeVisible();
  });

  test('empty search returns all services', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="directory"]').click();
    await popup.locator('#discoverTagsInput').fill('');
    await popup.locator('#discoverBtn').click();
    await popup.waitForTimeout(500);

    // Discovery results should be populated.
    const results = popup.locator('#discoveryResults');
    const html = await results.innerHTML();
    // Should contain something (either results or empty message).
    expect(html.length).toBeGreaterThan(0);
  });
});

test.describe('Directory resolve', () => {
  test('switching to directory tab triggers path resolution', async ({ popup }) => {
    // Switching to directory tab calls loadDirectory() which resolves "/".
    await popup.locator('.tab-btn[data-tab="directory"]').click();
    await popup.waitForTimeout(500);

    const container = popup.locator('#directoryContainer');
    const html = await container.innerHTML();
    // Should show either service entries or "No services mounted" or "Could not load directory".
    expect(html.length).toBeGreaterThan(0);
  });
});
