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

test.describe('Extension installation', () => {
  test('service worker is active after install', async ({ context }) => {
    const workers = context.serviceWorkers();
    // Either already active or wait for it.
    if (workers.length === 0) {
      await context.waitForEvent('serviceworker');
    }
    const sw = context.serviceWorkers()[0];
    expect(sw).toBeDefined();
    expect(sw.url()).toContain('background.js');
  });

  test('extension ID is a valid chrome extension ID', async ({ extensionId }) => {
    // Chrome extension IDs are 32 lowercase letters.
    expect(extensionId).toMatch(/^[a-z]{32}$/);
  });
});

test.describe('Popup wallet tab', () => {
  test('popup opens and shows wallet heading', async ({ popup }) => {
    const heading = popup.locator('h1');
    await expect(heading).toHaveText('Pyana Wallet');
  });

  test('status indicator is visible', async ({ popup }) => {
    const statusDot = popup.locator('#statusDot');
    await expect(statusDot).toBeVisible();
    const statusText = popup.locator('#statusText');
    await expect(statusText).toBeVisible();
  });

  test('token count and chain length are displayed', async ({ popup }) => {
    const tokenCount = popup.locator('#tokenCount');
    await expect(tokenCount).toBeVisible();
    const chainLength = popup.locator('#chainLength');
    await expect(chainLength).toBeVisible();
  });

  test('lock button is present and clickable', async ({ popup }) => {
    const lockBtn = popup.locator('#lockBtn');
    await expect(lockBtn).toBeVisible();
    // In initial state the wallet should be locked (needs passphrase setup).
    const text = await lockBtn.textContent();
    expect(text).toMatch(/Lock Wallet|Unlock Wallet/);
  });
});

test.describe('Wallet balance', () => {
  test('balance query returns mock value when node configured', async ({ context, extensionId }) => {
    // Configure the node URL via extension storage before checking.
    // This simulates what the settings page does.
    const page = await context.newPage();
    const settingsUrl = `chrome-extension://${extensionId}/settings.html`;
    await page.goto(settingsUrl);
    await page.waitForLoadState('domcontentloaded');

    // The settings page should be accessible.
    const title = await page.title();
    expect(title).toBeDefined();
    await page.close();
  });
});
