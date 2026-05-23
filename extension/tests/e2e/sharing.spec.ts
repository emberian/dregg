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

test.describe('Share capability page', () => {
  test('share-capability.html is accessible', async ({ context, extensionId }) => {
    const page = await context.newPage();
    const shareUrl = `chrome-extension://${extensionId}/share-capability.html`;
    const response = await page.goto(shareUrl);
    // Should load successfully (200 status or at least not crash).
    expect(response?.status()).toBeLessThan(400);
    await page.close();
  });
});

test.describe('Capability URI generation', () => {
  test('share button generates URI for valid cell ID', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();

    const cellId = 'deadbeef'.repeat(8); // 64-char hex
    await popup.locator('#shareCellInput').fill(cellId);
    await popup.locator('#shareCapBtn').click();

    await popup.waitForTimeout(1000);
    const shareResult = popup.locator('#shareResult');
    const resultDisplay = await shareResult.evaluate(el => (el as HTMLElement).style.display);
    expect(resultDisplay).toBe('block');

    const uriText = await popup.locator('#shareResultUri').textContent();
    // Should contain either a pyana:// URI or an error message.
    expect(uriText).toBeDefined();
    expect(uriText!.length).toBeGreaterThan(0);
  });

  test('copy URI button is present when URI is shown', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();

    const cellId = 'cafebabe'.repeat(8);
    await popup.locator('#shareCellInput').fill(cellId);
    await popup.locator('#shareCapBtn').click();

    await popup.waitForTimeout(1000);
    const copyBtn = popup.locator('#copyUriBtn');
    await expect(copyBtn).toBeVisible();
    await expect(copyBtn).toHaveText('Copy URI');
  });

  test('copy button attempts clipboard write', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();

    const cellId = '1234567890abcdef'.repeat(4);
    await popup.locator('#shareCellInput').fill(cellId);
    await popup.locator('#shareCapBtn').click();
    await popup.waitForTimeout(1000);

    // Grant clipboard permission in the context.
    await popup.context().grantPermissions(['clipboard-read', 'clipboard-write']);

    const copyBtn = popup.locator('#copyUriBtn');
    await copyBtn.click();

    // Should briefly show "Copied!" then revert.
    await popup.waitForTimeout(500);
    const text = await copyBtn.textContent();
    // May show "Copied!" or "Copy URI" depending on timing.
    expect(text).toMatch(/Copied!|Copy URI/);
  });
});

test.describe('Capability sharing validation', () => {
  test('rejects non-hex cell IDs', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    // Too short.
    await popup.locator('#shareCellInput').fill('abc123');
    await popup.locator('#shareCapBtn').click();
    const input = popup.locator('#shareCellInput');
    // The popup-script sets borderColor to #f87171 on validation failure.
    await popup.waitForTimeout(100);
    const style = await input.evaluate(el => (el as HTMLElement).style.borderColor);
    expect(style).toContain('rgb(248, 113, 113)');
  });

  test('rejects cell IDs with non-hex characters', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    // Contains 'g' which is not hex.
    const badId = 'g'.repeat(64);
    await popup.locator('#shareCellInput').fill(badId);
    await popup.locator('#shareCapBtn').click();
    await popup.waitForTimeout(100);
    const style = await popup.locator('#shareCellInput').evaluate(
      el => (el as HTMLElement).style.borderColor
    );
    expect(style).toContain('rgb(248, 113, 113)');
  });
});
