import { test, expect } from '../fixtures/extension';

test.describe('Tab navigation', () => {
  test('all four tabs are present', async ({ popup }) => {
    const tabs = popup.locator('.tab-btn');
    await expect(tabs).toHaveCount(4);

    const tabTexts = await tabs.allTextContents();
    expect(tabTexts).toEqual(['Wallet', 'Caps', 'Directory', 'Storage']);
  });

  test('wallet tab is active by default', async ({ popup }) => {
    const walletTab = popup.locator('.tab-btn[data-tab="wallet"]');
    await expect(walletTab).toHaveClass(/active/);

    const walletContent = popup.locator('#tab-wallet');
    await expect(walletContent).toHaveClass(/active/);
  });

  test('clicking Caps tab switches content', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();

    const capsTab = popup.locator('.tab-btn[data-tab="capabilities"]');
    await expect(capsTab).toHaveClass(/active/);

    const walletTab = popup.locator('.tab-btn[data-tab="wallet"]');
    await expect(walletTab).not.toHaveClass(/active/);

    const capsContent = popup.locator('#tab-capabilities');
    await expect(capsContent).toHaveClass(/active/);

    const walletContent = popup.locator('#tab-wallet');
    await expect(walletContent).not.toHaveClass(/active/);
  });

  test('clicking Directory tab switches content', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="directory"]').click();

    const dirTab = popup.locator('.tab-btn[data-tab="directory"]');
    await expect(dirTab).toHaveClass(/active/);

    const dirContent = popup.locator('#tab-directory');
    await expect(dirContent).toHaveClass(/active/);
  });

  test('clicking Storage tab switches content', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="storage"]').click();

    const storageTab = popup.locator('.tab-btn[data-tab="storage"]');
    await expect(storageTab).toHaveClass(/active/);

    const storageContent = popup.locator('#tab-storage');
    await expect(storageContent).toHaveClass(/active/);
  });

  test('rapid tab switching does not crash', async ({ popup }) => {
    const tabIds = ['wallet', 'capabilities', 'directory', 'storage', 'wallet', 'capabilities'];
    for (const tabId of tabIds) {
      await popup.locator(`.tab-btn[data-tab="${tabId}"]`).click();
    }
    // Verify we ended on capabilities.
    const activeTab = popup.locator('.tab-btn.active');
    await expect(activeTab).toHaveAttribute('data-tab', 'capabilities');
  });
});

test.describe('Popup layout', () => {
  test('popup body has expected dimensions', async ({ popup }) => {
    const body = popup.locator('body');
    const box = await body.boundingBox();
    expect(box).toBeDefined();
    // Width should be 360px as per CSS.
    expect(box!.width).toBe(360);
  });

  test('all action buttons are present in wallet tab', async ({ popup }) => {
    await expect(popup.locator('#lockBtn')).toBeVisible();
    await expect(popup.locator('#backupBtn')).toBeVisible();
    await expect(popup.locator('#intentsBtn')).toBeVisible();
    await expect(popup.locator('#managePermsBtn')).toBeVisible();
    await expect(popup.locator('#settingsBtn')).toBeVisible();
    await expect(popup.locator('#recoverBtn')).toBeVisible();
  });

  test('permissions section is hidden by default', async ({ popup }) => {
    const permsSection = popup.locator('#permissionsSection');
    const display = await permsSection.evaluate(el => (el as HTMLElement).style.display);
    expect(display).toBe('none');
  });

  test('clicking manage permissions toggles section', async ({ popup }) => {
    await popup.locator('#managePermsBtn').click();
    const permsSection = popup.locator('#permissionsSection');
    const display = await permsSection.evaluate(el => (el as HTMLElement).style.display);
    expect(display).toBe('block');

    // Click again to hide.
    await popup.locator('#managePermsBtn').click();
    const display2 = await permsSection.evaluate(el => (el as HTMLElement).style.display);
    expect(display2).toBe('none');
  });
});

test.describe('Error states', () => {
  test('WASM error banner is hidden by default', async ({ popup }) => {
    const wasmError = popup.locator('#wasmError');
    const display = await wasmError.evaluate(el => (el as HTMLElement).style.display);
    expect(display).toBe('none');
  });

  test('recent authorizations shows empty state', async ({ popup }) => {
    const logContainer = popup.locator('#logContainer');
    const emptyMsg = logContainer.locator('.empty');
    await expect(emptyMsg).toHaveText('No recent authorizations');
  });
});
