import { test as base, chromium, type BrowserContext, type Page } from '@playwright/test';
import path from 'path';

export type ExtensionFixtures = {
  context: BrowserContext;
  extensionId: string;
  popup: Page;
  backgroundPage: { url: string };
};

export const test = base.extend<ExtensionFixtures>({
  // Launch a persistent context with the extension loaded.
  context: async ({}, use) => {
    const pathToExtension = path.resolve(__dirname, '..', '..');
    const context = await chromium.launchPersistentContext('', {
      headless: false,
      args: [
        `--disable-extensions-except=${pathToExtension}`,
        `--load-extension=${pathToExtension}`,
        '--no-first-run',
        '--disable-gpu',
      ],
    });
    await use(context);
    await context.close();
  },

  // Extract the extension ID from the service worker URL.
  extensionId: async ({ context }, use) => {
    let [background] = context.serviceWorkers();
    if (!background) {
      background = await context.waitForEvent('serviceworker');
    }
    const extensionId = background.url().split('/')[2];
    await use(extensionId);
  },

  // Open the popup page directly by navigating to its chrome-extension:// URL.
  popup: async ({ context, extensionId }, use) => {
    const popupUrl = `chrome-extension://${extensionId}/popup.html`;
    const page = await context.newPage();
    await page.goto(popupUrl);
    await page.waitForLoadState('domcontentloaded');
    await use(page);
    await page.close();
  },

  // Expose background service worker info.
  backgroundPage: async ({ context }, use) => {
    let [background] = context.serviceWorkers();
    if (!background) {
      background = await context.waitForEvent('serviceworker');
    }
    await use({ url: background.url() });
  },
});

export { expect } from '@playwright/test';
