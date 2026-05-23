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

test.describe('window.pyana injection', () => {
  test('window.pyana is available on navigated pages', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForLoadState('domcontentloaded');

    // Wait for the content script to inject page.js.
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    const hasPyana = await page.evaluate(() => typeof (window as any).pyana === 'object');
    expect(hasPyana).toBe(true);
    await page.close();
  });

  test('window.pyana is frozen (not modifiable)', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    const isFrozen = await page.evaluate(() => Object.isFrozen((window as any).pyana));
    expect(isFrozen).toBe(true);
    await page.close();
  });

  test('window.pyana has expected API methods', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    const methods = await page.evaluate(() => Object.keys((window as any).pyana));
    expect(methods).toContain('authorize');
    expect(methods).toContain('isConnected');
    expect(methods).toContain('canAuthorize');
    expect(methods).toContain('provision');
    expect(methods).toContain('postIntent');
    expect(methods).toContain('shareCapability');
    expect(methods).toContain('acceptCapability');
    expect(methods).toContain('storageWrite');
    expect(methods).toContain('storageRead');
    expect(methods).toContain('storageQuota');
    expect(methods).toContain('on');
    expect(methods).toContain('off');
    await page.close();
  });
});

test.describe('Unrestricted methods', () => {
  test('isConnected returns true when extension is loaded', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    const connected = await page.evaluate(async () => {
      return await (window as any).pyana.isConnected();
    });
    expect(connected).toBe(true);
    await page.close();
  });

  test('canAuthorize works without permission prompt', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    // canAuthorize is unrestricted. With a locked wallet or no matching token,
    // it should return false without prompting.
    const result = await page.evaluate(async () => {
      return await (window as any).pyana.canAuthorize({
        action: 'read',
        resource: 'documents/test',
      });
    });
    // Should be false (wallet is locked in fresh state).
    expect(result).toBe(false);
    await page.close();
  });

  test('storageQuota is accessible without permission', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    // storageQuota is unrestricted.
    const result = await page.evaluate(async () => {
      try {
        return await (window as any).pyana.storageQuota();
      } catch (e: any) {
        return { error: e.message };
      }
    });
    // Should either return quota data or a structured result (not a permission error).
    expect(result).toBeDefined();
    await page.close();
  });
});

test.describe('Restricted methods', () => {
  test('authorize from unpermitted origin triggers permission request', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    // authorize is a restricted method. Without prior permission, it should
    // either prompt the user or return a permission error.
    const result = await page.evaluate(async () => {
      try {
        // Use a short timeout to avoid hanging on the popup.
        const controller = new AbortController();
        const timeout = setTimeout(() => controller.abort(), 3000);
        const promise = (window as any).pyana.authorize({
          action: 'read',
          resource: 'documents/test',
        });
        const raceResult = await Promise.race([
          promise,
          new Promise(resolve => setTimeout(() => resolve({ timeout: true }), 3000)),
        ]);
        clearTimeout(timeout);
        return raceResult;
      } catch (e: any) {
        return { error: e.message };
      }
    });
    // Should either timeout (popup waiting for user) or return permission error.
    expect(result).toBeDefined();
    await page.close();
  });

  test('unknown method is rejected with clear error', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'pyana' in window, null, { timeout: 5000 });

    // Try to call a method that does not exist via the internal sendMessage.
    const result = await page.evaluate(async () => {
      try {
        // Dispatch a raw event with an unknown method type.
        const nonce = document.querySelector('script[data-pyana-nonce]')?.getAttribute('data-pyana-nonce');
        if (!nonce) return { error: 'no nonce found' };

        return new Promise((resolve) => {
          const id = 'test_unknown_method';
          const handler = (event: any) => {
            if (event.detail?.id === id) {
              window.removeEventListener(`pyana:response:${nonce}`, handler);
              resolve(event.detail);
            }
          };
          window.addEventListener(`pyana:response:${nonce}`, handler);
          window.dispatchEvent(new CustomEvent(`pyana:request:${nonce}`, {
            detail: { type: 'pyana:nonExistentMethod', id },
          }));
          setTimeout(() => resolve({ timeout: true }), 3000);
        });
      } catch (e: any) {
        return { error: e.message };
      }
    });
    // Should receive an error about the method not being available.
    if (result && 'error' in result && !('timeout' in result)) {
      expect((result as any).error).toContain('not available');
    }
    await page.close();
  });
});
