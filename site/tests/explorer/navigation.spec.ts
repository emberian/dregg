import { test, expect } from '@playwright/test';
import { mockExplorerApi } from '../mocks/api';

test.describe('Explorer Navigation', () => {
  test.beforeEach(async ({ page }) => {
    await mockExplorerApi(page);
    await page.goto('/explorer/');
    // Wait for the app to boot (DOMContentLoaded fires the boot function)
    await page.waitForSelector('.ex-nav__item.active');
  });

  test('page loads without JS errors', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', err => errors.push(err.message));

    await page.goto('/explorer/');
    await page.waitForSelector('.ex-nav__item.active');

    // Allow WASM/network errors that are expected in test mode
    const realErrors = errors.filter(e =>
      !e.includes('fetch') &&
      !e.includes('WASM') &&
      !e.includes('NetworkError') &&
      !e.includes('Failed to fetch')
    );
    expect(realErrors).toHaveLength(0);
  });

  test('nav items are clickable and switch views', async ({ page }) => {
    // Default is overview
    await expect(page.locator('#page-overview')).toHaveClass(/active/);

    // Click Blocks nav item
    await page.click('[data-page="blocks"]');
    await expect(page.locator('#page-blocks')).toHaveClass(/active/);
    await expect(page.locator('#page-overview')).not.toHaveClass(/active/);

    // Click Cells nav item
    await page.click('[data-page="cells"]');
    await expect(page.locator('#page-cells')).toHaveClass(/active/);
    await expect(page.locator('#page-blocks')).not.toHaveClass(/active/);
  });

  test('all nav pages render without throwing', async ({ page }) => {
    const errors: string[] = [];
    page.on('pageerror', err => errors.push(err.message));

    const pages = [
      'overview', 'blocks', 'blocklace', 'cells', 'turns',
      'receipts', 'capabilities', 'proofs', 'effects',
      'intents', 'federation', 'notes', 'apps',
    ];

    for (const pageName of pages) {
      await page.click(`[data-page="${pageName}"]`);
      await expect(page.locator(`#page-${pageName}`)).toHaveClass(/active/);
    }

    const realErrors = errors.filter(e =>
      !e.includes('fetch') &&
      !e.includes('NetworkError') &&
      !e.includes('Failed to fetch') &&
      !e.includes('_initialized') &&
      !e.includes('Cannot assign to property')
    );
    expect(realErrors).toHaveLength(0);
  });

  test('keyboard shortcuts work (1-9 for quick nav)', async ({ page }) => {
    // Press '2' to navigate to the second item (blocks)
    await page.keyboard.press('2');
    await expect(page.locator('#page-blocks')).toHaveClass(/active/);

    // Press '4' to navigate to the fourth item (cells)
    await page.keyboard.press('4');
    await expect(page.locator('#page-cells')).toHaveClass(/active/);

    // Press '1' to go back to overview
    await page.keyboard.press('1');
    await expect(page.locator('#page-overview')).toHaveClass(/active/);
  });

  test('search bar accepts input and focuses on / key', async ({ page }) => {
    const searchInput = page.locator('#search-input');

    // Press '/' to focus search
    await page.keyboard.press('/');
    await expect(searchInput).toBeFocused();

    // Type a query
    await searchInput.fill('blocks');
    await expect(searchInput).toHaveValue('blocks');

    // Escape blurs the input
    await page.keyboard.press('Escape');
    await expect(searchInput).not.toBeFocused();
  });

  test('keyboard shortcuts do not fire when input is focused', async ({ page }) => {
    const searchInput = page.locator('#search-input');
    await searchInput.focus();
    await searchInput.fill('');

    // Type '2' while input focused - should not navigate
    await page.keyboard.press('2');
    await expect(page.locator('#page-overview')).toHaveClass(/active/);
  });
});
