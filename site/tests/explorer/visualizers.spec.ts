import { test, expect } from '@playwright/test';
import { mockExplorerApi } from '../mocks/api';

test.describe('Explorer Visualizers', () => {
  test.beforeEach(async ({ page }) => {
    await mockExplorerApi(page);
    await page.goto('/explorer/');
    await page.waitForSelector('.ex-nav__item.active');
  });

  test('blocklace page has visualization container', async ({ page }) => {
    await page.click('[data-page="blocklace"]');
    await expect(page.locator('#page-blocklace')).toHaveClass(/active/);

    // The page header describes the DAG visualization
    await expect(page.locator('#page-blocklace .ex-page__header h2')).toHaveText('Blocklace');
    await expect(page.locator('#page-blocklace .ex-page__header p')).toContainText('DAG visualization');
  });

  test('effects page has Effect VM content', async ({ page }) => {
    await page.click('[data-page="effects"]');
    await expect(page.locator('#page-effects')).toHaveClass(/active/);

    // Header should describe Effect VM
    await expect(page.locator('#page-effects .ex-page__header h2')).toHaveText('Effect VM');
  });

  test('proofs page renders proof system description', async ({ page }) => {
    await page.click('[data-page="proofs"]');
    await expect(page.locator('#page-proofs')).toHaveClass(/active/);

    await expect(page.locator('#page-proofs .ex-page__header h2')).toHaveText('Proofs');
    await expect(page.locator('#page-proofs .ex-page__header p')).toContainText('STARK');
  });
});
