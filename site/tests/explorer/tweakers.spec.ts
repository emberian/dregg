import { test, expect } from '@playwright/test';
import { mockExplorerApi } from '../mocks/api';

test.describe('Explorer Tweakers', () => {
  test.beforeEach(async ({ page }) => {
    await mockExplorerApi(page);
    await page.goto('/explorer/');
    await page.waitForSelector('.ex-nav__item.active');
  });

  test('effects page loads the effect builder interface', async ({ page }) => {
    await page.click('[data-page="effects"]');
    await expect(page.locator('#page-effects')).toHaveClass(/active/);

    // The effects page should contain the Effect VM header
    const header = page.locator('#page-effects .ex-page__header');
    await expect(header).toBeVisible();
    await expect(header.locator('h2')).toHaveText('Effect VM');
  });

  test('settings modal opens and closes', async ({ page }) => {
    const modal = page.locator('#settings-modal');
    await expect(modal).toBeHidden();

    // Open settings
    await page.click('#settings-btn');
    await expect(modal).not.toBeHidden();

    // Check form elements are present
    await expect(page.locator('#node-url-input')).toBeVisible();
    await expect(page.locator('#auto-refresh-toggle')).toBeVisible();

    // Cancel closes modal
    await page.click('#settings-cancel');
    await expect(modal).toBeHidden();
  });

  test('settings modal can be closed with Escape', async ({ page }) => {
    const modal = page.locator('#settings-modal');

    await page.click('#settings-btn');
    await expect(modal).not.toBeHidden();

    await page.keyboard.press('Escape');
    await expect(modal).toBeHidden();
  });
});
