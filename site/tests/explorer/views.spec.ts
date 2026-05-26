import { test, expect } from '@playwright/test';
import { mockExplorerApi, mockStatus, mockBlocks, mockCells } from '../mocks/api';

test.describe('Explorer Views', () => {
  test.beforeEach(async ({ page }) => {
    await mockExplorerApi(page);
    await page.goto('/explorer/');
    await page.waitForSelector('.ex-nav__item.active');
  });

  test('overview shows stat cards', async ({ page }) => {
    // Overview is the default page
    await expect(page.locator('#page-overview')).toHaveClass(/active/);

    // Stat cards within the overview section should exist
    const statCards = page.locator('#overview-stats .stat-card');
    await expect(statCards).toHaveCount(6);

    // Labels should be present
    await expect(page.locator('.stat-card__label').first()).toBeVisible();
  });

  test('overview summarizes live node state and links object routes', async ({ page }) => {
    await expect(page.locator('#devnet-node-url')).toContainText('devnet.dregg');
    await expect(page.locator('#devnet-fact-height')).toHaveText('42');
    await expect(page.locator('#map-blocks-value')).toHaveText('3 roots');

    await page.click('[data-map-page="blocks"]');
    await expect(page.locator('#page-blocks')).toHaveClass(/active/);
  });

  test('blocks view shows block list with mock data', async ({ page }) => {
    await page.click('[data-page="blocks"]');
    await expect(page.locator('#page-blocks')).toHaveClass(/active/);

    // The blocks table container should be visible
    const blocksTable = page.locator('#blocks-table');
    await expect(blocksTable).toBeVisible();
  });

  test('cells view shows cell list', async ({ page }) => {
    await page.click('[data-page="cells"]');
    await expect(page.locator('#page-cells')).toHaveClass(/active/);

    // Cells table container should be visible
    const cellsTable = page.locator('#cells-table');
    await expect(cellsTable).toBeVisible();
  });

  test('turns view renders its page section', async ({ page }) => {
    await page.click('[data-page="turns"]');
    await expect(page.locator('#page-turns')).toHaveClass(/active/);

    // Header should describe turns
    await expect(page.locator('#page-turns .ex-page__header h2')).toHaveText('Turns');
  });

  test('federation view shows node stats', async ({ page }) => {
    await page.click('[data-page="federation"]');
    await expect(page.locator('#page-federation')).toHaveClass(/active/);

    // Federation stats section should exist
    const fedStats = page.locator('#federation-stats');
    await expect(fedStats).toBeVisible();

    // Should have stat cards
    const statCards = fedStats.locator('.stat-card');
    await expect(statCards).toHaveCount(4);
  });

  test('apps view shows app card grid', async ({ page }) => {
    await page.click('[data-page="apps"]');
    await expect(page.locator('#page-apps')).toHaveClass(/active/);

    // App cards should be visible
    const appCards = page.locator('.app-card');
    await expect(appCards).toHaveCount(7);

    // Cards should have names
    await expect(page.locator('.app-card__name').first()).toBeVisible();
  });

  test('blocklace view has DAG content area', async ({ page }) => {
    await page.click('[data-page="blocklace"]');
    await expect(page.locator('#page-blocklace')).toHaveClass(/active/);

    // The blocklace content div should exist
    await expect(page.locator('.blocklace-content')).toBeVisible();
  });

  test('notes view shows note tree stats', async ({ page }) => {
    await page.click('[data-page="notes"]');
    await expect(page.locator('#page-notes')).toHaveClass(/active/);

    // Stats section
    const noteStats = page.locator('#notes-stats');
    await expect(noteStats).toBeVisible();
    await expect(noteStats.locator('.stat-card')).toHaveCount(4);
  });
});
