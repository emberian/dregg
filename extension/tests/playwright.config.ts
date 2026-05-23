import { defineConfig } from '@playwright/test';
import path from 'path';

export default defineConfig({
  testDir: './e2e',
  timeout: 30000,
  retries: 0,
  workers: 1, // Extensions require serial execution (single browser context)
  use: {
    headless: false, // Extensions require headed mode
  },
  projects: [{
    name: 'chromium',
    use: {
      launchOptions: {
        args: [
          `--disable-extensions-except=${path.resolve(__dirname, '..')}`,
          `--load-extension=${path.resolve(__dirname, '..')}`,
          '--no-first-run',
          '--disable-gpu',
        ],
      },
    },
  }],
});
