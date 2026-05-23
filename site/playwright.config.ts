import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './tests',
  use: {
    baseURL: 'http://localhost:8080',
  },
  webServer: {
    command: 'npx serve . -l 8080',
    port: 8080,
    reuseExistingServer: true,
  },
});
