#!/usr/bin/env node
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join, normalize, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const extensionRoot = normalize(join(__dirname, '..'));
const errors = [];
const checked = [];

function rel(path) {
  return relative(extensionRoot, path) || '.';
}

function requireFile(path, source) {
  const fullPath = normalize(join(extensionRoot, path));
  if (!fullPath.startsWith(extensionRoot)) {
    errors.push(`${source}: path escapes extension root: ${path}`);
    return false;
  }
  checked.push(rel(fullPath));
  if (!existsSync(fullPath)) {
    errors.push(`${source}: missing referenced file ${path}`);
    return false;
  }
  return true;
}

function readJson(path) {
  const fullPath = join(extensionRoot, path);
  try {
    return JSON.parse(readFileSync(fullPath, 'utf8'));
  } catch (error) {
    errors.push(`${path}: cannot parse JSON: ${error.message}`);
    return null;
  }
}

function readText(path, source) {
  const fullPath = join(extensionRoot, path);
  try {
    return readFileSync(fullPath, 'utf8');
  } catch (error) {
    errors.push(`${source}: cannot read ${path}: ${error.message}`);
    return '';
  }
}

function manifestDistReferenceToSource(path) {
  const match = /^dist\/(background|content|page|popup-script)\.js$/.exec(path);
  return match ? `src/${match[1]}.ts` : null;
}

function htmlScriptDistReferenceToSource(path) {
  const match = /^dist\/(popup-script)\.js$/.exec(path);
  return match ? `src/${match[1]}.ts` : null;
}

function requirePackagedOrSource(path, source) {
  const fullPath = normalize(join(extensionRoot, path));
  if (fullPath.startsWith(extensionRoot) && existsSync(fullPath)) {
    requireFile(path, source);
    return;
  }

  const sourcePath = manifestDistReferenceToSource(path) ?? htmlScriptDistReferenceToSource(path);
  if (sourcePath) {
    requireFile(sourcePath, `${source} build source for ${path}`);
    return;
  }

  requireFile(path, source);
}

function collectManifestScriptReferences(manifest, manifestPath) {
  if (manifest.background?.service_worker) {
    requirePackagedOrSource(manifest.background.service_worker, `${manifestPath} background.service_worker`);
  }

  for (const [index, contentScript] of (manifest.content_scripts ?? []).entries()) {
    for (const js of contentScript.js ?? []) {
      requirePackagedOrSource(js, `${manifestPath} content_scripts[${index}].js`);
    }
  }

  for (const [index, resourceBlock] of (manifest.web_accessible_resources ?? []).entries()) {
    for (const resource of resourceBlock.resources ?? []) {
      requirePackagedOrSource(resource, `${manifestPath} web_accessible_resources[${index}]`);
    }
  }

  if (manifest.action?.default_popup) {
    requireFile(manifest.action.default_popup, `${manifestPath} action.default_popup`);
    validateHtml(manifest.action.default_popup, `${manifestPath} action.default_popup`);
  }

  if (manifest.options_ui?.page) {
    requireFile(manifest.options_ui.page, `${manifestPath} options_ui.page`);
    validateHtml(manifest.options_ui.page, `${manifestPath} options_ui.page`);
  }
}

function validateHtml(htmlPath, source) {
  const html = readText(htmlPath, source);
  const scriptRegex = /<script\b[^>]*\bsrc=["']([^"']+)["'][^>]*>/gi;
  let match;
  while ((match = scriptRegex.exec(html)) !== null) {
    const scriptPath = match[1];
    if (/^(https?:)?\/\//.test(scriptPath)) continue;
    requirePackagedOrSource(scriptPath, `${source} script tag`);
  }
}

function validateBuildEntrypoints() {
  const buildText = readText('build.mjs', 'build.mjs');
  const expectedEntries = [
    'src/background.ts',
    'src/page.ts',
    'src/content.ts',
    'src/popup-script.ts',
  ];

  for (const entry of expectedEntries) {
    requireFile(entry, 'build.mjs expected entrypoint');
    if (!buildText.includes(`'${entry}'`) && !buildText.includes(`"${entry}"`)) {
      errors.push(`build.mjs: missing expected entrypoint ${entry}`);
    }
  }
}

for (const manifestPath of ['manifest.json', 'manifest-firefox.json']) {
  if (!existsSync(join(extensionRoot, manifestPath))) continue;
  const manifest = readJson(manifestPath);
  if (manifest) collectManifestScriptReferences(manifest, manifestPath);
}

validateBuildEntrypoints();

if (errors.length) {
  console.error('Extension package validation failed:');
  for (const error of errors) console.error(`- ${error}`);
  process.exit(1);
}

const uniqueChecked = [...new Set(checked)].sort();
console.log(`Extension package validation passed (${uniqueChecked.length} paths checked).`);
