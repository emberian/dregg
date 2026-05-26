#!/usr/bin/env node
/**
 * Dragon's Egg Site Build Script
 * Minimal. No frameworks. Just processing.
 */

const fs = require('fs');
const path = require('path');
const { createHighlighter } = require('shiki');
const { transform } = require('lightningcss');

const SRC = path.join(__dirname, 'src');
const DIST = path.join(__dirname, 'dist');

// Site root prefix for absolute paths in built HTML/CSS.
//
// GitHub Pages serves this project at https://emberian.github.io/dregg/, so
// templates that write `href="/foo"` must become `href="/dregg/foo"` before
// upload. CI sets BASE_PATH=/dregg; local dev leaves it empty so `npm run
// serve` works at http://localhost:3000/ unchanged. A leading slash is
// enforced; a trailing slash is stripped.
let BASE_PATH = process.env.BASE_PATH || '';
if (BASE_PATH && !BASE_PATH.startsWith('/')) BASE_PATH = '/' + BASE_PATH;
if (BASE_PATH.endsWith('/')) BASE_PATH = BASE_PATH.slice(0, -1);

// Rewrite root-absolute references (href="/x", src="/x", url(/x)) to include
// the BASE_PATH. Matches a single leading slash followed by a non-slash to
// avoid touching protocol-relative URLs ("//cdn...") or empty-root hrefs.
// Skipped when BASE_PATH is empty.
function applyBasePath(content) {
  if (!BASE_PATH) return content;
  // href="/x" or href='/x' or src=... — same shape
  content = content.replace(
    /\b(href|src)=(["'])\/(?!\/)/g,
    (_, attr, q) => `${attr}=${q}${BASE_PATH}/`
  );
  // CSS url(/x), url("/x"), url('/x')
  content = content.replace(
    /url\(\s*(["']?)\/(?!\/)/g,
    (_, q) => `url(${q}${BASE_PATH}/`
  );
  return content;
}

// Copy-through directories (preserved exactly)
const COPY_DIRS = [
  'playground',
  'explorer',
  'sandbox',
  'extension',
  'examples',
  'demos',
  'pkg',
  'old-site',
];

// Copy-through directories that live outside site/ but are served by the
// Studio. starbridge-apps are userspace app surfaces that must work both as
// standalone end-user pages and as Starbridge-embedded devtools targets.
const COPY_EXTERNAL_DIRS = [
  { from: path.join(__dirname, '..', 'starbridge-apps'), to: 'starbridge-apps' },
];

// Files copied from root-level site assets.
// `assets/dregg.pdf` is NOT listed: it is built by CI from paper/dregg.typ
// (see COPY_BUILT_FILES below) and is gitignored. Local builds without typst
// will simply not have a PDF in dist/ — that's fine for dev.
const COPY_FILES = [
  'discovery.json',
];

// CI-built files that may need relocation
const COPY_BUILT_FILES = [
  { from: 'paper/dregg.pdf', to: 'assets/dregg.pdf' },
];

const COPY_VENDOR_FILES = [
  {
    from: path.join(__dirname, 'node_modules', 'split.js', 'dist', 'split.es.js'),
    to: path.join('_includes', 'vendor', 'split.es.js'),
  },
];

let highlighter = null;

async function init() {
  highlighter = await createHighlighter({
    themes: ['github-dark'],
    langs: ['rust', 'typescript', 'javascript', 'bash', 'shell', 'json', 'toml', 'yaml', 'html', 'css'],
  });
}

function ensureDir(p) {
  if (!fs.existsSync(p)) fs.mkdirSync(p, { recursive: true });
}

function readSrc(file) {
  return fs.readFileSync(path.join(SRC, file), 'utf-8');
}

function writeDist(file, content) {
  const p = path.join(DIST, file);
  ensureDir(path.dirname(p));
  fs.writeFileSync(p, content, 'utf-8');
}

function copyDir(src, dst) {
  ensureDir(dst);
  for (const entry of fs.readdirSync(src, { withFileTypes: true })) {
    const s = path.join(src, entry.name);
    const d = path.join(dst, entry.name);
    if (entry.isDirectory()) {
      copyDir(s, d);
    } else if (BASE_PATH && /\.(html|css|js)$/.test(entry.name)) {
      // Rewrite root-absolute references in shipped text files so the
      // copy-through dirs (playground, explorer, old-site, ...) honor BASE_PATH.
      const text = fs.readFileSync(s, 'utf-8');
      fs.writeFileSync(d, applyBasePath(text), 'utf-8');
    } else {
      fs.copyFileSync(s, d);
    }
  }
}

function resolveInclude(currentFile, includePath) {
  if (includePath.startsWith('_')) {
    return path.join(SRC, includePath);
  }
  return path.join(path.dirname(path.join(SRC, currentFile)), includePath);
}

function processIncludes(content, currentFile, depth = 0) {
  if (depth > 10) throw new Error('Include depth exceeded in ' + currentFile);
  return content.replace(/<include\s+src="([^"]+)"\s*\/?>(?:<\/include>)?/g, (_, src) => {
    const p = resolveInclude(currentFile, src);
    if (!fs.existsSync(p)) {
      console.warn(`  Warning: include not found: ${src} (from ${currentFile})`);
      return `<!-- missing include: ${src} -->`;
    }
    let inc = fs.readFileSync(p, 'utf-8');
    inc = processIncludes(inc, path.relative(SRC, p), depth + 1);
    return inc;
  });
}

function processLayouts(content, currentFile) {
  const layoutMatch = content.match(/<layout\s+src="([^"]+)">([\s\S]*?)<\/layout>/);
  if (!layoutMatch) return content;
  const [, layoutPath, inner] = layoutMatch;
  const p = resolveInclude(currentFile, layoutPath);
  if (!fs.existsSync(p)) {
    console.warn(`  Warning: layout not found: ${layoutPath}`);
    return content;
  }
  let layout = fs.readFileSync(p, 'utf-8');
  layout = processIncludes(layout, path.relative(SRC, p));

  // Extract a per-page <title> from the page body so the layout can hoist it
  // into <head>. Pages declare it as `<title>Foo — Dragon's Egg</title>` anywhere
  // inside the layout slot; the build strips it out and substitutes it into
  // `{{ title }}` in the layout. Pages without a title fall back to "Dragon's Egg".
  let pageTitle = 'Dragon\'s Egg';
  let innerWithoutTitle = inner;
  const titleMatch = inner.match(/<title>([\s\S]*?)<\/title>/);
  if (titleMatch) {
    pageTitle = titleMatch[1].trim();
    innerWithoutTitle = inner.replace(titleMatch[0], '');
  }

  return layout
    .replace('{{ title }}', pageTitle)
    .replace('{{ content }}', innerWithoutTitle.trim());
}

function highlightCode(content) {
  return content.replace(/<pre><code\s+class="language-([a-z0-9+-]+)">([\s\S]*?)<\/code><\/pre>/g, (_, lang, code) => {
    const trimmed = code
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&amp;/g, '&');
    try {
      const html = highlighter.codeToHtml(trimmed, {
        lang: lang === 'shell' ? 'bash' : lang,
        theme: 'github-dark',
      });
      // Wrap in our custom class for styling
      return html.replace('<pre class="shiki', '<pre class="shiki code-block');
    } catch (e) {
      console.warn(`  Warning: failed to highlight ${lang}: ${e.message}`);
      return `<pre><code class="language-${lang}">${code}</code></pre>`;
    }
  });
}

function highlightInlineCode(content) {
  // We leave inline code alone; Shiki is for blocks only.
  return content;
}

function processHtml(file) {
  let content = readSrc(file);
  content = processLayouts(content, file);
  content = processIncludes(content, file);
  content = highlightCode(content);
  content = highlightInlineCode(content);
  content = applyBasePath(content);
  return content;
}

function buildCss() {
  const srcFile = path.join(SRC, 'assets', 'style.css');
  const docsFile = path.join(SRC, 'assets', 'docs.css');
  
  // Combine main + docs CSS
  let css = fs.readFileSync(srcFile, 'utf-8');
  if (fs.existsSync(docsFile)) {
    css += '\n' + fs.readFileSync(docsFile, 'utf-8');
  }

  // Add shiki token overrides mapped to our custom properties
  css += '\n' + fs.readFileSync(path.join(SRC, 'assets', 'shiki.css'), 'utf-8');

  const result = transform({
    filename: 'style.css',
    code: Buffer.from(css),
    minify: true,
  });

  writeDist('assets/style.css', applyBasePath(result.code.toString()));
}

function build() {
  console.log('Building Dragon\'s Egg site...\n');

  // Clean dist
  if (fs.existsSync(DIST)) {
    fs.rmSync(DIST, { recursive: true });
  }
  ensureDir(DIST);

  // Copy through directories
  for (const dir of COPY_DIRS) {
    const src = path.join(__dirname, dir);
    const dst = path.join(DIST, dir);
    if (fs.existsSync(src)) {
      console.log(`  Copy: ${dir}/`);
      copyDir(src, dst);
    }
  }

  for (const { from, to } of COPY_EXTERNAL_DIRS) {
    if (fs.existsSync(from)) {
      console.log(`  Copy: ${to}/`);
      copyDir(from, path.join(DIST, to));
    }
  }

  // Copy through files
  for (const file of COPY_FILES) {
    const src = path.join(__dirname, file);
    if (fs.existsSync(src)) {
      console.log(`  Copy: ${file}`);
      const dst = path.join(DIST, file);
      ensureDir(path.dirname(dst));
      fs.copyFileSync(src, dst);
    } else {
      console.log(`  Skip: ${file} (not found)`);
    }
  }

  // Copy CI-built files to their target locations
  for (const { from, to } of COPY_BUILT_FILES) {
    const src = path.join(__dirname, from);
    if (fs.existsSync(src)) {
      console.log(`  Copy: ${from} -> ${to}`);
      const dst = path.join(DIST, to);
      ensureDir(path.dirname(dst));
      fs.copyFileSync(src, dst);
    }
  }

  // Runtime browser dependencies used directly as ESM. The site intentionally
  // remains no-bundler; curated vendor files are copied from package manager
  // installs so versions are still tracked in package-lock.json.
  for (const { from, to } of COPY_VENDOR_FILES) {
    if (fs.existsSync(from)) {
      const dst = path.join(DIST, to);
      ensureDir(path.dirname(dst));
      fs.copyFileSync(from, dst);
      console.log(`  Copy: ${to}`);
    }
  }

  // Process HTML files
  function walk(dir, rel = '') {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const r = path.join(rel, entry.name);
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        if (entry.name.startsWith('_')) continue; // skip _includes, _layouts
        walk(p, r);
      } else if (entry.name.endsWith('.html')) {
        console.log(`  Build: ${r}`);
        const html = processHtml(r);
        writeDist(r, html);
      } else if (entry.name.endsWith('.css')) {
        // CSS handled separately
      } else {
        // Copy other assets
        fs.copyFileSync(p, path.join(DIST, r));
      }
    }
  }

  walk(SRC);

  // Build CSS
  console.log('  Build: assets/style.css');
  buildCss();

  // Copy public _includes assets (design tokens + runtime) to dist/_includes/.
  // The walker skips _-prefixed directories, but these few files need to be
  // reachable at page time via `<link>` / `<script type="module">`.
  const PUBLIC_INCLUDES = [
    'runtime-bootstrap.js',
    'visualizer-base.js',
    'vizzer.css',
  ];
  for (const f of PUBLIC_INCLUDES) {
    const src = path.join(SRC, '_includes', f);
    if (fs.existsSync(src)) {
      const dst = path.join(DIST, '_includes', f);
      ensureDir(path.dirname(dst));
      if (f.endsWith('.css')) {
        // Minify on the way through, matching how other CSS is handled.
        const result = transform({
          filename: f,
          code: fs.readFileSync(src),
          minify: true,
        });
        fs.writeFileSync(dst, result.code);
      } else {
        fs.copyFileSync(src, dst);
      }
      console.log(`  Copy: _includes/${f}`);
    }
  }

  // _includes/studio/ — Studio runtime substrate (URI, runtime impls,
  // inspector custom elements). Copied as a public asset tree because pages
  // import these as ES modules at runtime, not at build time.
  const studioSrc = path.join(SRC, '_includes', 'studio');
  if (fs.existsSync(studioSrc)) {
    const studioDst = path.join(DIST, '_includes', 'studio');
    console.log('  Copy: _includes/studio/');
    copyDir(studioSrc, studioDst);
  }

  // @dregg/sdk (built from sdk-ts/) — for §4.6 wiring into runtime-in-memory
  // and starbridge-apps. Served under /pkg/@dregg/sdk/ so browser ESM imports
  // from studio pages and spikes can `import { DreggRuntime } from '/pkg/@dregg/sdk/index.mjs'`.
  // The dist is CJS+ESM bundle; we copy the ESM entry + CJS for completeness.
  const sdkSrcDir = path.join(__dirname, '..', 'sdk-ts', 'dist');
  if (fs.existsSync(sdkSrcDir)) {
    const sdkDstDir = path.join(DIST, 'pkg', '@dregg', 'sdk');
    ensureDir(sdkDstDir);
    const mjsSrc = path.join(sdkSrcDir, 'index.mjs');
    const jsSrc = path.join(sdkSrcDir, 'index.js');
    if (fs.existsSync(mjsSrc)) {
      fs.copyFileSync(mjsSrc, path.join(sdkDstDir, 'index.mjs'));
      console.log('  Copy: pkg/@dregg/sdk/index.mjs (from sdk-ts/dist for SDK wiring)');
    }
    if (fs.existsSync(jsSrc)) {
      fs.copyFileSync(jsSrc, path.join(sdkDstDir, 'index.js'));
    }
  } else {
    console.log('  Skip: @dregg/sdk (no dist/ yet; run `cd sdk-ts && npm run build`)');
  }

  console.log('\nDone.');
}

async function main() {
  await init();
  build();
}

main().catch(e => {
  console.error(e);
  process.exit(1);
});
