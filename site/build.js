#!/usr/bin/env node
/**
 * Pyana Site Build Script
 * Minimal. No frameworks. Just processing.
 */

const fs = require('fs');
const path = require('path');
const { createHighlighter } = require('shiki');
const { transform } = require('lightningcss');

const SRC = path.join(__dirname, 'src');
const DIST = path.join(__dirname, 'dist');

// Copy-through directories (preserved exactly)
const COPY_DIRS = [
  'playground',
  'explorer',
  'sandbox',
  'extension',
  'examples',
  'demos',
  'pkg',
];

// Files copied from root-level site assets
const COPY_FILES = [
  'assets/pyana.pdf',
  'discovery.json',
];

// CI-built files that may need relocation
const COPY_BUILT_FILES = [
  { from: 'paper/pyana.pdf', to: 'assets/pyana.pdf' },
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
  // into <head>. Pages declare it as `<title>Foo — Pyana</title>` anywhere
  // inside the layout slot; the build strips it out and substitutes it into
  // `{{ title }}` in the layout. Pages without a title fall back to "Pyana".
  let pageTitle = 'Pyana';
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

  writeDist('assets/style.css', result.code.toString());
}

function build() {
  console.log('Building Pyana site...\n');

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
