#!/usr/bin/env node
/**
 * Migrate old docs/ pages to src/learn/ structure
 */

const fs = require('fs');
const path = require('path');

const DOCS_ROOT = path.join(__dirname, 'docs');
const DEST_ROOT = path.join(__dirname, 'src', 'learn');

const SECTION_MAP = {
  'users': 'Users',
  'operators': 'Operators',
  'developers': 'Developers',
  'architecture': 'Architecture',
};

function extractMainContent(html) {
  // Old docs use <div class="docs-content"> for the content area
  const startIdx = html.indexOf('<div class="docs-content">');
  if (startIdx === -1) {
    console.warn('  No docs-content found, skipping');
    return null;
  }
  const endIdx = html.lastIndexOf('</div>');
  if (endIdx === -1 || endIdx < startIdx) {
    console.warn('  Could not find closing div, skipping');
    return null;
  }
  // Extract content between <div class="docs-content"> and the last </div> before footer
  const contentStart = startIdx + '<div class="docs-content">'.length;
  // Find the </div> that closes docs-content (before footer)
  const footerIdx = html.indexOf('<footer');
  const actualEnd = footerIdx !== -1 ? html.lastIndexOf('</div>', footerIdx) : endIdx;
  let content = html.slice(contentStart, actualEnd).trim();
  // Strip old breadcrumb
  content = content.replace(/<div class="docs-breadcrumb">[\s\S]*?<\/div>\s*/, '');
  return content;
}

function fixPaths(content, section) {
  // Fix relative paths for the new structure
  // Old: ../developers/sdk.html or ./sdk.html
  // New: /learn/developers/sdk.html
  
  // Fix same-section relative links
  content = content.replace(/href="\.\.\/([^/]+)\/([^"]+)"/g, (m, otherSection, file) => {
    return `href="/learn/${otherSection}/${file}"`;
  });
  
  // Fix same-directory relative links
  content = content.replace(/href="\.\/([^"]+)"/g, (m, file) => {
    return `href="/learn/${section}/${file}"`;
  });
  
  // Fix root-level links that used ../index.html
  content = content.replace(/href="\.\.\/\.\.\/index\.html"/g, 'href="/"');
  content = content.replace(/href="\.\.\/index\.html"/g, 'href="/"');
  content = content.replace(/href="\/learn\/index\.html"/g, 'href="/learn.html"');
  
  // Fix paper, demo, docs links
  content = content.replace(/href="\.\.\/\.\.\/paper\.html"/g, 'href="/paper.html"');
  content = content.replace(/href="\.\.\/paper\.html"/g, 'href="/paper.html"');
  content = content.replace(/href="\.\.\/\.\.\/demo\.html"/g, 'href="/demo.html"');
  content = content.replace(/href="\.\.\/demo\.html"/g, 'href="/demo.html"');
  content = content.replace(/href="\.\.\/\.\.\/docs\/index\.html"/g, 'href="/learn.html"');
  content = content.replace(/href="\.\.\/\.\.\/docs\/([^"]+)"/g, 'href="/learn/$1"');
  
  // Fix playground/explorer links
  content = content.replace(/href="\.\.\/\.\.\/playground\/"/g, 'href="/playground/"');
  content = content.replace(/href="\.\.\/\.\.\/explorer\/"/g, 'href="/explorer/"');
  content = content.replace(/href="\.\.\/playground\/"/g, 'href="/playground/"');
  content = content.replace(/href="\.\.\/explorer\/"/g, 'href="/explorer/"');
  
  // Fix assets links
  content = content.replace(/href="\.\.\/\.\.\/assets\//g, 'href="/assets/');
  content = content.replace(/href="\.\.\/assets\//g, 'href="/assets/');
  
  // Fix stylesheets
  content = content.replace(/href="\.\.\/\.\.\/assets\/style\.css"/g, 'href="/assets/style.css"');
  content = content.replace(/href="\.\.\/assets\/style\.css"/g, 'href="/assets/style.css"');
  content = content.replace(/href="\.\.\/style\.css"/g, 'href="/assets/style.css"');
  content = content.replace(/href="style\.css"/g, 'href="/assets/style.css"');
  
  // Fix script src
  content = content.replace(/src="\.\.\/\.\.\//g, 'src="/');
  content = content.replace(/src="\.\.\//g, 'src="/');
  
  return content;
}

function fixStaleContent(content) {
  // Fix effect count inconsistencies
  content = content.replace(/14 effects/g, '24 effects');
  content = content.replace(/14-effect/g, '24-effect');
  content = content.replace(/32 effects/g, '24 effects');
  content = content.replace(/32-effect/g, '24-effect');
  
  // Fix stats
  content = content.replace(/~340k/g, '~395k');
  content = content.replace(/~355k/g, '~395k');
  content = content.replace(/44 crates/g, '46 crates');
  content = content.replace(/41 crates/g, '46 crates');
  content = content.replace(/3900\+ tests/g, '9,700+ tests');
  content = content.replace(/4,046 tests/g, '9,700+ tests');
  
  return content;
}

function addLanguageClasses(content) {
  // Add language classes to bare <pre><code> blocks
  // Heuristic: if it looks like Rust, add language-rust
  content = content.replace(/<pre><code>([\s\S]*?)<\/code><\/pre>/g, (match, code) => {
    if (code.includes('fn ') || code.includes('use ') || code.includes('let ') || code.includes('cargo ')) {
      return `<pre><code class="language-rust">${code}</code></pre>`;
    }
    if (code.includes('function ') || code.includes('const ') || code.includes('import ')) {
      return `<pre><code class="language-javascript">${code}</code></pre>`;
    }
    if (code.includes('$ ') || code.includes('git clone') || code.includes('cargo run')) {
      return `<pre><code class="language-bash">${code}</code></pre>`;
    }
    return match;
  });
  return content;
}

function wrapContent(content, section, fileName) {
  const title = fileName.replace('.html', '').replace(/-/g, ' ').replace(/\b\w/g, l => l.toUpperCase());
  const sectionName = SECTION_MAP[section] || section;
  
  return `<layout src="_layouts/default.html">

<div class="docs-layout">
  <aside class="docs-sidebar">
    <include src="_includes/sidebar-learn.html"></include>
  </aside>
  <main class="docs-content">
    <nav class="docs-breadcrumb">
      <a href="/learn.html">Learn</a>
      <span class="docs-breadcrumb__sep">/</span>
      <a href="/learn/${section}/">${sectionName}</a>
      <span class="docs-breadcrumb__sep">/</span>
      <span>${title}</span>
    </nav>
${content}
  </main>
</div>

</layout>
`;
}

function migrate() {
  for (const section of Object.keys(SECTION_MAP)) {
    const srcDir = path.join(DOCS_ROOT, section);
    if (!fs.existsSync(srcDir)) continue;
    
    const destDir = path.join(DEST_ROOT, section);
    fs.mkdirSync(destDir, { recursive: true });
    
    for (const file of fs.readdirSync(srcDir)) {
      if (!file.endsWith('.html')) continue;
      if (file === 'index.html') continue; // Skip old index pages
      
      const srcPath = path.join(srcDir, file);
      const html = fs.readFileSync(srcPath, 'utf-8');
      
      console.log(`Migrating: docs/${section}/${file}`);
      
      let content = extractMainContent(html);
      if (!content) continue;
      
      content = fixPaths(content, section);
      content = fixStaleContent(content);
      content = addLanguageClasses(content);
      content = wrapContent(content, section, file);
      
      fs.writeFileSync(path.join(destDir, file), content, 'utf-8');
    }
  }
  
  console.log('\nMigration complete.');
}

migrate();
