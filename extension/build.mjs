import * as esbuild from 'esbuild';
const watch = process.argv.includes('--watch');
const dev = process.argv.includes('--dev');

const config = {
  entryPoints: [
    'src/background.ts',
    'src/page.ts',
    'src/content.ts',
    'src/popup-script.ts',
  ],
  bundle: true,
  outdir: 'dist',
  format: 'iife',  // Chrome extension scripts need IIFE, not ESM
  target: ['chrome120'],
  // P2-2: sourcemaps only in dev / watch. Production builds expose internal
  // symbol names to devtools observers; never ship to users.
  sourcemap: watch || dev,
};

if (watch) {
  const ctx = await esbuild.context(config);
  await ctx.watch();
  console.log('Watching...');
} else {
  await esbuild.build(config);
  console.log('Built to dist/');
}
