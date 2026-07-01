// Bundle the pure TS modules under test (src/explain.ts, src/sse.ts) to ESM
// so `node --test test/` can import them without a TS runtime.
import * as esbuild from 'esbuild';

await esbuild.build({
  entryPoints: ['src/explain.ts', 'src/sse.ts', 'src/onboarding.ts', 'src/login.ts'],
  outdir: 'test/.build',
  format: 'esm',
  bundle: true,
  outExtension: { '.js': '.mjs' },
});
console.log('Test modules built to test/.build/');
