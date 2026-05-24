# Vendored runtime dependencies

These three files are the entire runtime layer for the pyana site's interactive
visualizers. They are vendored locally rather than loaded from a CDN because
direct `npm install` on the host (and trust in third-party CDNs like esm.sh)
has been flagged as risky in light of ongoing supply-chain attacks against the
npm registry. By isolating the fetch inside a disposable Docker container and
auditing the resulting bytes via SHA-256 we get reproducible, auditable
runtime deps with zero state added to the host machine.

## Files

| File          | Source package                 | Version | Format            |
|---------------|--------------------------------|---------|-------------------|
| `preact.js`   | `preact`                       | 10.22.0 | ESM (`dist/preact.mjs`)       |
| `signals.js`  | `@preact/signals-core`         | 1.8.0   | ESM (`dist/signals-core.mjs`) |
| `htm.js`      | `htm`                          | 3.1.1   | ESM (`dist/htm.module.js`)    |

All three files together are ~17 KB unminified (Preact's `.mjs` is already
minified by the publisher; signals + htm are tiny).

## SHA-256 (as of fetch on 2026-05-23)

```
087942b6f43a74de6a3abb2e0c4e287f03b54b4849cfa34d312402f24aa34a30  preact.js
93284268a0e37da474d3a3fa80cfd7473ba0c00827b8ffd4aab61894bd74d69f  signals.js
ab33dd3f38059b9be4d5f5350128eefb2356639c4e0bbe9d9e8b3ba75847e9e4  htm.js
```

Verify locally with:

```sh
cd site/src/_includes/vendor && sha256sum preact.js signals.js htm.js
# or on macOS without coreutils:
shasum -a 256 preact.js signals.js htm.js
```

If any hash changes you have either re-fetched (intentional bump — also update
this table) or had the file tampered with (investigate).

## How to refresh

Run from the repo root. This uses an ephemeral Docker container running
`node:20-alpine`. **No npm install ever touches the host.**

```sh
docker run --rm -v "$(pwd)/site/src/_includes/vendor:/out" -w /tmp \
  node:20-alpine sh -c '
    set -e
    npm pack --silent \
      preact@10.22.0 \
      @preact/signals-core@1.8.0 \
      htm@3.1.1 >/dev/null
    for f in *.tgz; do
      tar -xzf "$f"
      mv package "pkg_$(basename "$f" .tgz)"
    done
    cp pkg_preact-10.22.0/dist/preact.mjs              /out/preact.js
    cp pkg_preact-signals-core-1.8.0/dist/signals-core.mjs /out/signals.js
    cp pkg_htm-3.1.1/dist/htm.module.js                /out/htm.js
  '
```

Then recompute the SHA-256s and update this README.

To bump a version, change the pinned version in the `npm pack` line, re-run,
and update the table above. Always bump deliberately — never float.

## If Docker is unavailable

Each package can be downloaded directly from the npm CDN tarball endpoint and
extracted with `tar`. The SHA-256s in this README pin the bytes regardless of
how they are retrieved. Example for Preact:

```sh
curl -sLo /tmp/preact.tgz https://registry.npmjs.org/preact/-/preact-10.22.0.tgz
tar -xzf /tmp/preact.tgz -C /tmp
cp /tmp/package/dist/preact.mjs site/src/_includes/vendor/preact.js
```

Then verify the SHA-256 matches the value in this README **before** using the
file.

## Why these three

- **Preact** — 4 KB DOM renderer with a React-compatible API; gives builders
  components + reconciliation without a bundler.
- **@preact/signals-core** — 2 KB fine-grained reactive primitives. Every
  visualizer has a tiny piece of state that several sub-components need to
  react to; without signals we'd hand-roll an event bus per vizzer.
- **htm** — 700 byte tagged-template-literal alternative to JSX, so we never
  need a build step.

Total cost on the wire: ~17 KB unminified, ~9 KB gzipped.
