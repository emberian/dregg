#!/usr/bin/env python3
"""retype_geometry_guards.py -- re-type the literal side of failing `#guard LHS == <nat>` pins.

The rotated geometry is pinned by literals on purpose (re-typing them each flag day is the review).
This does the re-typing mechanically and prints every old -> new pair for that review:

  1. `probe FILE LINE...`   (run where the module's imports are built, e.g. the bb2 warm clone):
     copies FILE, turns each listed `#guard LHS == N` into a tagged `#eval` of LHS, elaborates the
     copy with `lake env lean`, and prints JSON {line: value}.
  2. `apply FILE JSON`      (run in the source tree): rewrites N at each line to the probed value,
     printing `FILE:LINE  LHS  old -> new`.

Only `#guard <expr> == <nat literal>` lines are touched; anything else is left for a person.
"""
import json, re, subprocess, sys, os, tempfile

GUARD = re.compile(r'^(#guard\s+)(.*?)(\s*==\s*)(\d+)(\s*(--.*)?)$')

def probe(path, lines):
    src = open(path).read().split('\n')
    out = list(src)
    for ln in lines:
        m = GUARD.match(src[ln - 1])
        if not m:
            print(f'skip {ln}: not a nat guard: {src[ln-1].strip()}', file=sys.stderr)
            continue
        out[ln - 1] = f'#eval IO.println ("@@G{ln} " ++ toString ({m.group(2)}))'
    d = os.path.dirname(os.path.abspath(path))
    tmp = os.path.join(d, '_retype_probe_' + os.path.basename(path))
    open(tmp, 'w').write('\n'.join(out))
    try:
        r = subprocess.run(['lake', 'env', 'lean', tmp], capture_output=True, text=True,
                           cwd=os.environ.get('LEAN_ROOT', '.'))
    finally:
        os.unlink(tmp)
    vals = {}
    for l in (r.stdout + r.stderr).splitlines():
        m = re.search(r'@@G(\d+) (\d+)', l)
        if m:
            vals[int(m.group(1))] = int(m.group(2))
    print(json.dumps(vals))

def apply(path, vals):
    src = open(path).read().split('\n')
    for ln, v in sorted((int(k), v) for k, v in vals.items()):
        m = GUARD.match(src[ln - 1])
        assert m, (path, ln, src[ln - 1])
        if int(m.group(4)) != v:
            print(f'{path}:{ln}  {m.group(2)}  {m.group(4)} -> {v}')
            src[ln - 1] = m.group(1) + m.group(2) + m.group(3) + str(v) + (m.group(5) or '')
    open(path, 'w').write('\n'.join(src))

def evals(path, after, exprs):
    """Elaborate FILE up to line AFTER and print the value of each EXPR (a literal `def` to re-type)."""
    src = open(path).read().split('\n')[:after]
    for i, e in enumerate(exprs):
        src.append(f'#eval IO.println ("@@E{i} " ++ toString ({e}))')
    d = os.path.dirname(os.path.abspath(path))
    tmp = os.path.join(d, '_retype_probe_' + os.path.basename(path))
    open(tmp, 'w').write('\n'.join(src))
    try:
        r = subprocess.run(['lake', 'env', 'lean', tmp], capture_output=True, text=True)
    finally:
        os.unlink(tmp)
    for l in (r.stdout + r.stderr).splitlines():
        m = re.search(r'@@E(\d+) (.*)', l)
        if m:
            print(f'{exprs[int(m.group(1))]} = {m.group(2)}')

if __name__ == '__main__':
    if sys.argv[1] == 'eval':
        evals(sys.argv[2], int(sys.argv[3]), sys.argv[4:])
    elif sys.argv[1] == 'probe':
        probe(sys.argv[2], [int(x) for x in sys.argv[3:]])
    elif sys.argv[1] == 'apply':
        apply(sys.argv[2], json.loads(sys.argv[3]))
