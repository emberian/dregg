#!/usr/bin/env python3
"""gen_rotated_geometry.py -- regenerate the LITERAL rotated-block walks from the one extent.

The rotated block's geometry has one source, `rotatedNumPreLimbs` in
metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean. Several proofs need the block's chained
absorption as a literal list (so every positional fact is `rfl` and `omega` never has to unfold a
`def`): `preLimbsAt` and `rotV3SitesAt` in EffectVmEmitRotationV3.lean, and `rotV3WideSpecs`, its
`rcases` admission walk and the `rotV3WidePin` chain in EffectVmEmitRotationWide.lean. A flag day
used to re-type those by hand. This script rewrites them in place from N, so a bump is: change N,
run this, build.

Usage: scripts/gen_rotated_geometry.py [--check]   (--check: exit 1 if any file would change)
"""
import re, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EMIT = os.path.join(ROOT, 'metatheory/Dregg2/Circuit/Emit')

def extent():
    s = open(os.path.join(EMIT, 'RotatedLayout.lean')).read()
    m = re.search(r'^def rotatedNumPreLimbs : Nat := (\d+)$', s, re.M)
    n = int(m.group(1))
    assert (n - 4) % 3 == 0, f'{n} is not body-aligned'
    return n

def sub1(s, pat, repl, what):
    new, k = re.subn(pat, lambda _m: repl, s, count=1, flags=re.S | re.M)
    if k != 1:
        sys.exit(f'gen_rotated_geometry: could not find {what}')
    return new

def v3(n, s):
    # preLimbsAt: six per line
    cells = [f'a (base + {i})' for i in range(n)]
    lines = []
    for i in range(0, n, 6):
        lines.append(('  [ ' if i == 0 else '  , ') + ', '.join(cells[i:i + 6]))
    body = '\n'.join(lines) + ' ]'
    s = sub1(s, r'(?<=def preLimbsAt \(base : Nat\) \(a : Assignment\) : List ℤ :=\n).*?\]\n(?=\ntheorem preLimbsAt_length)',
             body + '\n', 'preLimbsAt')
    s = sub1(s, r'(?<=\(preLimbsAt base a\)\.length = )\d+(?= := rfl)', str(n), 'preLimbsAt_length')
    # rotV3SitesAt: head, bodies, then the iroot onto state_commit
    iroot, sc, cb = n, n + 1, n + 2
    nb = (n - 4) // 3
    sites = [f'⟨base + {cb}, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩']
    for k in range(nb):
        l = 4 + 3 * k
        sites.append(f'⟨base + {cb + k + 1}, [.col (base + {cb + k}), .col (base + {l}), '
                     f'.col (base + {l + 1}), .col (base + {l + 2})], 4⟩')
    sites.append(f'⟨base + {sc}, [.col (base + {cb + nb}), .col (base + {iroot})], 2⟩')
    body = '\n'.join(('  [ ' if i == 0 else '  , ') + x for i, x in enumerate(sites)) + ' ]\n'
    s = sub1(s, r'(?<=def rotV3SitesAt \(base : Nat\) : List VmHashSite :=\n).*?\]\n(?=\n)', body, 'rotV3SitesAt')
    # the digest-chained byte-identity twin at base 0 (`.digest (k-1)` instead of `.col carrier`)
    sites = [f'⟨{cb}, [.col 0, .col 1, .col 2, .col 3], 4⟩']
    for k in range(nb):
        l = 4 + 3 * k
        sites.append(f'⟨{cb + k + 1}, [.digest {k}, .col {l}, .col {l + 1}, .col {l + 2}], 4⟩')
    sites.append(f'⟨{sc}, [.digest {nb}, .col {iroot}], 2⟩')
    body = '\n'.join(('  [ ' if i == 0 else '  , ') + x for i, x in enumerate(sites)) + ' ]\n'
    s = sub1(s, r'(?<=private def rotV3SitesDigestAt0 : List VmHashSite :=\n).*?\]\n(?=\n)', body, 'rotV3SitesDigestAt0')
    # the narrow pin's literal walk (`rotV3SitesAt_pin`)
    hs = [f'  show env.loc (base + {sc}) = wireCommitR hash (preLimbsAt base env.loc) (env.loc (base + {iroot}))']
    def site(dig, ins, ar):
        cols = ', '.join(f'.col (base + {c})' for c in ins)
        vals = ', '.join(f'env.loc (base + {c})' for c in ins)
        return dig, cols, vals, ar
    walk = [site(cb, [0, 1, 2, 3], 4)]
    for k in range(nb):
        l = 4 + 3 * k
        walk.append(site(cb + k + 1, [cb + k, l, l + 1, l + 2], 4))
    walk.append(site(sc, [cb + nb, iroot], 2))
    for i, (dig, cols, vals, ar) in enumerate(walk):
        hs.append(f'''  have h{i} : env.loc (base + {dig}) = hash [{vals}] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + {dig}, [{cols}], {ar}⟩
        (by simp [rotV3SitesAt])''')
    rw = ', '.join(f'h{k}' for k in range(len(walk) - 1, -1, -1))
    body = '\n'.join(hs) + f'\n  rw [{rw}]\n  rfl\n'
    s = sub1(s, r'(?<=      = wireCommitR hash \(preLimbsAt base env\.loc\) \(env\.loc \(base \+ B_IROOT\)\) := by\n)  show env\.loc \(base \+ \d+\) = wireCommitR.*?\n  rfl\n(?=\nset_option maxHeartbeats)',
             body, 'rotV3SitesAt_pin walk')
    return s

def wide(n, s):
    nb = (n - 4) // 3
    fin = nb + 1                       # the final (iroot) carrier index
    specs = ['([.var (base+0), .var (base+1), .var (base+2), .var (base+3)], carrierCols cbase 0)']
    for k in range(nb):
        l = 4 + 3 * k
        specs.append(f'(bodyIns cbase {k} (base+{l}) (base+{l + 1}) (base+{l + 2}), carrierCols cbase {k + 1})')
    specs.append(f'((carrierCols cbase {nb}).map .var ++ [.var (base+B_IROOT), .const 0, .const 0], carrierCols cbase {fin})')
    body = '  [ -- head: [l0,l1,l2,l3] → carrier 0\n    ' + specs[0] + '\n' + \
           ''.join(f'  , {x}\n' for x in specs[1:-1]) + f'  , {specs[-1]} ]\n'
    s = sub1(s, r'(?<=def rotV3WideSpecs \(base cbase : Nat\) : List \(List EmittedExpr × List Nat\) :=\n).*?\) \]\n',
             body, 'rotV3WideSpecs')
    alts = ' | '.join(['rfl'] * len(specs))
    # every case split over the spec list (admitted / fit / outCols / ...): one `rfl` per spec
    s, k = re.subn(r'(simp only \[rotV3WideSpecs, List\.mem_cons, List\.not_mem_nil, or_false\] at hp\n  rcases hp with )[^\n]*?(?=( <;>)?\n)',
                   lambda m: m.group(1) + alts, s)
    if k < 3:
        sys.exit(f'gen_rotated_geometry: expected >= 3 rotV3WideSpecs case splits, found {k}')
    s = sub1(s, r'(?<=        ∈ tbl\) :\n    carrierVals cbase )\d+(?= env\.loc\n      = wireCommitR8)', str(fin), 'rotV3WidePin statement')
    hs = ['''  have h0 : carrierVals cbase 0 env.loc
      = permW [env.loc (base+0), env.loc (base+1), env.loc (base+2), env.loc (base+3)] := by
    have := m ([.var (base+0), .var (base+1), .var (base+2), .var (base+3)], carrierCols cbase 0)
      (by simp [rotV3WideSpecs]); simpa [carrierVals, EmittedExpr.eval] using this''']
    for k in range(nb):
        l = 4 + 3 * k
        hs.append(f'''  have h{k + 1} : carrierVals cbase {k + 1} env.loc
      = permW (carrierVals cbase {k} env.loc ++ [env.loc (base+{l}), env.loc (base+{l + 1}), env.loc (base+{l + 2})]) := by
    have := m (bodyIns cbase {k} (base+{l}) (base+{l + 1}) (base+{l + 2}), carrierCols cbase {k + 1})
      (by simp [rotV3WideSpecs]); rw [bodyIns_eval] at this; simpa [carrierVals] using this''')
    hs.append(f'''  have h{fin} : carrierVals cbase {fin} env.loc
      = permW (carrierVals cbase {nb} env.loc ++ [env.loc (base+B_IROOT), 0, 0]) := by
    have := m ((carrierCols cbase {nb}).map .var ++ [.var (base+B_IROOT), .const 0, .const 0],
        carrierCols cbase {fin})
      (by simp [rotV3WideSpecs])
    simpa [carrierVals, EmittedExpr.eval, List.map_append, List.map_map, Function.comp_def] using this''')
    rw = ', '.join(f'h{k}' for k in range(fin, -1, -1))
    body = '\n'.join(hs) + f'\n  rw [{rw}]\n  rfl\n'
    s = sub1(s, r'(?<=      p\.2\.map env\.loc = permW \(p\.1\.map \(·\.eval env\.loc\)\) := hbind\n)  have h0 :.*?\n  rfl\n(?=\n#assert_axioms siteLookupN_sound)',
             body, 'rotV3WidePin walk')
    return s

def main():
    n = extent()
    changed = []
    for f, fn in (('EffectVmEmitRotationV3.lean', v3), ('EffectVmEmitRotationWide.lean', wide)):
        p = os.path.join(EMIT, f)
        old = open(p).read()
        new = fn(n, old)
        if new != old:
            changed.append(f)
            if '--check' not in sys.argv:
                open(p, 'w').write(new)
    print(f'gen_rotated_geometry: extent {n}; ' + (('changed ' + ', '.join(changed)) if changed else 'up to date'))
    return 1 if (changed and '--check' in sys.argv) else 0

if __name__ == '__main__':
    sys.exit(main())
