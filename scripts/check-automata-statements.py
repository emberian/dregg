#!/usr/bin/env python3
"""Fail stale statement reviews and missing kernel evidence; does not judge theorem meaning.

Run from anywhere. --self-test tests rejection on private copies, never the shared tree.
A review is scoped to named public statements, not every theorem in an imported module.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path('docs/automata/statement-audit.json')
COMPANION = Path('metatheory/Dregg2/Automata/StatementAudit.lean')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(root, sources):
    """Local import identity only: imported files are NOT thereby declared reviewed."""
    found = set()
    pending = list(sources)
    while pending:
        rel = pending.pop()
        if rel in found:
            continue
        found.add(rel)
        path = root / rel
        if not path.is_file():
            continue
        for imports in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',
                                  path.read_text(), re.M):
            for module in imports.split('--', 1)[0].split():
                if re.fullmatch(r'Dregg2\.[\w.]+', module):
                    pending.append('metatheory/' + module.replace('.', '/') + '.lean')
    return found | {'metatheory/lean-toolchain', 'metatheory/lake-manifest.json'}


def check(root):
    errors = []
    try:
        data = json.loads((root / MANIFEST).read_text())
        reviews = data['reviews']
        pins = data['axiom_pins']
        snapshots = data['source_sha256']
        if data['schema'] != 1 or not reviews or not pins:
            raise ValueError('empty or unsupported review manifest')
        sources = {r['source'] for r in reviews} | {str(COMPANION)}
        expected = closure(root, sources)
        if set(snapshots) != expected:
            errors.append('source snapshot does not cover exactly the local import closure')
        for rel, sha in snapshots.items():
            if not (root / rel).is_file() or digest(root / rel) != sha:
                errors.append(f'stale review: {rel}')
        companion = (root / COMPANION).read_text()
        if re.search(r'\b(?:native_decide|sorry|admit)\b|#exit|debug\.skipKernelTC', companion):
            errors.append('audit evidence contains a forbidden proof escape')
        seen = set()
        for review in reviews:
            if review['id'] in seen:
                errors.append(f'duplicate review id: {review["id"]}')
            seen.add(review['id'])
            for key in ('statement', 'witness', 'falsifier', 'scope'):
                if not isinstance(review[key], str) or not review[key].strip():
                    errors.append(f'{review["id"]}: missing {key}')
            if review['witness_scope'] not in ('checker-premise', 'relation-instance', 'relation-only'):
                errors.append(f'{review["id"]}: unspecified witness scope')
            for key in ('statement', 'witness', 'falsifier'):
                if review[key] not in pins:
                    errors.append(f'{review["id"]}: {key} lacks exact axiom pin')
        for name, report in pins.items():
            block = f'/-- {report} -/\n#guard_msgs in\n#print axioms {name}'
            if block not in companion:
                errors.append(f'missing exact axiom tripwire: {name}')
        # Pin removal/extra evidence cannot silently evade manifest coverage.
        actual = set(re.findall(r'^#print axioms ([\w.]+)$', companion, re.M))
        if actual != set(pins):
            errors.append('companion and manifest disagree on axiom coverage')
        return errors, len(reviews), len(pins), len(snapshots)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        return [f'invalid review manifest or source: {exc}'], 0, 0, 0


def self_test(root):
    """Mutation tests use copies: the production tree is never temporarily disarmed."""
    baseline = check(root)
    if baseline[0]:
        return baseline[0]
    data = json.loads((root / MANIFEST).read_text())
    mutations = (
        ('changed reviewed statement', lambda p, d: (p / d['reviews'][0]['source']).write_text(
            (p / d['reviews'][0]['source']).read_text() + '\n-- changed\n')),
        ('removed axiom pin', lambda p, d: (p / COMPANION).write_text(
            (p / COMPANION).read_text().replace('#guard_msgs in', '-- removed', 1))),
        ('missing falsifier', lambda p, d: d['reviews'][0].update(falsifier='')),
        ('changed transitive dependency', lambda p, d: (p / 'metatheory/lean-toolchain').write_text('changed')),
    )
    errors = []
    for label, mutate in mutations:
        with tempfile.TemporaryDirectory(prefix='automata-statement-audit-') as tmp:
            copy = Path(tmp)
            for rel in [*data['source_sha256'], str(MANIFEST)]:
                dest = copy / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(root / rel, dest)
            fixture = json.loads(json.dumps(data))
            mutate(copy, fixture)
            if label == 'removed axiom pin':
                # Exercise the evidence check independently of the digest check.
                fixture['source_sha256'][str(COMPANION)] = digest(copy / COMPANION)
            (copy / MANIFEST).write_text(json.dumps(fixture))
            if not check(copy)[0]:
                errors.append(f'mutation survived: {label}')
    return errors


def kernel_self_test(root):
    """Inject an axiom into a COPY of one proof; its unchanged exact pin must fail."""
    source = (root / COMPANION).read_text()
    needle = '(fallbackTable.wellFormed && TableRun.acceptsBytes fallbackTable ⟨#[]⟩) = false := by decide'
    if source.count(needle) != 1:
        return ['kernel mutation target changed: review the fixture']
    mutated = source.replace('set_option maxRecDepth 4096',
        'axiom statementAuditMutation : False\n\nset_option maxRecDepth 4096', 1)
    mutated = mutated.replace(needle, needle.removesuffix('by decide') +
        'by exact False.elim statementAuditMutation', 1)
    with tempfile.TemporaryDirectory(prefix='automata-statement-kernel-') as tmp:
        path = Path(tmp)
        (path / 'Mutation.lean').write_text(mutated)
        with (path / 'lean.log').open('w') as log:
            process = subprocess.Popen(['lake', 'env', 'lean', str(path / 'Mutation.lean')],
                cwd=root / 'metatheory', stdout=log, stderr=subprocess.STDOUT)
            (path / 'lean.pid').write_text(str(process.pid) + '\n')
            rc = process.wait()
        output = (path / 'lean.log').read_text()
        if (rc == 0 or not re.search(r'depends on axioms: \[[^]]*\bstatementAuditMutation\b[^]]*\]', output)
                or 'Docstring on `#guard_msgs` does not match' not in output):
            return ['kernel mutation did not fail with the injected axiom: ' + output[-2000:]]
    return []


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--kernel-self-test', action='store_true',
        help='single warm Lean check: inject a custom axiom on a temporary copy, expect refusal')
    args = parser.parse_args()
    errors, reviews, pins, sources = check(ROOT)
    if not errors and args.self_test:
        errors = self_test(ROOT)
    if not errors and args.kernel_self_test:
        errors = kernel_self_test(ROOT)
    if errors:
        for error in errors:
            print(f'automata-statements: {error}', file=sys.stderr)
        print('Review changed definitions and their consumers; do not merely refresh hashes.', file=sys.stderr)
        return 1
    print(f'automata-statements: {reviews} scoped reviews, {pins} exact axiom pins, '
          f'{sources} source identities current' + ('; 4 copy-only mutations rejected' if args.self_test else ''))
    print('Source/evidence gate only; Lean checks the pins, reviewers check the statements.')
    if args.kernel_self_test:
        print('Kernel mutation: injected custom axiom rejected by the unchanged exact pin.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
