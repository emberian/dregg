#!/usr/bin/env python3
"""Reproduce counted-repeat compilation counts, semantic checks and clocks.

Use native policyc binaries; no build is launched. Repeat benchmarks require exact
baseline table identity. --union tests the composed absence policy, whose state
numbering may differ from a derivative baseline. Inputs are entirely synthetic.
"""
import argparse
import hashlib
import json
import pathlib
import os
import subprocess
import tempfile
import time


def accepted(table, word):
    state = table['start']
    for byte in word:
        state = table['transitions'][state * 256 + byte]
    return state in table['accepting']


def compile_one(binary, source, seconds, work, name="p", absence=False):
    started = time.monotonic()
    with (work / 'stderr').open('w') as err, (work / 'stdout').open('w') as out:
        command = [str(binary), 'compile', str(source), '--pattern', name]
        if absence:
            command.append('--absence')
        process = subprocess.Popen(command, stdout=out, stderr=err,
                                   env={**os.environ, "POLICYC_PROFILE": "1"})
        pid_file = work / 'compiler.pid'
        pid_file.write_text(str(process.pid) + '\n')
        try:
            rc = process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            # Stop only this invocation's recorded PID; never pattern-match processes.
            assert int(pid_file.read_text()) == process.pid
            if process.poll() is None:
                command = subprocess.check_output(
                    ['ps', '-ww', '-p', str(process.pid), '-o', 'command='], text=True)
                if str(binary) not in command:
                    raise RuntimeError('recorded compiler PID no longer names this executable')
                process.kill()
            process.wait()
            return {'status': 'timeout', 'limit_seconds': seconds,
                    'phases': [line for line in (work / 'stderr').read_text().splitlines()
                               if line.startswith('policyc profile:')]}
    elapsed = time.monotonic() - started
    if rc:
        raise RuntimeError(f'{binary}: exit {rc}: {(work / "stderr").read_text()}')
    table = json.loads((work / 'stdout').read_text())
    n = table['num_states']
    assert n > 0 and len(table['transitions']) == n * 256
    assert 0 <= table['start'] < n
    assert all(0 <= state < n for state in table['transitions'] + table['accepting'])
    canonical = {key: table[key] for key in ('num_states', 'transitions', 'start', 'accepting')}
    digest = hashlib.sha256(json.dumps(canonical, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return {'status': 'ok', 'states': table['num_states'],
            'transitions': len(table['transitions']), 'table_sha256': digest,
            'seconds': round(elapsed, 6), 'table': table,
            'phases': [line for line in (work / 'stderr').read_text().splitlines()
                       if line.startswith('policyc profile:')]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('policyc', type=pathlib.Path)
    parser.add_argument('--baseline', type=pathlib.Path)
    parser.add_argument('--timeout', type=float, default=180)
    parser.add_argument('--output', type=pathlib.Path)
    parser.add_argument('--sizes', default='4,8,16,32,64,20:64')
    parser.add_argument('--union', action='store_true', help='benchmark the demo absence union')
    parser.add_argument('--table-output', type=pathlib.Path, help='save final successful union table')
    args = parser.parse_args()
    binaries = [('cached', args.policyc.resolve())]
    if args.baseline:
        binaries.insert(0, ('baseline', args.baseline.resolve()))
    results = []
    with tempfile.TemporaryDirectory(prefix='policy-compile-') as temporary:
        work = pathlib.Path(temporary)
        for size in (['union'] if args.union else args.sizes.split(',')):
            source = work / 'input.policy'
            if args.union:
                pattern = '"AKIA" [0-9A-Z]{16} | "-----BEGIN " [A-Z ]* "PRIVATE KEY-----"'
                source.write_text(f'pattern secrets = {pattern};\npolicy p {{ forbid pattern secrets in body; }}\n')
                row = {'pattern': pattern, 'absence': True}
                checks = [(b'', True), (b'ordinary text', True),
                          (b'AKIA' + b'0' * 16, False), (b'AKIA' + b'0' * 15, True),
                          (b'AKIA' + b'0' * 17, False),
                          (b'prefix AKIA' + b'A' * 16 + b' suffix', False),
                          (b'-----BEGIN PRIVATE KEY-----', False),  # dummy header fixture, no key material
                          (b'-----BEGIN RSA PRIVATE KEY-----', False),  # dummy header fixture, no key material
                          (b'-----BEGIN rsa PRIVATE KEY-----', True),
                          (b'-----BEGIN RSA PUBLIC KEY-----', True),
                          (b'-----BEGIN RSA PRIVATE KEY----', True),
                          (b'\x00AKIA' + b'Z' * 16 + b'\xff', False)]
            else:
                bounds = list(map(int, size.split(':')))
                lo, hi = bounds[0], bounds[-1]
                pattern = f'"sk-" \\w{{{lo},{hi}}}'
                source.write_text(f'pattern p = {pattern};\n')
                row = {'pattern': pattern, 'min_repeat': lo, 'max_repeat': hi}
                checks = [(b'sk-' + b'a' * n, lo <= n <= hi)
                          for n in sorted({0, max(0, lo - 1), lo, hi, hi + 1})]
                checks += [(b'sk-' + b'a' * lo + b'!', False),
                           (b'a' * lo, False), (b'SK-' + b'a' * lo, False),
                           (b'sk-' + (b'A_0' * (lo + 2))[:lo], True),
                           (b'sk-' + b'-' * max(lo, 1), False)]
            tables = []
            for label, binary in binaries:
                result = compile_one(binary, source, args.timeout, work,
                                     'secrets' if args.union else 'p', args.union)
                if result['status'] == 'ok':
                    table = result.pop('table')
                    for word, expected in checks:
                        if accepted(table, word) != expected:
                            raise AssertionError(f'{label} {pattern}: wrong verdict on {word!r}')
                    if args.union and args.table_output and label == 'cached':
                        args.table_output.write_text(json.dumps(table, separators=(',', ':')) + '\n')
                    result['semantic_checks'] = len(checks)
                    tables.append(result['table_sha256'])
                row[label] = result
            if not args.union and len(tables) == 2 and tables[0] != tables[1]:
                raise AssertionError(f'{pattern}: cached compiler changed the table')
            results.append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
    report = {'schema': 'policy-compile-benchmark-v1', 'cases': results}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    return 1 if any(row['cached']['status'] != 'ok' for row in results) else 0


if __name__ == '__main__':
    raise SystemExit(main())
