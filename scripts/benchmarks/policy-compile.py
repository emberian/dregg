#!/usr/bin/env python3
"""Reproduce counted-repeat compilation counts, semantic checks and clocks.

Use native policyc binaries; no build is launched. With --baseline, identical JSON
transition tables are required. Inputs are entirely synthetic.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import tempfile
import time


def accepted(table, word):
    state = table['start']
    for byte in word:
        state = table['transitions'][state * 256 + byte]
    return state in table['accepting']


def compile_one(binary, source, seconds, work):
    started = time.monotonic()
    with (work / 'stderr').open('w') as err, (work / 'stdout').open('w') as out:
        process = subprocess.Popen([str(binary), 'compile', str(source), '--pattern', 'p'],
                                   stdout=out, stderr=err)
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
            return {'status': 'timeout', 'limit_seconds': seconds}
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
            'seconds': round(elapsed, 6), 'table': table}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('policyc', type=pathlib.Path)
    parser.add_argument('--baseline', type=pathlib.Path)
    parser.add_argument('--timeout', type=float, default=180)
    parser.add_argument('--output', type=pathlib.Path)
    parser.add_argument('--sizes', default='4,8,16,32,64,20:64')
    args = parser.parse_args()
    binaries = [('cached', args.policyc.resolve())]
    if args.baseline:
        binaries.insert(0, ('baseline', args.baseline.resolve()))
    results = []
    with tempfile.TemporaryDirectory(prefix='policy-compile-') as temporary:
        work = pathlib.Path(temporary)
        for size in args.sizes.split(','):
            bounds = list(map(int, size.split(':')))
            lo, hi = bounds[0], bounds[-1]
            pattern = f'"sk-" \\w{{{lo},{hi}}}'
            source = work / 'input.policy'
            source.write_text(f'pattern p = {pattern};\n')
            row = {'pattern': pattern, 'min_repeat': lo, 'max_repeat': hi}
            tables = []
            for label, binary in binaries:
                result = compile_one(binary, source, args.timeout, work)
                if result['status'] == 'ok':
                    table = result.pop('table')
                    checks = [(b'sk-' + b'a' * n, lo <= n <= hi)
                              for n in sorted({0, max(0, lo - 1), lo, hi, hi + 1})]
                    checks += [(b'sk-' + b'a' * lo + b'!', False),
                               (b'a' * lo, False), (b'SK-' + b'a' * lo, False),
                               (b'sk-' + (b'A_0' * (lo + 2))[:lo], True),
                               (b'sk-' + b'-' * max(lo, 1), False)]
                    for word, expected in checks:
                        if accepted(table, word) != expected:
                            raise AssertionError(f'{label} {pattern}: wrong verdict on {word!r}')
                    result['semantic_checks'] = len(checks)
                    tables.append(result['table_sha256'])
                row[label] = result
            if len(tables) == 2 and tables[0] != tables[1]:
                raise AssertionError(f'{pattern}: cached compiler changed the table')
            results.append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
    report = {'schema': 'policy-compile-benchmark-v1', 'cases': results}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
