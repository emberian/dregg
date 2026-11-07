#!/usr/bin/env python3
"""Concrete signed-receipt association regressions; runs only the small metadata check.

Run after building absence-receipt: python3 -I demo/absence-receipt/tests/receipt_binding.py
No corpus clone, signing keys, Lean builds, or edits to published artifacts are needed.
"""
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]


def verify(work, *options):
    return subprocess.run([sys.executable, '-I', str(HERE/'verify_receipt.py'), str(work), *options],
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def refused(result, reason):
    assert result.returncode != 0, result.stdout
    assert reason in result.stdout, result.stdout


with tempfile.TemporaryDirectory(prefix='absence-receipt-binding-') as temp:
    work = Path(temp)
    original_signers = (HERE/'allowed_signers').read_bytes()
    with gzip.open(HERE/'documents.tsv.gz', 'rb') as source, (work/'documents.tsv').open('wb') as out:
        shutil.copyfileobj(source, out)
    honest = (HERE/'dfa-run.json').read_bytes()
    (work/'dfa-run.json').write_bytes(honest)
    ok = verify(work)
    assert ok.returncode == 0, ok.stdout
    print('original signature + complete tuple: PASS')

    changed = json.loads(honest)
    changed['count'] += 1
    changed['accepted'] -= 1
    changed['rejected_indices'] = sorted(changed['rejected_indices'] + [0])
    (work/'dfa-run.json').write_text(json.dumps(changed))
    refused(verify(work), 'signed receipt differs from computed tuple: count')
    print('internally consistent count substitution: REFUSE')
    (work/'dfa-run.json').write_bytes(honest)

    # Same DFA semantics, different serialized bytes: the signature binds the exact artifact.
    altered_table = work/'same-table-different-bytes.json'
    altered_table.write_bytes((HERE/'absence-table.json').read_bytes() + b'\n')
    refused(verify(work, '--table', str(altered_table)), 'signed receipt differs from computed tuple: table_blake3')
    print('table artifact substitution: REFUSE')

    other_signers = HERE.parent/'datalog-governance/allowed_signers'
    refused(verify(work, '--signers', str(other_signers)), 'receipt verification FAILED')
    assert (HERE/'allowed_signers').read_bytes() == original_signers
    print('untrusted signer: REFUSE; original trust anchor unchanged')
