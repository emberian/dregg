#!/usr/bin/env python3
"""Scratch-only regression for the source-commit → emit/stamp → provenance phases.

Run: python3 scripts/test-emit-routing-phases.py
The real checker bodies run against a synthetic temporary git index. No shared source,
artifact, index, hook configuration or stamp is mutated; no Lean/Cargo build is needed.
"""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("emit_descriptors", Path(__file__).with_name("emit_descriptors.py"))
emit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(emit)


class RoutingPhases(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="emit-routing-phases-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.desc = self.root / "circuit/descriptors"
        self.meta = self.root / "metatheory"
        (self.desc / "by-name").mkdir(parents=True)
        self.meta.mkdir()
        self.artifact = self.desc / "by-name/fixture.json"
        self.artifact.write_text('{"fixture":1}\n')
        self.router = self.meta / emit.BY_NAME_ROUTER
        self.router.write_text(
            emit.BY_NAME_TABLE_DECL + '\n  [("fixture.json", fixture)\n  ]\n'
            'theorem byNameDescriptors_length : byNameDescriptors.length = 1 := by rfl\n')
        # An actual emitter path makes the committed-source refusal non-vacuous.
        self.emitter = self.meta / emit.EMITTERS[0]
        self.emitter.parent.mkdir(parents=True)
        self.emitter.write_text('-- synthetic emitter closure member\n')
        workflow = self.root / ".github/workflows/fixture.yml"
        workflow.parent.mkdir(parents=True)
        workflow.write_text("jobs:\n  fixture:\n    steps:\n      - run: bash scripts/check.sh\n")
        script = self.root / "scripts/check.sh"
        script.parent.mkdir()
        script.write_text("#!/bin/sh\nexit 0\n")
        rust = self.root / "src/main.rs"
        rust.parent.mkdir()
        rust.write_text('const FIXTURE: &str = include_str!("../circuit/descriptors/by-name/fixture.json");\n')
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True, capture_output=True)
        self.track(self.artifact, self.router, self.emitter, workflow, script, rust)
        self.stamp = {
            "mode": "emit", "source_dirty": False, "dregg2_tree_hash": "synthetic-fixture",
            "descriptor_sha256": {}, "fp_file_sha256": {},
            "by_name_sha256": {"fixture.json": emit.sha256_hex(self.artifact.read_bytes())},
        }
        self.write_stamp()
        self.scope = emit.rooted_at(self.root)
        self.scope.__enter__()
        self.addCleanup(self.scope.__exit__, None, None, None)

    def track(self, *paths):
        subprocess.run(["git", "-C", str(self.root), "add", "--",
                        *(str(p.relative_to(self.root)) for p in paths)], check=True, capture_output=True)

    def write_stamp(self):
        (self.desc / emit.PROVENANCE_FILE).write_text(json.dumps(self.stamp))

    def static(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            findings = emit.verify_by_name_routing()
        return findings, output.getvalue()

    def provenance(self):
        # All routing and reference doors run too: this is the surviving full check body.
        with contextlib.redirect_stdout(io.StringIO()):
            return emit._verify_provenance_findings()[0]

    def test_clean_stamped_control_passes_both(self):
        self.assertEqual(self.static()[0], [])
        self.assertEqual(self.provenance(), [])

    def test_same_unstamped_artifact_passes_static_but_fails_provenance(self):
        self.stamp["by_name_sha256"] = {}
        self.write_stamp()
        findings, output = self.static()
        self.assertEqual(findings, [])
        self.assertIn("PENDING provenance", output)
        self.assertIn("NOT provenance evidence", output)
        self.assertTrue(any("fixture.json" in f and "NOT covered by the stamp" in f
                            for f in self.provenance()))

    def test_absent_stamp_passes_static_but_provenance_refuses(self):
        (self.desc / emit.PROVENANCE_FILE).unlink()
        findings, output = self.static()
        self.assertEqual(findings, [])
        self.assertIn("PENDING provenance", output)
        with self.assertRaisesRegex(SystemExit, "unstamped descriptor set"):
            self.provenance()

    def test_changed_bytes_remain_provenance_failure(self):
        self.artifact.write_text('{"fixture":2}\n')
        self.assertEqual(self.static()[0], [])
        self.assertTrue(any("does NOT match its stamped sha256" in f for f in self.provenance()))

    def test_dirty_source_stamp_remains_provenance_failure(self):
        self.stamp["source_dirty"] = True
        self.write_stamp()
        self.assertTrue(any("source_dirty=true" in f for f in self.provenance()))

    def test_non_emit_stamp_remains_provenance_failure(self):
        self.stamp["mode"] = "stamp-existing"
        self.write_stamp()
        self.assertTrue(any("not 'emit'" in f for f in self.provenance()))

    def test_static_ghost_still_refused(self):
        self.artifact.unlink()
        self.assertTrue(any(f.startswith("GHOST:") for f in self.static()[0]))

    def test_static_unrouted_tracked_artifact_still_refused(self):
        extra = self.desc / "by-name/unrouted.json"
        extra.write_text('{}\n')
        self.track(extra)
        self.assertTrue(any(f.startswith("UNROUTED:") for f in self.static()[0]))

    def test_static_reference_doors_still_refuse_missing_import(self):
        self.router.write_text(self.router.read_text() + 'import Dregg2.Missing\n')
        self.assertTrue(any("Dregg2.Missing" in f for f in self.static()[0]))

    def test_automatic_emitter_still_requires_committed_source(self):
        # All fixture source files are staged, but not committed: exactly the pre-stamp phase.
        self.assertEqual(self.static()[0], [])
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as refused:
            emit.require_committed_emit_source("synthetic source-phase test")
        self.assertEqual(refused.exception.code, emit.EXIT_REFUSED)
        self.assertIn(str(self.emitter.relative_to(self.root)), emit.emit_source_dirt())


if __name__ == "__main__":
    unittest.main(verbosity=2)
