#!/usr/bin/env python3
"""Regressions for trace-log acceptance and mutation case selection."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "dev/validation/stage-b-trace-comparison-run.py"
CONTROL = ROOT / "dev/validation/stage-b-trace-control.log"
spec = importlib.util.spec_from_file_location("trace_checks", ROOT / "dev/lean-twin-checks.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)


class TraceLogTests(unittest.TestCase):
    def setUp(self):
        self.valid = CONTROL.read_text()

    def reject_edit(self, before, after):
        self.assertEqual(self.valid.count(before), 1)
        with self.assertRaises(ValueError):
            checks.check_trace_log(self.valid.replace(before, after))

    def test_control_passes(self):
        checks.check_trace_log(self.valid)

    def test_undeferred_frontier_fails(self):
        self.reject_edit("row=acc-runtime-proof class=frontier check=refused deferred=stage-c",
                         "row=acc-runtime-proof class=frontier check=refused")

    def test_failed_pair_fails(self):
        self.reject_edit("row=binder-proof class=pair-runtime cmp=identical",
                         "row=binder-proof class=pair-runtime cmp=differs")

    def test_duplicate_row_fails(self):
        self.reject_edit("row=branch-dependent ", "row=binder-proof ")

    def test_replaced_fixture_fails(self):
        self.reject_edit("row=binder-proof ", "row=missing-fixture ")

    def test_class_count_mismatch_fails(self):
        self.reject_edit("row=binder-proof class=pair-runtime cmp=identical carried=differs",
                         "row=binder-proof class=single erase=accepted")

    def test_carried_count_mismatch_fails(self):
        self.reject_edit("row=binder-proof class=pair-runtime cmp=identical carried=differs",
                         "row=binder-proof class=pair-runtime cmp=identical carried=identical")

    def test_accepted_frontier_fails(self):
        self.reject_edit("row=acc class=frontier check=refused", "row=acc class=frontier check=accepted")

    def test_wrong_deferral_fails(self):
        self.reject_edit("row=acc class=frontier check=refused deferred=stage-c",
                         "row=acc class=frontier check=refused deferred=stage-d")

    def test_failed_shape_fails(self):
        self.reject_edit("row=f2-a-shape class=shape cmp=identical", "row=f2-a-shape class=shape cmp=differs")

    def test_unknown_shape_target_fails(self):
        self.reject_edit("against=f2-a", "against=missing-fixture")

    def test_wrong_refusal_fails(self):
        self.reject_edit("row=opaque-layout-refusal class=refusal exit=2",
                         "row=opaque-layout-refusal class=refusal exit=0")

    def test_failed_check_fails(self):
        self.reject_edit("row=acc-family class=check-only check=accepted",
                         "row=acc-family class=check-only check=refused")

    def test_failed_single_fails(self):
        self.reject_edit("row=duplicate-payload class=single erase=accepted",
                         "row=duplicate-payload class=single erase=refused")

    def test_duplicate_field_fails(self):
        self.reject_edit("row=binder-proof ", "row=binder-proof row=branch-dependent ")

    def test_unknown_field_fails(self):
        self.reject_edit("row=binder-proof ", "row=binder-proof ignored=true ")

    def test_malformed_field_fails(self):
        self.reject_edit("row=binder-proof ", "row=binder-proof invalid ")


class CaseSelectionTests(unittest.TestCase):
    def test_unknown_and_empty_selection_fail(self):
        for selection in ([], ["MISSING"], ["M1", "MISSING"]):
            with self.subTest(selection=selection):
                result = subprocess.run([sys.executable, "-P", str(RUNNER), "--only", *selection],
                                        cwd=ROOT, capture_output=True, text=True, timeout=10)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertNotIn("STAGE-B-TRACE-COMPARISON", result.stdout)


if __name__ == "__main__":
    unittest.main()
