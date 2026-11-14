#!/usr/bin/env python3
"""Regression checks for the trust audit, including real failing Lean modules."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import audit_axioms


class SourcePolicyTests(unittest.TestCase):
    def test_comments_and_strings_are_not_code(self):
        source = '''/- sorry /- unsafe -/ partial -/
-- Classical.choice
def message : String := "sorry unsafe partial Classical.choice"
theorem actual : True := True.intro
'''
        self.assertEqual(audit_axioms.source_policy_violations(source), [])

    def test_source_bans_report_line_numbers(self):
        self.assertEqual(
            audit_axioms.source_policy_violations("-- sorry\nunsafe def bad := 0\n"),
            [(2, "unsafe")],
        )
        self.assertEqual(
            audit_axioms.source_policy_violations("partial def loop : Nat := loop\n"),
            [(1, "partial")],
        )

    def test_each_forbidden_axiom_is_rejected(self):
        for axiom in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "extraAxiom"):
            with self.subTest(axiom=axiom):
                with self.assertRaisesRegex(audit_axioms.AuditError, "unapproved axioms"):
                    audit_axioms.validate_declarations(
                        [{"name": "bad", "module": "Fixture", "kind": "theorem",
                          "unsafe": False, "partial": False, "axioms": [axiom]}],
                        ["Fixture"],
                    )

    def test_source_edits_during_audit_cannot_publish_report(self):
        with tempfile.TemporaryDirectory(prefix="mugda2-audit-race-") as directory:
            root = Path(directory)
            source_file = root / "Fixture.lean"
            source_file.write_text("theorem first : True := True.intro\n")
            report = root / "report.json"

            def concurrent_edit(command, root, *, source=None, environment=None):
                if "--stdin" in command:
                    source_file.write_text("theorem changed : True := True.intro\n")
                    entry = {"name": "first", "module": "Fixture", "kind": "theorem",
                             "unsafe": False, "partial": False, "axioms": []}
                    return audit_axioms.REPORT_PREFIX + json.dumps([entry])
                return ""

            with patch.object(audit_axioms, "run", side_effect=concurrent_edit), patch.object(
                audit_axioms, "prepare_support", return_value=({}, {})
            ):
                with self.assertRaisesRegex(audit_axioms.AuditError, "changed during"):
                    audit_axioms.audit(root, ["lake"], report)
            self.assertFalse(report.exists())

    def test_partial_artifacts_require_an_audited_safe_parent(self):
        theorem = {"name": "valid", "module": "Fixture", "kind": "theorem",
                   "unsafe": False, "partial": False, "axioms": []}
        artifact = {"name": "missing._unsafe_rec", "module": "Fixture",
                    "kind": "definition", "unsafe": False, "partial": True,
                    "compilerImplementationOf": "missing",
                    "compilerImplementationKind": "total-recursion", "axioms": []}
        with self.assertRaisesRegex(audit_axioms.AuditError, "no audited safe parent"):
            audit_axioms.validate_declarations([theorem, artifact], ["Fixture"])
        artifact["compilerImplementationOf"] = None
        with self.assertRaisesRegex(audit_axioms.AuditError, "unsafe or partial"):
            audit_axioms.validate_declarations([theorem, artifact], ["Fixture"])

    def test_deriving_metadata_must_point_to_a_real_deriving_clause(self):
        source = "opaque BEq : Bool := false\n"
        entry = {
            "module": "Fixture", "name": "fake._unsafe_rec",
            "derivingOrigin": {
                "class": "BEq", "line": 1, "column": 7, "endLine": 1, "endColumn": 10,
                "declarationLine": 1, "declarationColumn": 0,
                "declarationEndLine": 1, "declarationEndColumn": len(source.rstrip()),
            },
        }
        with self.assertRaisesRegex(audit_axioms.AuditError, "no source deriving clause"):
            audit_axioms.verify_deriving_origin(entry, {"Fixture": source})


class LeanAuditTests(unittest.TestCase):
    """Use an independent Lake package; do not mutate or rebuild project proofs."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="mugda2-audit-tests-")
        cls.root = Path(cls.temporary.name)
        cls.script = Path(__file__).resolve().with_name("audit_axioms.py")
        cls.report = cls.root / "report.json"
        (cls.root / "lakefile.lean").write_text(
            "import Lake\nopen Lake DSL\npackage auditFixture\n"
            "@[default_target]\nlean_lib Fixture\n",
            encoding="utf-8",
        )
        toolchain = cls.script.parents[1] / "lean-toolchain"
        (cls.root / "lean-toolchain").write_text(toolchain.read_text(encoding="utf-8"))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def run_audit(self, source: str) -> subprocess.CompletedProcess:
        (self.root / "Fixture.lean").write_text(source, encoding="utf-8")
        # Prove a previous successful report cannot survive a subsequent failure.
        self.report.write_text("stale passing report", encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(self.script), "--root", str(self.root),
             "--report", str(self.report)],
            text=True, capture_output=True, check=False,
        )

    def test_success_records_all_theorems_in_any_namespace(self):
        completed = self.run_audit(
            "module\n"
            "namespace UnrelatedName\n"
            "public theorem first (x : Nat) : x = x := rfl\n"
            "private theorem hidden : True := True.intro\n"
            "public theorem second : True := hidden\n"
            "public def down : Nat → Nat\n"
            "  | 0 => 0\n"
            "  | n + 1 => down n\n"
            "public inductive Nested where\n"
            "  | node : List Nested → Nested\n"
            "  deriving BEq, Repr\n"
            "end UnrelatedName\n"
        )
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        report = json.loads(self.report.read_text(encoding="utf-8"))
        names = {entry["name"] for entry in report["declarations"]}
        self.assertIn("UnrelatedName.first", names)
        self.assertIn("UnrelatedName.second", names)
        self.assertTrue(any(name.endswith("hidden") for name in names))
        self.assertGreaterEqual(report["theoremCount"], 3)
        implementations = [
            entry for entry in report["declarations"]
            if entry.get("compilerImplementationOf") == "UnrelatedName.down"
        ]
        self.assertEqual(len(implementations), 1)
        self.assertEqual(implementations[0]["name"], "UnrelatedName.down._unsafe_rec")
        self.assertTrue(implementations[0]["partial"])
        self.assertFalse(implementations[0]["unsafe"])
        deriving = [
            entry for entry in report["declarations"]
            if entry.get("compilerImplementationKind") == "partial-deriving"
        ]
        self.assertEqual(len(deriving), 2)
        self.assertEqual({entry["derivingOrigin"]["class"] for entry in deriving}, {"BEq", "Repr"})
        self.assertEqual(report["partialDerivingImplementationCount"], 2)
        self.assertIn("opaque logical wrappers", report["runtimeTrustBoundary"])

    def test_separate_roots_preserve_same_named_declarations(self):
        with tempfile.TemporaryDirectory(prefix="mugda2-audit-roots-") as directory:
            root = Path(directory)
            (root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage separateRoots\n"
                "lean_lib First\nlean_lib Second\n",
                encoding="utf-8",
            )
            (root / "lean-toolchain").write_text(
                (self.root / "lean-toolchain").read_text(encoding="utf-8")
            )
            (root / "First.lean").write_text(
                "def main : IO Unit := pure ()\n"
                "theorem sharedName : 0 = 0 := rfl\n"
            )
            (root / "Second.lean").write_text(
                "def main : IO UInt32 := pure 0\n"
                "theorem sharedName : True := True.intro\n"
            )
            report = audit_axioms.audit(root, ["lake"], root / "report.json")
            identities = {
                (entry["module"], entry["name"]) for entry in report["declarations"]
            }
            self.assertTrue(
                {("First", "main"), ("Second", "main"),
                 ("First", "sharedName"), ("Second", "sharedName")} <= identities
            )

    def test_transitive_classical_choice_is_rejected(self):
        completed = self.run_audit(
            "module\n"
            "private theorem hiddenChoice (p : Prop) : p ∨ ¬p := Classical.em p\n"
            "public theorem independent : True := True.intro\n"
        )
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("Classical.choice", completed.stderr)
        self.assertFalse(self.report.exists())

    def test_unused_project_axiom_is_rejected(self):
        completed = self.run_audit(
            "axiom untrusted : False\n"
            "theorem independent : True := True.intro\n"
        )
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("project axiom declaration", completed.stderr)
        self.assertFalse(self.report.exists())

    def test_lean_failure_cannot_be_hidden_by_report_processing(self):
        completed = self.run_audit("theorem invalid : False := True.intro\n")
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("failed", completed.stderr)
        self.assertFalse(self.report.exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
