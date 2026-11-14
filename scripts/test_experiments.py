#!/usr/bin/env python3
"""Focused orchestration tests; fake tools do not claim Lean proof results."""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import run_experiments as runner


class ExperimentTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="mugda2-experiment-test-")
        self.root = Path(self.temporary.name).resolve()
        self.addCleanup(self.temporary.cleanup)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        (self.root / "lakefile.lean").write_text("import Lake\n")
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.source = self.root / "Bench.lean"
        self.source.write_text("theorem fixture : True := True.intro\n")
        self.manifest_path = self.root / "manifest.json"
        self.report_path = self.root / ".lake/build/experiments/result.json"
        self.audit_path = self.root / ".lake/build/audit/axioms.json"
        self.manifest = {
            "schemaVersion": 1, "protocolVersion": "test-host-v1", "kind": "host-control",
            "toolchain": "leanprover/lean4:v4.35.0",
            "cases": [{"id": "bench", "module": "Bench", "source": "Bench.lean",
                       "sourceSha256": runner.digest(self.source)}],
            "measurement": {"warmupRuns": 0, "measuredRuns": 1,
                            "elaborationTimeoutSeconds": 2, "replayTimeoutSeconds": 2,
                            "maxRssBytes": 256 * 1024 * 1024},
            "decision": {"selectionEligible": False,
                         "semanticGates": [{"id": "property", "status": "proved",
                                            "declarations": [{"module": "Bench", "name": "fixture"}]}],
                         "thresholds": {"proofTokenReduction": .25, "maxTermNodeRatio": 2,
                                        "maxReplayTimeRatio": 1.5}},
            "candidates": [{"id": "future", "artifactKind": "object-foundation",
                            "rulePinsStatus": "unresolved", "toolchainPinsStatus": "unresolved"}],
        }
        self.tool = self.root / "fake_tool.py"
        self.tool.write_text("#!" + sys.executable + "\n" + '''
import hashlib,json,os
from pathlib import Path
import sys
args=[arg for arg in sys.argv[1:] if arg!='--no-cache']
if args and args[0]=='env':
    os.execv(args[1],args[1:])
if args==['--version']:
    print('Lean fixture')
    raise SystemExit(0)
if args and args[0]=='build':
    raise SystemExit(0)
if '-o' in args:
    source=Path(args[-1]).read_bytes()
    if b'ELAB_FAIL' in source:
        print('deliberate elaboration failure',file=sys.stderr)
        raise SystemExit(7)
    output=Path(args[args.index('-o')+1])
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_bytes(source)
    print('fake elaboration')
elif '--fresh' in args:
    module=args[-1]
    first=Path(os.environ['LEAN_PATH'].split(os.pathsep)[0])
    artifact=first/(module.replace('.','/')+'.olean')
    if not artifact.is_file() or first.name!='fresh':
        raise SystemExit(8)
    if b'import Bench.Contract' in artifact.read_bytes() and not (first/'Bench/Contract.olean').is_file():
        raise SystemExit(10)
    print(json.dumps({'artifactSha256':hashlib.sha256(artifact.read_bytes()).hexdigest()}))
else:
    raise SystemExit(9)
''')
        self.tool.chmod(0o755)
        self.tools = {"lean": str(self.tool), "leanchecker": str(self.tool),
                      "leanVersion": "Lean fixture", "environment": {"LEAN_PATH": "stale-build-path"},
                      "binarySha256": {"lean": runner.digest(self.tool), "leanchecker": runner.digest(self.tool)}}
        self.write_inputs()

    def write_inputs(self) -> None:
        self.manifest["cases"][0]["sourceSha256"] = runner.digest(self.source)
        self.manifest_path.write_text(json.dumps(self.manifest))
        self.audit_path.parent.mkdir(parents=True, exist_ok=True)
        self.audit_path.write_text(json.dumps({
            "sources": runner.source_snapshot(self.root), "buildInputs": runner.config_snapshot(self.root),
            "toolchain": self.manifest["toolchain"], "leanVersion": "Lean fixture",
            "allowedAxioms": sorted(runner.audit_axioms.ALLOWED_AXIOMS), "modules": ["Bench"],
            "declarations": [{"module": "Bench", "name": "fixture", "kind": "theorem",
                              "unsafe": False, "partial": False, "axioms": []}],
        }))

    def run_fixture(self, **kwargs) -> dict:
        with patch.object(runner, "discover_environment", return_value=copy.deepcopy(self.tools)):
            return runner.run_experiment(self.manifest_path, self.root, [str(self.tool)],
                                         self.report_path, self.audit_path, **kwargs)

    def test_fresh_artifact_is_replayed_and_warmups_are_excluded(self) -> None:
        self.manifest["measurement"].update(warmupRuns=1, measuredRuns=2)
        self.write_inputs()
        result = self.run_fixture()
        self.assertEqual(result["status"], "measured")
        self.assertFalse(result["foundationDecision"]["selectionEligible"])
        case = result["cases"][0]
        self.assertEqual(len(case["runs"]), 3)
        self.assertEqual(case["summary"]["kernelReplay"]["successfulSamples"], 2)
        for run in case["runs"]:
            replay = run["kernelReplay"]
            self.assertIn("--fresh", replay["command"])
            observed = json.loads(Path(replay["stdout"]["path"]).read_text())
            self.assertEqual(observed["artifactSha256"], run["artifact"]["sha256"])
            self.assertEqual(run["artifact"]["sha256"], runner.digest(self.source))
        self.assertEqual(case["kernelTermNodes"]["status"], "unresolved")
        self.assertEqual(result["candidateEligibility"][0]["rulePinsStatus"], "unresolved")

    def test_stale_audit_prevents_any_measurement(self) -> None:
        audit = json.loads(self.audit_path.read_text())
        audit["sources"]["Bench.lean"] = "0" * 64
        self.audit_path.write_text(json.dumps(audit))
        with patch.object(runner, "discover_environment", side_effect=AssertionError("must not run tools")):
            result = runner.run_experiment(self.manifest_path, self.root, [str(self.tool)], self.report_path, self.audit_path)
        self.assertEqual(result["status"], "unresolved")
        self.assertFalse(result["measurementPerformed"])
        self.assertEqual(result["cases"], [])

    def test_same_package_overlay_links_dependencies_and_excludes_every_target_part(self) -> None:
        installed = self.root / ".lake/build/lib/lean"
        source = self.root / "Bench/Client.lean"
        source.parent.mkdir()
        source.write_text("import Bench.Contract\ntheorem fixture : True := True.intro\n")
        case = {"id": "package", "module": "Bench.Client", "source": "Bench/Client.lean",
                "sourceSha256": runner.digest(source)}
        for path in runner.artifact_part_paths(installed, "Bench.Contract"):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"installed-dependency")
        for path in runner.artifact_part_paths(installed, "Bench.Client"):
            path.write_bytes(b"installed-target-must-not-change")
        before = runner.installed_artifact_snapshot(self.root)
        result = runner.measure_case(case, self.manifest, self.root, self.tools,
                                     self.root / ".lake/package-artifacts")
        self.assertEqual(result["status"], "measured", result)
        self.assertEqual(runner.installed_artifact_snapshot(self.root), before)
        run = result["runs"][0]
        overlay = run["dependencyOverlay"]
        self.assertEqual(len(overlay["dependencies"]), 3)
        for record in overlay["dependencies"]:
            linked = Path(record["symlinkPath"])
            self.assertTrue(linked.is_symlink())
            self.assertEqual(runner.digest(linked), record["sha256"])
            self.assertFalse(linked.parent.is_symlink())
        self.assertFalse(Path(run["artifact"]["path"]).is_symlink())
        for path in runner.artifact_part_paths(Path(overlay["freshRoot"]), "Bench.Client")[1:]:
            self.assertFalse(path.exists())
            self.assertFalse(path.is_symlink())

    def test_installed_dependency_change_invalidates_report(self) -> None:
        dependency = self.root / ".lake/build/lib/lean/Other.olean"
        dependency.parent.mkdir(parents=True)
        dependency.write_bytes(b"installed-before")
        original = runner.measure_case

        def changed(*args, **kwargs):
            result = original(*args, **kwargs)
            dependency.write_bytes(b"installed-after")
            return result

        with patch.object(runner, "measure_case", side_effect=changed):
            result = self.run_fixture()
        self.assertEqual(result["status"], "invalidated")
        self.assertEqual(result["installedArtifactIntegrity"], "changed")
        self.assertIn("artifacts changed", result["invalidationReason"])

    def test_frozen_audit_hash_mismatch_prevents_measurement(self) -> None:
        self.manifest["auditReportSha256"] = "0" * 64
        self.manifest_path.write_text(json.dumps(self.manifest))
        result = self.run_fixture()
        self.assertEqual(result["status"], "unresolved")
        self.assertIn("frozen audit report changed", result["preflight"]["reason"])
        self.assertFalse(result["measurementPerformed"])

    def test_failed_elaboration_does_not_replay(self) -> None:
        self.source.write_text("-- ELAB_FAIL\ntheorem fixture : True := True.intro\n")
        self.write_inputs()
        result = self.run_fixture()
        self.assertEqual(result["status"], "incomplete")
        run = result["cases"][0]["runs"][0]
        self.assertEqual(run["elaboration"]["exitCode"], 7)
        self.assertNotIn("kernelReplay", run)
        self.assertIn("deliberate", Path(run["elaboration"]["stderr"]["path"]).read_text())

    def test_missing_fresh_artifact_prevents_replay(self) -> None:
        original = runner.measured_process

        def remove_artifact(command, *args, **kwargs):
            result = original(command, *args, **kwargs)
            if "-o" in command:
                Path(command[command.index("-o") + 1]).unlink()
            return result

        with patch.object(runner, "measured_process", side_effect=remove_artifact):
            result = self.run_fixture()
        run = result["cases"][0]["runs"][0]
        self.assertEqual(run["elaboration"]["reason"], "missingFreshArtifact")
        self.assertNotIn("kernelReplay", run)

    def test_source_change_invalidates_preserved_observations(self) -> None:
        original = runner.measure_case

        def changed(*args, **kwargs):
            result = original(*args, **kwargs)
            self.source.write_text(self.source.read_text() + "-- changed\n")
            return result

        with patch.object(runner, "measure_case", side_effect=changed):
            result = self.run_fixture()
        self.assertEqual(result["status"], "invalidated")
        self.assertTrue(result["cases"][0]["runs"])

    def test_bad_registration_removes_prior_green_report(self) -> None:
        self.report_path.parent.mkdir(parents=True, exist_ok=True)
        self.report_path.write_text('{"status":"measured"}')
        self.manifest["decision"]["selectionEligible"] = True
        self.manifest_path.write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(runner.ExperimentError, "disable foundation selection"):
            self.run_fixture()
        self.assertFalse(self.report_path.exists())

    def test_unpinned_source_and_invalid_thresholds_are_rejected(self) -> None:
        bad = copy.deepcopy(self.manifest)
        bad["cases"][0]["sourceSha256"] = "0" * 64
        with self.assertRaisesRegex(runner.ExperimentError, "source changed"):
            runner.validate_manifest(bad, self.root)
        bad = copy.deepcopy(self.manifest)
        bad["decision"]["thresholds"]["proofTokenReduction"] = 1
        with self.assertRaisesRegex(runner.ExperimentError, "less than one"):
            runner.validate_manifest(bad, self.root)
        bad = copy.deepcopy(self.manifest)
        bad["candidates"][0]["rulePinsStatus"] = "pinned"
        with self.assertRaisesRegex(runner.ExperimentError, "evidence"):
            runner.validate_manifest(bad, self.root)
        bad = copy.deepcopy(self.manifest)
        bad["cases"][0]["id"] = ".."
        with self.assertRaisesRegex(runner.ExperimentError, "safe"):
            runner.validate_manifest(bad, self.root)
        (self.root / "lake-manifest.json").write_text('{"packages":[{"name":"missing"}]}')
        with self.assertRaisesRegex(runner.ExperimentError, "never installs"):
            runner.validate_manifest(self.manifest, self.root)

    def test_proved_gate_requires_audited_theorem(self) -> None:
        self.manifest["decision"]["semanticGates"][0]["declarations"][0]["name"] = "absent"
        self.write_inputs()
        result = self.run_fixture()
        self.assertEqual(result["status"], "unresolved")
        self.assertIn("absent", result["preflight"]["reason"])

    def test_validation_mode_does_not_claim_measurements(self) -> None:
        self.audit_path.unlink()
        result = self.run_fixture(validate_only=True)
        self.assertEqual(result["status"], "registered")
        self.assertFalse(result["measurementPerformed"])
        self.assertEqual(result["cases"], [])

    def test_environment_query_executes_and_excludes_unrelated_variables(self) -> None:
        binaries = self.root / "bin"
        binaries.mkdir()
        for name in ("lean", "leanchecker"):
            (binaries / name).symlink_to(self.tool)
        with patch.dict(os.environ, {"PATH": str(binaries) + os.pathsep + os.environ.get("PATH", ""),
                                     "MUGDA2_TEST_SECRET": "must-not-be-queried"}):
            resolved = runner.discover_environment(self.root, [str(self.tool)])
        self.assertEqual(resolved["leanVersion"], "Lean fixture")
        self.assertEqual(resolved["lean"], str(binaries / "lean"))
        self.assertNotIn("MUGDA2_TEST_SECRET", resolved["environment"])

    def test_timeout_is_unknown_and_keeps_logs(self) -> None:
        result = runner.measured_process([sys.executable, "-c", "import time; print('started',flush=True); time.sleep(30)"],
                                         self.root, dict(os.environ), .1, 256 * 1024 * 1024,
                                         self.root / ".lake/timeout")
        self.assertEqual(result["status"], "unknown")
        self.assertEqual(result["reason"], "timeout")
        self.assertIn("started", Path(result["stdout"]["path"]).read_text())

    @unittest.skipUnless(hasattr(os, "wait4") and sys.platform in {"darwin", "linux"}, "wait4 RSS unavailable")
    def test_peak_rss_belongs_to_each_child_and_limit_is_honest(self) -> None:
        high = runner.measured_process([sys.executable, "-c", "x=bytearray(64*1024*1024); print(len(x))"],
                                       self.root, dict(os.environ), 5, 256 * 1024 * 1024,
                                       self.root / ".lake/high")
        low = runner.measured_process([sys.executable, "-c", "print('small')"], self.root, dict(os.environ),
                                      5, 1, self.root / ".lake/low")
        self.assertGreater(high["peakRssBytes"], low["peakRssBytes"] + 32 * 1024 * 1024)
        self.assertEqual(low["status"], "unknown")
        self.assertEqual(low["reason"], "rssGuardrailExceeded")
        self.assertIn("not a hard memory limit", low["rssEnforcement"])

    @unittest.skipUnless(os.environ.get("MUGDA2_REAL_LEAN_TEST") == "1", "opt-in real Lean replay")
    def test_real_source_elaboration_and_fresh_kernel_replay(self) -> None:
        project = Path(__file__).resolve().parents[1]
        tools = runner.discover_environment(project, ["lake"])
        self.manifest["measurement"]["elaborationTimeoutSeconds"] = 60
        self.manifest["measurement"]["replayTimeoutSeconds"] = 60
        self.manifest["measurement"]["maxRssBytes"] = 1024 * 1024 * 1024
        result = runner.measure_case(self.manifest["cases"][0], self.manifest, self.root, tools,
                                     self.root / ".lake/real-artifacts")
        self.assertEqual(result["status"], "measured", result)
        run = result["runs"][0]
        self.assertEqual(run["elaboration"]["exitCode"], 0)
        self.assertEqual(run["kernelReplay"]["exitCode"], 0)
        self.assertTrue(Path(run["artifact"]["path"]).is_file())

    @unittest.skipUnless(os.environ.get("MUGDA2_REAL_LEAN_TEST") == "1", "opt-in real same-package replay")
    def test_real_same_package_dependency_and_fresh_target(self) -> None:
        project = Path(__file__).resolve().parents[1]
        tools = runner.discover_environment(project, ["lake"])
        installed = self.root / ".lake/build/lib/lean"
        package = self.root / "Bench"
        package.mkdir()
        contract = package / "Contract.lean"
        contract.write_text("namespace Bench\ndef answer : Nat := 42\nend Bench\n")
        client = package / "Client.lean"
        client.write_text("import Bench.Contract\nnamespace Bench\ntheorem answer_ok : answer = 42 := rfl\nend Bench\n")
        contract_olean = runner.artifact_part_paths(installed, "Bench.Contract")[0]
        contract_olean.parent.mkdir(parents=True, exist_ok=True)
        environment = {**os.environ, **tools["environment"]}
        environment["LEAN_PATH"] = str(installed) + os.pathsep + environment.get("LEAN_PATH", "")
        compiled = subprocess.run([tools["lean"], "-R", str(self.root), "-o", str(contract_olean), str(contract)],
                                  cwd=self.root, env=environment, text=True, capture_output=True, timeout=60)
        self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
        installed_target = runner.artifact_part_paths(installed, "Bench.Client")[0]
        installed_target.write_bytes(b"deliberately-stale-target-not-to-be-imported-or-overwritten")
        before = runner.installed_artifact_snapshot(self.root)
        tools["environment"]["LEAN_PATH"] = environment["LEAN_PATH"]
        self.manifest["measurement"].update(elaborationTimeoutSeconds=60, replayTimeoutSeconds=60,
                                             maxRssBytes=1024 * 1024 * 1024)
        case = {"id": "same-package", "module": "Bench.Client", "source": "Bench/Client.lean",
                "sourceSha256": runner.digest(client)}
        result = runner.measure_case(case, self.manifest, self.root, tools,
                                     self.root / ".lake/real-package-artifacts")
        self.assertEqual(result["status"], "measured", result)
        self.assertEqual(runner.installed_artifact_snapshot(self.root), before)
        run = result["runs"][0]
        self.assertNotEqual(run["artifact"]["sha256"], runner.digest(installed_target))
        self.assertEqual(len(run["dependencyOverlay"]["dependencies"]), 1)
        self.assertTrue(Path(run["dependencyOverlay"]["dependencies"][0]["symlinkPath"]).is_symlink())


if __name__ == "__main__":
    unittest.main(verbosity=2)
