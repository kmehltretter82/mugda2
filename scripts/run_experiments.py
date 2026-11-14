#!/usr/bin/env python3
"""Measure frozen host controls; never select an object-language foundation.

Source elaboration and fresh Lean-kernel replay are separate child processes.
The latter uses the exact newly elaborated olean, not the normal build artifact.
Only the Python standard library, Lake, and the pinned Lean tools are needed.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shlex
import signal
import statistics
import subprocess
import sys
import tempfile
import time
import uuid

import audit_axioms


MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
SHA256 = re.compile(r"[0-9a-f]{64}")
CONFIG_FILES = ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
OLEAN_PART_SUFFIXES = (".olean", ".olean.server", ".olean.private")
SAFE_ENV_KEYS = (
    "PATH", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_LIB_DIR",
    "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH",
)


class ExperimentError(Exception):
    """Invalid registration, untrusted preflight, or failed orchestration."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ExperimentError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inside(root: Path, relative: str) -> Path:
    require(isinstance(relative, str), "source/evidence path must be a string")
    path = (root / relative).resolve()
    require(path.is_relative_to(root), f"path escapes the project: {relative}")
    require(path.is_file(), f"missing project file: {relative}")
    return path


def positive_number(value: object, name: str, *, allow_zero: bool = False) -> None:
    require(type(value) in (int, float) and math.isfinite(value), f"invalid number: {name}")
    require(value >= 0 if allow_zero else value > 0, f"invalid number: {name}")


def validate_manifest(manifest: object, root: Path) -> dict:
    require(isinstance(manifest, dict), "manifest must be an object")
    require(manifest.get("schemaVersion") == 1, "unsupported manifest schemaVersion")
    require(isinstance(manifest.get("protocolVersion"), str) and bool(manifest["protocolVersion"]),
            "protocolVersion is required")
    require(manifest.get("kind") == "host-control", "this runner only measures host controls")
    if "auditReportSha256" in manifest:
        require(isinstance(manifest["auditReportSha256"], str) and
                SHA256.fullmatch(manifest["auditReportSha256"]) is not None,
                "auditReportSha256 must be a SHA-256 digest")
    require(manifest.get("toolchain") == (root / "lean-toolchain").read_text().strip(),
            "manifest toolchain does not match lean-toolchain")
    package_manifest = json.loads((root / "lake-manifest.json").read_text())
    require(not package_manifest.get("packages", []),
            "this host-control runner requires a dependency-free package; it never installs dependencies")
    cases = manifest.get("cases")
    require(isinstance(cases, list) and bool(cases), "manifest needs cases")
    ids = set()
    for case in cases:
        require(isinstance(case, dict), "case must be an object")
        case_id, module = case.get("id"), case.get("module")
        require(isinstance(case_id, str) and re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", case_id) is not None,
                "case id must be a safe, nonempty identifier")
        require(case_id not in ids, f"duplicate case id: {case_id}")
        ids.add(case_id)
        require(isinstance(module, str) and MODULE.fullmatch(module) is not None,
                f"invalid module for {case_id}")
        expected_path = module.replace(".", "/") + ".lean"
        require(case.get("source") == expected_path, f"module/source mismatch: {case_id}")
        path = inside(root, case["source"])
        require(isinstance(case.get("sourceSha256"), str) and SHA256.fullmatch(case["sourceSha256"])
                is not None, f"sourceSha256 is required: {case_id}")
        require(digest(path) == case["sourceSha256"], f"frozen case source changed: {case_id}")
    measurement = manifest.get("measurement")
    require(isinstance(measurement, dict), "measurement is required")
    for key, minimum in (("warmupRuns", 0), ("measuredRuns", 1)):
        require(type(measurement.get(key)) is int and measurement[key] >= minimum,
                f"invalid {key}")
    for key in ("elaborationTimeoutSeconds", "replayTimeoutSeconds", "maxRssBytes"):
        positive_number(measurement.get(key), key)
    require(type(measurement["maxRssBytes"]) is int, "maxRssBytes must be an integer")
    decision = manifest.get("decision")
    require(isinstance(decision, dict) and decision.get("selectionEligible") is False,
            "host-control registration must explicitly disable foundation selection")
    thresholds = decision.get("thresholds")
    require(isinstance(thresholds, dict), "decision thresholds are required")
    reduction = thresholds.get("proofTokenReduction")
    positive_number(reduction, "proofTokenReduction")
    require(reduction < 1, "proofTokenReduction must be less than one")
    for key in ("maxTermNodeRatio", "maxReplayTimeRatio"):
        positive_number(thresholds.get(key), key)
    gates = decision.get("semanticGates")
    require(isinstance(gates, list) and bool(gates), "shared semantic gates are required")
    gate_ids = set()
    for gate in gates:
        require(isinstance(gate, dict) and isinstance(gate.get("id"), str) and bool(gate["id"]),
                "semantic gate needs an id")
        require(gate["id"] not in gate_ids, "duplicate semantic gate")
        gate_ids.add(gate["id"])
        require(gate.get("status") in {"proved", "checked", "unresolved"}, "invalid semantic gate status")
        if gate["status"] == "proved":
            declarations = gate.get("declarations")
            require(isinstance(declarations, list) and bool(declarations),
                    f"proved gate needs named theorem evidence: {gate['id']}")
            for declaration in declarations:
                require(isinstance(declaration, dict) and isinstance(declaration.get("module"), str)
                        and isinstance(declaration.get("name"), str), "malformed theorem evidence")
        if gate["status"] == "checked":
            evidence = gate.get("evidence")
            require(isinstance(evidence, list) and bool(evidence), "checked gate needs pinned evidence records")
            for record in evidence:
                require(isinstance(record, dict) and isinstance(record.get("sha256"), str)
                        and SHA256.fullmatch(record["sha256"]) is not None,
                        "checked evidence needs path/sha256")
                require(digest(inside(root, record.get("path"))) == record["sha256"],
                        f"checked evidence changed: {gate['id']}")
    candidates = manifest.get("candidates")
    require(isinstance(candidates, list) and bool(candidates), "candidate eligibility ledger is required")
    candidate_ids = set()
    for candidate in candidates:
        require(isinstance(candidate, dict) and isinstance(candidate.get("id"), str)
                and bool(candidate["id"]), "candidate needs an id")
        require(candidate["id"] not in candidate_ids, "duplicate candidate id")
        candidate_ids.add(candidate["id"])
        require(isinstance(candidate.get("artifactKind"), str), "candidate artifactKind is required")
        for key in ("rulePinsStatus", "toolchainPinsStatus"):
            require(candidate.get(key) in {"pinned", "unresolved"}, f"invalid candidate {key}")
            if candidate[key] == "pinned":
                require(bool(candidate.get(key.removesuffix("Status"))), f"missing candidate {key} evidence")
    return manifest


def source_snapshot(root: Path) -> dict[str, str]:
    return {str(path.relative_to(root)): digest(path) for _, path in audit_axioms.source_modules(root)}


def config_snapshot(root: Path) -> dict[str, str]:
    return {path: digest(root / path) for path in CONFIG_FILES if (root / path).is_file()}


def artifact_part_paths(directory: Path, module: str) -> list[Path]:
    stem = directory / module.replace(".", "/")
    return [Path(str(stem) + suffix) for suffix in OLEAN_PART_SUFFIXES]


def installed_artifact_snapshot(root: Path) -> dict[str, dict]:
    """Conservative input ledger: all installed project olean parts, not a minimal import closure."""
    directory = root / ".lake/build/lib/lean"
    if not directory.is_dir():
        return {}
    paths = sorted(path for path in directory.rglob("*") if path.is_file() and
                   any(path.name.endswith(suffix) for suffix in OLEAN_PART_SUFFIXES))
    return {path.relative_to(directory).as_posix(): {
        "path": str(path), "resolvedPath": str(path.resolve()), "sha256": digest(path),
        "isSymlink": path.is_symlink(), "bytes": path.stat().st_size,
    } for path in paths}


def prepare_dependency_overlay(root: Path, fresh: Path, module: str) -> dict:
    """Use real directories and dependency file symlinks; never link the measured target.

    Lean resolves a package prefix in the first search root that contains it.
    A target-only fresh root therefore masks same-package installed imports.
    Mirror their artifact files without ever writing into the installed tree.
    """
    fresh.mkdir(parents=True, exist_ok=True)
    target_paths = artifact_part_paths(fresh, module)
    excluded = {path.relative_to(fresh).as_posix() for path in target_paths}
    for path in target_paths:
        require(not path.exists() and not path.is_symlink(),
                f"fresh target part already exists: {path}")
    installed = installed_artifact_snapshot(root)
    dependencies = []
    for relative, record in installed.items():
        if relative in excluded:
            continue
        destination = fresh / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        require(not destination.exists() and not destination.is_symlink(),
                f"fresh dependency destination already exists: {destination}")
        destination.symlink_to(record["resolvedPath"])
        dependencies.append({**record, "relativePath": relative, "symlinkPath": str(destination)})
    target_before = []
    installed_root = root / ".lake/build/lib/lean"
    for path in artifact_part_paths(installed_root, module):
        target_before.append({"path": str(path), "exists": path.is_file(),
                              "sha256": digest(path) if path.is_file() else None,
                              "isSymlink": path.is_symlink()})
    return {"strategy": "normal directories and installed dependency file symlinks; exact target parts excluded",
            "scope": "all installed project olean parts except the target; not a minimal dependency closure",
            "installedRoot": str(installed_root), "freshRoot": str(fresh),
            "dependencies": dependencies, "installedTargetBefore": target_before,
            "excludedTargetParts": sorted(excluded)}


def dependency_overlay_unchanged(overlay: dict) -> bool:
    try:
        return all(Path(record["symlinkPath"]).is_symlink() and
                   str(Path(record["symlinkPath"]).resolve()) == record["resolvedPath"] and
                   digest(Path(record["symlinkPath"])) == record["sha256"]
                   for record in overlay["dependencies"])
    except OSError:
        return False


def preflight(manifest: dict, root: Path, report: Path) -> dict:
    require(report.is_file(), "current axiom audit is required before measurement")
    if "auditReportSha256" in manifest:
        require(digest(report) == manifest["auditReportSha256"], "frozen audit report changed")
    audit = json.loads(report.read_text())
    sources = source_snapshot(root)
    require(audit.get("sources") == sources, "axiom report is stale or omits current Lean sources")
    require(audit.get("buildInputs") == config_snapshot(root), "axiom report build inputs are stale")
    require(audit.get("toolchain") == manifest["toolchain"], "axiom report toolchain mismatch")
    require(set(audit.get("allowedAxioms", [])) == audit_axioms.ALLOWED_AXIOMS,
            "axiom report uses another trust policy")
    source_texts = {module: path.read_text() for module, path in audit_axioms.source_modules(root)}
    for module, source in source_texts.items():
        require(not audit_axioms.source_policy_violations(source), f"source policy failed in {module}")
        code = audit_axioms.code_without_comments_and_strings(source)
        require(re.search(r"\baxiom\b", code) is None, f"authored axiom in {module}")
    declarations = audit_axioms.validate_declarations(audit.get("declarations"),
                                                      audit.get("modules", []), source_texts)
    indexed = {(entry["module"], entry["name"]): entry for entry in declarations}
    for case in manifest["cases"]:
        require(case["module"] in audit.get("modules", []), f"unaudited case: {case['id']}")
    for gate in manifest["decision"]["semanticGates"]:
        if gate["status"] == "proved":
            for declaration in gate["declarations"]:
                evidence = indexed.get((declaration["module"], declaration["name"]))
                require(evidence is not None and evidence["kind"] == "theorem",
                        f"gate theorem absent from audited environment: {gate['id']}")
    return {"status": "passed", "auditReport": str(report), "auditReportSha256": digest(report),
            "leanVersion": audit["leanVersion"], "sourcesSha256": sources,
            "buildInputsSha256": config_snapshot(root),
            "semanticGates": manifest["decision"]["semanticGates"]}


def discover_environment(root: Path, lake: list[str]) -> dict:
    # Query only known tool variables; never dump credentials or the whole environment.
    query = ("import json,os,shutil; keys=" + repr(SAFE_ENV_KEYS) + "; "
             "print(json.dumps({'lean':shutil.which('lean'),"
             "'leanchecker':shutil.which('leanchecker'),'environment':{key:os.environ[key] "
             "for key in keys if key in os.environ}}))")
    result = subprocess.run([*lake, "--no-cache", "env", sys.executable, "-c", query], cwd=root,
                            capture_output=True, text=True, timeout=30)
    require(result.returncode == 0, f"cannot obtain Lake tool environment: {result.stderr}")
    resolved = json.loads(result.stdout)
    for tool in ("lean", "leanchecker"):
        require(isinstance(resolved.get(tool), str) and Path(resolved[tool]).is_file(), f"missing {tool}")
    version = subprocess.run([resolved["lean"], "--version"], cwd=root,
                             env={**os.environ, **resolved["environment"]},
                             capture_output=True, text=True, timeout=30)
    require(version.returncode == 0, "cannot obtain actual Lean version")
    resolved["leanVersion"] = version.stdout.strip()
    resolved["binarySha256"] = {tool: digest(Path(resolved[tool])) for tool in ("lean", "leanchecker")}
    return resolved


def measured_process(command: list[str], root: Path, environment: dict[str, str],
                     timeout: float, rss_limit: int, logs: Path) -> dict:
    logs.parent.mkdir(parents=True, exist_ok=True)
    stdout_path, stderr_path = logs.with_suffix(".stdout"), logs.with_suffix(".stderr")
    started = time.perf_counter()
    usage, timed_out = None, False
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(command, cwd=root, env=environment, stdin=subprocess.DEVNULL,
                                   stdout=stdout, stderr=stderr, start_new_session=(os.name == "posix"))
        if hasattr(os, "wait4"):
            while True:
                pid, status, child_usage = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    process.returncode = os.waitstatus_to_exitcode(status)
                    usage = child_usage
                    break
                if time.perf_counter() - started >= timeout:
                    timed_out = True
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    _, status, usage = os.wait4(process.pid, 0)
                    process.returncode = os.waitstatus_to_exitcode(status)
                    break
                time.sleep(0.01)
        else:
            try:
                process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                process.kill()
                process.wait()
    elapsed = time.perf_counter() - started
    # Polling has finite resolution: an observation beyond the frozen cap is
    # conservatively unknown even if the child exited just before observation.
    timed_out = timed_out or elapsed >= timeout
    peak_rss = None
    if usage is not None and sys.platform in {"darwin", "linux"}:
        peak_rss = int(usage.ru_maxrss) * (1 if sys.platform == "darwin" else 1024)
    status, reason = "measured", None
    if timed_out:
        status, reason = "unknown", "timeout"
    elif process.returncode != 0:
        status, reason = "failed", "processError"
    elif peak_rss is not None and peak_rss > rss_limit:
        status, reason = "unknown", "rssGuardrailExceeded"
    return {"command": command, "status": status, "reason": reason, "exitCode": process.returncode,
            "elapsedSeconds": elapsed, "peakRssBytes": peak_rss,
            "rssMeasurement": "direct-child wait4 high-water mark" if peak_rss is not None else "unresolved",
            "rssEnforcement": "post-run guardrail; not a hard memory limit",
            "timeoutSeconds": timeout, "maxRssBytes": rss_limit,
            "stdout": {"path": str(stdout_path), "sha256": digest(stdout_path)},
            "stderr": {"path": str(stderr_path), "sha256": digest(stderr_path)}}


def measure_case(case: dict, manifest: dict, root: Path, tools: dict, artifacts: Path) -> dict:
    settings = manifest["measurement"]
    source_bytes = (root / case["source"]).stat().st_size
    runs = []
    total = settings["warmupRuns"] + settings["measuredRuns"]
    base_environment = {**os.environ, **tools["environment"]}
    installed_before = installed_artifact_snapshot(root)
    for index in range(total):
        run_dir = artifacts / case["id"] / str(index)
        fresh = run_dir / "fresh"
        overlay = prepare_dependency_overlay(root, fresh, case["module"])
        olean = fresh / (case["module"].replace(".", "/") + ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        elab_command = [tools["lean"], "-R", str(root), "-o", str(olean), str(root / case["source"])]
        elaboration = measured_process(elab_command, root, base_environment,
                                       settings["elaborationTimeoutSeconds"], settings["maxRssBytes"],
                                       run_dir / "elaboration")
        run = {"index": index, "warmup": index < settings["warmupRuns"],
               "dependencyOverlay": overlay, "elaboration": elaboration}
        runs.append(run)
        if elaboration["status"] != "measured":
            break
        if not olean.is_file():
            elaboration.update(status="failed", reason="missingFreshArtifact")
            break
        if not dependency_overlay_unchanged(overlay):
            elaboration.update(status="failed", reason="dependencyOverlayChanged")
            break
        parts = [path for path in artifact_part_paths(fresh, case["module"]) if path.is_file()]
        if any(path.is_symlink() for path in parts):
            elaboration.update(status="failed", reason="freshTargetIsSymlink")
            break
        run["artifact"] = {"module": case["module"], "path": str(olean),
                           "sha256": digest(olean), "bytes": olean.stat().st_size,
                           "totalPartBytes": sum(p.stat().st_size for p in parts if p.is_file()),
                           "parts": [{"path": str(p), "sha256": digest(p), "bytes": p.stat().st_size}
                                     for p in parts if p.is_file()]}
        replay_environment = {**base_environment, "LEAN_PATH": str(fresh) + os.pathsep +
                              base_environment.get("LEAN_PATH", "")}
        replay_command = [tools["leanchecker"], "--fresh", case["module"]]
        run["replayLeanPath"] = replay_environment["LEAN_PATH"]
        run["kernelReplay"] = measured_process(replay_command, root, replay_environment,
                                                settings["replayTimeoutSeconds"], settings["maxRssBytes"],
                                                run_dir / "replay")
        if not dependency_overlay_unchanged(overlay):
            run["kernelReplay"].update(status="failed", reason="dependencyOverlayChanged")
            break
        if any(not Path(part["path"]).is_file() or Path(part["path"]).is_symlink() or
               digest(Path(part["path"])) != part["sha256"] for part in run["artifact"]["parts"]):
            run["kernelReplay"].update(status="failed", reason="freshArtifactChanged")
            break
        if run["kernelReplay"]["status"] != "measured":
            break
    measured = [run for run in runs if not run["warmup"]]
    summary = {}
    for stage in ("elaboration", "kernelReplay"):
        samples = [run[stage] for run in measured if stage in run and run[stage]["status"] == "measured"]
        seconds = [sample["elapsedSeconds"] for sample in samples]
        rss = [sample["peakRssBytes"] for sample in samples if sample["peakRssBytes"] is not None]
        summary[stage] = {"successfulSamples": len(samples),
                          "medianSeconds": statistics.median(seconds) if seconds else None,
                          "rangeSeconds": [min(seconds), max(seconds)] if seconds else None,
                          "maxPeakRssBytes": max(rss) if rss else None,
                          "complete": len(samples) == settings["measuredRuns"]}
    installed_unchanged = installed_artifact_snapshot(root) == installed_before
    complete = installed_unchanged and len(runs) == total and all(
        run["elaboration"]["status"] == "measured" and
        run.get("kernelReplay", {}).get("status") == "measured" for run in runs)
    return {"id": case["id"], "module": case["module"], "source": case["source"],
            "sourceSha256": case["sourceSha256"], "sourceBytes": source_bytes,
            "status": "measured" if complete else "incomplete", "runs": runs, "summary": summary,
            "installedArtifactIntegrity": {"status": "unchanged" if installed_unchanged else "changed",
                                           "before": installed_before},
            "kernelTermNodes": {"status": "unresolved", "reason": "No frozen kernel-expression exporter"},
            "handwrittenProofTokens": {"status": "unresolved", "reason": "No frozen proof-token classifier"}}


def machine_record() -> dict:
    memory = None
    try:
        memory = os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE")
    except (OSError, ValueError):
        pass
    return {"system": platform.system(), "release": platform.release(), "machine": platform.machine(),
            "processor": platform.processor(), "logicalCpuCount": os.cpu_count(), "physicalMemoryBytes": memory}


def write_report(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                     prefix=".experiment-", delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write("\n")
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def run_experiment(manifest_path: Path, root: Path, lake: list[str], report_path: Path,
                   audit_path: Path, selected: list[str] | None = None, *, validate_only: bool = False) -> dict:
    report_path.unlink(missing_ok=True)
    require(bool(lake) and not {"--update", "--try-cache"}.intersection(lake),
            "Lake update/cache-download options are not measurement commands")
    manifest_digest = digest(manifest_path)
    manifest = validate_manifest(json.loads(manifest_path.read_text()), root)
    cases = manifest["cases"]
    if selected:
        require(set(selected) <= {case["id"] for case in cases}, "unknown selected case")
        cases = [case for case in cases if case["id"] in selected]
    snapshot = source_snapshot(root)
    configs = config_snapshot(root)
    runner_digest = digest(Path(__file__))
    audit_tool_digest = digest(Path(audit_axioms.__file__))
    report = {"schemaVersion": 1, "kind": "host-control", "protocolVersion": manifest["protocolVersion"],
              "createdAt": datetime.now(timezone.utc).isoformat(), "manifest": str(manifest_path),
              "manifestSha256": manifest_digest, "runnerSha256": runner_digest,
              "auditToolSha256": audit_tool_digest,
              "machine": machine_record(), "measurementSettings": manifest["measurement"],
              "selectedCaseIds": [case["id"] for case in cases], "cases": [],
              "foundationDecision": {"status": "not-performed", "selectionEligible": False,
                                     "reason": "Host measurements do not select an object foundation"},
              "decisionRegistration": manifest["decision"], "candidateEligibility": manifest["candidates"],
              "registrationBoundary": "Host-control registration only; candidate-rule pins, project review, and foundation selection remain separate gates",
              "cachePolicy": "Fresh target artifacts and separate processes; existing dependency artifacts and OS caches reused; no cold-cache claim",
              "replayBoundary": "Separate invocation of the same Lean kernel, replaying all constants into a fresh environment; not an external verifier"}
    if validate_only:
        report.update(status="registered", measurementPerformed=False)
        write_report(report_path, report)
        return report
    try:
        report["preflight"] = preflight(manifest, root, audit_path)
    except (ExperimentError, audit_axioms.AuditError, OSError, ValueError) as error:
        report.update(status="unresolved", measurementPerformed=False,
                      preflight={"status": "unresolved", "reason": str(error)})
        write_report(report_path, report)
        return report
    tools = discover_environment(root, lake)
    require(tools["leanVersion"] == report["preflight"]["leanVersion"], "actual Lean build differs from audit")
    report["tools"] = {key: tools[key] for key in ("lean", "leanchecker", "leanVersion", "binarySha256")}
    report["toolEnvironment"] = {key: value for key, value in tools["environment"].items() if key != "PATH"}
    artifacts = report_path.parent / (report_path.stem + ".artifacts") / uuid.uuid4().hex
    build_command = [*lake, "--no-cache", "build", *(case["module"] for case in cases)]
    # Use the same process-group cleanup for prerequisites; no orphan Lean
    # workers survive a timed-out Lake invocation. This run is outside metrics.
    report["prerequisiteBuild"] = measured_process(
        build_command, root, dict(os.environ), 300, manifest["measurement"]["maxRssBytes"],
        artifacts / "prerequisites" / "build")
    report["prerequisiteBuild"]["excludedFromBenchmark"] = True
    if report["prerequisiteBuild"]["status"] != "measured":
        report.update(status="unresolved", measurementPerformed=False)
        write_report(report_path, report)
        return report
    installed_before = installed_artifact_snapshot(root)
    report["installedArtifactsBefore"] = installed_before
    for case in cases:
        report["cases"].append(measure_case(case, manifest, root, tools, artifacts))
    report["measurementPerformed"] = True
    report["status"] = "measured" if all(case["status"] == "measured" for case in report["cases"]) else "incomplete"
    if installed_artifact_snapshot(root) != installed_before:
        report.update(status="invalidated", invalidationReason="Installed project dependency/target artifacts changed during measurements")
    report["installedArtifactIntegrity"] = "unchanged" if installed_artifact_snapshot(root) == installed_before else "changed"
    try:
        stable = (source_snapshot(root) == snapshot and config_snapshot(root) == configs and
                  digest(manifest_path) == manifest_digest and digest(Path(__file__)) == runner_digest and
                  digest(Path(audit_axioms.__file__)) == audit_tool_digest)
    except (OSError, audit_axioms.AuditError):
        stable = False
    if not stable:
        report.update(status="invalidated", invalidationReason="Sources, configuration, registration, or runner changed during measurements")
    try:
        binaries_stable = all(digest(Path(tools[tool])) == tools["binarySha256"][tool]
                              for tool in ("lean", "leanchecker"))
    except OSError:
        binaries_stable = False
    if not binaries_stable:
        report.update(status="invalidated", invalidationReason="Measured tool binary changed")
    write_report(report_path, report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--report", type=Path, default=Path(".lake/build/experiments/host-controls.json"))
    parser.add_argument("--audit-report", type=Path, default=Path(".lake/build/audit/axioms.json"))
    parser.add_argument("--case", action="append", dest="selected")
    parser.add_argument("--validate-only", action="store_true")
    options = parser.parse_args()
    root = options.root.resolve()
    report_path = options.report if options.report.is_absolute() else root / options.report
    report_path.unlink(missing_ok=True)
    try:
        manifest_path = options.manifest if options.manifest.is_absolute() else root / options.manifest
        result = run_experiment(manifest_path.resolve(), root, shlex.split(options.lake), report_path,
                                options.audit_report if options.audit_report.is_absolute() else root / options.audit_report,
                                options.selected, validate_only=options.validate_only)
    except (ExperimentError, audit_axioms.AuditError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"Experiment error: {error}", file=sys.stderr)
        return 1
    print(f"Host-control registration: {result['protocolVersion']}; status: {result['status']}")
    print(f"Report: {report_path}")
    print("No foundation selection performed.")
    return 0 if result["status"] in {"registered", "measured"} else 2


if __name__ == "__main__":
    raise SystemExit(main())
