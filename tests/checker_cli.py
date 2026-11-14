#!/usr/bin/env python3
"""Check semantic expectations through the same JSON CLI used by people/tools."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/mugda2"
FLAGS = {
    "checkerFuel": "--fuel",
    "comparisonFuel": "--comparison-fuel",
    "closureFuel": "--closure-fuel",
    "lexerFuel": "--lex-fuel",
    "parserFuel": "--parse-fuel",
}
EXIT_CODES = {"accepted": 0, "rejected": 1, "unknown": 2}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run_case(case: dict) -> dict:
    command = [str(BINARY), "check"]
    for budget, value in case.get("budget", {}).items():
        require(budget in FLAGS, f"unknown budget: {budget}")
        require(type(value) is int and value >= 0, f"invalid budget: {budget}={value}")
        command += [FLAGS[budget], str(value)]
    command.append(case["path"])
    completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=30)
    require(not completed.stderr, f"unexpected stderr: {completed.stderr}")
    result = json.loads(completed.stdout)
    require(result["schemaVersion"] == "mugda2.check.v1", "wrong schema")
    require(result["checker"] == "legacy-m1", "wrong checker")
    require(result["source"] == case["path"], "wrong source path")
    require(result["baseline"] == "b0c5b53c92673e4a7d57b218b4050690e719f0e7", "wrong baseline")
    status = result["status"]
    require(status in EXIT_CODES, f"invalid status: {status}")
    require(completed.returncode == EXIT_CODES[status], "exit code does not match JSON status")
    if status == "rejected":
        require(bool(result["diagnostic"]["message"]), "missing rejection message")
        span = result["diagnostic"]["span"]
    elif status == "unknown":
        require(result["reason"] in {"outOfFuel", "unsupportedCoverage"}, "wrong uncertainty reason")
        require(bool(result["context"]), "missing uncertainty context")
        span = result["span"]
    else:
        require(isinstance(result["declarations"], list), "missing accepted declarations")
        span = None
    if span is not None:
        require(span == {
            "startByte": 0, "endByte": len((ROOT / case["path"]).read_bytes()), "scope": "document"
        }, "wrong document byte span")
    for key, expected_value in case.get("budget", {}).items():
        require(result["budget"][key] == expected_value, f"budget ignored: {key}")

    expected = case["expected"]
    require(status == expected["status"], f"expected {expected}, observed {result}")
    if status == "rejected":
        require("diagnostic" in expected, "rejection expectation must name an exact category")
        require(result["diagnostic"]["category"] == expected["diagnostic"],
                f"expected {expected}, observed {result}")
    if status == "unknown":
        require(expected.get("reason") == result["reason"], "wrong expected uncertainty reason")
        if "context" in expected:
            require(expected["context"] == result["context"],
                    f"expected uncertainty at {expected['context']}, observed {result['context']}")
        else:
            require(expected.get("stage") == "coverage" and result["reason"] == "unsupportedCoverage",
                    "uncertainty expectation must name its stage")
            require("coverage" in result["context"].lower(), "missing coverage stage in context")
    return {"id": case["id"], "command": command, "expected": expected,
            "sourceSha256": sha256_file(ROOT / case["path"]),
            "exitCode": completed.returncode, "result": result}


def main() -> int:
    report = ROOT / ".lake/build/reports/checker-results.json"
    # A malformed manifest or an interrupted run must not leave an earlier green report.
    report.unlink(missing_ok=True)
    binary_sha256 = sha256_file(BINARY)
    legacy = json.loads((ROOT / "tests/legacy/manifest.json").read_text())
    modern = json.loads((ROOT / "tests/cases/manifest.json").read_text())
    coverage = json.loads((ROOT / "tests/coverage/manifest.json").read_text())
    require(legacy["version"] == modern["version"] == 1, "unsupported manifest version")
    require(coverage["version"] == 1, "unsupported coverage manifest version")
    all_cases = legacy["cases"] + modern["cases"] + coverage["cases"]
    ids = [case["id"] for case in all_cases]
    require(len(ids) == len(set(ids)), "duplicate case ID")
    sources = {str(p.relative_to(ROOT)) for p in (ROOT / "tests/legacy/examples").rglob("*.ma")}
    require(sources == {case["path"] for case in legacy["cases"]}, "legacy corpus inventory drift")
    coverage_sources = {str(p.relative_to(ROOT)) for p in (ROOT / "tests/coverage").glob("*.ma")}
    require(coverage_sources == {case["path"] for case in coverage["cases"]},
            "coverage corpus inventory drift")
    baseline = json.loads((ROOT / "tests/legacy/baseline.json").read_text())
    for record in baseline["files"]:
        if record["source"].endswith(".ma"):
            require(sha256_file(ROOT / record["path"]) == record["sha256"],
                    f"pinned example changed: {record['path']}")

    observations, failures, pending = [], [], []
    for case in all_cases:
        require((ROOT / case["path"]).is_file(), f"missing source: {case['path']}")
        if case["expected"] is None:
            require(bool(case.get("unresolved")), "pending case needs an unresolved obligation")
            pending.append(case["id"])
            continue
        try:
            observations.append(run_case(case))
            print(f"PASS {case['id']}")
        except (AssertionError, KeyError, ValueError, subprocess.TimeoutExpired) as error:
            failures.append({"id": case["id"], "error": str(error)})
            print(f"FAIL {case['id']}: {error}", file=sys.stderr)

    # Harness/transport failures have distinct exit codes and cannot count as rejections.
    for args, expected_code in [(["check"], 64), (["check", "--fuel", "-1", "missing.ma"], 64),
                                (["check", "tests/does-not-exist.ma"], 74)]:
        completed = subprocess.run([str(BINARY), *args], cwd=ROOT, capture_output=True, timeout=30)
        if completed.returncode != expected_code or completed.stdout:
            failures.append({"id": f"cli/{args}", "error": "wrong harness failure outcome"})

    # Exercise the actual JSON transport with quotes, backslashes, control bytes,
    # and multibyte Unicode in a filename and an unexpected source token.
    with tempfile.TemporaryDirectory(prefix="mugda2-json-") as temporary:
        path = Path(temporary) / 'λ-"\\\n🌱.ma'
        path.write_text('data Ω : Set { τέλος : Ω }\n', encoding="utf-8")
        try:
            observation = run_case({
                "id": "cli/json-unicode-escaping", "path": str(path),
                "expected": {"status": "rejected", "diagnostic": "parse"},
            })
            require(observation["result"]["diagnostic"]["message"] == "Unexpected character: Ω",
                    "Unicode diagnostic changed during decoding/encoding")
            observations.append(observation)
            print("PASS cli/json-unicode-escaping")
        except (AssertionError, KeyError, ValueError, subprocess.TimeoutExpired) as error:
            failures.append({"id": "cli/json-unicode-escaping", "error": str(error)})
        invalid_path = Path(temporary) / "invalid-utf8.ma"
        invalid_path.write_bytes(b"\xc0\x80")
        completed = subprocess.run([str(BINARY), "check", str(invalid_path)],
                                   cwd=ROOT, capture_output=True, timeout=30)
        if completed.returncode != 74 or completed.stdout or b"Invalid UTF-8" not in completed.stderr:
            failures.append({"id": "cli/invalid-utf8", "error": "invalid source encoding was not an I/O failure"})

    if sha256_file(BINARY) != binary_sha256:
        failures.append({"id": "checker-binary", "error": "checker binary changed during this run"})
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps({
        "schemaVersion": 1, "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "checkerBinarySha256": binary_sha256,
        "checkerSourcesSha256": {
            path: sha256_file(ROOT / path)
            for path in ("Main.lean", "Mugda2/Checker.lean", "Mugda2/Json.lean",
                         "Mugda2/Legacy/Core.lean", "Mugda2/Legacy/Checking.lean",
                         "Mugda2/Coverage/Legacy.lean", "Mugda2/Coverage/Matrix.lean")
        },
        "manifestSha256": {
            path: sha256_file(ROOT / path)
            for path in ("tests/legacy/manifest.json", "tests/cases/manifest.json",
                         "tests/coverage/manifest.json")
        },
        "baseline": baseline["revision"], "passed": observations,
        "failures": failures, "pending": pending,
    }, indent=2) + "\n")
    print(f"{len(observations)}/{len(observations) + len(failures)} asserted cases passed; "
          f"{len(pending)} classified legacy sources still need reviewed expectations")
    print(f"Report: {report.relative_to(ROOT)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
