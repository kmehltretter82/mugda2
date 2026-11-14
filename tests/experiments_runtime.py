#!/usr/bin/env python3
"""Validate host-control observations against independent finite recurrences."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/experiments/host-controls-v2.json"
BINARY = ROOT / ".lake/build/bin/mugda2-experiments"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def check_client_imports() -> list[str]:
    library = (ROOT / ".lake/build/lib/lean").resolve()
    agenda, visited = ["Mugda2.Experiments.QueueClient"], set()
    allowed = {"Mugda2.Experiments.QueueClient", "Mugda2.Experiments.QueueContract",
               "Mugda2.Queue", "Mugda2.Cost"}
    while agenda:
        module = agenda.pop()
        if module in visited:
            continue
        require(module in allowed, f"concrete implementation leaked into abstract client: {module}")
        visited.add(module)
        source = module.replace(".", "/") + ".lean"
        completed = subprocess.run(["lake", "--no-cache", "env", "lean", "--deps", source],
                                   cwd=ROOT, text=True, capture_output=True, timeout=30)
        require(completed.returncode == 0, f"cannot inspect compiler imports: {completed.stderr}")
        for line in completed.stdout.splitlines():
            dependency = Path(line).resolve()
            if dependency.is_relative_to(library):
                agenda.append(".".join(dependency.relative_to(library).with_suffix("").parts))
    require(visited == allowed, "abstract client import closure changed")
    return sorted(visited)


def check_constructor_equation() -> dict:
    statement = """import Mugda2.Experiments.SizedCertificates
open Mugda2.Experiments.SizedCertificates
example (helper : Preprocessor) (children : List Certificate) :
    normalize helper (.sequence children) =
      .sequence (children.attach.map fun child => normalize helper (helper.run child.val)) := by
"""
    command = ["lake", "--no-cache", "env", "lean", "--json", "--stdin"]
    positive = subprocess.run(command, cwd=ROOT, input=statement + "  exact normalize_sequence helper children\n",
                              text=True, capture_output=True, timeout=30)
    require(positive.returncode == 0, f"open constructor theorem failed: {positive.stdout}{positive.stderr}")
    negative = subprocess.run(command, cwd=ROOT, input=statement + "  rfl\n",
                              text=True, capture_output=True, timeout=30)
    messages = [json.loads(line) for line in negative.stdout.splitlines() if line.strip()]
    errors = [message for message in messages if message.get("severity") == "error"]
    require(negative.returncode != 0 and len(errors) == 1 and
            "Tactic `rfl` failed" in errors[0].get("data", ""),
            "open constructor equation's non-definitional check failed for an unexpected reason")
    return {"classification": "P", "provedBy": "normalize_sequence", "reflexivityFailure": errors[0]}


def main() -> int:
    report = ROOT / ".lake/build/experiments/runtime-results.json"
    report.unlink(missing_ok=True)
    manifest = json.loads(MANIFEST.read_text())
    ladder = manifest["runtimeInputs"]
    expected = {}
    for n in ladder["queueSizes"]:
        expected[("EXP-A-host-control", n)] = {
            "inputSize": n, "budget": n * (n + 3), "batchedCost": 3 * n,
            "singleListCost": n * (n + 3) // 2,
        }
    for depth in ladder["certificateDepths"]:
        for counter in ladder["certificateCounters"]:
            expanded = 1
            for _ in range(depth):
                expanded = 1 + counter * expanded
            for helper in ("identity", "neutral"):
                if helper == "identity" or depth == 0:
                    result_nodes, result_height = 5 * depth + 1, 2 * depth
                elif counter == 0:
                    result_nodes, result_height = 4, 2
                elif counter == 1:
                    result_nodes, result_height = 3 * depth + 1, depth + 1
                else:
                    result_nodes, result_height = 4 * depth + 1, 2 * depth
                expected[("EXP-B-host-control", depth, counter, helper)] = {
                    "depth": depth, "counter": counter, "helper": helper,
                    "sourceHeight": 2 * depth, "sourceSyntaxNodes": 5 * depth + 1,
                    "sourceCounterBits": depth * (1 + max(1, counter.bit_length())),
                    "expandedEvents": expanded, "resultHeight": result_height,
                    "resultSyntaxNodes": result_nodes, "resultExpandedEvents": expanded,
                }
    binary_hash = hashlib.sha256(BINARY.read_bytes()).hexdigest()
    import_closure = check_client_imports()
    constructor_equation = check_constructor_equation()
    result = subprocess.run([str(BINARY)], cwd=ROOT, capture_output=True, text=True, timeout=30)
    require(result.returncode == 0 and not result.stderr, f"control executable failed: {result.stderr}")
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    require(len(rows) == len(expected), "missing or extra control observations")
    require(len(result.stdout) < 100_000, "expanded event data leaked into a compact observation")
    observed = set()
    for row in rows:
        require(row["schemaVersion"] == "mugda2.experiments.v1", "wrong schema")
        require(row["evidence"] == "measured", "wrong finite evidence label")
        if row["experiment"] == "EXP-A-host-control":
            key = (row["experiment"], row["inputSize"])
            require(row["endpoint"] == "host-Lean-declared-abstract-steps", "wrong cost endpoint")
            booleans = ["batchedCorrect", "singleListCorrect", "batchedWithinBudget", "singleListWithinBudget"]
        else:
            require(row["experiment"] == "EXP-B-host-control", "unexpected experiment")
            key = (row["experiment"], row["depth"], row["counter"], row["helper"])
            require(row["endpoint"] == "raw-certificate-AST", "wrong erasure endpoint")
            booleans = ["heightPreserved", "eventsPreserved"]
        require(key in expected and key not in observed, f"unregistered or duplicate case: {key}")
        observed.add(key)
        for field, value in expected[key].items():
            require(type(row[field]) is type(value) and row[field] == value,
                    f"wrong {field} at {key}: {row[field]} != {value}")
        require(all(row[field] is True for field in booleans), f"failed finite obligation: {key}")
    require(observed == set(expected), "control ladder coverage drift")
    require(hashlib.sha256(BINARY.read_bytes()).hexdigest() == binary_hash, "binary changed during observations")
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps({
        "schemaVersion": 1, "status": "passed", "observations": rows,
        "binarySha256": binary_hash, "manifestSha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
        "validatorSha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "abstractClientProjectImports": import_closure,
        "openConstructorEquation": constructor_equation,
        "scope": "Finite host controls; no foundation selection or native cost theorem.",
    }, indent=2) + "\n")
    print(f"{len(rows)}/{len(expected)} host-control observations match independent recurrences")
    print(f"Report: {report.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
