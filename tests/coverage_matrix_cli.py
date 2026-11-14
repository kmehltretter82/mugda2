#!/usr/bin/env python3
"""Exhaust all Bool × Bool pattern matrices against their finite truth tables."""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import tempfile

from checker_cli import BINARY, ROOT, require, run_case, sha256_file


def main() -> int:
    report = ROOT / ".lake/build/reports/coverage-matrices.json"
    report.unlink(missing_ok=True)
    binary_hash = sha256_file(BINARY)
    patterns = list(itertools.product(("x", "tt", "ff"), ("y", "tt", "ff")))
    inputs = list(itertools.product(("tt", "ff"), repeat=2))
    observations, failures = [], []
    with tempfile.TemporaryDirectory(prefix="mugda2-coverage-") as directory:
        path = Path(directory) / "matrix.ma"
        for mask in range(1 << len(patterns)):
            rows = [row for index, row in enumerate(patterns) if mask & (1 << index)]
            if mask % 2:
                rows.reverse()
            # Independent reference: enumerate all four actual input pairs.
            missing = [values for values in inputs if not any(
                all(pattern in {"x", "y"} or pattern == value
                    for pattern, value in zip(row, values)) for row in rows)]
            source = ("data Bool : Set { tt : Bool; ff : Bool }\n"
                      "fun f : Bool -> Bool -> Bool {\n" +
                      ";\n".join(f"  f {a} {b} = tt" for a, b in rows) + "\n}\n")
            path.write_text(source)
            expected = ({"status": "rejected", "diagnostic": "coverage"} if missing
                        else {"status": "accepted"})
            case = {"id": f"coverage-matrix/{mask:03x}", "path": str(path), "expected": expected}
            try:
                result = run_case(case)
                observations.append({"mask": mask, "rows": rows, "missing": missing,
                                     "sourceSha256": result["sourceSha256"],
                                     "result": result["result"]})
            except (AssertionError, KeyError, ValueError) as error:
                failures.append({"mask": mask, "rows": rows, "missing": missing,
                                 "error": str(error)})
    require(sha256_file(BINARY) == binary_hash, "checker binary changed during matrix checks")
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps({
        "schemaVersion": 1, "checkerBinarySha256": binary_hash,
        "validatorSha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "All subsets of nine Bool × Bool wildcard/constructor rows; all four inputs.",
        "passed": observations, "failures": failures,
    }, indent=2) + "\n")
    print(f"{len(observations)}/{1 << len(patterns)} coverage matrices agree with finite truth tables")
    for failure in failures[:5]:
        print(f"FAIL {failure['mask']:03x}: {failure['error']}")
    print(f"Report: {report.relative_to(ROOT)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
