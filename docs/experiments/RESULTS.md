# Host-control results, protocol 2

Local measurements on 2026-11-14. These are profiles of the host controls, not a comparison of object equality foundations or native sized rules. No foundation was selected.

## Registered procedure

One warm-up pair followed by five source-elaboration and five fresh-kernel-replay samples per artifact. Limits remained 300 seconds for elaboration, 60 seconds for replay, and a 1 GiB observed RSS guardrail. Fresh target artifacts were used; dependency artifacts and OS caches were reused.

Each replay used the same pinned Lean kernel in a separate process and rebuilt its complete declaration environment. It is not an independent kernel implementation. All registered samples completed within their limits.

| Host control | Elaboration median (range), seconds | Fresh replay median (range), seconds | Maximum child RSS, MiB | Target `.olean` bytes |
|---|---:|---:|---:|---:|
| `exp-a-abstract-client` | 0.507 (0.302–0.806) | 43.326 (40.400–52.100) | 457.0 | 226,800 |
| `exp-b-translation` | 0.549 (0.523–0.697) | 41.202 (40.231–45.636) | 438.8 | 788,576 |

Machine: `Darwin` / `arm64`, 8 logical CPUs. Exact host, tool-version, and binary hashes are retained in the raw report.

The replay times include the imported dependency environment. The two artifacts perform different work; their times are not evidence that one theory is better. Handwritten proof-token and kernel-expression-node metrics remain unresolved, so the registered richer-foundation improvement criterion cannot be evaluated.

## Provenance and retained observations

- Registration: [host-controls-v2.json](host-controls-v2.json).
- Registration SHA-256: `028436ca867a0b06da76d09b9c8e9128b84e9e248ab53033094843c327fc39c7`.
- Raw report: `.lake/build/experiments/host-controls-v2.json`, SHA-256 `031d1ce046eb25c58f6d2dcb62ed7ce5225d23674735ebf075ef69cdcff9c80c`.
- Audited source/configuration report SHA-256: `f31d7bcc4beb6db6bda12f7ebbc2c18277eada9c870ae18b430d68ddb39a0589`.
- Raw stdout/stderr, fresh target parts, dependency-overlay hashes, tool hashes, and installed-artifact integrity observations are retained in the report and its adjacent artifact directory.
- The first registration and `.lake/build/experiments/host-controls-attempt-1.json` are retained. Its queue replay failed before checking because a sibling dependency was hidden by the initial overlay. Its successful certificate samples remain protocol 1 data and are not pooled into this table.
- The protocol 2 infrastructure correction was checked against a real same-package dependency and a deliberately stale installed target before these runs. Sources, inputs, thresholds, and budgets were unchanged.

## Functional and semantic scope

All 70 finite observations match independent queue-cost and certificate-metric recurrences. The abstract queue client imports no concrete implementation module. The open certificate sequence equation has a checked propositional proof, while `rfl` fails for that same open equation.

The host proofs cover their stated operation contracts, height bounds, denotation, and restricted annotation erasure. They do not implement a native parametric quantifier, a full object calculus, the composed integration probe, or the M2 checker/consistency/normalization/elaboration theorems. The measured snapshot predates the [coverage gate](../COVERAGE.md); its archived audit is retained as `.lake/build/experiments/frozen-audit-f31d7bcc4beb6db6bda12f7ebbc2c18277eada9c870ae18b430d68ddb39a0589.json`. These timings do not include the later checker changes or establish their soundness. A new timing run after source changes needs a new registration; the protocol 1/2 files remain immutable historical records.
