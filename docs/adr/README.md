# Architecture decision records

These records make the M0 policies in [the roadmap](../../MILESTONES.md) explicit.
They distinguish policies adopted for continued implementation from foundational
choices still awaiting M1.5 evidence. Recording a policy does not prove its
implementation correct or complete the M0 exit gate.

| Record | Policy status | Remaining decision |
|---|---|---|
| [ADR-01: equality](01-equality-policy.md) | Conditional policy adopted | `DEC-EQ-001`: select and specify the object equality after EXP-A |
| [ADR-02: Lean boundary](02-lean-proof-boundary.md) | Boundary policy adopted | `DEC-HOST-001`: select the first supported object/host bridge |
| [ADR-03: core extensions](03-core-extension-reverification.md) | Reverification policy adopted | `DEC-REC-001`: translation or native sized rule after EXP-B |
| [ADR-04: quantities and cost](04-quantitative-judgments.md) | Reporting policy adopted | `DEC-COST-001`: select the first language cost model and endpoint |

The decision identifiers refer to [Requirements Section 9](../../REQUIREMENTS.md#9-open-decisions-and-controlled-experiments).
Each record states its consequences and the evidence needed to change its status.
An unresolved choice remains unresolved when a preparatory example passes.

## M0 evidence and remaining work

Assessment date: **2026-11-14**. This is a source inventory, not an approval record
or a completed experiment report.

| Exit condition | Evidence in this repository | What remains |
|---|---|---|
| Requirements baseline | [Proposed v0.1 requirements](../../REQUIREMENTS.md) with acceptance criteria and open decisions | Adoption and review of outstanding scope/decision choices; record revisions explicitly |
| Teaching baseline | [Three-level concept guide](../index.html) | Check rendering, accessibility, examples, links, and status accuracy against the supported implementation |
| Experiment protocol | [EXP-A and EXP-B protocol v0.1](../EXPERIMENTS.md) | Freeze candidate manifests, sources, exact equations, opacity boundaries, metrics, budgets, numerical improvement thresholds, and decision owner before comparison runs |
| ADRs 01–04 | The four records linked above | Foundational selections remain gated by M1.5; implementation evidence is tracked separately |
| Preparatory implementation | [Giralf cost prototype](../../Mugda2/Giralf.lean) | Preserve its limited proof scope; do not count it as a completed foundation comparison or the L1 pipeline |
| Host controls and timing registration | [M1.5 controls](../experiments/README.md) and [host registration](../experiments/host-controls-v2.json) | Exact object-candidate rule/toolchain pins and the integration comparison remain unresolved; host timing registration does not freeze those missing fragments |

The Giralf module contains a host-Lean queue/client benchmark and a separate
small source-to-IR cost calculus. These are useful preparatory artifacts. The
repository does not yet contain the frozen cross-foundation comparison or the
EXP-B comparison required for M1.5. **M0 remains in progress.**

## Updating a record

Preserve its number and the associated requirement IDs. Record the date, changed
scope, evidence, and affected rules or acceptance conditions. A selection needs
the versioned experiment manifest, retained unsuccessful runs, assumption ledger,
and decision report described by the protocol. Passing a sample, invoking a
fallback without recording its trigger, or importing a Lean package does not
silently resolve an open decision.
