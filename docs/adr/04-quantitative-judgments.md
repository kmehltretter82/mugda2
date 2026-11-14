# ADR-04: four separate quantitative judgments

**Date:** 2026-11-14\
**Status:** Reporting policy adopted from M0; first language cost model open.\
**Decision:** `DEC-COST-001`.\
**Requirements:** `REQ-COST-001`–`REQ-COST-004`, `REQ-EXT-001`, `REQ-CERT-001`, `REQ-CERT-002`.

## Context

A terminating program may run for exponentially many events. A small input or
compact certificate may describe a long execution, and fast certificate checking
does not imply fast certificate generation. These quantities must not substitute
for one another in a release claim.

## Policy

Every benchmark report keeps four quantities visible:

| Quantity | Required specification |
|---|---|
| Input/output encoding size | Encoding, size parameter, and whether the measure counts bits, cells, AST nodes, or another representation |
| Construction cost | Events and endpoint of the generator producing the instance/program/certificate |
| Algorithm execution cost | Counted events, evaluation strategy, sharing policy, units, and source/IR endpoint |
| Certificate size and checking cost | Encoded certificate length and checker cost as separate fields, with their parameters and certificate-generation cost separately stated |

For each cost theorem, specify the relation actually proved:

| Claim | Preservation needed across a transformation |
|---|---|
| Transfer a source upper bound | Target cost no larger than source cost, or a separately justified overhead relation |
| Transfer a source lower bound | Target cost no smaller than source cost, or a relation sufficient for the stated lower bound |
| Preserve an exact event count | Equality of the named source and target counts |

Returned-value preservation alone supplies none of these cost relations. Keep
inspection, pivot, arithmetic, allocation, and bit-operation metrics distinct.
Finite observed timings remain measurements at the recorded inputs and machine;
they do not establish asymptotic theorems or intrinsic complexity differences
between foundations.

## Current evidence and limitations

In [the Giralf prototype](../../Mugda2/Giralf.lean), the small calculus counts
explicit natural-number `tick` charges. Its source/IR theorem preserves these
charges exactly. It does not count every evaluator action or establish a native
machine-time or allocation bound.

The separate queue example counts declared abstract operation costs: enqueue
charges one step in `BatchedQ`, and reversal-based dequeue charges the rear-list
length plus one. `SingleListQ` enqueue charges its current list length plus one.
The client enqueues and drains an input list of length `n`; the two-list theorem
proves a roundtrip bound `3 * n`, and both implementations satisfy the shared
budget `n * (n + 3)`.

These are abstract cost theorems for the stated host-Lean operations. Input bit
size, constructing the input, certificate encoding/checking cost, native timing,
and a compiled source-to-IR queue translation are not supplied by those queue
theorems. The prototype's tick model and queue model are distinct; neither
silently selects the first integrated language cost model.

## Model-selection gate

Freeze counted events, encodings, evaluation/sharing policy, parameter, endpoint,
and common EXP-A budget before comparing candidates. Retain a report exposing
all four quantities, marking unsupported fields unclaimed, and link every
preservation statement to its theorem. The first integrated F-cost model and
endpoint still require the recorded `DEC-COST-001` selection and applicable M5A
proofs.
