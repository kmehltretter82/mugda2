# M1.5 protocol review

Review date: **2026-11-14**. This document recommends a concrete registration;
it is neither the frozen manifest nor a comparison result. Numerical values
below are proposed before new candidate measurements. The parent protocol is
[EXPERIMENTS.md](../EXPERIMENTS.md), with gates in
[MILESTONES.md](../../MILESTONES.md) and [ADRs 01–04](../adr/README.md).

## What remains before a comparison can start

| Required manifest item | Current evidence | Registration still needed |
|---|---|---|
| Version, sources, inputs, observations | Written EXP-A/EXP-B protocol; preparatory host queue | Immutable manifest version, exact source hashes, finite input encodings and ladder, symbolic cases, expected semantic outcomes |
| Exact candidate fragment | Named intensional, OTT, cubical, translation, native-rule directions | A candidate rule ledger and artifact/toolchain revision for each actual entry; paper titles alone do not specify rules |
| Reproducible environment | Lean toolchain is pinned in this repository | Host/prototype commits, complete dependency pins, compiler flags, CPU/OS/RAM, per-run limits and candidate effort cap |
| Interface and opacity | Generic host queue correctness proof | Per-operation cost contract, client-only import boundary, allowed equations and assumptions, unchanged client hash |
| Cost endpoint | Manually instrumented host queue; separate small GExpr/IRExpr calculus | Exact event table and strategy for each benchmark; no implicit queue-to-GExpr extraction bridge |
| Semantic gates and numerical decision rule | Requirement IDs and qualitative policy | Exact mandatory properties, one primary practical endpoint, guardrails, frozen aggregation and tie policy |
| Decision ownership | No comparison owner recorded | A named reviewer or designated project role with an identified responsible person; do not claim human review occurred merely by naming one |

The M0 exit also literally requires committed ADRs and a frozen protocol. A local
content-hashed artifact is useful evidence, but an uncommitted worktree does not
by itself satisfy that wording. A frozen benchmark specification can be prepared
while candidate implementations remain unresolved; it must say which candidate
slots are not yet eligible to run or select.

## EXP-A: preserve abstraction and strengthen the cost boundary

### What the existing host proof establishes

In [Giralf.lean](../../Mugda2/Giralf.lean), `QueueModule Q E` abstracts the state
type, operations, `contents`, and FIFO laws. `fifoRoundtrip_correct` is generic in
`M : QueueModule Q E`; it does not inspect a concrete queue representation.
Implementation-specific unfolding occurs in the corresponding implementation
proofs, where it belongs. This is valid host-Lean representation independence.

`BoundedQueueModule.roundtrip_cost_le`, however, is exactly the whole-client
cost obligation. `expA_client_correct_and_bounded` projects that field. The theorem
is valid, but does not derive the client bound compositionally from operation
contracts. It is a weaker preparatory result than that stronger language-design
claim. Do not count the implementation's separate whole-client proof as zero
additional cost-proof effort.

Use the unchanged runtime client with a contract containing an abstract potential
and per-operation cost laws. One adequate common contract has enqueue amortized
charge at most `length(contents q) + 2` and dequeue amortized charge at most one.
Record the exact post-potential convention for an empty dequeue. The potential
starts at zero; the client's final potential is nonnegative. Both implementations
may instantiate different potentials without editing the client. A tighter
batched-queue `3*n` theorem is an additional result, not a replacement for the
shared budget.

For physical opacity, the minimal faithful dependency split preserves the
existing namespace and names while moving the cost monad to `Mugda2/Cost.lean`
and generic queue definitions to `Mugda2/Queue.lean`. A per-operation contract
module imports only the generic queue; the abstract cost-client module imports
only that contract. Concrete implementation witnesses can import both the client
and Giralf. Check the transitive import closure, not only the first import line.
No duplicate cost monad or hidden concrete implementation belongs in the client.

### Proposed common registration

- Element type for concrete observations: `Nat`. Input families are `range n`,
  its reverse, and a constant list of length n, for
  `n = 0, 1, 2, 4, 8, 16, 32, 64, 128`. Keep the symbolic theorem for arbitrary
  input lists; finite observations are not a substitute.
- Keep `B(n) = n * (n + 3)` for the common upper bound. The manifest must point
  to a derivation from the frozen primitive contracts, not merely a table of
  measured outputs below B.
- Count one abstract base unit per queue operation, plus list-cons traversal
  work: append visits existing cons cells; rear reversal visits rear cons cells.
  This matches the current instrumented costs `length q + 1`, `1`, and
  `length rear + 1`. Do not describe it as counting every native allocation,
  constructor inspection, or machine step.
- Persistent lists, no memoization, deterministic call-by-value costed
  operations; specification observations and ghost potentials are not charged.
  Name the endpoint as the explicitly instrumented algorithm. Queue extraction
  through the separate GExpr calculus remains unresolved until a bridge exists.
- Freeze the client definition and generic behavioral/cost theorem by source
  hash. The swap edits only the implementation witness selected by a separate
  assembly module. Count every implementation invariant, adapter, transport,
  and proof added to install either implementation.
- Mark concrete operation defining clauses as D, abstract FIFO laws as P, and
  client correctness/cost as P/S. Test open-variable equations at their stated
  constructor boundaries, independently of closed list execution.

### Foundation eligibility

A host Lean record benchmark is `host-lean-preparation`. It does not select
minimal object identity, OTT, or cubical rules, nor prove absence of object K.
For a foundation comparison, each entry needs the same object benchmark or an
explicit source-to-target account, exact fragment/rule ledger, and assumption
closure. A missing candidate is `unresolved`, not a failed semantic theory and
not evidence that a richer foundation has no advantage.

The candidate ledgers must cite and pin the actual rules they implement. This
review makes no claim that any particular published system supplies a rule set
already implemented here. Any postulated rule remains a declared assumption;
it cannot pass the corresponding proof gate by convenient host equality.

## EXP-B: finite control without silently claiming parametric sizes

Freeze one raw finite AST with `event`, `sequence`, and `repeat k child`.
Choose and record a single height convention, including empty sequences.
Use a canonical binary encoding for k, with zero represented by `0` and no
leading zeros elsewhere. Keep height, encoded byte/bit size, and expanded event
count as different functions. Large repeat counters must remain compact during
syntax-size measurements.

An adequate finite translation control can use an abstract raw helper H with:

1. `height(H c) <= height(c)`;
2. `denote(H c) = denote(c)`;
3. runtime behavior independent of the irrelevant bound used to package c.

Lift that helper to `Certificate i` with a bound proof. Identity and removal of
a singleton sequence wrapper are two required implementations. They stay opaque
to the traversal proof. The traversal must recurse on `H child`, with descent
obtained from the smaller child bound plus the helper contract, rather than
syntactic subterm inspection or helper-body inlining.

This explicit finite host construction is useful control evidence. Ordinary
dependent functions over inspectable `Nat` do not, by themselves, implement
the proposed object-language parametric quantifier. If H is chosen as a raw
size-independent function, a coherence theorem for its lifted wrappers proves
that particular construction uniform; it does not validate an unrestricted
native quantifier or all future helpers.

Proposed concrete ladders are unary depths `0, 1, 2, 4, 8, 16`, balanced binary
depths `0..8`, widths `0, 1, 2, 4, 8, 16, 32`, and repeat counters
`0, 1, 2, 2^8, 2^32`. Register the selected finite combinations explicitly,
rather than leaving the Cartesian product implicit. Use symbolic denotation
proofs at large counters; do not expand `2^32` events to validate syntax size.

Freeze these observations before comparing translation and a native rule:

| Obligation | Required evidence |
|---|---|
| Abstract traversal | Checked using only helper size/meaning contracts; client source unchanged for both helpers |
| Constructor equation | D, P, or unsupported for an open child and opaque helper; report generated recursor/accessibility terms |
| Size irrelevance | Equal erased behavior under two admissible bound annotations, with the exact coherence theorem |
| Denotation and extraction | Explicit source/target witness and erasure endpoint; a host evaluation result alone is insufficient |
| Increasing helper | Rejection at the bound-preservation obligation for a tight-bound input |
| Same-bound recursion | Rejection at the absent strict descent obligation when the helper may be identity |
| Pattern refinement | A translated genuine exploit reaches and fails the intended refinement check; unrelated parser/scope failure does not count |

Keep the negative fixture's semantic obligation and raw checker diagnostic
together. If a candidate cannot express a fixture, record `unsupported` or
`unresolved` instead of crediting an earlier error as its desired rejection.

## Suggested numerical rule and budgets

The following is a concrete proposal for the root manifest writer, not an
already adopted decision:

- All frozen semantic requirements and permitted-assumption gates must pass.
- Primary practical endpoint: total handwritten proof tokens for the benchmark,
  both implementations/helpers, client, transports, adapters, and auxiliary
  lemmas. A richer mechanism needs at least **25% fewer tokens** than the
  corresponding control. Count statements/annotations consistently; list exact
  included source files. Report new foundation/metatheory burden separately.
- Guardrails: generated kernel-term nodes at most **2x** control; median
  independent rechecking at most **1.5x** control; peak resident memory at most
  **1 GiB** for an individual measured process. Source proof reduction alone
  cannot justify an unchecked trusted rule.
- A predeclared mandatory equation/computation requirement that the control
  cannot meet is a separate semantic reason to prefer a candidate. Name the
  exact requirement and equation category before results; do not substitute a
  candidate-specific sanity check afterward.
- One warm-up and **five timed repetitions**, preserving all raw observations,
  median and range. Record a cold source elaboration separately. Per-instance
  caps: **300 s elaboration**, **60 s independent rechecking**. An exhausted
  cap is `unknown`, not rejection. Keep elaboration and rechecking separate.
- Select and record a candidate-development effort cap and comparison start/end
  before work begins. The roadmap's four-week fallback is not triggered merely
  because the implementations are currently absent or a single turn ends.
- Ties, unmet guardrails, and unavailable comparable measurements are
  `inconclusive`; retain the protocol's explicitly provisional control and the
  missing obligations. Do not manufacture a foundation winner.

Define generated-term counting before collection: count the metadata-erased
kernel expression tree and separately record the unique referenced project
declaration closure and shared dependencies. Preserve serialized artifact bytes
as a second measure. Unmeasured generated files cannot hide transports or proof
arguments. Importing an `.olean` is not independent kernel rechecking; leave that
metric unresolved until the actual rechecking procedure is specified and used.

## Freeze and report discipline

Each candidate record should include artifact kind, exact source/target fragment,
source/dependency/toolchain hashes, rule and assumption ledger paths, unchanged
client hash, input ID, budget, expected equation category, expected semantic
obligation, actual checker result/diagnostic, raw measurements, and evidence
label (`measured`, `checked`, `proved`, or `unresolved`). Record unsupported and
unsuccessful runs as first-class results.

Version any change to a theorem, cost event, opacity boundary, size encoding,
budget, candidate fragment, or threshold. Results measured before that change
belong to the old version. Only the eventual decision report can close
`DEC-EQ-001`/`DEC-REC-001`; the selected combination still requires the integration
probe and M2's checker, semantic, conversion, and elaboration obligations.
