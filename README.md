# Mugda2

> **Status:** Design baseline and cost prototype; **M1 checker hardening in progress**. The adapted pinned Mugda checker now has structured results, separate provisional function signatures, atomic mutual blocks, and explicit budget exhaustion. [Current evidence and remaining gates](docs/M1-STATUS.md) distinguish this legacy implementation from the planned, independently verified Mugda2 core. Neither M0 nor M1 is declared complete.

**A dependent programming language and workbench in Lean 4 for constructive algorithms with checked termination, modular abstraction, and computational cost (upper bounds, lower bounds, and cost preservation), with first-class support for agent-assisted proof and certificate synthesis.**

> **Core Research Question:** *Can we build a practical dependent language in which recursive components expose termination and resource contracts, those contracts survive abstraction and representation changes, and agents can synthesize independently checked evidence for them?*

## Start Here: Documentation, Requirements & Formalization

| Deliverable | Purpose |
|---|---|
| **[`Mugda2/Checker.lean`](Mugda2/Checker.lean)** | M1 API over the adapted [pinned legacy checker](Mugda2/Legacy/Core.lean): `accepted`, categorized `rejected`, or `unknown` with `outOfFuel` / `unsupportedCoverage`. The CLI prints JSON and uses the same API. |
| **[Constructor coverage](docs/COVERAGE.md)** | Finite typed pattern-matrix certificates, validated missing-input witnesses, and conservative legacy integration before function promotion. Dependent core soundness remains open. |
| **[Architecture decisions](docs/adr/README.md)** · **[Corpus record](docs/M1-CORPUS.md)** | Explicit proof boundaries and open foundation choices; semantic classification of all 79 imported examples with independently reviewed expected results. |
| **[M1.5 host controls](docs/experiments/README.md)** | Operation-based queue cost proofs behind an enforced import boundary; height-founded certificate traversal through abstract helpers; explicit size-erasure and uniformity scope; registered elaboration/replay procedure. Object candidates remain unresolved. |
| **[Interactive Concept Guide (GitHub Pages)](https://kmehltretter82.github.io/mugda2/)** · ([source: `docs/index.html`](docs/index.html)) | **Three-level concept guide** (Introductory, Intermediate, Advanced) with two interactive illustrations: an $n$-bit countdown demonstrating termination vs. execution cost, and a two-list queue demonstrating potential-based amortized cost accounting. |
| **[`Mugda2/Giralf.lean`](Mugda2/Giralf.lean)** | Constructive Lean prototype inspired by Giralf/Calf: a small explicitly costed calculus, exact erasure theorem, and separate host-Lean queue benchmark. This does not implement the complete published calculi or connect the queue to the calculus's extraction theorem. |
| **[`REQUIREMENTS.md`](REQUIREMENTS.md)** | **Requirements baseline (`v0.1`)** with 34 stable requirement IDs (`REQ-CHECK-*`, `REQ-CORE-*`, `REQ-SIZE-*`, `REQ-COST-*`, `REQ-HOST-*`, `REQ-WORK-*`, `REQ-APP-*`), required acceptance evidence, open decisions (`DEC-*`), and the first implementation release scope (`L1`). |
| **[`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md)** | **Controlled M1.5 experiment protocols (`EXP-A` and `EXP-B`)** comparing minimal intensional identity, Observational Type Theory, and Cubical foundations for modular cost/abstraction (`EXP-A`), and comparing accessibility translation against a native sized-recursion rule (`EXP-B`). |
| **[`MILESTONES.md`](MILESTONES.md)** | **Milestone roadmap (`M0`–`M11`)** connecting the requirements baseline and M1.5 experiments to the language track, the Avis–Friedmann complexity application track, and the per-milestone theorem/assumption matrix. |

## Machine-Checked Constructive Theorems in [`Mugda2/Giralf.lean`](Mugda2/Giralf.lean)

Built with **Lean 4 (`v4.35.0`)** and verified via `make test`. The environment-based audit checks every project theorem and definition, including private declarations, permitting only Lean's `propext` and `Quot.sound` axioms. It rejects unfinished proofs, classical choice, native proof evaluation, additional axioms, and authored unsafe/partial declarations. Lean-generated runtime implementations are identified and reported separately. Proof reports are written under `.lake/build/audit/`; checker results are under `.lake/build/reports/`.

| Section | Theorem | Statement Verified in Lean 4 |
|---|---|---|
| **§1. `Calf` Cost Monad & Phase Distinction** | `step_extEq_ret`, `bind_refines` | Monad laws, behavioral noninterference (`step c x` is invisible in the behavioral phase), and monotonicity of quantitative refinement. |
| **§2. Physicist's View (Potential & Gluing)** | `totalActual_add_phi_eq`, `exact_trace_from_zero`, `bounded_trace_cost_le` | Exact telescoping identity $\text{actualCost} + \Phi(s_k) = \text{amortizedCharge} + \Phi(s_0)$ (matching the interactive widget in `docs/index.html`) and upper-bound soundness. |
| **§3. Banker's View (`Credit`, `Debit`, `CreditList`)** | `storedCredits_eq_linear_potential` | **Banker $\leftrightarrow$ Physicist Equivalence:** storing $k$ credits per constructor cell in `CreditList k A` is constructively equal to the Physicist's potential $\Phi(\mathit{xs}) = k \cdot |\mathit{xs}|$. |
| **§4. Deeply Embedded `Giralf` & Cost-Adequate Erasure** | `erase_behavioral_and_cost_adequate`, `giralf_credit_soundness`, `inferCreditBound_ir_cost_le` | **Bi-directional behavioral & cost adequacy (`REQ-COST-003`):** $e \Downarrow_{\text{src}}^{c} v \iff \operatorname{erase}(e) \Downarrow_{\text{IR}}^{c} v$ (completely axiom-free: `does not depend on any axioms`), plus soundness of executable credit inference (`inferCreditBound`). |
| **§5. `EXP-A` FIFO Queue Benchmark & Swap** | `enqueue_exact_amortized`, `dequeue_nonempty_exact_amortized`, `batched_fifoRoundtrip_cost_le`, `expA_implementation_swap_agreement` | Amortized $O(1)$ bounds for the two-list `BatchedQ` ($3n$ roundtrip cost), $O(n^2)$ bound for `SingleListQ`, and modular client swap across `BoundedQueueModule` without modifying the client proof. |

### Building & Running Locally

```bash
lake build
make test

# Structured checking (exit 0 = accepted, 1 = rejected, 2 = unknown)
lake exe mugda2 check tests/cases/structural-recursion.ma
lake exe mugda2 check --fuel 0 tests/cases/structural-recursion.ma

# Original queue demonstration
lake exe mugda2 demo

# Finite host-control observations (70 JSON records)
lake exe mugda2-experiments
```

Checking also accepts `--comparison-fuel`, `--closure-fuel`, `--lex-fuel`, and
`--parse-fuel`. These are recursive search limits, not measured execution costs.
Usage and I/O failures have separate exit codes 64 and 74. Diagnostic spans cover
the entire UTF-8 document because the imported parser does not retain locations.
Legacy acceptance is not an M2 typing, consistency, normalization, or elaboration
soundness theorem. The eight native-backed closed tests in the old metatheory are
now runtime regressions, rather than trusted proof artifacts.
Tri-valued matching blocks neutral clause fallthrough. Constructor coverage now
rejects the nullary empty-type exploit and preserves genuine empty elimination.
The [coverage boundary](docs/COVERAGE.md) and [independent review](docs/M1-REVIEW.md)
describe unsupported dependent refinements and the remaining full soundness
obligations; acceptance by this checker cannot yet certify a host proposition.

## Overview

Mugda2 is the successor to [Mugda](https://github.com/kmehltretter82/mugda/tree/b0c5b53) (Karl Mehltretter's dependently typed language combining sized inductive/coinductive types with size-change termination, ported and verified in Constructive Lean 4).

Mugda2 investigates how **parametric sized programming** ($\forall^p i$), **internal parametricity**, and **modular cost reasoning** (*Abstraction Functions as Types* / *Potential Functions as Types* / *Decalf*) work together in a small, verified core.
