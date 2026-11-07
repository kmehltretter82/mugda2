# Mugda2

> **Status:** Design Baseline (`M0` / `D0`) + First Constructive Lean 4 Formalization ([`Mugda2/Giralf.lean`](Mugda2/Giralf.lean)). This repository contains the requirements baseline ([`REQUIREMENTS.md`](REQUIREMENTS.md)), the controlled experiment protocols ([`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md)), the three-level interactive HTML concept guide ([`docs/index.html`](docs/index.html)), the milestone plan ([`MILESTONES.md`](MILESTONES.md)), and the first machine-checked Constructive Lean 4 module [`Mugda2/Giralf.lean`](Mugda2/Giralf.lean) formalizing *Potential Functions as Types* (Giralf & Calf), cost-adequate erasure (`REQ-COST-003`), and the `EXP-A` modular FIFO queue swap.

**A dependent programming language and workbench in Lean 4 for constructive algorithms with checked termination, modular abstraction, and computational cost (upper bounds, lower bounds, and cost preservation), with first-class support for agent-assisted proof and certificate synthesis.**

> **Core Research Question:** *Can we build a practical dependent language in which recursive components expose termination and resource contracts, those contracts survive abstraction and representation changes, and agents can synthesize independently checked evidence for them?*

## Start Here: Documentation, Requirements & Formalization

| Deliverable | Purpose |
|---|---|
| **[Interactive Concept Guide (GitHub Pages)](https://kmehltretter82.github.io/mugda2/)** · ([source: `docs/index.html`](docs/index.html)) | **Three-level concept guide** (Introductory, Intermediate, Advanced) with two interactive illustrations: an $n$-bit countdown demonstrating termination vs. execution cost, and a two-list queue demonstrating potential-based amortized cost accounting. |
| **[`Mugda2/Giralf.lean`](Mugda2/Giralf.lean)** | **Pure Constructive Lean 4 formalization** of *Potential Functions as Types* (Grodin, Chu, Li, Hoffmann & Harper, 2026) + Ratiu–Schwichtenberg cost-adequate erasure + the `EXP-A` modular FIFO queue benchmark. Zero `sorry`, zero `partial`, zero `unsafe`, zero `Classical.choice`. |
| **[`REQUIREMENTS.md`](REQUIREMENTS.md)** | **Requirements baseline (`v0.1`)** with 34 stable requirement IDs (`REQ-CHECK-*`, `REQ-CORE-*`, `REQ-SIZE-*`, `REQ-COST-*`, `REQ-HOST-*`, `REQ-WORK-*`, `REQ-APP-*`), required acceptance evidence, open decisions (`DEC-*`), and the first implementation release scope (`L1`). |
| **[`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md)** | **Controlled M1.5 experiment protocols (`EXP-A` and `EXP-B`)** comparing minimal intensional identity, Observational Type Theory, and Cubical foundations for modular cost/abstraction (`EXP-A`), and comparing accessibility translation against a native sized-recursion rule (`EXP-B`). |
| **[`MILESTONES.md`](MILESTONES.md)** | **Milestone roadmap (`M0`–`M11`)** connecting the requirements baseline and M1.5 experiments to the language track, the Avis–Friedmann complexity application track, and the per-milestone theorem/assumption matrix. |

## Machine-Checked Constructive Theorems in [`Mugda2/Giralf.lean`](Mugda2/Giralf.lean)

Built with **Lean 4 (`v4.35.0`)** and verified via `make test` (`#print axioms` enforces zero `Classical.choice`, zero `sorryAx`, and zero `Lean.ofReduceBool`):

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
```

## Overview

Mugda2 is the successor to [Mugda](https://github.com/kmehltretter82/mugda/tree/b0c5b53) (Karl Mehltretter's dependently typed language combining sized inductive/coinductive types with size-change termination, ported and verified in Constructive Lean 4).

Mugda2 investigates how **parametric sized programming** ($\forall^p i$), **internal parametricity**, and **modular cost reasoning** (*Abstraction Functions as Types* / *Potential Functions as Types* / *Decalf*) work together in a small, verified core.
