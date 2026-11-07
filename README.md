# Mugda2

> **Status:** Design & Specification Stage (`M0` / `D0`). This repository currently contains the requirements baseline ([`REQUIREMENTS.md`](REQUIREMENTS.md)), the controlled experiment protocols ([`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md)), the three-level interactive HTML concept guide ([`docs/index.html`](docs/index.html)), the milestone plan ([`MILESTONES.md`](MILESTONES.md)), and initial design notes. The Mugda2 core checker, rechecker, and JSON-RPC workbench service are planned components building on the verified Mugda v1.0 baseline in [`github.com/kmehltretter82/mugda` @ `b0c5b53`](https://github.com/kmehltretter82/mugda/tree/b0c5b53).

**A dependent programming language and workbench in Lean 4 for constructive algorithms with checked termination, modular abstraction, and computational cost (upper bounds, lower bounds, and cost preservation), with first-class support for agent-assisted proof and certificate synthesis.**

> **Core Research Question:** *Can we build a practical dependent language in which recursive components expose termination and resource contracts, those contracts survive abstraction and representation changes, and agents can synthesize independently checked evidence for them?*

## Start Here: Documentation & Requirements Baseline (`v0.1`)

| Document | Purpose |
|---|---|
| **[Interactive Concept Guide (GitHub Pages)](https://kmehltretter82.github.io/mugda2/)** · ([source: `docs/index.html`](docs/index.html)) | **Three-level concept guide** (Introductory, Intermediate, Advanced) with two interactive illustrations: an $n$-bit countdown demonstrating termination vs. execution cost, and a two-list queue demonstrating potential-based amortized cost accounting. |
| **[`REQUIREMENTS.md`](REQUIREMENTS.md)** | **Requirements baseline (`v0.1`)** with 34 stable requirement IDs (`REQ-CHECK-*`, `REQ-CORE-*`, `REQ-SIZE-*`, `REQ-COST-*`, `REQ-HOST-*`, `REQ-WORK-*`, `REQ-APP-*`), required acceptance evidence, open decisions (`DEC-*`), and the first implementation release scope (`L1`). |
| **[`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md)** | **Controlled M1.5 experiment protocols (`EXP-A` and `EXP-B`)** comparing minimal intensional identity, Observational Type Theory, and Cubical foundations for modular cost/abstraction (`EXP-A`), and comparing accessibility translation against a native sized-recursion rule (`EXP-B`). |
| **[`MILESTONES.md`](MILESTONES.md)** | **Milestone roadmap (`M0`–`M11`)** connecting the requirements baseline and M1.5 experiments to the language track, the Avis–Friedmann complexity application track, and the per-milestone theorem/assumption matrix. |

## Overview

Mugda2 is the successor to [Mugda](https://github.com/kmehltretter82/mugda/tree/b0c5b53) (Karl Mehltretter's dependently typed language combining sized inductive/coinductive types with size-change termination, ported and verified in Constructive Lean 4).

Mugda2 investigates how **parametric sized programming** ($\forall^p i$), **internal parametricity**, and **modular cost reasoning** (*Abstraction Functions as Types* / *Potential Functions as Types* / *Decalf*) work together in a small, verified core:

- **Andreas Abel's lineage:** Compositional termination and productivity via parametric sized types ($\forall^p i$), dependent (co)pattern elaboration into case trees, and Normalization by Evaluation (NbE).
- **Martin Hofmann's lineage:** Potential functions, amortized resource analysis, and modular cost contracts that survive across representation changes.
- **Helmut Schwichtenberg's lineage:** Decorated proofs and extraction to a specified executable IR with erasable proofs, sizes, and ghost cost credits — backed by separate behavioral and cost adequacy theorems.
- **Lean 4 architecture:** An object language implemented and verified in Lean 4 (`recheck_sound` + semantic consistency/normalization + conversion soundness + elaboration correctness), a snapshot-based JSON-RPC checking service for humans and LLM agents, and certificate-checked bridges to Lean 4 formalizations (starting with the Avis–Friedmann exponential simplex/policy-iteration lower bounds and effective-horizon upper bounds).
