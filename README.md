# Mugda2

> **Status:** Design & Specification Stage (`M0`). This repository currently contains the milestone plan ([`MILESTONES.md`](MILESTONES.md)), architectural specifications, and design notes. The Mugda2 core checker, rechecker, and JSON-RPC workbench service are planned components building on the verified Mugda v1.0 baseline in [`github.com/kmehltretter82/mugda` @ `b0c5b53`](https://github.com/kmehltretter82/mugda/tree/b0c5b53).

**A dependent programming language and workbench in Lean 4 for constructive algorithms with checked termination, modular abstraction, and computational cost (upper bounds, lower bounds, and cost preservation), with first-class support for agent-assisted proof and certificate synthesis.**

> **Core Research Question:** *Can we build a practical dependent language in which recursive components expose termination and resource contracts, those contracts survive abstraction and representation changes, and agents can synthesize independently checked evidence for them?*

## Overview

Mugda2 is the successor to [Mugda](https://github.com/kmehltretter82/mugda/tree/b0c5b53) (Karl Mehltretter's dependently typed language combining sized inductive/coinductive types with size-change termination, ported and verified in Constructive Lean 4).

Mugda2 investigates how **parametric sized programming** ($\forall^p i$), **internal parametricity**, and **modular cost reasoning** (*Abstraction Functions as Types* / *Potential Functions as Types* / *Decalf*) work together in a small, verified core:

- **Andreas Abel's lineage:** Compositional termination and productivity via parametric sized types ($\forall^p i$), dependent (co)pattern elaboration into case trees, and Normalization by Evaluation (NbE).
- **Martin Hofmann's lineage:** Potential functions, amortized resource analysis, and modular cost contracts that survive across representation changes.
- **Helmut Schwichtenberg's lineage:** Decorated proofs and extraction of native executables with erasable proofs, sizes, and ghost cost credits — backed by both behavioral and cost adequacy theorems.
- **Lean 4 architecture:** An object language implemented and verified in Lean 4 (`recheck_sound` + semantic consistency/normalization + conversion soundness + elaboration correctness), a snapshot-based JSON-RPC checking service for humans and LLM agents, and certificate-checked bridges to Lean 4 formalizations (starting with the Avis–Friedmann exponential simplex/policy-iteration lower bounds and effective-horizon upper bounds).

## Roadmap

See **[`MILESTONES.md`](MILESTONES.md)** for the full milestone plan (`M0`–`M11`), controlled foundational design experiments (`M1.5`), proof-boundary ADRs, and per-milestone theorem/assumption matrix.
