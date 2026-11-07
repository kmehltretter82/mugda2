# Mugda2

**A dependent programming language and workbench in Lean 4 for constructive algorithms with checked termination, modular abstraction, and computational cost (upper bounds, lower bounds, and cost preservation), with first-class support for agent-assisted proof and certificate synthesis.**

> **Core Research Question:** *Can we build a practical dependent language in which recursive components expose termination and resource contracts, those contracts survive abstraction and representation changes, and agents can synthesize independently checked evidence for them?*

## Overview

Mugda2 is the successor to [Mugda](../mugda) (Karl Mehltretter's dependently typed language combining sized inductive/coinductive types with size-change termination, ported and verified in Constructive Lean 4).

Mugda2 investigates how **parametric sized programming** ($\forall^p i$), **internal parametricity**, and **modular cost reasoning** (*Abstraction Functions as Types* / *Potential Functions as Types* / *Decalf*) work together in a small, verified core:

- **Andreas Abel's lineage:** Compositional termination and productivity via parametric sized types ($\forall^p i$), dependent (co)pattern elaboration into case trees, and Normalization by Evaluation (NbE).
- **Martin Hofmann's lineage:** Potential functions, amortized resource analysis, and modular cost contracts that survive across representation changes.
- **Helmut Schwichtenberg's lineage:** Decorated proofs and extraction of clean executables with erasable proofs, sizes, and ghost cost credits.
- **Lean 4 architecture:** A small verified core rechecker (`recheck_sound`), snapshot-based JSON-RPC checking service for humans and LLM agents, and direct integration with Lean 4 formalizations (starting with the Avis–Friedmann exponential simplex/policy-iteration lower bounds and effective-horizon upper bounds).

## Roadmap

See **[MILESTONES.md](MILESTONES.md)** for the full milestone plan (`M0`–`M11`), foundational design experiments (`M1.5`), and agent work packages.
