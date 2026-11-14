# ADR-03: core extensions require reverification

**Date:** 2026-11-14\
**Status:** Reverification policy adopted from M0; recursion selection open.\
**Decision:** `DEC-REC-001`.\
**Requirements:** `REQ-CORE-001`–`REQ-CORE-005`, `REQ-SIZE-001`–`REQ-SIZE-004`, `REQ-EXT-002`.

## Context

The planned language grows from F0 through sized and cost-aware fragments. New
recursion, equality, relevance, and erasure rules may invalidate earlier checker
or semantic arguments. Separate proofs about component calculi do not justify
their combination.

## Policy

For every extension, choose and document one of two paths:

1. Translate the feature into an already justified core, with a theorem preserving
   the claimed typing, meaning, and defining equations. State any additional
   erasure or cost preservation obligations separately.
2. Extend the core specification and re-establish all affected checker,
   conversion, semantic, and elaboration obligations for the extended fragment.

Track the following evidence for each supported fragment/version:

| Obligation | Evidence required |
|---|---|
| Checker soundness | Accepted checking implies both environment well-formedness and declarative typing |
| Semantic justification | A model/reduction argument establishing the stated consistency and normalization, or separately stated productivity property |
| Conversion | Soundness for a specified relation, `unknown` on exhausted budgets, and sufficient-budget completeness on the claimed decidable fragment |
| Elaboration | Successful source elaboration preserves typing, meaning, and the promised definitional or propositional equations |
| Extension-specific claims | Explicit size uniformity, pattern refinement, erasure, abstraction, and cost theorems where claimed |

Record changed rules, assumptions, source/target fragments, outstanding proofs,
and artifact paths. Never relabel an earlier fragment's proof as establishing an
extended calculus.

## Sized recursion gate

Run the frozen EXP-B comparison of accessibility/recursor translation and a
native sized rule using the same opaque helper contracts, traversal, semantics,
and required equations. Ordinary dependent quantification over an inspectable
natural number is not by itself the promised parametric size quantifier.

Keep helper opacity, size bounds, denotation preservation, permitted comparisons,
pattern constraints, and size erasure explicit. Retain negative fixtures for
size-increasing helpers, unjustified same-bound recursion, and genuine dependent
pattern exploits. Native recursion requires a recorded unmet requirement or
pre-registered practical improvement plus a credible semantic account; fewer
handwritten proof lines alone do not justify a trusted core rule.

## Current evidence and consequences

The existing Giralf prototype is a separate finite cost calculus and host-Lean
queue development. It does not provide F0's four obligations, parametric sized
recursion, or a verified integration of sizes and cost. M1 baseline hardening
also does not establish those later claims.

Foundational comparisons remain preparatory until their integration probe checks
the combined substitution, opacity, conversion, and erasure behavior. Record the
M1.5 result before fixing the F0 architecture. `DEC-REC-001` stays **open** pending
that evidence.
