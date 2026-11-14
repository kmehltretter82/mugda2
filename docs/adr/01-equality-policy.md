# ADR-01: conditional equality policy

**Date:** 2026-11-14\
**Status:** Conditional policy adopted from M0; object equality selection open.\
**Decision:** `DEC-EQ-001`.\
**Requirements:** `REQ-EQ-001`, `REQ-EQ-002`, `REQ-CORE-001`, `REQ-CHECK-003`.

## Context

The roadmap compares minimal intensional identity with explicit simulations,
Observational Type Theory (OTT), and a cubical foundation. They do not share all
identity rules. The historical `k.ma` example therefore cannot have a single
foundation-independent expected result. Host Lean equality used in a benchmark
does not select the identity rules of a future Mugda2 object calculus.

## Policy

Keep equality-dependent expectations indexed by an explicitly named fragment and
foundation:

| Candidate | Unrestricted K/UIP on its general identity | Required boundary |
|---|---|---|
| Minimal intensional identity | Do not add it as a general rule | Distinguish general identity from restrictions, such as identity on proved sets |
| Cubical/path identity | Do not add it for general paths | Specify interval, paths, composition, transport, universes, and any strict equality separately |
| The proposed OTT candidate | UIP for its proof-irrelevant observational equality is intended | Name the precise observational equality, relevance, quotient, elimination, and conversion rules |
| A strict-equality/path combination | No inherited default | Treat the combination as a separate extension with explicit interaction rules and justification |

Select the object foundation only through the EXP-A comparison in
[the protocol](../EXPERIMENTS.md#4-exp-a--modular-abstraction-and-equality).
The selection must cover computation, dependent matching, transport/elimination,
universe behavior, relevance, and the required equations. Postulating a convenient
extensional equality does not provide these rules or their semantic justification.

The fallback in the protocol is a provisional implementation target when its
recorded trigger applies. It does not establish consistency, normalization,
checker soundness, or completion of M1.5/M2.

## Current evidence and consequences

[The Giralf prototype](../../Mugda2/Giralf.lean) uses host Lean structures and
propositional equalities for its queue laws. Its source/IR cost calculus has no
object identity rules. Neither part selects an object equality foundation or
proves that unrestricted K is unavailable in a proposed intensional calculus.

Use foundation-indexed regression expectations while preserving the original
source and its classification. Label a legacy checker's observed result
separately from a selected Mugda2 fragment's intended policy.

## Selection gate

Record the frozen EXP-A manifest and exact candidate fragments, unchanged client
obligations and budget, equation classifications, assumption reports, measured
effort/checking costs, failed runs, and the decision rationale. The selected F0
still needs M2's checker, semantic, conversion, and elaboration proofs. Until that
evidence exists, `DEC-EQ-001` stays **open**.
