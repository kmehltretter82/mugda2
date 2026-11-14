# ADR-02: the Lean proof boundary

**Date:** 2026-11-14\
**Status:** Boundary policy adopted from M0; first general object/host bridge open.\
**Decision:** `DEC-HOST-001`.\
**Requirements:** `REQ-TRUST-001`, `REQ-TRUST-002`, `REQ-HOST-001`, `REQ-HOST-002`, `REQ-EXT-001`.

## Context

Lean checks the declarations and proofs used to implement a language. That alone
does not show that the language's rules are consistent or that its checker only
accepts well-typed programs. A host proof about a source representation must be
distinguished from executing a source program or proving an arbitrary host
proposition with it.

## Policy

Mugda2 remains an object language implemented and formalized in Lean. Its
supported fragments must specify their own syntax, environments, typing,
conversion, evaluation, and permitted assumptions. State each bridge explicitly:

| Connection | Required connecting evidence |
|---|---|
| Object judgments to a host semantic interpretation | Accepted checking implies a well-formed environment and object typing; the specified interpretation then justifies the claimed consistency/normalization property |
| Object definitions translated into host Lean definitions | A preservation/refinement theorem for the supported source fragment, translated statement, and generated definition |
| Object-generated certificates checked in Lean | A theorem such as `checkCert c = true → Spec` with the source claim, certificate format, checker, and host specification visible |

Certificate exchange is the proposed primary Phase II bridge. Choosing it for a
particular release still requires a worked, independently checked exchange.
Importing a Lake package, compiling a host executable, or proving an unrelated
Lean theorem does not supply a missing connecting theorem.

Each exported claim must name its fragment/version, exact theorem or certificate
claim, premises, and trusted assumptions. Preserve reproducible toolchain and
dependency pins and inspect axiom closures. Standard Lean axioms must be reported
under the declared trust policy; absence of `Classical.choice` is not the same as
absence of every axiom.

## Current evidence and limitations

[The Giralf module](../../Mugda2/Giralf.lean) defines a small `GExpr` language,
`GEval`, erased `IRExpr`, and `IREval`. Its
`erase_behavioral_and_cost_adequate` theorem states:

```text
GEval env e v c ↔ IREval env (erase e) v c
```

This is exact preservation for that calculus's explicit `tick` charges, using the
same `Val` representation on both sides. `inferCreditBound_ir_cost_le` provides a
bound conditional on successful inference and an IR evaluation derivation.
`HasCreditBound` is a cost judgment, not a general object typing judgment or a
proof that evaluation succeeds.

The queue benchmark is expressed separately as host Lean `QueueModule` and
`CostM` programs. Its client theorem is not a source-to-IR extraction theorem for
that queue program. Neither the small calculus nor the queue benchmark establishes
F0's dependent-language soundness, an arbitrary object-to-host proof bridge, or
native backend cost preservation.

## Bridge gate

For the first supported exchange, retain the source statement, object artifact,
encoding/translation, host specification, and checked connecting theorem with
their exact dependency closure. State the source and target cost metrics if cost
is claimed. IR correctness ends at the named IR; Lean's compiler, generated C,
runtime, allocation, and machine timing need separate assumptions or proofs.
`DEC-HOST-001` stays **open** until its worked bridge is selected and evidenced.
