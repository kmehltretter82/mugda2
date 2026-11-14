# M1 independent review and open soundness boundary

Review date: **2026-11-14**. The adapted legacy checker has useful state,
diagnostic, budget, and pattern-matching guarantees. It is **not a verified
decision procedure for a total, logically consistent Mugda2 core**. In
particular, the coverage certificate is for a finite model; its executable
legacy adapter does not establish the complete dependent source/core soundness
bridge. `accepted` is not a host proposition or a full language consistency claim.

## Fixed: neutral matching fell through to a later clause

The pinned baseline represented both a definite constructor mismatch and an
unresolved match on a neutral variable by `none`. Its clause evaluator therefore
advanced to a later catch-all clause during open conversion. This was unsafe for
dependent types: a type family could reduce one way on an unknown argument and
another way after substitution.

[The modern counterexample](../tests/cases/overlap-conversion.ma) defines
`F tt = Empty` and `F b = Unit`. Before the fix, the checker reduced `F b` to
`Unit` for neutral `b`, accepted `bad b = unit : F b`, and then accepted
`contradiction : Empty = bad tt`.

The fix ports the matching change from Mugda revision
`919465fdb995245f395f18423eaf31729fa8cea6` into the adapted
[Core](../Mugda2/Legacy/Core.lean), preserving its typed exhaustion and transaction
rules. `MatchResult` distinguishes:

- `matched`: use the first matching clause's result;
- `mismatch`: a definite mismatch permits advancing to the next clause;
- `stuck`: preserve the unresolved application and stop searching later clauses.

The updated [component metatheory](../Mugda2/Legacy/Metatheory.lean) preserves the
size-erasure theorems with an explicit `MatchResult.map`, and proves stuckness
barriers, definite-mismatch advancement, and first-match preservation. These are
matching properties, not a complete object-language semantic soundness theorem.

Targeted verification checked that the counterexample is now rejected with exact
category `typeMismatch`. It also checked neutral blocking, definite mismatch,
first-match selection, underapplied constructors, typed matching exhaustion,
coinductive forcing, and valid dependent constructor branches. The modern
manifest includes the negative source; it does not change the pinned 79-file
legacy inventory or its hashes.

## Fixed for the supported fragment: unjustified empty elimination

Before the coverage gate, the checker accepted this complete source document:

```text
data Empty : Set {}
fun hole : Empty {}
let witness : Empty = hole
```

Observed using the rebuilt CLI on 2026-11-14: exit **0**, JSON status
`accepted`, declarations `Empty`, `hole`, and `witness`. A direct execution of
`MugdaCore.checkSource` also returned `isOk = true`. This was an **unsafe
acceptance for the intended total constructive language**, not a passing
positive example or a consistency result. The current CLI rejects it with
`coverage`; valid empty-domain elimination remains accepted.

The original source cause remains relevant when reviewing the separate size,
clause-typing, and termination checks:

1. `completePatterns` checks size-pattern restrictions with `List.all`. An empty
   clause list passes vacuously; it is not a well-typed coverage judgment.
2. `checkFun` checks each supplied clause with `forM`; no supplied clauses require
   no bodies to be checked.
3. The empty call graph satisfies the termination check, so `typeCheckFuns` can
   mark the nullary declaration checked even though no case or body constructs
   its result.

This behavior effectively introduces an unjustified object-language constant of
empty type. It does not construct a contradiction in host Lean: Lean verifies the
implementation of this legacy algorithm, and that is different from proving the
algorithm's accepted object judgments sound. The explicit M2 obligations in the
[roadmap](../MILESTONES.md#m2--explicit-core-conditional-equality-and-four-part-verification)
remain necessary.

A blanket ban on empty clause lists would also reject legitimate empty-input
elimination. For example,
[the modern empty-domain fixture](../tests/cases/empty-domain.ma) defines a
function `Empty -> Empty` with no clauses. There is no possible input, so a
well-typed coverage account should justify that definition while rejecting the
nullary `hole : Empty` above. Counting clauses alone cannot make that distinction.

Before claiming M2 checker soundness, consistency, normalization, or valid total
elaboration, the supported core must supply:

- a typed coverage or case-tree judgment distinguishing impossible inputs from
  missing branches and unjustified nullary declarations;
- elaboration that checks constructor constraints, dependent refinements, and
  first-match behavior against that judgment;
- a checker soundness theorem covering the accepted environment as well as term
  typing, and the stated semantic model for that fragment;
- negative regression evidence for the nullary example and positive evidence for
  genuine empty elimination, with diagnostic categories established by the
  specified checking rules.

The active [coverage fixtures](../tests/coverage/manifest.json) require rejection
of the nullary example and acceptance of genuine empty elimination.
[`Certificate.sound`](../Mugda2/Coverage/Matrix.lean) proves finite, signature-typed
matrix coverage. The [adapter](../Mugda2/Coverage/Legacy.lean) checks this gate before
mutual promotion, validates missing inputs against the original telescope, and
returns `unknown/unsupportedCoverage` when its abstraction cannot resolve the
obligation. Inductive recursive emptiness and restricted root codata observations
have separate representations; codata is not treated as a finite inductive tree.

These changes close the demonstrated nullary acceptance and ordinary constructor
holes. They do not supply the complete dependent elaboration and semantic
soundness theorems listed above. `acc.ma`, `vec.ma`, and `sort.ma` remain valid
total-language targets but now return `unknown` pending typed index coverage;
those outcomes must not be described as semantic rejections. See the
[coverage boundary](COVERAGE.md) for the supported scope.

## Scope of the new experiment controls

The host-Lean queue and certificate controls do not use legacy acceptance as a
premise of their theorems. Their evidence comes from their Lean definitions and
proofs, under the reported kernel dependencies.

Source review of [QueueContract](../Mugda2/Experiments/QueueContract.lean) and
[QueueClient](../Mugda2/Experiments/QueueClient.lean) confirms that the client
derives its cost bound from per-operation contracts and an abstract potential.
Its import closure contains the abstract queue and cost monad, not either
concrete queue representation. The interface does not assume the complete
client-cost theorem as a field.

Source review of
[SizedCertificates](../Mugda2/Experiments/SizedCertificates.lean) confirms that
recursive calls after an abstract helper use its height contract; its denotation
proof uses the separate preservation contract. The following limits matter:

- It is a finite host-Lean traversal control, not native Mugda2 `forall^p`.
- Uniformity is proved for helpers lifted from a single raw helper. The ordinary
  dependent-family counterexample changes the raw AST while preserving event
  denotation; it does not disprove denotational noninterference.
- The traversal preserves height bounds and denotation. It is not claimed to
  produce a canonical or idempotent normal form.
- Repeat metrics use structural sums, multiplication, and binary counter lengths
  without expanding the event list. Counter-bit accounting is not a complete
  serialization-size theorem.
- The erasure endpoint is the raw certificate AST and its finite event denotation,
  not `Mugda2.IR` execution or a native machine-cost theorem.

These controls can inform M1.5. Their proofs do not depend on the coverage
adapter, select a foundation, or discharge the later core soundness obligations.
