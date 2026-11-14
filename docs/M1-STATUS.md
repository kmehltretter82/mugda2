# M1 implementation evidence

Status: **in progress**, 2026-11-14. This is a local implementation record, not a
release or an assertion that the M0–M11 roadmap is complete.

## Implemented

- [Architecture records](adr/README.md) state the equality policy, object/host
  boundary, extension rule, and four separate quantitative judgments. Equality
  and recursion selections remain open pending M1.5.
- [Core](../Mugda2/Legacy/Core.lean) adapts Mugda at
  `b0c5b53c92673e4a7d57b218b4050690e719f0e7`. Function signatures under review
  live in `ProvisionalEnv`, outside the accepted signature; bodies cannot unfold
  them. A mutual block commits all functions after every gate passes. Failure
  discards the entire block, including when a caller catches the failure.
- Typed `TCError` distinguishes categorized rejection from `outOfFuel` throughout
  lexing, parsing, scope checking, conversion, admissibility, and call-graph
  analysis. `unsupportedCoverage` separately records unresolved coverage
  obligations. Catch handlers preserve both kinds of uncertainty. Declaration checking requires
  call-graph stabilization and uses budget-aware syntactic comparison.
- [API](../Mugda2/Checker.lean) and [CLI](../Main.lean) share that implementation.
  The CLI emits JSON and returns 0/1/2 for accepted/rejected/unknown. Usage and
  I/O errors return 64/74. Spans explicitly cover the whole document in UTF-8
  bytes; token/declaration locations have not been implemented.
- [Corpus manifest](../tests/legacy/manifest.json) classifies all 79 imported
  `.ma` sources. All have independently reviewed exact outcome expectations,
  preserving semantic intentions when conservative coverage is unresolved. See the
  [semantic discrepancies](M1-CORPUS.md) before interpreting these fixtures.
- [New fixtures](../tests/cases/manifest.json) exercise actual sized-constructor,
  positivity, size-completeness, mutual-block, source-error, and exhaustion
  paths. [Runtime regressions](../Mugda2/Regression.lean) inspect rollback state,
  subsequent lookups, successful mutual commit, and previously swallowed errors.
- [Transaction theorems](../Mugda2/Legacy/Transactions.lean) prove complete
  state rollback on caught failure, preservation of exhaustion through tracing,
  and preservation of checked signature flags by the actual promotion fold.
  The scope collector now derives its bound from the pattern's node count;
  regressions cover more than 1,000 variables and a duplicate after that point.
  These are state and promotion properties, not a proof of full checker soundness.
- [Axiom audit](../scripts/audit_axioms.py) enumerates declarations from Lean's
  environment, including private declarations and definitions in any project
  namespace. Only `propext` and `Quot.sound` are permitted. Additional axioms,
  unfinished proofs, classical choice, native proof evaluation, and authored
  unsafe/partial declarations fail the gate. Compiler-generated recursive
  runtime implementations are recognized through Lean metadata and reported
  separately; their existence does not expand the kernel theorem claim.
  Build failures invalidate reports.
  [Audit tests](../scripts/test_audit_axioms.py) exercise failure cases in isolated
  packages. [CI](../.github/workflows/lean.yml) uses the pinned toolchain.
- Constructive Unicode decoding and the finite [JSON encoder](../Mugda2/Json.lean)
  avoid classical dependencies of the pinned standard-library string/JSON
  interfaces. Source files are read as bytes and invalid UTF-8 is an I/O failure.
- Tri-valued matching distinguishes success, definite mismatch, and neutral
  stuckness. A stuck earlier clause blocks fallthrough; the
  [dependent-conversion exploit](../tests/cases/overlap-conversion.ma) now rejects
  with `typeMismatch`. Matching/erasure lemmas and operational regressions retain
  the first-match distinction. See the [independent review](M1-REVIEW.md).

- [Coverage certificates](COVERAGE.md) now gate function promotion. A finite typed
  pattern-matrix kernel proves coverage, or produces a typed unmatched tuple;
  the adapter validates missing tuples against the original telescope before
  rejection. Complete datatype metadata is sealed only after every constructor
  checks. Failed declarations restore that metadata along with every state field.
  Restricted codata observations use inhabited opaque leaves. Unsupported
  dependent refinements return `unknown`, separately from budget exhaustion.

**Remaining soundness boundary:** the demonstrated nullary empty-type exploit
now rejects, while genuine empty elimination remains accepted. The finite
certificate theorem does not establish the complete dependent source/core
bridge, conversion soundness, normalization, or consistency. These remain
explicit M2 obligations. M1 is not declared complete by passing finite tests.

The [M1.5 host controls](experiments/README.md) now provide compositional queue
cost proofs and height-founded certificate traversal. They use the actual Lean
kernel and do not obtain their proof claims from legacy checker acceptance.

## Reproduce

```sh
make test
lake exe mugda2 check tests/cases/structural-recursion.ma
lake exe mugda2 check --fuel 0 tests/cases/structural-recursion.ma
```

The second checking command returns exit 2 and JSON `unknown`, rather than a
semantic rejection. Further flags select lexical, parser, syntactic-comparison,
and closure budgets. Fuel bounds recursive search depth/iterations; it is not a
global operation count, elapsed-time limit, or a runtime-cost certificate.

The proof dependency ledger at `.lake/build/audit/axioms.json` and CLI outcomes
at `.lake/build/reports/checker-results.json` retain source hashes. They are build artifacts, not committed
claims that automatically remain valid after source changes. `make test` rebuilds
the actual modules and reruns the checks.

## Earlier local verification checkpoint

Earlier on 2026-11-14, before the independent overlap review, `make test`
completed with exit 0 on that source snapshot:

- All 79 pinned legacy sources, 17 modern fixture cases, and one JSON transport
  case passed their exact CLI expectations: **97/97**. Usage, I/O, and invalid
  UTF-8 checks also passed. No legacy expectation remains unresolved.
- State, budget, imported executable-fixture, scope-bound, and Unicode boundary
  regressions passed: **24/24**.
- Audit-tool positive and negative tests passed: **11/11**.
- The environment audit checked **1,005 theorems and 3,854 total declarations**
  across 11 modules. These counts include generated declarations, not only named
  research theorems. Only `propext` and `Quot.sound` occur in their axiom closures.
  The report identifies 185 generated runtime implementations, including 14
  partial deriving artifacts with the boundary described below.
- The original queue demonstration returned the input in order, with 15 declared
  abstract steps for the batched queue and 20 for the single-list queue at n = 5.

This is local evidence. GitHub Actions has been configured but has not run for
these unpublished changes. The M0 foundational experiments and M2–M11 work are
not discharged by this verification record.

The subsequent matching fix passed focused checks of **31 runtime regressions**
and **98 CLI assertions**. The new host executable passed **70 finite
observations**. The historical audit counts above are not claimed for the changed
source tree; the current source-linked audit and full checks must be rerun after
changes, as recorded under `.lake/build/`.

## Matching and host-control checkpoint, before coverage integration

The expanded `make test` run subsequently passed on the matching fix and both
host controls: **98 CLI assertions**, **31 runtime regressions**, **70 finite
control observations**, and **11 audit-tool tests**. The current dependency
report covers **1,179 theorems and 4,285 declarations across 18 modules**, with
only `propext` and `Quot.sound`. Its 199 generated runtime implementation entries
include the same 14 partial deriving artifacts. Counts include generated
declarations and are not counts of new research results.

The later measurement-runner correction was separately checked by **15 fast
tests** and a real same-package elaboration/replay test. Two real-tool tests are
opt-in in the default test suite. The correction did not change Lean sources or
the audited snapshot. [Protocol 2](experiments/host-controls-v2.json) preserves
the original sources, inputs, thresholds, and budgets while recording the
dependency-overlay fix; the first attempt is retained.

These checks established the stated artifact and operational properties at that
snapshot. They did not remove the then-known coverage unsoundness, choose an
object foundation, or complete the first verified language pipeline. Generated
observations remain local until publication is reviewed.

[Protocol 2 measurements](experiments/RESULTS.md) subsequently completed for both
host controls, with one warm-up and five measured source-elaboration/replay pairs
per artifact. No source or budget changed between registration and those runs.
The failed first queue replay is retained as an infrastructure observation,
alongside the first attempt's successful certificate samples. Host timing results
do not select a foundation or close the remaining M2 coverage/consistency gate.

## Coverage checkpoint before the requested pause

`make test` passed on this checkpoint: **129 CLI assertions**, **37 runtime
regressions**, **512 finite Boolean pattern matrices**, **70 host-control
observations**, **11 audit-tool tests**, and **15 runner tests**. The runner's
two real-tool integration tests remain opt-in and were skipped in this run;
their earlier recorded real-tool checks remain historical evidence. Pinned
legacy fixtures retain all 79 original source hashes. Current reports under
`.lake/build/` match the final source, manifest, and executable hashes.

The source-linked audit after coverage integration checks **1,341 theorems and
4,983 declarations across 21 modules**. Their axiom closures contain only
`propext` and `Quot.sound`. The ledger identifies 219 generated recursive runtime
implementations, including the same 14 partial deriving artifacts. These counts
include generated declarations, not just named research results.

The kernel proves `Certificate.sound`, `Result.sound`, and `check_sound` for
finite signature-typed constructor trees. The legacy adapter remains an
executable boundary, rather than a full dependent source/core soundness theorem.
Its unresolved indexed cases include the semantically valid `acc.ma`, `vec.ma`,
and `sort.ma`; they return `unknown/unsupportedCoverage`. `str.ma` now rejects an
actual missing Nat input. Nested successor-size tests do not inherit the
top-level cofunction observation rule and remain explicitly unresolved.

Resume with typed dependent-index coverage and the source/core bridge, followed
by the remaining foundational experiment and verified-core gates below. The
historical timing registrations and reports still describe their original
pre-coverage source snapshot.

## Pinned import and proof boundary

[baseline.json](../tests/legacy/baseline.json) records original source paths and
SHA-256 hashes from the pinned Mugda revision. Imported `.ma` files remain
byte-identical and the test runner verifies their hashes. The adapted Lean files
have the following intentional differences:

| Source | Adaptation |
|---|---|
| `Mugda/Core.lean` | Split into `Legacy/Checking.lean` and `Legacy/Core.lean`. Typed errors, explicit budget propagation, provisional function environment, atomic commit, duplicate-name guards, sealed datatype metadata, structural scope bounds, constructive Unicode decoding, coverage before promotion, and tri-valued matching ported from Mugda `919465fdb995245f395f18423eaf31729fa8cea6`. The legacy namespace `MugdaCore` is retained. |
| `Mugda/Soundness.lean` | Imported unchanged as `Mugda2/Legacy/Soundness.lean`; its model hypotheses and component-level scope are retained. |
| `Mugda/Metatheory.lean` | Import paths and typed-error statements adapted. A constructive equality witness removes a classical dependency. Matching/erasure statements faithfully use `MatchResult` rather than conflate stuckness with `none`; explicit first-match lemmas were added. See the recorded matching-fix revision and review. |
| Last section of `Mugda/Metatheory.lean` | Input definitions moved to `Fixtures.lean`. Eight `native_decide` theorem declarations became runtime assertions in `Regression.lean`; they are no longer advertised as kernel proof artifacts. Their original names are listed below. |

The eight migrated facts are `snat_and_sub_accepted`, `snat_mat_bug_rejected`,
`loop_wrapped_rejected`, `llet_bug_rejected`, `snat_div_source_accepted`,
`cody_nowraps_source_rejected`, `fib_source_evaluates_to_5`, and
`natpair_source_accepted`. Rejection runtime checks now also require the relevant
diagnostic category.

The old pure `compareExpr`/`completeCalls` helpers remain for component theorem
compatibility. They retain their legacy truncation behavior and are **not** the
checking entry point. `typeCheckFuns` uses the `WithFuel` versions. A theorem about
an old helper does not prove the entire new checking path sound.

Lean's recursive `BEq`/`Repr` derivings also create partial native implementations
behind opaque, safe kernel wrappers. The audit identifies their actual deriving
origins and records a `partial-deriving` runtime boundary; it does not prove those
implementations total or establish that a native run matches every kernel
reduction. Legacy checking still relies on Lean's deriving and compilation.
This is distinct from the total recursive definitions' generated implementations
and from authored unsafe/partial code, which remains rejected.

The cost prototype in `Giralf.lean` contains a small `GExpr`/`IRExpr` semantics and
an exact abstract-tick erasure theorem. Its queue proofs are host-Lean programs,
not programs extracted through that calculus. Neither prototype nor adapted
legacy checking establishes the specified M2 core, its semantic consistency,
normalization, conversion completeness, or surface elaboration theorem.

## Remaining gates

1. Review the implementation and retain the same source-linked acceptance
   evidence when publishing. GitHub CI remains unrun for these local changes.
2. Extend the isolated fixtures and model evidence as the supported language
   grows. The new rose-tree fixture reaches the missing traversal measure;
   supporting it through modular sized contracts remains M4 work. Preserve
   unsupported terminating programs and actual counterexamples as different
   categories, and add positive counterparts where justified.
3. Freeze the M1.5 experiment manifests, candidate fragments, numerical
   thresholds, resource budgets, and decision ownership. Recorded architecture
   policies do not themselves establish M0 review or foundational selections.
4. Run EXP-A/EXP-B comparisons and retain the actual measurements, assumptions,
   unsuccessful candidates, and decision report before selecting the M2 core.
5. Implement and prove the finite M2 core, then the M3 interface and M4 sized
   fragment. The existing CLI is an M1 legacy interface, not the planned core
   rechecker or JSON-RPC workbench.

These gates remain part of the roadmap; green checks on the current assertions
do not imply M1 or the first complete language release is finished.
