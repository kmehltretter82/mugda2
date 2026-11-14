# M1: semantic regression corpus

**Status:** All 79 imported `.ma` files have source-reviewed classifications and
strict executable expectations. These include the 39 curated baseline fixtures
and 40 additional reviews against the actual checking rules. Executable
validation is recorded separately from those expectations. This remains
**partial M1 evidence**, not a completed checker or release gate.

## Source and purpose

[The manifest](../tests/legacy/manifest.json) records each source's semantic role,
rationale, curated-suite membership, and expected result where established.
The imported sources and [provenance inventory](../tests/legacy/baseline.json)
come from Mugda revision `b0c5b53c92673e4a7d57b218b4050690e719f0e7`.
The baseline Makefile selects 22 positive and 17 negative fixtures. Its flat
success/failure policy does not establish why a negative fixture was rejected,
whether every positive fixture expresses its intended algorithm, or soundness
of the language.

The corpus distinguishes these questions:

1. What does this source attempt to express, and is it a genuine divergence or
   refinement exploit, an unsupported terminating program, or a source error?
2. Which pipeline outcome and diagnostic must a particular regression assert?
3. Which language fragment and foundation justify that expectation?

A filename beginning with `bad` is not sufficient evidence of a soundness
counterexample. A nonzero process exit or an exhausted budget is not sufficient
evidence that the intended semantic check rejected a program.

## Classifications

| Category | Meaning and examples |
|---|---|
| `PositiveExample` | A positive language exercise or exploratory positive source; curated status is recorded separately. Acceptance does not prove the intended algorithm correct. |
| `SoundnessCounterexample` | An actual recursive cycle, unproductive computation, missing valid input, or historical refinement/admissibility exploit. Examples include `llet_bug.ma`, `snat_mat_bug.ma`, `stree_mat_bug.ma`, and `str.ma`. |
| `UnsupportedTerminating` | A valid total-language target whose descent or dependent coverage is not established by this checker. Examples include division in `badterm2.ma`, breadth-first traversal in `rose.ma`, and indexed coverage in `acc.ma` / `vec.ma`. |
| `UnsupportedCoverage` | A coverage obligation outside the current bridge, without a claimed semantic rejection. The modern nested cofunction size-pattern fixture exercises this boundary. |
| `IncompleteAnnotation` | Missing evidence prevents acceptance without establishing a reachable divergence. `badterm.ma` recurses over an empty datatype; the checker does not infer vacuous termination from that emptiness. |
| `FoundationDependent` | The meaning of acceptance depends on the identity theory. `k.ma` is accepted by the legacy checker; general Mugda2 K/UIP policy remains open under ADR-01. |
| `SourceError` | Malformed syntax, scope, or typing masks the intended language experiment. `badco.ma`, `badlist.ma`, and the original `hang.ma` fall here. |
| `ResourceExhaustion` | A deliberately budget-limited run must return `unknown` with reason `outOfFuel`. Use a well-scoped modern fixture and name the exhausted budget; an unrelated earlier error does not exercise this category. |

An inventory entry may have a semantic classification while `expected` is
`null`. This means its exact supported-pipeline result remains unresolved. It
does not mean acceptance, a skipped successful test, or permission to adopt the
current checker's observed behavior as its specification.

The additional reviewed entries include a `checkingBoundary` record naming the
concrete parser, scope, type, admissibility, or termination rule and the argument
for that expectation. These records were written before executing those new
assertions. In particular, whole-file parsing and scope checking precede all
type checking: a later source error can mask an earlier declaration's intended
typing test.

## Strict expectations

Each manifest entry uses a unique `id`, repository-relative `path`, `category`,
`reason`, and `baselineSuite` (`positive`, `negative`, or `null`). `expected` is
either `null` or a result record:

```json
{"status": "accepted"}
{"status": "rejected", "diagnostic": "patternRefinement"}
{"status": "unknown", "reason": "outOfFuel", "context": "termination comparison"}
{"status": "unknown", "reason": "unsupportedCoverage", "context": "coverage of head: an erased coverage hole is not a checked typed input"}
```

Budgeted cases may provide `budget` with `checkerFuel`, `comparisonFuel`,
`closureFuel`, `lexerFuel`, and `parserFuel` overrides. If a source appears under
multiple budgets, use different case IDs. Missing overrides use the checker's
documented defaults.

Every asserted rejection fixes **one exact category**, not a list of acceptable
failures. Stable categories are `parse`, `scope`, `typeMismatch`, `admissibility`,
`sizePatternCompleteness`, `termination`, `patternRefinement`, `positivity`, and `coverage`.
Unexpected `unknown`, an earlier source failure replacing a semantic diagnostic,
or a different diagnostic fails the regression. Report unresolved inventory
entries separately from executed assertions.
Budget regressions also require the exact exhausted stage in `expected.context`;
an exhaustion at an unrelated stage cannot satisfy their contract.

The expectation records were chosen from source review, the curated baseline
contract, and the pipeline's specified checks. Do not regenerate them from
checker output. A failure requires investigation of the fixture, checking rule,
or recorded contract; changing the expected category solely to make a run pass
would destroy the regression's purpose.

## Discrepancies and baseline holes

These findings preserve the imported sources and explicitly reconcile differences
with [the original roadmap classification](../MILESTONES.md#m1--harden-the-lean-4-baseline-and-classify-the-corpus).

- **`badterm3.ma` and `badterm4.ma`:** The roadmap lists these as incomplete
  annotations. Their equations are respectively `F x = F (F x)` and `f = f` at
  type `Set -> Set`. Both give unguarded recursion on inhabited inputs. The
  manifest classifies them as `SoundnessCounterexample`, with exact
  `termination` rejection. Merely adding a size annotation cannot repair the
  identical recursive behavior.
- **`badterm.ma`:** Its `Unit` datatype has no constructors. Keep its
  `IncompleteAnnotation` classification and exact `termination` rejection while
  recording that no closed Unit input witnesses divergence. The separate
  [empty-domain fixture](../tests/cases/empty-domain.ma) supplies an accepted
  counterpart using explicit empty elimination.
- **`badterm2.ma`:** The subtraction-based division algorithm needs an exposed
  descent contract. The separate [sized division
  fixture](../tests/cases/sized-division.ma) supplies a positive counterpart
  without modifying the imported source or overlooking bad clauses mixed into
  historical `snat.ma`.
- **`rose.ma`:** Breadth-first traversal needs a worklist measure, but the
  imported file fails earlier: `List` declares `A` without a `+` strictly positive
  parameter annotation. The positivity checker therefore rejects the nested
  occurrence `List (Rose A)` in the `rose` constructor. Preserve the
  `UnsupportedTerminating` classification for the intended traversal and assert
  the actual source's `positivity` obstruction. The separate
  [positively annotated List fixture](../tests/cases/rose-positive-parameter.ma)
  reaches the intended traversal `termination` obstruction; the imported file
  supplies neither that coverage nor a positive sized traversal counterpart.
- **`badco.ma` and `badlist.ma`:** The roadmap lists these as soundness
  counterexamples. Both declare an ordinary, unsized datatype/codatatype indexed
  by `Size`; the illegal Set-valued index produces `typeMismatch` before the
  intended sized-constructor check. They are `SourceError` regressions. Separate
  [sized-data](../tests/cases/bad-sized-data.ma) and
  [sized-codata](../tests/cases/bad-sized-codata.ma) fixtures have `sized` present
  and isolate the intended invalid constructor target.
- **`hang.ma`:** Mutual `f` refers to `F` in its signature before the scope
  checker makes `F` available for other signatures. Its exact adequate-budget
  result is `rejected/scope`. Lowering checker fuel cannot honestly demonstrate
  conversion exhaustion because scope checking occurs first. Use a separately
  well-scoped fixture for each budget path; keep `unknown/outOfFuel` distinct
  from semantic rejection.
- **`badpos.ma`:** The negative constructors are commented out. The active
  declarations are positive examples, so this file does not exercise a
  positivity rejection.
- **`ord.ma` and `sort.ma`:** These are curated source examples with important
  limitations. `ord.ma` uses variable pattern `ozero` rather than constructor
  `ordzero`; `sort.ma` uses variable patterns `true` and `false` rather than
  constructors `tt` and `ff`. Legacy acceptance therefore does not prove the
  intended constructor equations, Boolean branching, sorting correctness, or
  totality. `sort.ma` now returns `unknown/unsupportedCoverage` for the indexed
  `insert` matrix, while its intended typing/coverage verdict remains accepted.
- **`str.ma`:** Its clause head `cons` inside `zeroes` is ignored by the legacy
  parser, leaving only a successor input row. The closed input `zero : Nat` is
  missing. It now rejects with `coverage` and is classified as a counterexample;
  emptiness of result `Stream zero` cannot justify missing a valid input.
- **`acc.ma` and `vec.ma`:** Both remain valid total-language targets. `Lt x zero`
  needs dependent-index emptiness checking; `Vec A (succ n)` needs exclusion of
  the incompatible nil constructor. The conservative bridge returns
  `unknown/unsupportedCoverage` rather than claim a false missing input. These
  expectations preserve `semanticIntended: accepted` and an explicit obligation.
- **Mixed exploratory files:** `snat.ma`, `stream.ma`, `sp4.ma`, and several
  others combine plausible positive code with explicitly bad code, old forms,
  or unsupported declarations. Whole-file failure cannot stand in for a
  narrowly targeted checker obligation. Their first obstructions are recorded
  per entry. In particular, `snat.ma` correctly declares `sized data SNat`, then
  rejects `wkSNat2 : (i : Size) -> SNat ($ i) -> SNat i` for `admissibility`:
  the input size is `$ i` rather than the required inductive witness at `i`,
  and the fallback nonoccurrence check fails because `i` occurs in that input.
  This precedes checking the explicitly incomplete clauses. Its `SourceError`
  classification records that invalid declaration among positive arithmetic
  examples, without claiming a separately demonstrated closed divergence.
  `sp4.ma` first rejects a mixed `fun`/`cofun` mutual block during scope checking,
  and `stream.ma` first rejects the size-dependent input of `wkStream_ok`.
- **Additional source restrictions:** `set.ma` uses `A -> Set` as an ordinary
  datatype index outside the imported Set-valued-index fragment. `subtype.ma`
  repeats `_`, which is an ordinary identifier rather than wildcard syntax.
  Their exact whole-file obstructions are `typeMismatch` and `scope`
  respectively; the mathematical ideas themselves are not refuted.
- **Unsized positive intentions:** `natstream.ma` and `proc.ma` express intended
  productive examples, but their first cofunctions recurse through unsized
  coinductive constructors. The imported size-change rule supplies neither a
  guarded-output argument nor a sized decrease, so they reject for `termination`.
  `sum.ma` is an unsupported terminating traversal because wrapping a smaller
  natural number in a different constructor loses the order relation used by
  this particular checker.
- **`perf.ma`:** Its first mutual block contains the recursive-call cycle
  `f(2,2) → f(4,1) → g(3,1) → g(2,2) → f(2,2)`, using unary natural numbers.
  The helper `h` traverses both arguments, so these recursive calls cannot be
  discarded. Classify the whole file as `SoundnessCounterexample` and require
  `termination` rejection; the later Wahlstedt-style stress block does not
  repair the first block's divergent computation.

## Remaining M1 acceptance work

Validate every reviewed assertion and retain independent boundary arguments;
add or link further positive counterparts where annotations make a terminating algorithm
expressible; and retain modern isolated fixtures for constructor admissibility,
positivity, pattern safety, each budget path, and transactional mutual blocks.
Run the corpus through the same checking engine and structured CLI used by human
and agent clients. Failure, exhaustion, or cancellation of a mutual block must
also be checked against the accepted environment before the attempt.

This corpus records the legacy checker boundary. It does not select F0 equality,
establish the M2 semantic theorems, or provide the completed M1.5 experiments.
