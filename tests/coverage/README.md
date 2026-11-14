# Coverage specifications

These 30 fixtures specify constructor coverage for the intended total language
and now run in the main CLI suite. Their semantic targets were classified
independently of the old checker outcomes.

`manifest.json` distinguishes two things:

- `semanticIntended` describes whether a complete, sound checker should accept
  the source. A coverage rejection means a well-typed missing argument tuple
  exists. `missingInput` gives one such tuple where useful; `[]` is the unique
  input tuple for a nullary function.
- `expected` describes the conservative integration target. Dependent indices,
  sized indices, and recursive emptiness originally required `unknown` until
  justified support was implemented. The certificate kernel now proves recursive
  inductive emptiness; the adapter covers the complete sized matrix and checks
  concrete indexed/sized missing witnesses. The two remaining indexed
  impossibility cases require `unknown`. Unknown is not evidence of invalidity.

The diagnostic category is `coverage`. Unresolved typed coverage has reason
`unsupportedCoverage`, distinct from search exhaustion (`outOfFuel`). Unknown
records name their stage and the remaining obligation.

`observed-legacy.json` records a read-only run of the existing compiled checker,
with its binary hash and each source hash. That binary accepted 27 fixtures and
rejected three in existing diagnostic categories. Nine semantically invalid
definitions were accepted. These observations are historical evidence of the
gap, separate from the intended expectations.

The highest-priority cases cover the closed `Empty` exploit, nullary definitions,
both missing `Nat` constructors, nested constructor holes, correlated holes in
multiple arguments, empty first and later domains, and mutual-block rejection.
The remaining cases protect polymorphic wildcards, constructor arguments that
are empty, recursive emptiness, indexed impossibility, sized patterns, dot
validation, and first-match conversion.

Coverage is over the argument telescope, not the result datatype. No clauses
for `Empty -> Nat` is valid; no clauses for `Empty` is invalid. A constructor
name alone does not establish an inhabited datatype: `box : Empty -> Box` and
`roll : Void -> Void` do not supply closed finite values. A finite-tree coverage
procedure must not infer that a coinductive type is empty from its lack of finite
trees.

Rows may have fewer patterns than the function's Pi telescope. The checker
checks their right-hand sides at the remaining function type, and `matchClause`
applies the right-hand side to surplus actual arguments. The two lambda cases
protect valid wildcard suffixes, including a zero-pattern clause whose body is
a lambda.

`first-match.ma` requires overlapping rows to retain source order.
`neutral-first-match-barrier.ma` retains the previously fixed rule that a stuck
earlier constructor row blocks fallback during conversion. Exhaustiveness alone
does not justify evaluating a later row.

The manifest's `apiScenarios` entry specifies a rollback check using the actual
`TypeCheck` state API. Whole-document CLI rejection cannot establish rollback.
After a caught coverage failure, every saved state field must survive unchanged,
neither mutual function may be visible, and a corrected block using those names
must still commit. The recovery fixture is also independently valid source.

The [coverage boundary](../../docs/COVERAGE.md) describes the finite certificate
theorem and its conservative legacy adapter. These fixtures are operational
evidence, not a proof of complete language consistency.
