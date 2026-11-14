# Constructor coverage boundary

Function promotion needs a coverage check in addition to clause typing and
termination. Checking each supplied clause cannot establish that every possible
input has a branch. In particular, `fun hole : Empty {}` has one missing input
tuple, `[]`, while `fun eliminate : Empty -> Empty {}` has no possible input.

## Certificate kernel

[`Matrix.lean`](../Mugda2/Coverage/Matrix.lean) describes finite constructor
signatures, signature-typed value trees, patterns, and matrices. `Covers` means
that every typed argument vector matches a supplied row. Positive certificates
use wildcard defaults, complete constructor specialization, or justified
emptiness. `Certificate.sound` proves that these certificates establish `Covers`.
The certificate is independent of the search procedure and its fuel.

A negative result requires an actual typed, unmatched argument vector. Failing
to find a positive certificate is insufficient. Search exhaustion and unsupported
source features remain explicit uncertainty.

The finite-tree model concerns inductive values. It cannot establish that
coinductive inputs are empty merely because no finite constructor tree exists.
The adapter handles a restricted root observation of codata using inhabited
opaque fields; missing codata witnesses remain unresolved. Sized observations
are restricted to the supported infinite-size case. This is a finite observation
approximation, not an inductive interpretation of an entire stream.
Top-level cofunction successor-size patterns use the existing admissibility and
termination gates for the result's observation size. This erasure rule does
not propagate into unrelated constructor fields; the
[nested-size regression](../tests/cases/nested-cofun-size.ma) remains explicitly
unresolved.
Likewise, an underapplied `succ : Nat -> Nat` pattern does not make the function
type `Nat -> Nat` a datatype with just the constructors of `Nat`.

## Legacy adapter

[`Legacy.lean`](../Mugda2/Coverage/Legacy.lean) connects coverage search to the
legacy checking pipeline. Datatype metadata records the complete constructor
inventory and is sealed only after every constructor passes checking. Absence
of a constructor from the signature is not an emptiness proof. The metadata is
part of transactional checking state and rolls back with that state.

Constructor coverage runs before a mutual function block is committed. A failed
or unresolved coverage obligation cannot publish a checked function. Rows with
fewer patterns remain valid when their checked right-hand side handles the
remaining function arguments; a zero-pattern lambda clause covers its inputs.
The existing source scope rule still requires uniform supplied clause arities.

Dependent indices, size constraints, abstract types, and higher-order domains
require care at this boundary. An overapproximation can justify positive
coverage, but a missing tuple in that approximation need not be an actual
source-language input. A coverage rejection must validate its witness at the
original telescope. Unsupported obligations return `unknown` instead.

The JSON API retains exit codes 0/1/2 for accepted/rejected/unknown. Its
`unknown.reason` distinguishes `outOfFuel` from `unsupportedCoverage`;
`context` identifies the unresolved stage. A realized coverage failure has
diagnostic category `coverage`. Whole-document UTF-8 spans remain unchanged.

## Evidence and limits

[`tests/coverage`](../tests/coverage/README.md) records semantic expectations,
including valid empty elimination, missing constructor branches, nested and
correlated matrix holes, short rows, and unresolved advanced cases. Historical
legacy observations are retained separately from the intended outcomes.
[`coverage_matrix_cli.py`](../tests/coverage_matrix_cli.py) compares all 512
subsets of the nine wildcard/constructor rows over `Bool × Bool` against an
independent truth table of all four inputs. Runtime tests inspect full state
rollback and recovery, rather than infer rollback from a CLI exit code.

The finite coverage theorem is not a proof of source elaboration, legacy
conversion, or consistency of the complete language. A formal bridge from a
well-formed dependent source environment to this model remains part of the
M2 core obligations. Foundation selection, sized parametricity, productivity,
and the complete verified pipeline remain separate roadmap gates.
