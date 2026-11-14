# M1.5 host controls

The finite host-Lean controls are implemented and have checked proofs. They are
preparation for the foundation comparison, not completed implementations of three
object calculi. No equality foundation or native recursion rule is selected.

[Protocol 2 results](RESULTS.md) record five successful elaboration and fresh
kernel-replay samples for each artifact. The initial infrastructure failure and
its successful certificate samples are retained separately.

The [registration](host-controls-v2.json) fixes the source cases, input ladder,
equations, abstract cost model, timing procedure, resource budgets, and proposed
decision thresholds. Its audit hash pins the complete Lean/configuration
snapshot. The candidate ledger explicitly retains missing object-rule and
toolchain pins. The cross-foundation comparison remains unfrozen until those
entries are resolved. The [protocol review](PROTOCOL-REVIEW.md) records why the
older preparatory artifacts alone could not discharge that comparison.

## EXP-A: derive a client bound from operation contracts

| Artifact | Checked claim |
|---|---|
| [Cost](../../Mugda2/Cost.lean) and [abstract queue](../../Mugda2/Queue.lean) | Shared cost-instrumented computations, behavioral laws, and generic FIFO client |
| [Operation contract](../../Mugda2/Experiments/QueueContract.lean) | An abstract potential, enqueue charge at most `length(contents q)+2`, dequeue charge at most one |
| [Client proof](../../Mugda2/Experiments/QueueClient.lean) | The operation bounds telescope to the common `n*(n+3)` bound; behavioral correctness uses only queue laws |
| [Implementations](../../Mugda2/Experiments/QueueImplementations.lean) | Both existing concrete representations satisfy those operation contracts and instantiate the same client theorem |

The client imports the contract, abstract queue, and cost monad. Its project
import closure contains no concrete implementation module; the runtime tests
inspect the compiler's dependency output recursively to check this boundary.
The proof may use abstract `contents` and `potential` fields, but cannot unfold
their concrete definitions.

The old `Giralf.BoundedQueueModule` remains as a compatibility bundle. Its field
already states the complete client cost bound, so projecting that field is a
weaker packaging result. The new control instead derives the bound from enqueue
and dequeue contracts without assuming a theorem about the complete client.

Costs count declared abstract operations: queue inspection/pop, one rear-cell
transfer, or one single-list enqueue visit/allocation. Specification observations,
instrumentation overhead, native list allocation, and compiler/runtime work are
not included. This is not a native timing or allocation theorem.

## EXP-B: recurse through an abstract helper

[SizedCertificates.lean](../../Mugda2/Experiments/SizedCertificates.lean) defines
finite event/sequence/repeat trees. A preprocessor supplies only a raw function,
a nonincreasing-height proof, and a denotation-preservation proof. Well-founded
recursion on height permits recursively processing its output even when that
output is not a syntactic subterm. The correctness proof uses those contracts,
without inspecting the helper implementation.

The identity and neutral-root helpers instantiate the same traversal. This is a
contract-preserving traversal, not a proved canonical or idempotent normalizer.
Its constructor equations with an open helper are **P**, proved equality. A
runtime test checks both the explicit equation proof and the failure of `rfl`
for the open sequence equation; a parsing or missing-import error cannot count
as that negative observation.

`SizedCertificate i` is a height-bounded subtype. Lifting a single raw helper
gives a restricted, proved annotation-uniform interface: equal erased inputs
produce equal erased outputs. Arbitrary ordinary quantification over a natural
bound does not provide that restriction. A counterexample changes the erased
tree while preserving its event denotation, so it does not refute denotational
noninterference. None of this implements a native `∀ᵖ` quantifier.

The declared erasure endpoint is the raw certificate AST. It is neither
`Mugda2.IR` nor a theorem about compiled native execution. Pointwise bound/descent
checks demonstrate why a growing helper or a same-bound recursive call lacks the
required evidence; they are not a Mugda2 source typechecker. Native rule checks,
dependent pattern-refinement exploits in that rule, and a composed object-language
semantics remain separate gates.

## Finite observations

```sh
make test
lake exe mugda2-experiments
```

The executable emits 70 JSON records: ten queue sizes and thirty certificate
depth/counter combinations with two helpers. The tests check them against
independent recurrences. A repeat counter of `2^40` is handled without expanding
the event list. Height, AST nodes, canonical counter-bit accounting, and expanded
event counts are separate quantities. Counter-bit accounting is not a serialized
certificate format.

These finite observations were explored during development, before the timing
registration. The registration says so explicitly. They are not retrospectively
described as preregistered comparison results.

## Elaboration and fresh kernel replay

```sh
python3 scripts/run_experiments.py docs/experiments/host-controls-v2.json \
  --validate-only --report .lake/build/experiments/registration.json
python3 scripts/run_experiments.py docs/experiments/host-controls-v2.json \
  --report .lake/build/experiments/host-controls-v2.json
```

Measurement requires a current all-project axiom audit whose hash matches the
registration. Every measured run elaborates the source into a fresh target
`.olean`; a separate `leanchecker --fresh` process replays that actual artifact
and its dependencies into an empty environment. Existing dependency artifacts
and OS caches are reused. This is a second invocation of the same pinned kernel,
not an external kernel implementation or a cold-cache benchmark.

The fixed procedure uses one warm-up and five measured runs, with 300 seconds
for elaboration and 60 seconds for replay. Timeouts retain an `unknown` record
and terminate the child process group. Peak RSS is a per-child observation, with
a 1 GiB guardrail; it is not advertised as a hard allocation limit. Commands,
source/configuration/tool hashes, raw stdout/stderr, fresh artifact parts, and
elapsed/RSS observations are retained under `.lake/build/experiments/`.

The [first registration](host-controls-v1.json) is preserved. Its queue warm-up
replay could not resolve a sibling module after the fresh target shadowed the
package's normal dependency path; no queue proof was checked in that failed
replay. The certificate case completed its five measured samples. The complete
attempt and raw logs are retained as `host-controls-attempt-1.json` and its
artifact directory under `.lake/build/experiments/`.

Version 2 fixes that dependency overlay and records linked dependency hashes,
while leaving the installed artifacts untouched. It was validated using a real
same-package import with an intentionally stale installed target before the new
timing run. Source cases, input ladders, thresholds, and budgets are unchanged.
The two attempts are not silently pooled. Only completed version 2 observations
may support a version 2 timing summary.

Handwritten proof-token and kernel-expression-node metrics remain unresolved
until their exporters/classifiers are frozen. Module `.olean` bytes are recorded
separately. The proposed 25% proof-token improvement, 2x term-node guardrail, and
1.5x replay-time guardrail therefore cannot currently select a richer foundation.
Neither missing data nor timeout is a semantic rejection or a winning result.

## Reference theories and remaining selection gates

The references identify mechanisms to investigate; their separate results do not
establish a combined Mugda2 calculus:

- [Observational Equality Meets CIC, TOPLAS 2025](https://pujet.fr/pdf/toplas25_cicobs.pdf), DOI `10.1145/3719342`.
- [Abstraction Functions as Types, POPL 2026](https://www.cs.cmu.edu/~runmingl/paper/afat.pdf), DOI `10.1145/3776673`.
- [Definitional Proof Irrelevance Made Accessible, LICS 2026](https://doi.org/10.4230/LIPIcs.LICS.2026.41).

An object candidate must still pin its exact rules, implementation revision,
dependency closure, permitted assumptions, and source/core correspondence. The
chosen equality and recursion fragments must pass the integration probe together.
The legacy checker retains the [coverage unsoundness](../M1-REVIEW.md); host-Lean
control proofs do not repair or conceal that boundary. M2 requires the specified
typing, consistency/normalization, conversion, and elaboration theorems before
the first verified language pipeline can be claimed.
