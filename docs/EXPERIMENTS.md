# Mugda2 — Controlled Design Experiments

**Status:** Proposed protocol v0.1 for M1.5. The host-Lean queue benchmark in
[`Mugda2/Giralf.lean`](../Mugda2/Giralf.lean) is preparatory evidence: it proves
client correctness and a common cost bound across two implementations. The frozen
cross-foundation EXP-A comparison, EXP-B comparison, and integration probe have
not been run; no candidate has been selected. The queue benchmark is separate from
the small `GExpr` calculus and its source-to-IR erasure theorem.

**Implementation update (2026-11-14):** [host controls](experiments/README.md)
now derive the queue client bound from operation contracts and verify finite
certificate traversal through abstract height-preserving helpers. A
[host-control timing registration](experiments/host-controls-v2.json) fixes their
local source snapshot and prospective measurement procedure. Candidate object
rules and toolchain pins remain unresolved; this does not freeze or complete
the cross-foundation comparison. Host proofs and finite observations retain
their explicit boundaries.

These protocols support requirements engineering before implementation. They operationalize [MILESTONES.md](../MILESTONES.md) and the decisions and acceptance criteria in [REQUIREMENTS.md](../REQUIREMENTS.md).

The priority remains **Language Track First**. The small fixtures below exercise language interfaces; they do not import the full Avis–Friedmann development, prove a new complexity bound, or build its application UI.

## 1. Decisions and scope

| Experiment | Decision informed | Requirements exercised |
|---|---|---|
| **EXP-A: abstraction and equality** | `DEC-EQ-001`: intensional control, OTT, or cubical foundation | `REQ-EQ-001`, `REQ-HOST-001`, `REQ-COST-002`, `REQ-COST-003` |
| **EXP-B: modular sized recursion** | `DEC-REC-001`: translation or native recursion | `REQ-SIZE-001`, `REQ-SIZE-002`, `REQ-CORE-003`, `REQ-EXT-001` |
| **Integration probe** | Whether the selected fragments compose as claimed | The above plus `REQ-CERT-001` |

Run EXP-A and EXP-B on their smallest adequate fragments before testing the selected combination. Do not implement six full calculi to obtain a comparison.

The 3–4 week M1.5 timebox covers prototypes, measurements, and a decision report. M2 remains responsible for its formal verification obligations; an experiment cannot discharge them by demonstration alone.

## 2. Freeze the comparison before running it

For each experiment, commit a manifest containing:

1. Protocol version, benchmark sources, input encodings, and expected observations.
2. The exact calculus and fragment for every candidate, with paper/version references and any deviations.
3. Host/prototype/toolchain commits, compiler flags, dependencies, machine details, and resource budgets.
4. The shared abstraction interfaces, opacity boundaries, equations, and permitted assumptions.
5. A cost model: counted event, evaluation strategy, sharing policy, input-size parameter, and measurement endpoint.
6. Named non-negotiable requirements and numerical thresholds for a worthwhile improvement, chosen before results are inspected.
7. The reviewer responsible for recording the decision and resolving inconclusive results.

Keep requirements fixed across candidates. A weaker theorem, transparent helper, extra axiom, or changed cost metric is a changed experiment and requires a new manifest version.

Use these evidence labels in every result:

- `measured`: observed on the recorded finite inputs.
- `checked`: accepted by the named checker under the listed assumptions.
- `proved`: accompanied by the stated theorem and its checked dependencies.
- `unresolved`: a missing argument, unfinished implementation, or resource limit.

An axiom-backed prototype may inform ergonomics, but must identify the axiom and cannot satisfy the corresponding proof gate. Exhausted budgets are `unknown`, not semantic rejection.

## 3. Small language-design fixtures

| ID | Fixed fixture | Observation or obligation |
|---|---|---|
| **FX-01** | A finite ordered set of actions and state `(configuration, cursor)` | One inspection advances the cursor; a selected action updates both configuration and history according to a fixed convention. |
| **FX-02** | Event labels `inspect` and `pivot`, with costs in `Nat × Nat` | A skipped candidate costs `(1, 0)`; an accepted pivot adds `(0, 1)`. Sequential costs add componentwise. |
| **FX-03** | A finite certificate AST with `event`, `sequence`, and `repeat k` | State syntax height, encoded size, and expanded event count separately. `k` has a fixed binary encoding. |
| **FX-04** | Exact rational system `A v = b`, with `A = diag(2, 3)`, `b = (4, 9)` | Check `v = (2, 3)` using exact arithmetic and an explicit invertibility witness; reject an incorrect vector. |

FX-01 is a toy scheduling contract, not a claimed formalization of Cunningham's rule. Its initial cursor, scan origin, update convention, and terminal condition must be explicit.

For FX-03, interpret the AST mathematically as an event sequence; a large repeat must not be expanded merely to measure syntax size. A compact AST alone establishes neither polynomial checking nor an all-parameter lower bound.

For FX-04, a singular but consistent system is a separate negative fixture for the *uniqueness* claim. Checking its equation may succeed; a checker must not thereby certify a unique solution.

These fixtures can be represented initially by specifications and tiny reference models. Production integration remains in Phase II.

## 4. EXP-A — Modular abstraction and equality

### Shared benchmark

Use a finite FIFO queue interface: `empty`, `enqueue`, `dequeue`, and an abstract sequence observation `contents`.
Compare a single-list implementation with a two-list implementation. The common client enqueues an input sequence and then drains the queue.

Freeze these obligations:

- `contents(empty) = []`.
- `contents(enqueue(q, x)) = contents(q) ++ [x]`.
- Dequeue returns the first element and remaining abstract sequence, or reports an empty queue.
- The client returns its input sequence in order.
- The client satisfies the same declared upper-bound contract `cost ≤ B(length input)` after either implementation is installed.

Choose and justify a common budget `B` from a reference count of list-cell visits, then freeze it before comparing foundations. A tighter amortized bound for one implementation is an optional separate result.

The client's source and abstract correctness/cost proof stay unchanged during the swap. Implementation-specific proofs may change and their effort is measured.

### Compared foundations

| Candidate | Required description |
|---|---|
| **Control: minimal intensional `Id`** | Explicit representation relations and simulation records; list any extensionality assumptions actually used. |
| **OTT** | Name the precise observational-equality, proof-irrelevance, quotient, and conversion rules used; do not silently add rules from a different OTT. |
| **Cubical** | Name the interval/path, transport/composition, universe, and univalence fragment used; distinguish computational rules from postulated equalities. |

Raw queue representations need not be equivalent: several concrete states may denote the same sequence. Any quotient, invariant restriction, or abstract specification needed to use univalence is part of the candidate's work and assumptions.

A Lean implementation of an object calculus is different from a benchmark expressed directly with host Lean equality. Label both accurately. Host equality does not determine the intended identity rules of the object language.

### Equations and opacity

Classify each frozen equation as `D` (required by definitional computation), `P` (proved equality), or `S` (simulation/cost property). Record when a candidate supports only a weaker category.

- Require the concrete operation's defining clause to unfold at its designated constructor boundary (`D`).
- Treat abstract sequence laws and the unchanged client theorem as `P` or `S`, as specified in the manifest.
- Keep representation invariants, abstraction maps, and concrete implementations opaque to the client.
- Record all representation-change transports and any local proof edits; do not hide them inside an unmeasured generated file.

A candidate-specific computation example, such as Boolean transport along an equivalence, is a sanity check. It is not evidence of a shared-benchmark advantage unless that capability is an agreed requirement.

### EXP-A decision evidence

Report whether the swap preserved the exact client theorem and budget; which equations computed; what new assumptions were needed; and which proof or checking costs changed. Select a richer foundation only for a requirement it demonstrably serves and an explicit semantic path for the chosen fragment.

## 5. EXP-B — Sized recursion through opaque helpers

### Shared benchmark

Use FX-03's finite certificate trees. `Certificate i` bounds syntax height; it does not bound expanded execution length.
The preprocessor's contract is `preprocess : ∀ᵖ i. Certificate i → Certificate i`, together with a separate certificate-denotation preservation obligation.

The target traversal has the following schematic shape; this is a specification, not implemented syntax:

```text
normalize preprocess (sequence children) =
  sequence (map (fun child => normalize preprocess (preprocess child)) children)
```

Matching a parent exposes a smaller child bound `j < i`. Preprocessing retains bound `j`, so recursion is justified even when the result is not a syntactic subterm.

Use at least two helpers: identity, and removal of semantically neutral wrappers or empty sequential components. Their implementations remain opaque to the traversal checker; only their size and denotation contracts are available.

Start with a specified finite-sized fragment. Large ordinals, a largest size, unrestricted internal parametricity, and coinductive recursion require separate gates. Ordinary `Π` over an inspectable number is not an implementation of the promised parametric quantifier without an additional uniformity argument.

### Compared recursion mechanisms

| Candidate | Evidence to retain |
|---|---|
| **Translation control** | Generated recursors/accessibility arguments, bounds, equation theorems, source-to-target correspondence, and size-erasure account. |
| **Native sized rule** | Exact typing and unfolding rules, permitted size comparisons, pattern constraints, conversion behavior, and the assumptions needed for soundness. |

Use the same surface traversal, helper interfaces, mathematical size bounds, and certificate semantics. Generated proof arguments count toward term size and checking effort for both approaches.

### Required observations

1. The traversal is accepted using helper contracts, without helper-body inspection or inlining `map`.
2. Its designated constructor equation is classified as definitional, propositional, or unsupported, including with an opaque helper and open variables.
3. Admissible changes of irrelevant size annotations preserve the stated runtime behavior; any stronger conversion claim is tested and proved separately.
4. Extraction preserves certificate denotation and erases the specified size evidence at the declared IR endpoint.
5. The implementation cannot bypass the smaller-size obligation through a dependent pattern refinement.

Include a size-increasing helper falsely advertised as preserving its bound, a same-bound recursive call lacking other descent evidence, and a minimized genuine pattern-refinement exploit. Specify the expected diagnostic and why it applies.

Do not classify every rejection as a soundness result. A terminating program missing an annotation belongs to an incompleteness category and may have a positive annotated counterpart. Follow the M1 corpus classifications.

### EXP-B decision evidence

Native recursion earns consideration only for an unmet required computation/modularity property or a pre-registered practical improvement over the best translation, with a credible semantic account. Reduced handwritten proof text alone does not establish that the trusted core must change.

## 6. Minimal semantic gates and integration probe

For each candidate, supply an assumption ledger and a map from proposed rules to the cited calculus or a new proof obligation.
Before a candidate becomes a trusted M2 commitment, identify the exact fragment and the following proof targets:

| Boundary | Required argument |
|---|---|
| Checker to object judgments | Accepted checking implies well-formed environment and declared typing. |
| Object judgments to semantics | Consistency and the appropriate normalization/productivity property for that fragment. |
| Conversion procedure | Soundness, explicit budget behavior, and the claimed sufficient-budget completeness. |
| Surface to core | Typing/meaning preservation and the promised status of defining equations. |
| Source to IR | Behavioral erasure; cost adequacy only for a named metric and endpoint. |

In a 4-week prototype, unfinished targets remain `unresolved`; they are not established by passing examples. A newly proposed rule without a model or reduction argument remains an experimental branch.

The integration probe applies the selected equality mechanism to the sized traversal's denotation-preservation proof and one FX-02 cost contract. Check substitution, erasure, opacity, and conversion together. Separate results for sizes and equality do not automatically prove their combination sound.

Keep upper-bound inequalities, lower-bound inequalities, and exact event preservation distinct. An erasure theorem for returned values does not establish any of them; an IR theorem does not by itself certify the native backend's runtime.

## 7. Measurement and reporting

Use symbolic/open-term cases and a fixed ladder of concrete syntax sizes, depths, and repeat counters. Record the actual instances; select budgets before each candidate runs.

| Dimension | Record |
|---|---|
| User effort | Source tokens/lines, explicit annotations, auxiliary lemmas, and client edits after a swap. |
| Generated evidence | Serialized core bytes/nodes, proof-term size, and dependencies included or shared. |
| Checking | Elaboration and independent rechecking separately; wall time, fuel, peak memory, failures, and `unknown` outcomes. |
| Computation | Required equations achieved by conversion versus explicit theorem rewriting. |
| Runtime claims | Named source/IR events and extracted behavior; keep native timings separate from formal cost theorems. |
| Theory burden | New rules, axioms, outstanding proofs, and interactions requiring reverification. |

For timings, record a warm-up and repeated runs with median and range; preserve raw observations. A timing comparison measures implementations and toolchains, not an intrinsic complexity separation between theories.

## 8. Decision and fallback policy

- **Positive:** a candidate meets all non-negotiable requirements, has the required semantic path, and shows an agreed improvement. Record the exact selected fragment and remaining M2 obligations in the decision ADR.
- **Negative:** preserve the failing example or theorem obligation and its cause. Select the control where it satisfies the requirements; retain the candidate as an explicitly separate research task.
- **Inconclusive or out of time:** retain minimal intensional `Id` plus explicit simulations and the translation approach as the provisional implementation target. Do not label this target verified before its M2 obligations are proved.
- **Control also fails a requirement:** record the conflict and narrow or revise scope through a versioned requirements decision. Do not silently weaken the theorem or declare a winning foundation.

Neither a benchmark win nor this fallback authorizes adding an unchecked rule. Foundational choices are recorded before the core is fixed; later extensions follow the M0 reverification rule.

## 9. Reusable agent outputs

The experiment report is planned at `docs/experiments/m1_5_report.md`; this protocol does not create or claim that report.
Each agent work package should return:

1. Experiment/fixture IDs, manifest version, source and dependency commits, and commands needed to reproduce the result.
2. Exact obligation statements, expected outcomes, allowed assumptions, and candidate artifact paths.
3. Machine-readable outcome records: candidate, input, equation category, checker result, diagnostic, metrics, and evidence label.
4. A minimized failure or a checked proof artifact, with an explicit list of unresolved obligations.
5. A comparison against the frozen control and a proposed decision with its limitations.

Agents may propose amendments in separate patches. They must not alter the frozen target, opacity boundary, budget, or expected classification to make their candidate pass. The decision report retains unsuccessful runs so later work can reproduce and improve on them.
