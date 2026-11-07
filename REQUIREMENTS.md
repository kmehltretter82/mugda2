# Mugda2 Requirements Baseline

**Version:** proposed 0.1 · **Date:** 2026-11-07 · **Stage:** requirements and documentation.

**Source baseline:** [README.md](README.md) and [MILESTONES.md](MILESTONES.md) at commit
d228f6e982136ab55ae300ff3a06d038341669d9.
The referenced Mugda implementation baseline is [mugda @ b0c5b53](https://github.com/kmehltretter82/mugda/tree/b0c5b53).
These pins identify the evidence used to write this document; they do not freeze future toolchain choices.

This is a proposed acceptance contract, not a report of implemented features or proved theorems.
The current work establishes requirements and teaching documentation before implementation.
No equality foundation, native recursion rule, or combined sized/cost calculus is selected by publishing this file.

## 1. Intent, proposals, and authority

### Established project intent

- Develop Mugda2 as a dependent programming language; the language track comes first.
- Make termination/productivity, modular abstraction, and computational cost expressible and checkable.
- Support both human users and agents constructing independently checked evidence.
- Use Lean 4 for implementation, metatheory, and explicit connections to existing formal mathematics.
- Use the Avis–Friedmann development as a demanding later application, not as the language's entire identity.
- Teach the ideas at introductory, intermediate, and advanced levels.

### Architecture still requiring evidence

The roadmap proposes a native object language implemented in Lean, explicit proof bridges, a small rechecker,
and successive fragments F0, F-size, and F-cost. This baseline retains that direction while leaving the
equality theory, recursion mechanism, size semantics, surface syntax, and first cost model open.
The intensional control, OTT, and cubical variants are experiment candidates, not three promised products.
References to published systems identify techniques to investigate; their separate soundness results do not
establish soundness of a Mugda2 combination.

### Reading the requirements

- **MUST** means required for the stated release or supported fragment once this baseline is adopted.
- **SHOULD** means the default; an alternative needs a recorded reason and evidence of the resulting behavior.
- **MAY** identifies optional scope.
- A requirement outside the current release slice does not block that slice.
- An open research question is not a promised theorem or implementation feature.

Requirement IDs are stable. Changes should preserve IDs, record changed acceptance conditions, and identify
affected decisions and evidence. A source document's newer wording does not silently change this baseline.
Where documents disagree, record the discrepancy and reconcile it explicitly.

## 2. Users, tasks, and boundaries

| User | Principal task | Observable success |
|---|---|---|
| Language researcher | Define a recursive abstraction and investigate its typing rules | The accepted fragment, obligations, and metatheoretic assumptions are inspectable |
| Algorithm researcher | Specify behavior and cost across an implementation boundary | A client proof survives a certified implementation change |
| Learner | Understand a concept and work through an example | The explanation separates intuition, formal rules, and implementation status |
| Agent or tool author | Propose a program, proof, or certificate | Structured feedback and the same acceptance gate used for human submissions |

### Scope

The first implementation release is the finite language pipeline described in Section 10.
Later releases may add productive computations, lower bounds, proof exchange, and application-specific tools.
The legacy language is a regression source whose examples require semantic classification, not an infallible oracle.

### Non-goals for the first implementation release

- A full HoTT library or simultaneous implementation of all equality candidates.
- General large-size parametricity, unrestricted recursion, or automatic complexity inference for arbitrary programs.
- A new simplex complexity theorem as a condition for shipping the language.
- A polynomial-time checker for arbitrary dependent proofs.
- Proof that Lean's native compiler, the C compiler, or the operating system preserves source cost.
- Distributed execution, a package ecosystem comparable in size to Lean's, or production hosting of a public service.

## 3. Trust and host-language boundaries

### REQ-TRUST-001 — State exactly what is checked

Every exported result MUST identify its fragment, theorem or certificate claim, premises, checker version,
and material trusted assumptions. Documentation MUST distinguish planned, experimental, and verified results.
**Acceptance evidence:** an example result record and a release inventory linking each verification claim to its proof.

### REQ-TRUST-002 — Audit proof dependencies

Release proof artifacts MUST have reproducible dependency and axiom reports.
Unfinished proofs, additional axioms, native evaluation, and external computations MUST be reported explicitly;
the presence of standard Lean axioms MUST be interpreted against the declared trust policy.
**Acceptance evidence:** pinned builds and dependency reports; no unfinished proof advertised as completed verification.

### REQ-HOST-001 — Specify every object/host bridge

The project MUST distinguish implementing Mugda2 in Lean from producing a proof of a host Lean proposition.
Each bridge MUST state its domain, translation or checker, semantic relation, and soundness theorem.
Importing a Lake package alone MUST NOT count as such a bridge.
**Acceptance evidence:** one worked claim whose source statement, object artifact, host specification, and connecting theorem are visible.

### REQ-HOST-002 — Reproduce imported mathematics

Imported developments MUST record exact revisions, compatible toolchains, and relevant assumptions.
A migration or adaptation MUST preserve the declared mathematical statement or document its change.
**Acceptance evidence:** a clean build of the selected dependency closure and a statement comparison for adapted results.

## 4. Core language and verification

### REQ-CORE-001 — Give each fragment an independent specification

Each supported fragment MUST define syntax, environments, typing, conversion, evaluation, and permitted assumptions.
Its semantic justification MUST state precisely which consistency, normalization, or productivity properties hold.
Termination of finite evaluation and productivity of infinite observations MUST be separate claims.
**Acceptance evidence:** a fragment specification and named metatheorems; a checker implementation alone is insufficient.

### REQ-CORE-002 — Recheck declarations and their environments

Accepted declarations MUST have independently checked core evidence in a well-formed accepted environment.
The checker soundness statement MUST cover environment validity as well as term typing.
**Acceptance evidence:** a theorem connecting acceptance to well-formedness and typing, plus dependency-validation tests.

### REQ-CORE-003 — Separate conversion from resource budgets

The conversion algorithm MUST be sound for the declared mathematical conversion relation.
For its claimed decidable fragment, well-typed inputs MUST admit sufficient fuel to obtain the correct decision.
Budget exhaustion MUST return unknown; mathematical existence of sufficient fuel MUST NOT be presented as a
practical bound, an automatic retry policy, or a performance guarantee.
**Acceptance evidence:** soundness and sufficient-budget completeness statements, exhaustion tests, and measured benchmark budgets.

### REQ-CORE-004 — Preserve source meaning during elaboration

Successful elaboration MUST produce a core term of the translated type and preserve the specified source semantics.
The supported defining equations and their status as definitional or propositional MUST be explicit.
Well-scoped but ill-typed input MUST NOT be assumed to elaborate successfully.
**Acceptance evidence:** a preservation theorem for the supported surface fragment and examples exercising name binding and equations.

### REQ-CORE-005 — Reverify extensions

Every feature added after F0 MUST either translate into an already justified fragment with preservation evidence,
or extend the core specification and re-establish the applicable checker, conversion, and semantic obligations.
An earlier fragment's proof MUST NOT be presented as covering new rules.
**Acceptance evidence:** a fragment/version matrix recording changed rules, new assumptions, and discharged obligations.

### REQ-EQ-001 — Select equality by an explicit decision

Equality-dependent behavior MUST follow the selected foundation.
Under the cited OTT candidate, UIP is intended; under a general intensional/cubical path interpretation,
unrestricted K is not an accepted default. A strict-equality/path combination requires its own specification.
**Acceptance evidence:** DEC-EQ-001, foundation-indexed regression expectations, and an explanation of the chosen equality.

### REQ-EQ-002 — Include computation and matching in the equality decision

The equality specification MUST cover conversion, transport/elimination, universes, dependent matching, and relevance.
A cubical choice MUST be reflected in the initial core architecture; later library milestones cannot supply that choice retroactively.
**Acceptance evidence:** the chosen fragment's rules and small computation examples, not only a list of extensionality axioms.

## 5. Sized programming and declaration safety

### REQ-SIZE-001 — Check recursion across opaque interfaces

The sized fragment MUST support a documented benchmark whose recursive calls pass through a separately checked,
size-preserving helper. Checking clients MUST use its interface rather than inspecting its implementation.
**Acceptance evidence:** the certificate-normalizer benchmark in EXP-B, with the helper opaque and its size contract explicit.

### REQ-SIZE-002 — Require evidence for native recursion

A native sized-recursion rule MUST be justified against a standard-recursion translation on the same benchmark,
including required computation equations, generated evidence size, checking cost, and metatheoretic obligations.
Reducing user-written proof boilerplate alone MUST NOT establish that a trusted core extension is necessary.
**Acceptance evidence:** DEC-REC-001 and the controlled EXP-B comparison; either result may be a valid project outcome.

### REQ-SIZE-003 — Specify parametricity and erasure

Parametric size abstraction MUST be distinguished from ordinary dependent quantification.
The supported size operations, inequalities, subtyping, and elimination restrictions MUST be explicit.
Erasure or size-uniformity claims MUST be proved for the selected fragment, not inferred from notation alone.
**Acceptance evidence:** size-parametricity/erasure statements and rejection examples attempting forbidden size-dependent behavior.

### REQ-SIZE-004 — Preserve dependent pattern semantics

Pattern elaboration MUST justify branch refinements, inaccessible patterns, constructor constraints, and first-match behavior.
Termination arguments MUST use only size relations valid under those refinements.
**Acceptance evidence:** case-tree correctness for the supported patterns and the classified historical counterexamples.

### REQ-CHECK-001 — Report acceptance, rejection, and uncertainty separately

The checker, CLI, API, and documentation MUST agree on accepted, rejected, and unknown outcomes.
Rejections MUST identify a diagnostic category; exhaustion MUST NOT be counted as a soundness-counterexample rejection.
**Acceptance evidence:** end-to-end fixtures asserting outcome and diagnostic category at each interface.

### REQ-CHECK-002 — Commit mutual declarations transactionally

Mutual declarations MUST remain provisional until every required obligation succeeds.
Failure, exhaustion, or cancellation MUST leave the previously accepted environment unchanged.
**Acceptance evidence:** a partially failing mutual block and an environment comparison before and after the attempt.

### REQ-CHECK-003 — Classify the regression corpus semantically

The corpus MUST distinguish actual counterexamples, unsupported terminating programs, incomplete annotations,
foundation-dependent programs, and budget-sensitive runs. Classifications MUST carry a rationale.
**Acceptance evidence:** a manifest with exact expected outcomes and annotated positive counterparts where appropriate.

## 6. Cost, abstraction, and executable extraction

### REQ-COST-001 — Keep the four quantities distinct

Specifications MUST distinguish input/output encoding size, construction cost, algorithm execution cost,
and certificate size/checking cost. Termination or a compact rank representation MUST NOT imply a polynomial cost bound.
**Acceptance evidence:** one benchmark report exposing all relevant quantities and leaving unsupported ones explicitly unclaimed.

### REQ-COST-002 — Name the metric and semantic endpoint

Every cost claim MUST define its counted events, units, evaluation/sharing assumptions, and semantic endpoint.
Pivots, candidate inspections, arithmetic operations, allocations, and bit operations MUST remain distinguishable.
**Acceptance evidence:** a costed evaluation or transition relation and an example demonstrating different metrics on the same program.

### REQ-COST-003 — Preserve the direction of cost claims

Upper bounds, lower bounds, and exact event counts MUST have separately stated preservation conditions.
A transformation proving that target cost is no larger than source cost MUST NOT be used to transfer a source lower bound.
**Acceptance evidence:** explicit inequalities or exact-cost simulation theorems for each supported transformation.

### REQ-COST-004 — Preserve abstraction in client reasoning

A client MUST be verifiable against a declared behavioral and resource interface without access to implementation details.
Replacing the component MUST require a proof that the replacement satisfies that interface.
**Acceptance evidence:** EXP-A's two implementations with the same client proof and explicit cost obligations.

### REQ-EXT-001 — Bound extraction claims by the proved endpoint

Extraction MUST have separate behavioral and cost-adequacy statements for the chosen source-to-IR translation.
Any use of Lean's native backend, a C compiler, or runtime support MUST state its trust assumptions.
A source-to-IR theorem MUST NOT be advertised as a theorem about native machine time or allocations without an additional bridge.
**Acceptance evidence:** source/IR semantics, the cost relation actually proved, and a documented boundary for native execution.

### REQ-EXT-002 — Erase only computationally irrelevant evidence

Proofs, sizes, and ghost credits MAY be erased only under the fragment's relevance and preservation rules.
Executable output MUST contain a computable witness; an abstract existential or noncomputable definition alone is insufficient.
**Acceptance evidence:** an extracted finite program, its source witness, and behavioral and cost-adequacy proofs.

## 7. Human, agent, and teaching interfaces

### REQ-TOOL-001 — Use one authoritative checking engine

CLI, browser, and agent clients MUST obtain acceptance from the same versioned engine.
A legacy or independent implementation MAY support differential testing but MUST NOT silently become a second authority.
**Acceptance evidence:** the same fixtures produce equivalent outcomes through all supported clients.

### REQ-TOOL-002 — Isolate candidate exploration

Search snapshots MUST be immutable or equivalently isolated, with explicit parent versions.
An agent candidate MUST NOT change the goal, assumptions, accepted declarations, or claimed metric without a visible change record.
**Acceptance evidence:** branching/replay fixtures and a human and agent completing the same fixed obligation.

### REQ-TOOL-003 — Explain obligations structurally

Diagnostics SHOULD include source locations, local context, the failed obligation, and machine-readable categories.
Users MUST be able to inspect the core claim and assumptions behind an accepted result.
**Acceptance evidence:** examples for a pattern-refinement error, unsolved size relation, exhausted budget, and accepted contract.

### REQ-DOC-001 — Teach at three levels

HTML documentation MUST offer an introductory explanation, an intermediate worked example, and an advanced account
of rules, semantics, proof obligations, and references for the central concepts.
Examples MUST distinguish executable, schematic, experimental, and proposed material.
**Acceptance evidence:** connected learning paths covering sizes, equality choices, cost, proof boundaries, and the initial release.

### REQ-DOC-002 — Make the documentation usable independently

The teaching site SHOULD be readable as static HTML, support keyboard navigation, work on narrow screens,
and expose source/reference links. It MUST not imply that the planned checker or live workbench already exists.
**Acceptance evidence:** link and rendering checks, accessible navigation, and visible implementation-status labels.

## 8. Later application requirements

### REQ-EXEC-001 — Include algorithm memory in execution contracts

Application states MUST include all history affecting the next move, including Cunningham's cursor.
Initial states, ordering, tie policy, legal transitions, halting, and counted events MUST be specified.
**Acceptance evidence:** a cursor-sensitive example and a simulation theorem preserving the stated execution contract.

### REQ-APP-001 — Certify exact evaluation with uniqueness

A proposed rational policy value or basis solution MUST be linked to the specification by both its defining
linear equations and a justified uniqueness condition, such as invertibility or the applicable transience theorem.
**Acceptance evidence:** a host Lean checker theorem for the chosen nonterminal-state model and malformed-certificate tests.

### REQ-CERT-001 — State certificate complexity in the correct parameter

A restricted phase-certificate format MUST have separate soundness, encoded-size, checking-cost, and uniformity claims.
Polynomial checking in a family parameter n MUST NOT be called polynomial in encoded length N without a proved
relation n ≤ poly(N), or a direct bound in N. The bound N ≤ poly(n) alone does not supply that implication.
**Acceptance evidence:** a specified encoding, bit-cost model, parameter relations, and all-n generator/checker theorem.

### REQ-CERT-002 — Bound generation separately from checking

An efficiency claim for instance or certificate generation MUST have its own cost bound and parameter encoding.
Constructive uniformity, polynomial output size, and polynomial checking do not establish efficient generation.
A bound polynomial in n MUST NOT be called polynomial in the binary input length of n, which is logarithmic in n.
**Acceptance evidence:** generator work and output-size bounds stated in n, encoded input length, or an explicit output-sensitive measure.

### REQ-SCI-001 — Separate established mathematics from research targets

Research outputs MUST distinguish a formalization of a known result, an implementation contribution,
a conjecture, a conditional theorem, and a claimed new mathematical result.
Novelty claims MUST identify the literature comparison and exact strengthened statement.
**Acceptance evidence:** a theorem-status record; a counterexample or revised hypothesis is an acceptable research outcome.

## 9. Open decisions and controlled experiments

All decisions below are open in this baseline; roadmap defaults are fallback proposals, not completed selections.
Experiment criteria MUST be recorded before comparison, with equal benchmarks and explicit unsupported features.
The [experiment protocol](docs/EXPERIMENTS.md) specifies EXP-A, EXP-B, and their shared fixtures.

| Decision | Question | Evidence and selection criterion |
|---|---|---|
| DEC-EQ-001 | Intensional control, OTT, or cubical foundation? | EXP-A: identical client/interface swap; compare required equations, proof burden, checking cost, and new semantic obligations |
| DEC-REC-001 | Translate sized recursion or add a native rule? | EXP-B: opaque helper traversal; compare source obligations, core size, computation equations, and verification effort |
| DEC-SIZE-001 | Which size and parametricity fragment is supported first? | A written grammar, decidable constraint fragment or explicit evidence discipline, and a tractable semantic argument |
| DEC-HOST-001 | Which object/host bridge ships first? | One complete certificate or definition exchange with source fidelity and host soundness; no unsupported universal embedding claim |
| DEC-COST-001 | Which first cost model and IR endpoint? | An operational model supporting the finite abstraction benchmark and a defensible adequacy theorem |
| DEC-SYNTAX-001 | Standalone syntax, embedded DSL, or both? | The same worked example, inspectable generated core, and maintained single-engine semantics |

EXP-A and EXP-B are planned comparisons, not experiments already performed.
The minimal intensional/translation control is the proposed fallback if an alternative lacks a demonstrated advantage.
Choosing a fallback still requires the decision record and a precise supported fragment.

## 10. Release slices and acceptance evidence

### D0 — Requirements and teaching documentation: current work

Deliver this proposed baseline, an experiment protocol, and the three-level HTML learning material.
Document open decisions and unproved research questions. No implementation or foundational choice is implied.
Start with the [HTML concept guide](docs/index.html); the [README](README.md) explains local viewing.

### L1 — First implementation release: a finite language pipeline

Deliver the hardened checker interface, one selected F0, a small justified sized fragment, one finite cost model,
one modular client/component benchmark, and extraction to a specified IR. A minimal CLI/API is sufficient;
the full research workbench, streams, cubical libraries, and Avis–Friedmann branches are not release blockers.
The proposed roadmap alignment is M1, the selected finite M2 fragment, the minimal M3 checking interface,
the finite portion of M4, and M5A through the stated IR endpoint. Native-backend integration is separately staged.
Any smaller F0-only preview MUST identify its missing L1 obligations and must not claim the complete pipeline.

| Acceptance evidence | Required content |
|---|---|
| Core dossier | Fragment rules; environment, checker, conversion, elaboration, and semantic theorems; assumptions and revisions |
| Regression record | Semantic manifest, exact outcomes, transactional failure and budget-exhaustion tests |
| Modularity benchmark | Opaque-helper recursion and a component replacement with unchanged client obligations |
| Extraction record | Computable source witness, runnable IR example, behavioral theorem, cost relation, backend trust boundary |
| User/documentation check | Human/agent parity on a fixed obligation and examples matching the actual supported fragment |

Evidence MUST state what was proved, tested, measured, or manually reviewed; those categories are not interchangeable.
Quantitative performance comparisons MUST record input sizes, budgets, toolchain, and environment rather than a timeless speed claim.

## 11. Research questions, not promised results

- **RQ-SIZE:** Which parametric sized fragment provides useful abstraction and computational behavior with manageable metatheory?
- **RQ-COST:** Can the chosen size and abstraction mechanisms support useful resource inference beyond the first finite upper-bound fragment?
- **RQ-CERT:** Can this particular lower-bound family admit compact, uniformly generated certificates with polynomial bit-cost checking?
- **RQ-HORIZON:** Does the precisely specified cyclic policy-iteration model satisfy the proposed effective-horizon bound?
- **RQ-FRONTIER:** Which stronger realization, robustness, or language theorem remains new after comparison with current literature?

The horizon theorem and the new combinations of sized, equality, and cost rules remain targets until their proofs exist.
A failed hypothesis should produce an explicit counterexample, missing premise, or revised scope.
Milestone dates are planning estimates, not evidence that a research question will have a positive answer.

## 12. Traceability to the roadmap

| Requirement group | Primary milestones | Principal evidence |
|---|---|---|
| TRUST, HOST | M0, M2, M6 | Proof-boundary ADRs, artifact/assumption reports, checked bridge |
| CHECK | M1, M3 | Corpus manifest, transaction tests, common outcomes |
| EQ, open decisions | M0, M1.5, M2 | EXP-A report and foundation-specific rules/tests |
| CORE | M2 and each extension | Fragment specification and independent theorem inventory |
| SIZE | M1.5, M4 | EXP-B, translation/native justification, matching and parametricity proofs |
| COST, EXT | M5A; M5B separately | Finite cost/abstraction benchmark, behavioral and cost adequacy |
| TOOL | M3 | Engine parity, isolated snapshots, structured feedback |
| DOC | D0 and every supported fragment | Three-level explanations, accurate status, working examples |
| EXEC, APP | M6, M7 | Cursor-aware simulation and uniqueness-certified evaluator |
| CERT | M5B-1, M8 | Encoding, soundness, size, checking cost, uniformity |
| SCI, research questions | M9, M10, M11 | Exact theorem status, literature comparison, proof or obstruction |

## 13. Primary reading behind the requirements

- [Observational Equality Meets CIC](https://pujet.fr/pdf/toplas25_cicobs.pdf): the OTT candidate and its intended UIP; not a compatibility theorem for Mugda2.
- [Definitional Proof Irrelevance Made Accessible](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.41): two accessibility variants and a conservativity result for the theories specified there.
- [Normalization by Evaluation for Sized Dependent Types](https://publications.lib.chalmers.se/records/fulltext/252072/local_252072.pdf): size abstraction and conversion concerns.
- [Constructing (Co)inductive Types via Large Sizes](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2026.21): semantic foundations and remaining computational questions.
- [Cubical Agda documentation](https://agda.readthedocs.io/en/latest/language/cubical.html): concrete consequences of choosing a cubical foundation.
- [Lean recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/): structural versus well-founded computation and their checking behavior.

These sources motivate requirements and experiments. Passing Mugda2's acceptance gates requires evidence about
the actual selected fragment and implementation, not only citations to related theories.
