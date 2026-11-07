# Mugda2 — Milestone Plan

Synthesized from [idea1.txt](idea1.txt), [idea2.txt](idea2.txt), the foundational literature synthesis, and the Lean 4 baseline in `../mugda`.

**Identity:** *A dependent programming language and workbench in Lean 4 for constructive algorithms with checked termination, modular abstraction, and computational cost (upper bounds, lower bounds, and cost preservation), with strong support for agents constructing the proofs.*

**Distinctive research question:**
> *Can we build a practical dependent language in which recursive components expose termination and resource contracts, those contracts survive abstraction and representation changes, and agents can synthesize independently checked evidence for them?*

**Core scientific thesis:** Investigate how **parametric sized programming** ($\forall^p i$), **internal parametricity**, and **modular cost reasoning** (*Abstraction Functions as Types* / *Potential Functions as Types* / *Decalf*) work together in a practical, sound language.

---

## Ranking of Foundational Directions

| Direction | Role in Mugda2 |
|---|---|
| **1. Modular reasoning about cost and abstraction** (Grodin–Li–Harper POPL '26; Giralf/Calf '26; Decalf) | **Main distinguishing capability:** components expose mathematical behavior *and* resource guarantees across abstraction boundaries; extended from Giralf's structural recursion to sized recursion and exponential bounds. |
| **2. Parametric sized programming** ($\forall^p i$, Laarakker–Otten–van den Berg '26; Cavallo–Harper) | **Central termination & language-research question:** size uniformity across opaque interfaces (`preprocess : ∀ᵖ i. Certificate i → Certificate i`) without leaking sizes into runtime behavior or carrying large termination proofs. |
| **3. Observational Type Theory (OTT)** (Pujet–Tabareau TOPLAS '25; *Definitional Proof Irrelevance Made Accessible* LICS '26) | **Primary candidate equality foundation:** pointwise function equality, quotient/representation reasoning, and two-level translation (convenient unfolding in frontend $\to$ decidable core). |
| **4. Cubical / univalent foundations** | **Enabling option (not the selling point):** chosen at M2 *only if* the M1.5 design experiments show univalent abstraction makes modular cost/representation transfer substantially cleaner than OTT. |
| **5. Guarded / clocked recursion** (*Greatest HITs*) | **Secondary track:** relevant when productive stream processors with latency bounds become the main focus. |
| **6. Directed cost ordering (Decalf)** vs. general simplicial HoTT | **Targeted adoption:** adopt Decalf-style intrinsic cost ordering on types (supporting upper/lower bounds and later randomized pivot rules); defer general synthetic higher category theory. |

### The Four Distinct Quantities Mugda2 Must Separate
Driven by the Avis–Friedmann benchmark, Mugda2 never conflates:
1. **Input size** ($\operatorname{bits}(I_n)$).
2. **Construction cost** of the instance generator producing $I_n$.
3. **Execution cost** of the algorithm on $I_n$ (e.g., $\ge 2^n$ pivots vs. $O(m^2 H \log(2H))$ upper bound).
4. **Certificate size and checking cost** of the symbolic proof explaining that execution.

---

## Baseline: What `../mugda` Already Provides

- **Executable Lean 4 compiler:** `Mugda/Core.lean` (~2.4k lines, Lean `v4.35.0`, zero external dependencies, 0 `sorry`/`partial`/`unsafe`) + `Main.lean` CLI + 22 positive / 17 negative regression suites.
- **In-place formal metatheory:** 34 theorems in `Mugda/Soundness.lean` and 63 theorems in `Mugda/Metatheory.lean`.
- **Gaps to close in M1–M3:**
  1. `examples/k.ma` is currently accepted in `POS_EXAMPLES`.
  2. Fuel exhaustion (`whnf: out of fuel`) is conflated with type rejection (`Except String`).
  3. Failed obligations in `typeCheckFuns` append to `st.warnings` and leave `FunSig ... false` in the signature.
  4. Single `Set` universe; no separate small core or verified rechecker yet; no parametric size quantifier $\forall^p i$.
  5. Browser playground `docs/mugda-engine.js` duplicates the checker in JS.

---

## Structure: Language Track First, Then Application Track

```mermaid
flowchart LR
    B["../mugda Lean 4 baseline"] --> M0
    subgraph P1["Phase I: Language track (Priority)"]
        M0["M0 Framing"] --> M1["M1 Harden Lean baseline"] --> M15["M1.5 Two design experiments (OTT vs Cubical)"] --> M2["M2 Core, equality & verified rechecker"] --> M3["M3 Service and workbench"] --> M4["M4 Parametric sized fragment"] --> M5["M5 Modular cost, abstraction & extraction"]
    end
    subgraph P2["Phase II: Application track"]
        M6["M6 Avis-Friedmann integration"] --> M7["M7 Cursor-aware executions & transport"] --> M8["M8 Symbolic phase certificates"] --> M9["M9 Effective-horizon bound"]
    end
    subgraph P3["Phase III: Shared"]
        M10["M10 Frontier selection"] --> M11["M11 Flagship result"]
    end
    M5 --> M6
    M9 --> M10
```

## Timeline Overview

| # | Milestone | Track | Target window |
|---|---|---|---|
| M0 | Framing and foundational decisions | L | Nov 2026 (2 wks) |
| M1 | Harden the Lean 4 baseline | L | Nov – Dec 2026 |
| M1.5 | Two foundational design experiments (OTT vs. Cubical) | L | Jan 2027 (3–4 wks) |
| M2 | Explicit core, equality foundation, and verified rechecker | L | Feb – Mar 2027 |
| M3 | Checking service and interactive workbench | L | Apr – May 2027 |
| M4 | Parametric sized programming ($\forall^p i$) and pattern elaboration | L | May – Jul 2027 |
| M5 | Modular cost, abstraction contracts, and extraction | L | Aug – Oct 2027 |
| M6 | Avis–Friedmann integration and shared interfaces | A | Nov – Dec 2027 |
| M7 | Cursor-aware executions and representation transport | A | Jan – Feb 2028 |
| M8 | Symbolic phase certificates | A | Mar – Apr 2028 |
| M9 | Effective-horizon upper bound | A | May – Jun 2028 |
| M10 | Frontier selection | Shared | Jul – Aug 2028 |
| M11 | Flagship result and packaging | Shared | Sep – Dec 2028 |

---

# Phase I — Language Track

## M0 — Framing and Foundational Decisions
Commit short architecture decision records (ADRs):
- **Main ambition:** checked termination, modular abstraction, and computational cost with strong agent support.
- **Implementation:** Lean 4 throughout; `Mugda` v1.0 stays as a regression oracle.
- **No global K:** pattern matching must not implicitly prove UIP on general identity/observational types.
- **Two-tier architecture (inspired by LICS '26 *Definitional Proof Irrelevance Made Accessible*):** convenient unfolding and recursion in the frontend elaborated into explicit evidence checked by a decidable, small core.
- **Four separate judgments:** *terminates/productive*, *input/output size bounded*, *construction/execution cost bounded*, and *certificate size/check cost bounded*.

**Exit:** ADRs committed in repository.

---

## M1 — Harden the Lean 4 Baseline
- Commit untracked assets in `../mugda` (`tests/`, `examples/showcase/`, `examples/tutorial/`, `examples/README.md`) and tag `mugda-v1-baseline`.
- **Three-valued checker result:** `accepted | rejected(Diagnostic) | unknown(OutOfFuel)` across `MugdaCore`, CLI, and golden tests.
- **Strict declaration state:** replace the boolean flag in `FunSig` with distinct provisional vs. accepted environment entries; remove string warnings as the failure mechanism in `typeCheckFuns`.
- **Structured diagnostics:** source spans, structured obligation payloads, and JSON output.
- **Trust & axiom audit:** CI reports `#print axioms` on all theorems; isolate `native_decide` usage.

**Exit:** every example has a classified status; failed or out-of-fuel checks cannot install accepted declarations.

---

## M1.5 — Two Foundational Design Experiments (Gate Before M2)
Before locking in the M2 core equality and recursion rules, run two focused experiments (prototyped in Lean 4 / Cubical Agda):

1. **Experiment A — Modular data-structure & cost abstraction:**
   Swap two concrete implementations behind an abstract interface while preserving a client's correctness and cost proof (Grodin–Li–Harper style). Compare:
   - *Option 1:* Observational Type Theory (OTT) + explicit abstraction/simulation types.
   - *Option 2:* Univalent/cubical abstraction.
2. **Experiment B — Sized certificate normalizer across opaque helpers:**
   Write a recursive certificate traverser using an opaque helper `preprocess : ∀ᵖ i. Certificate i → Certificate i`. Measure computation rules, proof burden, and checking cost under:
   - *Approach A:* translation to accessibility/recursors with two-level unfolding (LICS '26 style).
   - *Approach B:* native parametric sized recursion rule in the core.

**Exit:** written comparison report selecting the M2 equality foundation (OTT vs. Cubical vs. minimal intensional `Id`) and recursion core (Approach A vs. B) with concrete evidence.

---

## M2 — Explicit Core, Equality Foundation, and Verified Rechecker
- Specify `Mugda2.Core`: predicative universe hierarchy, $\Pi/\Sigma$, inductives, explicit eliminators / well-typed case trees, explicit relevance, and the equality foundation chosen in M1.5 (default candidate: **Observational Equality** following Pujet–Tabareau TOPLAS '25, or restricted cubical if Experiment A demands it).
- Define the declarative typing and conversion judgment `HasType` as an inductive `Prop` in Lean 4.
- Implement the executable core rechecker `recheck : Env → CoreTerm → CoreTy → Outcome` and prove `recheck_sound : recheck env t ty = .accepted → HasType env t ty`.
- `examples/k.ma` is rejected for types that are not provably h-sets / proof-irrelevant propositions.

**Exit:** emitted core modules recheck independently of elaboration, backed by a Lean soundness theorem.

---

## M3 — Checking Service and Interactive Workbench
- Lean 4 JSON-RPC service: `checkDocument`, `getGoals`, `getConstraints`, `explainObligation`, `tryCandidate`, `normalizeWithBudget`, `recheckCore`.
- Immutable environment snapshots and branching search states (Pantograph-style) so agents can explore candidate proofs, potentials, and size contracts in parallel without reparsing files.
- **Single engine:** connect the web UI directly to the Lean 4 service (retiring the duplicate checker in `docs/mugda-engine.js`).
- Workbench panels: **Goal**, **Pattern Refinement**, **Parametric Size & Termination**, **Cost & Potential Contracts**, **Abstraction Boundary**, **Extraction**.

**Exit:** a human and an LLM agent complete the same verification obligation through the snapshot API.

---

## M4 — Parametric Sized Programming ($\forall^p i$) and Pattern Elaboration
- Introduce explicit **parametric size quantification** $\forall^p i$ distinct from ordinary dependent $\Pi$, so size-preserving interfaces (`preprocess : ∀ᵖ i. Certificate i → Certificate i`) compose across abstraction boundaries while keeping sizes erasable.
- Port and generalize the Pattern-Refinement Invariant (`checkNoccEnv`, `checkNoccDomains`, parameter `nocc`), `ORDER_+` SCT, and ordinal/parametric soundness proofs from `Mugda/Soundness.lean` and `Mugda/Metatheory.lean`.
- Cockx–Abel dependent (co)pattern elaboration into explicit case trees with inspectable branch refinements.
- Copatterns/observations for streams and infinite traces (finite observation conversion; bisimulation/observational equality for coinductive equality).
- All 17 negative counterexamples (`cody_*`, `loop_wrapped`, `*_mat_bug`, `llet_bug`) verified as rejected in the new core.

**Exit:** modular sized recursion works across opaque $\forall^p i$ interfaces with machine-checked soundness and full counterexample coverage.

---

## M5 — Modular Cost, Abstraction Contracts, and Extraction
Combine Hofmann's potential method, Schwichtenberg's extraction, and the 2026 Calf/Giralf/Decalf advances:
- **Type-level credits, debits, and potentials** (*Potential Functions as Types* / Giralf), generalized from structural recursion to Mugda2's parametric sized recursion and supporting **both polynomial and exponential bounds** + **Decalf-style intrinsic cost ordering** (upper and lower bounds).
- **Modular cost abstraction** (*Abstraction Functions as Types*): prove a client's cost bound against an abstract specification without inspecting the concrete implementation.
- **Decorated extraction** (Ratiu–Schwichtenberg): relevance annotations, erasure of proofs, sizes, and ghost cost credits, extracting to a clean executable IR with a Lean-proved erasure correctness theorem.
- **Benchmarks:**
  1. Verified sorting and a modular data-structure swap preserving client cost bounds.
  2. Stream processor with both productivity and per-observation latency/lookahead bounds $L_{G \circ F}(n) \le L_F(L_G(n))$ (Köpp–Schwichtenberg).

**Exit:** a client program's correctness, termination, and cost bound are verified against an abstract interface, and its extracted executable erases all size and cost evidence. **End of Phase I.**

---

# Phase II — Application Track (Avis–Friedmann & Pivot Rules)

## M6 — Avis–Friedmann Integration and Shared Interfaces
- Link the Avis–Friedmann Lean 4 repository via Lake; verify full dependency closure ($n \ge 3$, $\ge 2^n$ Cunningham pivots, $5(n-1)$ constraints, $10(n-1)$ variables).
- Define modular interfaces in Mugda2/Lean:
  - **Stateful algorithm with memory:** $s = (\text{basis/policy}, \text{cyclic cursor})$.
  - **Cost-preserving simulation contract** (using M5's abstraction/refinement types) distinguishing pivots, candidate inspections, arithmetic ops, and bit ops.
- **Certified exact evaluator:** extracted from Mugda2 (M5) with bounded construction/evaluation cost, emitting certificates $(I - P_\pi)v = r_\pi$ verified in Lean.
- Add workbench views for MDP/game graphs, basis/policy, cyclic cursor, reduced costs, and phase invariants.

**Exit:** workbench executes and visualizes legal Cunningham pivots with a checked link to the Lean specification.

---

## M7 — Cursor-Aware Executions and Representation Transport
- Executable refinement of the noncomputable rational simplex definitions.
- Cost-preserving simulations instantiated across Parity Games $\to$ MDPs $\to$ LPs.
- **Rational $\to$ Real transport:** trajectory preservation (determinants, feasibility, reduced-cost signs, ratio tests, cursor updates) and real polyhedral geometry (vertices, adjacency).
- Formalize Maat's direct strategy-improvement $\leftrightarrow$ simplex correspondence using the shared simulation interface.

**Exit:** the prescribed execution and its exact pivot count transport across game, MDP, rational LP, and real LP representations.

---

## M8 — Symbolic Phase Certificates (The Four-Quantity Benchmark)
Demonstrate all four distinct quantitative guarantees on the Avis–Friedmann family:
1. **Bounded construction cost** of the hard-instance generator $G(n)$ (polynomial time and bit-size $\le C n^d$).
2. **Exponential execution lower bound** ($\ge 2^n$ pivots) on $G(n)$.
3. **Compact symbolic phase certificate** (gadget invariant, phase entry/exit, counter relation, recurrence $T(n+1) \ge 2T(n) + d$) checked in polynomial time without enumerating $2^n$ steps, using M4's $\forall^p i$ certificate combinators.
4. **Explicit bit-encoding theorem** connecting instance bit-size to execution length ($2^{\Omega(\operatorname{bits}(G(n))^{1/d})}$).

**Exit:** the all-$n$ exponential lower bound is verified via compositional symbolic certificates in the workbench.

---

## M9 — Effective-Horizon Upper Bound
Prove the complementary quantitative upper bound for cyclic Cunningham policy iteration on maximizing MDPs with transience certificate $1 \le w_s \le H$, $\sum_t P(s,a,t)w_t \le w_s - 1$:
$$\operatorname{CunninghamPivots} = O\!\left(m^2 H \log(2H)\right)$$
1. Fair sweep semantics ($m$ consecutive inspections).
2. Bellman progress $v' \ge \mathcal{T}v$ per sweep.
3. Weighted norm $\|x\|_w$ contraction by $q = 1 - 1/H$.
4. Action elimination in $O(H \log(2H))$ sweeps (using M5's potential contracts).
5. Combine with the $2^n$ lower bound on $m = O(n)$ to deduce $H \log(2H) \ge 2^n / \operatorname{poly}(n)$.

**Exit:** Lean-checked theorem (or pinpointed formal obstruction) + generalized cover-time $O(m B H \log(2H))$ corollary. **End of Phase II.**

---

# Phase III — Shared Frontier & Flagship

## M10 — Frontier Selection
Select **one** primary open research target based on Phase I–II evidence:
- **Language frontier:** full internal parametricity for large sizes + modular cost inference for higher-order/exponential programs, or Decalf-style probabilistic cost bounds for randomized pivot rules.
- **Complexity frontier:** polynomial-bit LP realizations for Disser–Loho–Maat–Mosis (STACS 2026) generalized families, quantitative $\varepsilon(n)$-robustness of Cunningham lower bounds, or bounded-memory controller lower bounds.

**Exit:** formal candidate statement, literature positioning, and agent-assisted experimental validation.

## M11 — Flagship Result and Packaging
- Complete the M10 theorem and package the Mugda2 language, verified core, cost/abstraction library, and Avis–Friedmann workbench as a reproducible Lake distribution.
- **Flagship end-to-end demonstration:** a user writes an abstract specification with termination and cost contracts; an agent synthesizes the implementation, potential function, and phase certificate; Mugda2 checks all obligations in the verified core and extracts the erasable executable.

---

## Cross-Cutting Agent Work Packages

| Work package | Milestones | Agent role | Checker / human gate |
|---|---|---|---|
| Baseline & axiom audit | M1 | Refactor diagnostics, 3-valued fuel, `#print axioms` CI | `lake build && make test` |
| Design experiments | M1.5 | Mechanize OTT vs. Cubical modular cost & $\forall^p i$ prototypes | Human architectural decision for M2 |
| Core & rechecker proofs | M2 | Prove `recheck_sound` cases in Lean 4 | Kernel check (0 `sorry`) |
| Workbench & JSON-RPC | M3 | Build Lean server & UI panels, retire JS engine duplicate | Snapshot consistency tests |
| Parametric size & potential synthesis | M4, M5 | Propose $\forall^p i$ annotations, potential functions $\Phi$, and case-tree lemmas | Rechecker validates certificate |
| Prove2Me formalization missions | M6–M9 | Prove evaluator soundness, simulation steps, rational$\to$real transport, sweep contraction | Fixed theorem statements in Lean 4 |
| Counterexample & coefficient search | M4, M8, M10 | Mutate `.ma` files; search for compact LP coefficients or perturbation margins | Minimized witness + formal verification |

## Open Decisions
1. **Repository layout:** add `Mugda2/` inside `../mugda` alongside `Mugda/`, or initialize `mugda2/` as a Lake project importing `../mugda`?
2. **Surface syntax:** standalone `.ma` syntax, embedded Lean 4 DSL (`mugda2%` macros/elaborators), or both?
