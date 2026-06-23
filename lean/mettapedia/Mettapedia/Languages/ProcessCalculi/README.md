# Process Calculi

## What this is about

In a *process calculus*, a program is not a function that maps an input to an output but a
collection of concurrent *processes* that run side by side and interact by passing messages.
The calculus fixes a tiny grammar of processes (do nothing; run two things in parallel;
send/receive on a channel; create a fresh private name; replicate) and a *reduction rule*
saying what happens when a sender meets a receiver. From that minimal kit you can model
everything from network protocols to biological signalling — and, because the rules are so
sharp, you can *prove* when two systems are indistinguishable to any observer
(**bisimilarity**) or when a translation from one calculus into another is faithful.

This directory formalizes five such systems and the bridges between them: the **π-calculus**
(Milner's classic, with channel mobility), the reflective **ρ-calculus** (Meredith &
Radestock — *names are quoted processes*), the **MeTTa-calculus**, the **MQ** quantum
calculus (Born-rule measurement as a reduction outcome), and a **MORK** execution kernel.
Each calculus is also wired into the shared OSLF back-end as a `LanguageDef` where
applicable, so its modal type theory and open-map bisimulation come for free.

The π-, ρ-, MeTTa-, and MQ-calculus lanes have their own detailed READMEs; this top-level
README owns the shared `Common/` infrastructure and the `MORK/` kernel, and gives the
cross-calculus overview.

Paper: `../../../../../papers/process-calculi.tex` — *Process Calculi Formalized in Lean 4:
Rho, Pi, MQ, and Modal Mu-Calculus with Cross-Calculus Bridges* (March 2026)

## Common Infrastructure (4 files)

Shared vocabulary and generic constructions reused across all calculi.

| File | Description |
|------|-------------|
| `Common.lean` | Barrel re-export of Common modules |
| `Congruence.lean` | Structural congruence infrastructure shared across pi, rho, MQ |
| `ProcessAlgebra.lean` | Shared typeclasses: `HasPar`, `HasNu`, `HasNil` |
| `Star.lean` | Generic reflexive-transitive closure with congruence lifters |

## Pi-Calculus (19 files)

Asynchronous, choice-free pi-calculus following Lybech (2022). Six process
constructors: nil, par, input, output (async), restriction, replication
(input-guarded).

### Core
| File | Description |
|------|-------------|
| `Syntax.lean` | Process type (6 constructors), Name = String |
| `StructuralCongruence.lean` | Alpha-equivalence and structural congruence (Type-valued) |
| `Reduction.lean` | COMM reduction rule, substitution lemmas |
| `MultiStep.lean` | Reflexive-transitive closure (P =>* Q) |
| `PiCalcInstance.lean` | Pi-calculus as OSLF LanguageDef instance |
| `Main.lean` | Entry point re-exporting core modules and open-map bridges |

### Pi-to-Rho Encoding (Lybech 2022)
| File | Description |
|------|-------------|
| `RhoEncoding.lean` | Encoding function with Lybech-style name server |
| `ForwardSimulation.lean` | Forward simulation for restriction-free fragment (proven) |
| `EncodingMorphism.lean` | Encoding as structured LanguageMorphism |
| `RhoEncodingCorrectness.lean` | Clean RF forward-correctness surface |
| `NameServerLemmas.lean` | Name server operational lemmas |
| `WeakBisim.lean` | Weak N-restricted barbed bisimilarity |
| `WeakBisimDerived.lean` | Weak bisimilarity with derived reductions |
| `BackwardNormalization.lean` | Normalization helpers for backward proofs |
| `BackwardAdminReflection.lean` | EncodedSC predicate, admin trace reflection (2,745 lines) |
| `RhoParTactic.lean` | Custom tactic for rhoPar/rhoSubstitute commutativity |

### Open-Map Bisimulation Bridges
| File | Description |
|------|-------------|
| `BranchingBisim.lean` | Branching/stuttering via generalized open maps |
| `WeakBisimOpenMapBridge.lean` | Weak bisimilarity to generalized open-map path bisimulation |
| `OpenMapBridgeRegression.lean` | Regression checks for pi/rho open-map bridge equivalences |

## Rho-Calculus (11 files)

Locally nameless formalization of Meredith's rho-calculus. Processes communicate
via quoted names: `@(p)` (quote), `*(n)` (dereference), with the key equation
`@(*(n)) = n`. Includes the spice calculus extension (n-step lookahead).

| File | Description |
|------|-------------|
| `Types.lean` | Process/Name types, COMM reduction, quote/dereference |
| `StructuralCongruence.lean` | Locally nameless structural congruence |
| `Reduction.lean` | COMM rule with locally nameless substitution |
| `MultiStep.lean` | ReducesStar, ReducesN (n-step) |
| `DerivedRepNu.lean` | Derived replication/restriction administrative layer |
| `SpiceRule.lean` | Spice calculus: n-step lookahead (Meredith 2026) |
| `CommRule.lean` | COMM with n-step lookahead |
| `Context.lean` | Evaluation contexts and labeled transitions |
| `PresentMoment.lean` | Present moment: surface + internal channels |
| `Engine.lean` | Executable rewrite engine for the paper-faithful COMM/PAR core, proven sound |
| `Soundness.lean` | Type preservation under substitution |

## MeTTa-Calculus (9 files)

Symmetric reflective higher-order concurrent calculus with COMM
(rendezvous via first-order unification with dot-substitution) and REFL
(self-reflection using COMM-only fragment).

| File | Description |
|------|-------------|
| `Syntax.lean` | Process grammar and LanguageDef for MeTTa-calculus |
| `StructuralCongruence.lean` | Parallel-bag algebra and inactive-process law |
| `Reduction.lean` | COMM with lightweight unifier and REFL with one-step lookahead |
| `Adequacy.lean` | Premise adequacy bridging IR contract to executable reduction |
| `Premises.lean` | Premises as PremiseProgram IR with datalog contract |
| `PaperMap.lean` | Theorem index mapping paper clauses to Lean theorems |
| `Interoperability.lean` | Bridge from MeTTa quote/drop/parallel to rho/open-map stack |
| `Regression.lean` | Positive/negative regression corpus with exact expected outputs |
| `RelationNames.lean` | Single source of truth for relation/builtin identifiers |

## MQ-Calculus (10 files)

Quantum process calculus (Stay & Meredith 2026) with De Bruijn wire
indices, Born-rule measurement, and gate application.

| File | Description |
|------|-------------|
| `Syntax.lean` | MQ process grammar (MQNil, MQPar, MQNu, MQGate, MQOut, MQIn) |
| `StructuralCongruence.lean` | Par-comm, par-assoc, nu-nil, scope-extrusion |
| `Reduction.lean` | One-step `Reduces` and reflexive-transitive `MultiStep` |
| `CommRule.lean` | COMM with quantum measurement: branches by Born probabilities |
| `Denotational.lean` | Denotational semantics (Stay & Meredith 2026, Section 6.3) |
| `Shift.lean` | Wire-index shifting with equational law proofs |
| `Backend.lean` | Semantic backend: gate application, wire allocation, measurement |
| `PaperMap.lean` | Theorem index from mq-calculus.pdf to Lean names |
| `Interoperability.lean` | MQ COMM non-determinism aligns with MORK binary-fold |
| `MQCalculus.lean` | Facade, integration tests, canary theorems |

## MORK (25 files)

MM2 execution kernel formalization: prioritized exec rules over
PathMap-backed atom spaces. The table below lists the core modules; the lane also
includes arithmetic-extension, bridge, and regression files (25 `.lean` in total).

| File | Description |
|------|-------------|
| `Syntax.lean` | MM2 execution language: prioritized exec rules over PathMap |
| `Space.lean` | MORK space semantics: finite Finset Atom with exec-rule firing |
| `MatchSpec.lean` | Relational specification for `matchAtom` |
| `ThreePhaseExec.lean` | Three-phase protocol: UNFOLD, BASE, FOLD |
| `MORKCommBridge.lean` | MORK three-phase ↔ MQ COMM correspondence |
| `PathMapBridge.lean` | MORK transitions as PathMapDistributiveLattice operations |
| `MeTTaILBridge.lean` | MORK execution ↔ MeTTaIL declarative reduction |

## Key Results

- Forward simulation for restriction-free pi-to-rho encoding (Prop 4, Lybech 2022)
- Backward admin reflection with three-branch decomposition (2,745 lines)
- Weak correspondence composing forward + backward (`calculus_weak_correspondence_full_encode`)
- MQ COMM non-determinism ↔ MORK binary-fold (`comm_nondeterminism_iff_mork_binary`)
- MeTTa↔ρ shared-core forward/backward bisimulation
- SC-quotiented Hennessy-Milner (assumption-free for finite-carrier canonical relations)
- Executable rho-calculus engine, proven sound
- Spice calculus: recovers standard rho-calculus at n=0
- Pi-calculus and MQ-calculus as OSLF LanguageDef instances
- Open-map bisimulation bridges (weak bisim ↔ generalized open-map path bisim)

## Formalization status

This README's **own scope** (the shared `Common/` modules and the `MORK/` kernel —
everything not under the π/ρ/MeTTa/MQ sub-trees, which have their own READMEs) is **35
`.lean` files, all `sorry`-free**. There are no source-level `axiom` declarations in this
scope (a source grep, *not* a per-theorem `#print axioms` audit, so a theorem can still
inherit a standard Mathlib axiom transitively).

**Trusted base — `native_decide`.** Two files in this scope discharge fixtures with
`native_decide`, which *compile-evaluates* a Boolean rather than kernel-checking it (so it
trusts the Lean compiler and enlarges the trusted base): `Ambient/LanguageDefDSL.lean`
(13 invocations) and `MORK/ArithmeticExtension.lean` (3) — **16 in this scope**, flagged for
migration to kernel `decide`. The structural results (reductions, the MORK three-phase
protocol, the bridge correspondences) do not depend on them. The π/ρ/MeTTa/MQ sub-trees
carry their own `native_decide` invocations, disclosed in their respective READMEs.

Reproduce from this directory — the `sorry` regex is a *raw* scan that also matches prose in
comments/strings, so the footer count (0) is the authoritative comment-stripped figure:

```bash
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .   # prints nothing
rg -n --glob '*.lean' 'native_decide' .                 # Ambient/LanguageDefDSL.lean, MORK/ArithmeticExtension.lean
```

Recursively (including the four sub-READMEs' trees) the whole `Mettapedia/Languages/ProcessCalculi`
tree is 95 `.lean` files.

## References

- L. G. Meredith & Matthias Radestock, [*A Reflective Higher-Order Calculus*](https://doi.org/10.1016/j.entcs.2005.05.016), Electronic Notes in Theoretical Computer Science 141(5):49–67 (2005) — the ρ-calculus.
- Stian Lybech, [*Encodability and Separation for a Reflective Higher-Order Calculus*](https://arxiv.org/abs/2209.02356), EXPRESS/SOS 2022 (EPTCS 368:95–112) — the π → ρ encoding and the separation result this lane formalizes.
- Robin Milner, Joachim Parrow & David Walker, [*A Calculus of Mobile Processes, Part I*](https://doi.org/10.1016/0890-5401(92)90008-4), Information and Computation 100(1):1–40 (1992) — the π-calculus.
- L. G. Meredith (2026). *How the Agents Got Their Present Moment* — the spice-calculus extension (manuscript; no public URL located).
- Mike Stay & L. G. Meredith (2026). *MQ-Calculus* — the quantum process calculus (manuscript `papers/mq-calculus-lean-formalization.tex`; no public URL located).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 35 .lean files, 0 with sorries.*
