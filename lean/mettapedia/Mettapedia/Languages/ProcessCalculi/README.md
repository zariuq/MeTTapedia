# Mettapedia/Languages/ProcessCalculi

Formalization of six process calculus layers with operational semantics,
structural congruence, OSLF instances, cross-calculus bridges, and the
pi-to-rho encoding.

65 files total (6 sorries across 3 files; the rest sorry-free).

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
| `Engine.lean` | Executable rewrite engine (COMM, DROP, PAR), proven sound |
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

## MORK (7 files)

MM2 execution kernel formalization: prioritized exec rules over
PathMap-backed atom spaces.

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

## References

- Lybech, S. (2022). "A Correct Translation from Rho to Pi"
- Meredith, L.G. & Radestock, M. (2005). "A Reflective Higher-Order Calculus"
- Meredith, L.G. (2026). "How the Agents Got Their Present Moment"
- Stay, M. & Meredith, L.G. (2026). "MQ-Calculus"
