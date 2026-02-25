# Mettapedia/Languages/ProcessCalculi

Formalization of pi-calculus and rho-calculus with operational semantics,
structural congruence, OSLF instances, and the pi-to-rho encoding.

29 files total, zero sorries.

## Pi-Calculus (16 files)

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
| `BackwardAdminReflection.lean` | EncodedSC predicate, admin trace reflection |
| `RhoParTactic.lean` | Custom tactic for rhoPar/rhoSubstitute commutativity |

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

## Key Results

- Forward simulation for restriction-free pi-to-rho encoding (Prop 4, Lybech 2022)
- Pi-calculus as OSLF LanguageDef instance
- Executable rho-calculus engine, proven sound
- Spice calculus: recovers standard rho-calculus at n=0

## References

- Lybech, S. (2022). "A Correct Translation from Rho to Pi"
- Meredith, L.G. & Radestock, M. (2005). "A Reflective Higher-Order Calculus"
- Meredith, L.G. (2026). "How the Agents Got Their Present Moment"
