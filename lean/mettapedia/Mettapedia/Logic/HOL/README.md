# Higher-Order Logic (HOL)

Church-style higher-order logic formalized in Lean 4.28: syntax,
natural deduction, Henkin semantics, soundness, Lindenbaum quotients,
Henkinization, and bridges to world-model reasoning and probabilistic
semantics. **21 top-level files + 5 subdirectories (33 files) = 54 total. Zero sorry.**

## Syntax (`Syntax/`)

| File | Contents |
|------|----------|
| `Type.lean` | `Ty` — prop, base, arrow |
| `Term.lean` | Terms: variables, constants, application, lambda, forall, exists |
| `Subst.lean` | Simultaneous substitution on terms and formulas |
| `Closed.lean` | `ClosedFormula` / `ClosedTerm` aliases |
| `ConstMap.lean` | `mapConst` for signature morphisms; rename/subst commutation |

## Proof Theory

| File | Contents |
|------|----------|
| `Derivation.lean` | `Derivation` — natural deduction (24 constructors: propositional + quantifier + equality + lambda) |
| `DerivationExtensionality.lean` | `ExtDerivation` — overlay adding propositional and argument congruence |

## Semantics (`Semantics/`)

| File | Contents |
|------|----------|
| `Henkin.lean` | `PreModel` / Henkin model; type denotation, valuations |
| `HeytingHenkin.lean` | `HeytingHenkinModel` for intuitionistic semantics |
| `Extensionality.lean` | Extensionality lemmas for semantic equality |
| `SetBased.lean` | Set-based semantic interpretation |

## Canonical Construction

| File | Contents |
|------|----------|
| `CanonicalTheory.lean` | `ClosedTheorySet`, `Provable`, `DeductivelyClosed`, `Consistent`, canonical `World` |
| `CanonicalKripke.lean` | Kripke forcing over ordered canonical worlds |
| `CanonicalSemantics.lean` | Truth events and canonical truth evaluation |

## Henkinization

| File | Contents |
|------|----------|
| `Henkinization.lean` | `WitnessProvider`, `OneStepHenkinConst` |
| `HenkinizationStages.lean` | Cumulative `HenkinConstStage` with universe lifting |
| `HenkinAxiomsInfinity.lean` | Countable Henkinization axioms with inductive limit |
| `HenkinizationInfinity.lean` | Full cumulative Henkin constant construction |
| `HenkinWitnessClosure.lean` | `ExWitnessClosed`, `AllCounterexampleClosed` |
| `PrimeHenkinExtension.lean` | Prime filter extensions and prime-world construction |

## Soundness and Lindenbaum

| File | Contents |
|------|----------|
| `Soundness.lean` | Classical soundness: derivable formulas hold in all Henkin models |
| `IntuitionisticSoundness.lean` | Intuitionistic soundness for Heyting-Henkin models |
| `Lindenbaum.lean` | Lindenbaum quotient for `ClosedTheory`; `HeytingAlgebra` instance |
| `LindenbaumSet.lean` | Lindenbaum quotient for `ClosedTheorySet`; `HeytingAlgebra` instance |

## World-Model Bridge

| File | Contents |
|------|----------|
| `WorldModel.lean` | `holEvidence` from multisets of pointed Henkin models; WM instance |
| `WorldModelCompleteness.lean` | Semantic implication ↔ WM strength order; categorical bridges |

## First-Order Embedding (`Embedding/`)

| File | Contents |
|------|----------|
| `FirstOrder.lean` | FO→HOL via Church encoding (curried function/relation symbols) |

## Logical Induction (`LogicalInduction/`)

Dynamic belief system above real HOL semantics: canonical formula
coding, deductive processes, rational belief markets, calibration,
and theory-extension conditioning. 10 files.

## Probabilistic Semantics (`Probabilistic/`)

Infinitary-first semantics: measurable spaces of pointed Henkin models,
sentence probabilities via measure integration, hierarchical uncertainty
(beliefs about beliefs), flattening theorems, and benchmark bridges.
13 files.
