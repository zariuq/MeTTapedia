# OSLF Framework

Core construction and applications of **OSLF** (Operational Semantics as
a Logical Framework). **74 files, ~33,800 lines. Zero sorry. Zero
custom axioms.**

Paper: `papers/leanOSLF.pdf` — "Verified Operational Semantics in
Logical Form: A Lean 4 Formalization of the OSLF Algorithm"
(Meredith & Stay 2020; Lean 4 formalization 2026).

## What OSLF Does

OSLF is an algorithm that takes an operational rewrite system and
mechanically produces a modal type system:

```
Input:  LanguageDef  (sorts, terms, rewrite rules, premise queries)
          ↓
        RelationEnv  (executable premise evaluation)
          ↓
Output: langOSLF     (◇, □, Galois connection ◇ ⊣ □,
                       formula semantics, sound executable checker)
```

1. `langRewriteSystemUsing` defines a one-step reduction relation
   matching the executable engine.
2. `langDiamondUsing` / `langBoxUsing` derive modal operators:
   - **◇** (diamond) = "there exists a rewrite step reaching a state
     satisfying φ"
   - **□** (box) = "every rewrite step leads to a state satisfying φ"
3. `langGaloisUsing` proves **◇ ⊣ □** (adjunction).
4. `checkLangUsing` provides an executable formula checker with a
   proven soundness theorem (`checkLangUsing_sat_sound`).

The modal operators are **definitional** — grounded in operational
reduction via definitional equality, not ad-hoc axioms.

## Instantiated Languages

OSLF is instantiated for **seven concrete languages**, each with a
fully proven Galois connection:

| Instance | File | Notes |
|----------|------|-------|
| ρ-calculus | `RhoInstance.lean` | Full reduction semantics + SC |
| Lambda calculus | `LambdaInstance.lean` | β-reduction, Galois proof |
| Petri nets | `PetriNetInstance.lean` | Token-firing semantics |
| TinyML | `TinyMLInstance.lean` | Small ML with OSLF type system |
| MeTTa (minimal) | `MeTTaMinimalInstance.lean` | Core MeTTa fragment |
| MeTTa (full) | `MeTTaFullInstance.lean` | Full MeTTa with spec-atoms endpoint |
| PLN selector | `PLNSelectorLanguageDef.lean` | Premise selection language |

## Core Synthesis

| File | Contents |
|------|----------|
| `TypeSynthesis.lean` | `langOSLF`, `langDiamond`, `langBox`, `langGalois` — the main pipeline |
| `RewriteSystem.lean` | Core rewrite system abstraction |
| `DerivedModalities.lean` | Derived diamond/box operators via Galois connections |
| `DerivedTyping.lean` | Derived typing rules and fiber semantics |
| `GeneratedTyping.lean` | Generated typing context and dependent modal operators |
| `ModalEquivalence.lean` | Modal equivalence and interdefinability |

## NTT (Native Type Theory)

Categorical uplifting of OSLF into presheaf topoi with explicit
name/path semantics. The pipeline is OSLF → NTT → WM (world model).

| File | Contents |
|------|----------|
| `CategoryBridge.lean` | `SortPresheafCategory`, `predFibration`, `oslf_fibration` — presheaf-primary consumer path (1,609 lines) |
| `BeckChevalleyOSLF.lean` | Substitution square in lifted base; Beck-Chevalley + reduction graph; includes proven counterexample showing strong condition fails (1,708 lines) |
| `OSLFNTTWMBridge.lean` | Atom-level OSLF → NTT → WM triangle bridge |
| `OSLFNTTWMCanonicalClosure.lean` | Formula-to-WM evidence transport via presheaf/subobject modal semantics |
| `OSLFNTTTheoryClosure.lean` | Theory closure for the OSLF → NTT pipeline |
| `ToposTOGLBridge.lean` | Internal logic package (NTT Proposition 19: cosmic fibration) |
| `ToposReduction.lean` | Internal reduction graph with premises in presheaf topos |
| `ConstructorCategory.lean` | Constructor category with SubobjectFibration and ChangeOfBase |
| `ConstructorFibration.lean` | Constructor fibration structure |
| `MeTTaToNTT.lean` | MeTTaFullLegacy → NTT bridge |
| `ModalSubobjectBridge.lean` | Modal operators via subobject classifier |

## Governance

DDLPlus deontic logic instantiated over PyashCore operational semantics,
showing OSLF's composability for normative reasoning:

| File | Contents |
|------|----------|
| `GovernanceInstance.lean` | `GovFrame`, `ClosedGovAccessibility`, `govDDLFrameClosed`; CJ3, axiomD, CJ4, Kant theorems |
| `GovernanceGSLTVertex.lean` | GSLT vertex rewrite rules for governance |
| `GovNormCycle.lean` | Governance norm cycle |

## Pyash Instance

Sentence-first operational dispatch semantics with mood system
(MDo, MPrah, MYa, MDef) and Grammatical Framework integration:

| File | Contents |
|------|----------|
| `PyashCoreModel.lean` | Focused core OSLF/GSLT instance (2,601 lines) |
| `PyashCoreProofs.lean` | Core proof theorems and validations |
| `PyashGF.lean` | GF integration (1,969 lines) |
| `PyashGFEnglishFragment.lean` | English linguistic fragment |
| `PyashGFModel.lean` | GF semantic model |
| `PyashGFInventory.lean` | Coverage tracking |
| `PyashGFComparative.lean` | Comparative linguistics |

## PLN / World-Model Bridges

| File | Contents |
|------|----------|
| `WMProbabilityEmbedding.lean` | World model probability embedding |
| `PLNWMHypercubeBasis.lean` | PLN world model hypercube basis |
| `SynthesisBridge.lean` | Formula → WM evidence synthesis |
| `HypercubeGSLTFunctor.lean` | Hypercube GSLT functor (PLN categoricals) |
| `HypercubeTemporalGSLTFunctor.lean` | Temporal extension |
| `LanguageMorphism.lean` | Language morphism / semantic transfer |
| `SimulationPreservation.lean` | Simulation preservation theorems |
| `PiRhoCanonicalBridge.lean` | π→ρ canonical bridge (2,285 lines) |

## Audit and Status Tracking

| File | Contents |
|------|----------|
| `AssumptionNecessity.lean` | Proves what cannot be proven globally (image-finiteness, atom-all, commDi) with counterexamples |
| `FULLStatus.lean` | Machine-readable milestone tracker (60+ rows); paper parity gated by `paperParityRemaining` |
| `NTTClaimTracker.lean` | NTT proposition parity (Prop 12, 14, 17, 21, 23) |
| `PaperClaimTracker.lean` | Paper-level claims tracking |
| `MATTProvableNow.lean` | MATT (MeTTa Type Theory) provability status |

## Scope Non-Claims

OSLF is **not**:
- A claim of global decidability (premises may be undecidable)
- A full MeTTa interpreter or parser
- A guarantee that premise relations are computable in Lean

## References

- Meredith, L.G. & Stay, M. (2020). "Operational Semantics as a
  Logical Framework"
- Paper: `papers/leanOSLF.pdf` (March 2026 draft)
