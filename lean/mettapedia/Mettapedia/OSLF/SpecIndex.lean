import Mettapedia.OSLF.Main

/-!
# OSLF Specification Index

Paper definition <-> Lean constant <-> bridge theorem mapping for the OSLF
formalization. Serves as a traceability matrix for review.

## References

- [MS] Meredith & Stay, "Operational Semantics in Logical Form"
- [WS] Williams & Stay, "Native Type Theory" (ACT 2021)
- [MR] Meredith & Radestock, "A Reflective Higher-Order Calculus"
- [APSS] Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)

## Architecture Overview

```
                    LanguageDef
                        |
         +--------------+------------------+
         |                                 |
 langReduces (default, empty env)   langReducesUsing (explicit env)
         |                                 |
 rewriteWithContextWithPremises      rewriteWithContextWithPremisesUsing
                        |
              +---------+---------+
              |                   |
      DeclReduces          DeclReducesWithPremises
 (legacy no-premise)      (premise-aware, env-parametric)
              |                   |
              +----proven iff-----+
                        |
                langRewriteSystem
                        |
                    langSpan
                   /        \
            langDiamond    langBox
                   \        /
                 langGalois (automatic)
                        |
                   langOSLF
              /       |       \
         rhoOSLF  lambdaOSLF  petriOSLF
```

## I. Core OSLF Framework (INPUT/OUTPUT)

### Input: RewriteSystem
- Paper [MS] Def 1: "A rewrite system is a set of sorts, terms, and a
  one-step reduction relation on the process sort."
- Lean: `RewriteSystem` (Framework/RewriteSystem.lean:50)

### Output: OSLFTypeSystem
- Paper [MS] §4, §6: "The OSLF algorithm produces predicates at each sort,
  a complete Heyting algebra (frame) structure, and modal operators ◇/□
  forming a Galois connection."
- Lean: `OSLFTypeSystem` (Framework/RewriteSystem.lean:82)

### Native Types
- Paper [WS] §3: "A native type is a pair (sort, predicate)."
- Lean: `NativeTypeOf` (Framework/RewriteSystem.lean:126)

## II. Modal Operators

### Step-Future (◇)
- Paper [MS] §3: "◇φ(p) = ∃q. p ⇝ q ∧ φ(q)"
- Lean (hand-proven): `possiblyProp` (RhoCalculus/Reduction.lean:103)
- Lean (derived): `derivedDiamond` (Framework/DerivedModalities.lean:143)
- Lean (generic): `langDiamond` (Framework/TypeSynthesis.lean:93)
- Bridge: `derived_diamond_eq_possiblyProp` (Framework/DerivedModalities.lean:208)

### Step-Past (□)
- Paper [MS] §3: "□φ(p) = ∀q. q ⇝ p → φ(q)"
- Lean (hand-proven): `relyProp` (RhoCalculus/Reduction.lean:107)
- Lean (derived): `derivedBox` (Framework/DerivedModalities.lean:151)
- Lean (generic): `langBox` (Framework/TypeSynthesis.lean:101)
- Bridge: `derived_box_eq_relyProp` (Framework/DerivedModalities.lean:216)

### Galois Connection (◇ ⊣ □)
- Paper [MS] §4: "The adjoint pair ◇ ⊣ □ forms a Galois connection."
- Lean (hand-proven): `galois_connection` (RhoCalculus/Reduction.lean:113)
- Lean (derived): `derived_galois` (Framework/DerivedModalities.lean:161)
- Lean (generic): `langGalois` (Framework/TypeSynthesis.lean:108)
- Lean (Mathlib): `rho_mathlib_galois` (Framework/RhoInstance.lean:117)
- Bridge: `rho_galois_from_span` (Framework/DerivedModalities.lean:224)

## III. ρ-Calculus Concrete Layer

### Reduction Rules
- Paper [MR] §2: COMM, DROP, structural congruence
- Lean: `Reduces` (RhoCalculus/Reduction.lean:50)
  - Policy note: this low-level relation is intentionally unsplit and includes
    both bag/set congruence constructors; canonical-vs-extension behavior is
    enforced at the `LanguageDef`/`langReduces` layer.
  - `.comm`: {n!(q) | for(<-n){p} | rest} ⇝ {substBVar p (@q) | rest}
  - `.drop`: *(@q) ⇝ q
  - `.equiv`: p ≡ p' ⇝ q' ≡ q ⇒ p ⇝ q

### Canonical vs Extension Language Policy
- Canonical language: `rhoCalc` (`congruenceCollections := [.hashBag]`)
- Optional extension: `rhoCalcSetExt`
  (`congruenceCollections := [.hashBag, .hashSet]`)
- Theorem-level comparison:
  `rhoSetDropWitness_canonical_vs_setExt`
  (`Framework/TypeSynthesis.lean:377`) proves set-context descent is blocked
  in canonical `rhoCalc` and enabled in `rhoCalcSetExt` for the same witness.

### Type Judgment (Locally Nameless)
- Paper [APSS] for locally nameless representation
- Lean: `HasType` (RhoCalculus/Soundness.lean:90)
  - Cofinite quantification for input rule (line 117)
  - Substitutability theorem (line 457): Γ,x:τₓ ⊢ p : U ∧ Γ ⊢ q : τₓ → Γ ⊢ p[q/x] : U
  - Progress theorem (line 683): ⊢ p : τ → isInert p ∨ ∃q. p ⇝ q
  - COMM type preservation (line 478)

## IV. Generic Engine & Matching

### Executable Engine (Two Paths)
- Legacy baseline (no premises): `rewriteWithContextNoPremises` and alias `rewriteWithContext`
- Premise-aware: `rewriteWithContextWithPremisesUsing` / `rewriteWithContextWithPremises`
- Relation environment: `RelationEnv` for pluggable `relationQuery` tuples
- Safety choice: builtin `relationQuery "reduces"` uses the no-premise baseline
  (`rewriteWithContextNoPremises`) to avoid recursive premise self-reference.
- Canonical-vs-extension policy: `LanguageDef.congruenceCollections` controls
  whether collection-context descent is enabled per language instance.

### Declarative Reduction
- Legacy: `DeclReduces` (MeTTaIL/DeclReduces.lean)
  - Soundness: `engine_sound`
  - Completeness: `engine_complete`
- Premise-aware: `DeclReducesWithPremises` (MeTTaIL/DeclReducesWithPremises.lean)
  - Env-aware soundness/completeness:
    `engineWithPremisesUsing_sound`, `engineWithPremisesUsing_complete`
  - Default-env wrappers:
    `engineWithPremises_sound`, `engineWithPremises_complete`

### Relational Matching Specification
- Lean: `MatchRel` (MeTTaIL/MatchSpec.lean:48)
- Soundness: `matchPattern_sound` — `bs ∈ matchPattern pat t → MatchRel pat t bs`
- Completeness: `matchRel_complete` — `MatchRel pat t bs → bs ∈ matchPattern pat t`
- Independence: `DeclReducesRel` (MeTTaIL/MatchSpec.lean:471)
- Triangle: `engine_sound_rel`, `engine_complete_rel`

## V. Categorical Structure

### Adjunction (Galois → Categorical)
- Lean: `langModalAdjunction` (Framework/CategoryBridge.lean:162)
- Lean: `rhoModalAdjunction` (Framework/CategoryBridge.lean:168)

### Predicate Fibration
- Paper [WS] §4: Sub(Y(X)) fibered over sorts
- Lean (default, presheaf-primary): `predFibration`, `oslf_fibration`
  over `SortPresheafCategory`
- Lean (legacy sort-wise wrappers): `predFibrationSortApprox`,
  `oslf_fibrationSortApprox`
- Agreement theorem (discrete-base): `predFibration_presheafSortApprox_agreement`
- Agreement theorem (concrete type-sorted instance):
  `typeSortsOSLFFibrationUsing_presheafAgreement`
- Agreement theorem (generic language-wrapper instance):
  `langOSLFFibrationUsing_presheafAgreement`
- Agreement theorem (concrete language-wrapper instance):
  `rhoLangOSLFFibrationUsing_presheafAgreement`
- Lean (interface-parametric): `predFibrationUsing`, `oslf_fibrationUsing`
- Lean (full language-presheaf λ-theory lift):
  `languagePresheafLambdaTheory`, `languageSortRepresentableObj`,
  `languageSortFiber`, `languageSortFiber_characteristicEquiv`,
  `languageSortPredicateFibration`
- Pattern-predicate bridge into representable fibers:
  `languageSortPredNaturality`, `commDiPred`,
  `commDiWitnessLifting`, `pathSem_commSubst`,
  `languageSortPredNaturality_commDi`,
  `languageSortFiber_ofPatternPred`,
  `languageSortFiber_ofPatternPred_subobject`,
  `languageSortFiber_ofPatternPred_characteristicMap`,
  `languageSortFiber_ofPatternPred_characteristicMap_spec`,
  `rhoProc_langOSLF_predicate_to_fiber_mem_iff`

## VI. Formula Checker

### Formula AST
- Lean: `OSLFFormula` (Formula.lean:69) — ⊤, ⊥, atom, ∧, ∨, ◇, □

### Bounded Model Checker
- Lean: `check` (Formula.lean:211)
- Language-bound entrypoints:
  - `checkLangUsing` (explicit `RelationEnv`)
  - `checkLang` (default `RelationEnv.empty`)
- Soundness: `check_sat_sound` — `check = .sat → sem holds` (Formula.lean:290)
- Soundness (language-bound):
  - `checkLangUsing_sat_sound`
  - `checkLang_sat_sound`
- Enhanced: `checkWithPred` for □ support (Formula.lean:381)

### Semantic Bridge
- `sem_dia_eq_langDiamond` (Formula.lean:135): formula ◇ = framework ◇
- `sem_box_eq_langBox` (Formula.lean:142): formula □ = framework □
- `formula_galois` (Formula.lean:152): formula-level Galois
- Env-aware variants:
  - `sem_dia_eq_langDiamondUsing`
  - `sem_box_eq_langBoxUsing`
  - `formula_galoisUsing`

## VII. Language Instances

### 1. ρ-Calculus (rhoCalc)
- Lean: `rhoCalc` (MeTTaIL/Syntax.lean)
- OSLF: `rhoOSLF` (Framework/RhoInstance.lean:90)
- Galois: proven via `galois_connection` and `rho_mathlib_galois`
- Canaries: 6 engine tests, 8 agreement tests (Engine.lean)

### 2. Lambda Calculus (lambdaCalc)
- Lean: `lambdaCalc` (Framework/LambdaInstance.lean)
- OSLF: `lambdaOSLF` (Framework/LambdaInstance.lean)
- Galois: `lambdaGalois` (automatic from langGalois)
- Canaries: 8 demos + capture-safety canaries 7-8

### 3. Petri Nets (petriNet)
- Lean: `petriNet` (Framework/PetriNetInstance.lean)
- OSLF: `petriOSLF` (Framework/PetriNetInstance.lean)
- Galois: `petriGalois` (automatic from langGalois)
- Canaries: 8 demos + proved dead marking `D_is_dead` + `AB_has_one_reduct`

## VIII. Key Bridge Theorems (Traceability Matrix)

| # | Theorem | File | Statement |
|---|---------|------|-----------|
| 1 | `galois_connection` | Reduction.lean:113 | hand-proven ◇ ⊣ □ for ρ-calc |
| 2 | `derived_galois` | DerivedModalities.lean:161 | generic ◇ ⊣ □ from span |
| 3 | `rho_galois_from_span` | DerivedModalities.lean:224 | ρ-calc Galois as corollary |
| 4 | `langGalois` | TypeSynthesis.lean:108 | automatic for any LanguageDef |
| 5 | `langModalAdjunction` | CategoryBridge.lean:162 | Galois → categorical Adjunction |
| 6 | `engine_sound` | DeclReduces.lean:138 | engine → declarative |
| 7 | `engine_complete` | DeclReduces.lean:175 | declarative → engine |
| 8 | `matchPattern_sound` | MatchSpec.lean:336 | executable → relational match |
| 9 | `matchRel_complete` | MatchSpec.lean:439 | relational → executable match |
| 10 | `declReducesRel_iff_declReduces` | MatchSpec.lean:514 | independence triangle |
| 11 | `substitutability` | Soundness.lean:457 | substitution preserves types |
| 12 | `progress` | Soundness.lean:683 | type soundness (progress) |
| 13 | `check_sat_sound` | Formula.lean:290 | checker soundness |
| 14 | `sem_dia_eq_langDiamond` | Formula.lean:135 | formula↔framework bridge |
| 15 | `rhoSetDropWitness_canonical_vs_setExt` | TypeSynthesis.lean:377 | canonical bag-only vs set-extension one-step divergence |
| 16 | `representable_commDi_patternPred_beckChevalley` | BeckChevalleyOSLF.lean | representable-fiber BC instantiated for COMM direct image |
| 17 | `representable_commDi_bc_and_graphDiamond` | BeckChevalleyOSLF.lean | bundles COMM representable BC and graph-◇ witness characterization |
| 18 | `checkLangUsingWithPred_sat_sound_graphObj_dia` / `..._box` | Formula.lean | checker-facing `.dia`/`.box` soundness over packaged premise-aware `ReductionGraphObj` |

## IX. Sorry / Axiom Census

**Current core-OSLF status (scope of this index):**
- 0 `sorry` in `Mettapedia/OSLF/RhoCalculus/Reduction.lean`
- 0 custom axioms introduced in this core OSLF slice
- Canonical-vs-extension policy is theorem-checked by
  `rhoSetDropWitness_canonical_vs_setExt`

Outside this scope, experimental Pi-calculus layers still contain open `sorry`s.

The formalization otherwise relies only on:
- Lean 4 core axioms (propext, Quot, Classical.choice)
- Mathlib library
- LeanHammer automation

No custom `axiom` placeholders are used in this OSLF slice.
-/

namespace Mettapedia.OSLF.SpecIndex

open Mettapedia.OSLF

-- Verify key definitions are accessible through Main re-exports
#check @MatchRel
#check @MatchArgsRel
#check @MatchBagRel
#check @matchPattern_sound
#check @matchRel_complete
#check @DeclReducesRel
#check @declReducesRel_iff_declReduces
#check @engine_sound_rel
#check @engine_complete_rel
#check @DeclReduces
#check @engine_sound
#check @engine_complete
#check @OSLFTypeSystem
#check @RewriteSystem
#check @langOSLF
#check @langGalois
#check @langDiamond
#check @langBox
#check @SortPresheafCategory
#check @predFibration
#check @oslf_fibration
#check @predFibrationSortApprox
#check @oslf_fibrationSortApprox
#check @predFibration_presheafSortApprox_agreement
#check @Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_canonical_vs_setExt
#check @commDiPred
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting
#check @Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred
#check @Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_liftEq
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLiftPkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_pathSemLift_pkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_commDiWitnessLifting_of_pkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
#check @pathSem_commSubst
#check @Mettapedia.OSLF.Framework.CategoryBridge.pathSemClosedPred_closed
#check @languageSortPredNaturality_commDi
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_mem_iff
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_mem_iff_satisfies
#check @languageSortFiber_ofPatternPred_characteristicMap
#check @languageSortFiber_ofPatternPred_characteristicMap_spec
#check @rhoProc_langOSLF_predicate_to_fiber_mem_iff
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber_mem_iff
#check @representable_commDi_patternPred_beckChevalley
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_lifting
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_pathSemLift
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_pathSemClosed
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg
#check @representable_commDi_bc_and_graphDiamond
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_lifting
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemLift
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemClosed
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.rhoProc_commDi_bc_and_graphDiamond_of_pathSemLift_pkg
#check @possiblyProp
#check @relyProp
#check @galois_connection
#check @rhoOSLF
#check @lambdaOSLF
#check @petriOSLF
#check @Mettapedia.OSLF.Framework.TinyMLInstance.tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph
#check @Mettapedia.OSLF.Framework.TinyMLInstance.tinyML_commDiPathSemLiftPkg_of_liftEq
#check @Mettapedia.OSLF.Framework.TinyMLInstance.tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_commDiPathSemLiftPkg_of_liftEq
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_pathOrder
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaSpecAtomCheck
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaSpecAtomSem
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checkLangUsing_sat_sound_specAtoms
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checkLang_sat_sound_specAtoms
#check @OSLFFormula
#check @check_sat_sound
#check @Mettapedia.OSLF.Formula.checkLangUsing_sat_sound_sort_fiber
#check @Mettapedia.OSLF.Formula.checkLangUsing_sat_sound_sort_fiber_mem_iff
#check @checkLangUsing_sat_sound_proc_fiber
#check @checkLangUsing_sat_sound_proc_fiber_using
#check @checkLangUsing_sat_sound_proc_fiber_using_mem_iff
#check @checkLang_sat_sound_proc_fiber
#check @checkLang_sat_sound_proc_fiber_using
#check @Mettapedia.OSLF.Formula.checkLangUsingWithPred_sat_sound_graphObj_dia
#check @Mettapedia.OSLF.Formula.checkLangUsingWithPred_sat_sound_graphObj_box
#check @sem_dia_eq_langDiamond
#check @sem_box_eq_langBox
#check @HasType
#check @substitutability
#check @Mettapedia.OSLF.RhoCalculus.Soundness.progress
#check @langModalAdjunction
#check @rhoModalAdjunction

end Mettapedia.OSLF.SpecIndex
