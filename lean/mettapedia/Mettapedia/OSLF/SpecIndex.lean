import Mettapedia.OSLF.Main
import Mettapedia.OSLF.CoreMain
import Mettapedia.Languages.MeTTa.PeTTa
import Mettapedia.Logic.LP
import Mettapedia.OSLF.PathMap
import Mettapedia.Logic.OSLFImageFinite
import Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
import Mettapedia.OSLF.Framework.AssumptionNecessity
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure
import Mettapedia.OSLF.Framework.PaperClaimTracker
import Mettapedia.OSLF.Framework.PaperParityCanaries
import Mettapedia.OSLF.Framework.NTTClaimTracker

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
- Canonical packaged topos/internal-language + TOGL graph bridge endpoints:
  `ToposTOGLBridge.topos_internal_language_bridge_package`,
  `ToposTOGLBridge.topos_internal_language_full_route_family`,
  `ToposTOGLBridge.togl_graph_modal_bridge_package`,
  `ToposTOGLBridge.togl_internal_graph_correspondence_layer`,
  `ToposTOGLBridge.graphChain2`,
  `ToposTOGLBridge.togl_graph_composition_reductionGraphObj_family`,
  `ToposTOGLBridge.togl_graph_composition_diamond_family`
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

## IX. Conservative MaTT Claim Map (No Overclaim)

This section indexes only currently-proven MaTT-style claims in the
runtime/behavioral layer:

| # | Theorem | File | Scope |
|---|---------|------|-------|
| 1 | `doctrine_galois_is_langGalois` | MATTProvableNow.lean | runtime/behavioral indexed doctrine carries per-language Galois |
| 2 | `doctrine_adjunction_is_langModalAdjunction` | MATTProvableNow.lean | doctrine recovers per-language modal adjunction |
| 3 | `mode2SkeletonLaws` | Mode2SkeletonLaws.lean | bundled mode-skeleton id/assoc/mapPred laws |
| 4 | `runtime_runtime_square_coherence` | MATTProvableNow.lean | runtime/runtime mapPred commuting square |
| 5 | `runtime_behavioral_square_coherence` | MATTProvableNow.lean | runtime/behavioral mapPred commuting square |
| 6 | `runtime_mode_diamond_transport_comp` | MATTProvableNow.lean | composed runtime morphism diamond witness transport |
| 7 | `matt_canonical_runtime_behavioral_package` | MATTClaimMap.lean | canonical composed package: doctrine + mapPred functoriality + commuting squares + transport |
| 8 | `pure_mode_isolation` | MATTProvableNow.lean | current pure boundary: any morphism touching pure is pure identity |
| 9 | `mettaPure_runtime_behavioral_transport` | MATTProvableNow.lean | specialized runtime→behavioral witness transport for `mettaPure` |

Intentionally out of current theorem scope:
- full mode-2-category formalization
- pure-mode morphism theory (deferred until MeTTa-Pure bridge is established)

## X. Sorry / Axiom Census

**Current core-OSLF status (scope of this index):**
- 0 `sorry` in `Mettapedia/OSLF/RhoCalculus/Reduction.lean`
- 0 custom axioms introduced in this core OSLF slice
- Canonical-vs-extension policy is theorem-checked by
  `rhoSetDropWitness_canonical_vs_setExt`

Outside this scope, the π→ρ correspondence layer is tracked separately from this
core OSLF index.

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
#check @Mettapedia.Logic.OSLFImageFinite.imageFinite_langReducesExecUsing
#check @Mettapedia.Logic.OSLFImageFinite.imageFinite_langReducesUsing
#check @Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces
#check @Mettapedia.Logic.OSLFImageFinite.hm_converse_langReducesUsing
#check @Mettapedia.Logic.OSLFImageFinite.hm_converse_langReduces
#check @Mettapedia.OSLF.Framework.LangMorphism.sem_transfer_of_broadFragment
#check @Mettapedia.OSLF.Framework.LangMorphism.sem_transfer_of_diaBoxFragment
#check @Mettapedia.OSLF.Framework.LangMorphism.sem_of_diaBoxFragment_on_domain
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.sem_iff_of_endpointBroadFragment
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_converse_of_finiteSubrelation
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.reachableCoreStarFiniteSubrelation
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.reachableDerivedStarFiniteSubrelation
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_predDomain_endpoint
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end
#check @Mettapedia.OSLF.coreMain_nativeType_piOmega_translation_endpoint
#check @Mettapedia.OSLF.coreMain_nativeType_piOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.coreMain_nativeType_piSigmaOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.coreMain_nativeType_piOmegaProp_constructor_transport_bundle
#check @Mettapedia.OSLF.coreMain_nativeType_comp_piOmegaProp_constructor_transport_bundle
#check @Mettapedia.OSLF.coreMain_nativeType_piProp_colax_rules_endpoint
#check @Mettapedia.OSLF.coreMain_nativeType_piSigmaProp_colax_rules_endpoint
#check @Mettapedia.OSLF.coreMain_nativeType_constructor_grothendieck_endpoint
#check @Mettapedia.OSLF.coreMain_nativeType_constructor_groth_roundtrip
#check @Mettapedia.OSLF.coreMain_nativeType_piOmegaProp_grothendieck_package
#check @Mettapedia.OSLF.coreMain_nativeType_id_piOmega_canary
#check @Mettapedia.OSLF.coreMain_nativeType_id_piSigmaOmegaProp_canary
#check @Mettapedia.OSLF.coreMain_representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.coreMain_representable_patternPred_piSigma_transport_via_prop12_pack
#check @Mettapedia.OSLF.coreMain_representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.coreMain_representable_patternPred_piSigma_transport_pack
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.oslf_formula_ntt_wm_star_sound_ctx
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_star_to_fixpoint_endpoint
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_and_fixpoint_endpoint
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalClosureContext
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalModalSquare
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalHyperSquare
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalFormulaArgs
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalGoalArgs
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalTransportGoalArgs
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceObligation_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceConsequenceRuleOn_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceConsequenceRuleOn_compact_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceConsequenceRuleOn_compact_of_goal_canary
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_fixpoint
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_fixpoint_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal
#check @Mettapedia.OSLF.coreMain_canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact
#check @Mettapedia.OSLF.coreMain_canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
#check @Mettapedia.OSLF.coreMain_canonicalConsequenceRuleOn_compact_fixpoint
#check @Mettapedia.OSLF.coreMain_section12_worked_examples
#check @Mettapedia.OSLF.coreMain_dependent_parametric_generated_typing
#check @Mettapedia.OSLF.Framework.GeneratedTyping.dependent_parametric_generated_type_system_extension
#check @Mettapedia.OSLF.Framework.GeneratedTyping.rhoCalc_dependent_parametric_generated_type_system_extension
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.CalcPreludeDomainIndexedSemanticMorphism.transfer_domain_star_reachable_fragment_paramAtom_predDomainPair
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain.transfer_fragment_bundle_predDomainPair
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_predDomain_transfer_bundle_end_to_end
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.predDomain_rf_fragment_canary_nontrivial
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.predDomain_rf_fragment_canary_nontrivial_progress
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.predDomain_derivedStar_fragment_canary_nontrivial
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.predDomain_derivedStar_fragment_canary_nontrivial_progress
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.rhoCoreStarRel_not_imageFinite
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.rhoDerivedStarRel_not_imageFinite
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.not_global_hImageFinite_rhoCoreStarRel
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.not_global_hImageFinite_rhoDerivedStarRel
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.counterexample_hAtomAll_for_global_diaBox_transfer
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.counterexample_hDiaTopAll_for_global_diaBox_transfer
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.not_commDiWitnessLifting_rho_example
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.commDiWitnessLifting_not_derivable_globally
#check @Mettapedia.OSLF.NativeType.TheoryMorphism
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.preserves_piType
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.preserves_omegaTop
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.preserves_propImp
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.colax_piType
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.lax_piType
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.colax_propImp
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.lax_propImp
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.colax_pi_elim
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.colax_pi_intro
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.colax_prop_mp
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.colax_prop_intro
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.PiPropColaxRuleSet
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.PiSigmaPropColaxRuleSet
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piProp_colax_rules
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piSigmaProp_colax_rules
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.comp
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.comp_piProp_colax_rules
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.comp_piSigmaProp_colax_rules
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piOmega_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piSigmaOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piOmegaProp_with_constructor_transport_bundle
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.comp_piOmegaProp_with_constructor_transport_bundle
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.id_piOmega_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.id_piOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.id_piSigmaOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.NativeType.prop12_piSigmaPredicateRulePack
#check @Mettapedia.OSLF.NativeType.prop12_piEta_presheaf
#check @Mettapedia.OSLF.NativeType.prop12_sigmaEta_presheaf
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.NativeType.constructorPredFiberFunctorDual
#check @Mettapedia.OSLF.NativeType.ConstructorGrothendieckDual
#check @Mettapedia.OSLF.NativeType.constructorNatType_toGrothObj
#check @Mettapedia.OSLF.NativeType.grothObj_to_constructorNatType
#check @Mettapedia.OSLF.NativeType.constructorNatType_obj_roundtrip
#check @Mettapedia.OSLF.NativeType.constructorNatTypeHom_to_grothHom
#check @Mettapedia.OSLF.NativeType.grothHom_to_constructorNatTypeHom
#check @Mettapedia.OSLF.NativeType.constructorNatTypeHom_groth_roundtrip
#check @Mettapedia.OSLF.NativeType.fullPredFiberFunctorDual
#check @Mettapedia.OSLF.NativeType.FullPresheafGrothendieckObj
#check @Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom
#check @Mettapedia.OSLF.NativeType.ScopedConstructorPred
#check @Mettapedia.OSLF.NativeType.ScopedConstructorPred.toFullGrothObj
#check @Mettapedia.OSLF.NativeType.ScopedConstructorPredHom
#check @Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.toFullGrothHom
#check @Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.toFullGrothHom_comp
#check @Mettapedia.OSLF.NativeType.scoped_full_constructor_comparison_package
#check @Mettapedia.OSLF.NativeType.scoped_full_constructor_obj_comparison
#check @Mettapedia.OSLF.NativeType.scoped_fullGroth_base_eq_representable
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
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_internal_language_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_internal_language_full_route_family
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_modal_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_internal_graph_correspondence_layer
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_algebra_reductionGraphObj_family
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_composition_reductionGraphObj_family
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_composition_diamond_family
-- Paper-parity M3: full internal logic bridge
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_full_internal_logic_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_full_internal_logic_piSigma_rule_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
-- Paper-parity M4: n-step graph bridge
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.relCompN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.diamondIterN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN_iff_relCompN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2_eq_graphChainN_2
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.diamondIterN_iff_graphChainN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_complete_graph_bridge_package
#check @Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle
#check @Mettapedia.OSLF.NativeType.ScopedReachable
#check @Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle_reachable
#check @Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle_reachable_fragment
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
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_sigma_transport_via_prop12_pack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_pi_transport_via_prop12_pack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_via_prop12_pack
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
#check @Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
#check @Mettapedia.OSLF.Framework.theorem1_substitutability_forward
#check @Mettapedia.OSLF.Framework.theorem1_substitutability_imageFinite
#check @Mettapedia.OSLF.coreMain_theorem1_canonical_contract
#check @Mettapedia.OSLF.coreMain_theorem1_substitutability_forward
#check @Mettapedia.OSLF.coreMain_theorem1_substitutability_imageFinite
#check @Mettapedia.OSLF.coreMain_theorem1_langReduces_imageFinite
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalSCQuotRelOn
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedCanonicalSCQuotRelOn
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.predFinite_rhoCoreCanonicalSCQuotRelOn
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.predFinite_rhoDerivedCanonicalSCQuotRelOn
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn_pair_canary
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn_pair_canary
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_scoped_coreSC_edge_preservation_canary
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_scoped_derivedSC_edge_preservation_canary
#check @Mettapedia.OSLF.CoreMainHMEndpointMap
#check @Mettapedia.OSLF.coreMain_hm_endpoint_recommendation_map
#check @Mettapedia.OSLF.coreMain_paper_parity_theorem_package
#check @Mettapedia.OSLF.coreMain_paper_parity_theorem_package_langReduces
#check @Mettapedia.OSLF.CoreMainPaperParityCanonicalPackage
#check @Mettapedia.OSLF.coreMain_paper_parity_canonical_package
-- Paper-parity M1+M2: Category instance + equivalence at representables
#check @Mettapedia.OSLF.NativeType.fullPresheafGrothendieckCategory
#check @Mettapedia.OSLF.NativeType.fullGrothObj_to_scopedConstructorPred_at_representable
#check @Mettapedia.OSLF.NativeType.scoped_full_scoped_obj_roundtrip
#check @Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence
#check @Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
-- Unified paper-parity full package
#check @Mettapedia.OSLF.coreMain_paper_parity_full_package
#check @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness.progress
#check @langModalAdjunction
#check @rhoModalAdjunction
-- Paper-parity canaries
#check @Mettapedia.OSLF.Framework.PaperParityCanaries.rhoCalc_paper_parity_canary
#check @Mettapedia.OSLF.Framework.PaperParityCanaries.lambdaCalc_paper_parity_canary
#check @Mettapedia.OSLF.Framework.PaperParityCanaries.negative_canary_nonclosed_fragment
-- Paper-claim tracker
#check @Mettapedia.OSLF.Framework.PaperClaimTracker.paperClaimList_all_resolved
#check @Mettapedia.OSLF.Framework.PaperClaimTracker.provenCount_eq
#check @Mettapedia.OSLF.Framework.PaperClaimTracker.assumptionScopedCount_eq
-- Strict NTT theorem-number parity tracker (fully closed)
#check @Mettapedia.OSLF.Framework.NTTClaimTracker.nttRemaining_empty
#check @Mettapedia.OSLF.Framework.NTTClaimTracker.nttRemainingCount_zero
#check @Mettapedia.OSLF.Framework.NTTClaimTracker.fullNTTParity_closed
-- Canonical OSLF -> NTT -> WM closure wrappers
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.oslf_formula_ntt_wm_star_sound_of_pathOrder
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.oslf_formula_ntt_wm_step_sound_of_pathOrder
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.oslf_formula_ntt_wm_star_internalLogic_endpoint_of_pathOrder
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.oslf_formula_ntt_wm_star_wmObligation_via_topos_transport_canary_of_pathOrder
-- Conservative MaTT theorem map
#check @Mettapedia.OSLF.Framework.Mode2SkeletonLaws.mode2SkeletonLaws
#check @Mettapedia.OSLF.Framework.Mode2SkeletonLaws.mapPred_comp_holds
#check @Mettapedia.OSLF.Framework.MATTProvableNow.doctrine_galois_is_langGalois
#check @Mettapedia.OSLF.Framework.MATTProvableNow.doctrine_adjunction_is_langModalAdjunction
#check @Mettapedia.OSLF.Framework.MATTProvableNow.runtime_runtime_square_coherence
#check @Mettapedia.OSLF.Framework.MATTProvableNow.runtime_behavioral_square_coherence
#check @Mettapedia.OSLF.Framework.MATTProvableNow.runtime_mode_diamond_transport_comp
#check @Mettapedia.OSLF.Framework.MATTProvableNow.pure_mode_isolation
#check @Mettapedia.OSLF.Framework.MATTProvableNow.mettaPure_runtime_behavioral_transport
#check @Mettapedia.OSLF.Framework.MATTClaimMap.matt_pure_boundary_package
#check @Mettapedia.OSLF.Framework.MATTClaimMap.matt_canonical_runtime_behavioral_package
-- NTT endpoints
#check @Mettapedia.OSLF.NativeType.prop12_package
#check @Mettapedia.OSLF.NativeType.prop14_cosmicFibration
#check @Mettapedia.OSLF.NativeType.prop17_reification
#check @Mettapedia.OSLF.NativeType.def21_codomainFibration
#check @Mettapedia.OSLF.NativeType.def21_cartesianLift_proj
#check @Mettapedia.OSLF.NativeType.def21_cartesianLift_universal_comp
#check @Mettapedia.OSLF.NativeType.imageComprehensionAdjunction
#check @Mettapedia.OSLF.NativeType.imageComprehension_iff
#check @Mettapedia.OSLF.NativeType.thm23_internalLanguagePackage
#check @Mettapedia.OSLF.NativeType.thm23_functorialLaws

-- X. PathMap algebraic interface (ring.rs formalization)
-- AlgebraicResult carries the structural-sharing result tag from ring.rs
#check @Mettapedia.PathMap.AlgebraicResult
-- Lattice / DistributiveLattice / Quantale typeclass hierarchy
#check @Mettapedia.PathMap.PathMapLattice
#check @Mettapedia.PathMap.PathMapDistributiveLattice
#check @Mettapedia.PathMap.PathMapQuantale
-- Algebraic law typeclasses (proved at the resolve/value level)
#check @Mettapedia.PathMap.JoinComm
#check @Mettapedia.PathMap.MeetComm
#check @Mettapedia.PathMap.JoinIdem
#check @Mettapedia.PathMap.MeetIdem
#check @Mettapedia.PathMap.Absorption
-- Zipper typeclass hierarchy (ZipperMoving → ZipperValues → ZipperWriting → ZipperIteration)
#check @Mettapedia.PathMap.ZipperMoving
#check @Mettapedia.PathMap.ZipperBounded
#check @Mettapedia.PathMap.ZipperValues
#check @Mettapedia.PathMap.ZipperWriting
#check @Mettapedia.PathMap.ZipperIteration
#check @Mettapedia.PathMap.ZipperIterationRooted
#check @Mettapedia.PathMap.ZipperAbsolutePath
#check @Mettapedia.PathMap.ZipperForking
-- Extended Zipper trait families
#check @Mettapedia.PathMap.ZipperSubtries
#check @Mettapedia.PathMap.ZipperSubtriesNonEmpty
#check @Mettapedia.PathMap.ZipperProduct
#check @Mettapedia.PathMap.ZipperProductSpec
#check @Mettapedia.PathMap.ZipperPathBuffer
#check @Mettapedia.PathMap.ZipperPathBufferSpec
#check @Mettapedia.PathMap.ZipperReadOnlyIteration
#check @Mettapedia.PathMap.ZipperReadOnlyIterationSpec
#check @Mettapedia.PathMap.ZipperCreateResult
#check @Mettapedia.PathMap.ZipperCreation
#check @Mettapedia.PathMap.ZipperCreationSpec
-- AlgebraicStatus (in-place ops) + derived combinators
#check @Mettapedia.PathMap.AlgebraicStatus
#check @Mettapedia.PathMap.joinAll
-- Invariants from ring.rs documentation
#check @Mettapedia.PathMap.NonePrecedesIdentity
#check @Mettapedia.PathMap.SubtractLeftBiased
-- RelationalSpace: abstract interface over RelationEnv / PathMap-backed stores
#check @Mettapedia.OSLF.PathMap.RelationalSpace
#check @Mettapedia.OSLF.PathMap.toRelationEnv
#check @Mettapedia.OSLF.PathMap.toRelationEnv_query
#check @Mettapedia.OSLF.PathMap.query_comm_bridge

-- XI. PathMap Council additions (Math Council review)
-- AlgebraicResult.WellFormed — representation soundness predicate
#check @Mettapedia.PathMap.AlgebraicResult.WellFormed
-- WellFormed theorems for all four operations on Finset α
#check @Mettapedia.PathMap.pjoin_wellFormed
#check @Mettapedia.PathMap.pmeet_wellFormed
#check @Mettapedia.PathMap.psubtract_wellFormed
#check @Mettapedia.PathMap.prestrict_wellFormed
-- PathMapQuantale (Finset α) instance + associativity
#check @Mettapedia.PathMap.prestrict_assoc
-- ZipperLiveness — ascend succeeds when not at root (dual of ZipperBounded)
#check @Mettapedia.PathMap.ZipperLiveness
-- ZipperIterationComplete — completeness dual of ZipperIterationRooted
#check @Mettapedia.PathMap.ZipperIterationComplete
-- ZipperFunctorDerivative — zipper as ∂PathMap/∂V (McBride 2001)
#check @Mettapedia.PathMap.ZipperFunctorDerivative
#check @Mettapedia.PathMap.ZipperFunctorDerivativeSpec
-- PathMap OSLF instance
#check @Mettapedia.OSLF.PathMap.OSLFInstance.pathMapLang
#check @Mettapedia.OSLF.PathMap.OSLFInstance.pathMapOSLF
#check @Mettapedia.OSLF.PathMap.OSLFInstance.pathMapGalois
-- NTT soundness theorems (pathMap_pjoin_diamond / pathMap_pmeet_diamond pending)

-- PathMap ↔ PLN Evidence bridge (K&S / WorldModel grounded)
#check @Mettapedia.OSLF.PathMap.PLNBridge.finsetPathEvidence
#check @Mettapedia.OSLF.PathMap.PLNBridge.pjoin_evidence_additive
#check @Mettapedia.OSLF.PathMap.PLNBridge.prestrict_evidence_partition
#check @Mettapedia.OSLF.PathMap.PLNBridge.PathMapWorldModel

-- Weighted & Solomonoff evidence bridge
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.weightedPathEvidence
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.weightedPathEvidence_additive
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.weightedPathEvidence_partition
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.solomonoffPathEvidence
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.solomonoffPathEvidence_additive
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.solomonoffPathEvidence_strength
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.weightedPathMapWorldModel
#check @Mettapedia.OSLF.PathMap.SolomonoffBridge.finsetPathEvidence_eq_uniform

-- PathMapValuation (K&S-style valuation on stores)
#check @Mettapedia.OSLF.PathMap.Measure.PathMapValuation
#check @Mettapedia.OSLF.PathMap.Measure.countingPathMapValuation
#check @Mettapedia.OSLF.PathMap.Measure.mkWeightedValuation
#check @Mettapedia.OSLF.PathMap.Measure.solomonoffValuation
#check @Mettapedia.OSLF.PathMap.Measure.pathMapValuation_evidence_split
#check @Mettapedia.OSLF.PathMap.Measure.counting_valuation_eq_evidence_total

-- ZipperComplexity — formal O(k) / O(depth) depth-bound contracts
#check @Mettapedia.PathMap.ZipperComplexity

-- WorldModel bridge: Multiset α is the free commutative monoid solution
#check @Mettapedia.OSLF.PathMap.WorldModelBridge.multisetPathWorldModel
#check @Mettapedia.OSLF.PathMap.WorldModelBridge.multisetPathEvidence_additive
#check @Mettapedia.OSLF.PathMap.WorldModelBridge.finset_multiset_evidence_agree
#check @Mettapedia.OSLF.PathMap.WorldModelBridge.multisetWorldModel_finset_eq

-- XII. ZAM (Zipper Abstract Machine) — execution model soundness
-- ZipperReachableValue: inductively reachable values via toNextVal iteration
#check @Mettapedia.OSLF.PathMap.ZipperExecution.ZipperReachableValue
-- ZipperStoreValues: specification of all stored values
#check @Mettapedia.OSLF.PathMap.ZipperExecution.ZipperStoreValues
-- ZipperIterationSound: reachable ↔ stored (biconditional contract)
#check @Mettapedia.OSLF.PathMap.ZipperExecution.ZipperIterationSound
-- ZipperSpace: zipper-backed RelationalSpace
#check @Mettapedia.OSLF.PathMap.ZipperExecution.ZipperSpace
-- ZAM soundness: zipper-backed OSLF reduction = flat-env reduction
#check @Mettapedia.OSLF.PathMap.ZipperExecution.zam_oslf_sound
#check @Mettapedia.OSLF.PathMap.ZipperExecution.zam_diamond_sound
#check @Mettapedia.OSLF.PathMap.ZipperExecution.zam_box_sound
-- FlatZipper: reference ZipperIterationSound instance (list-backed)
#check @Mettapedia.OSLF.PathMap.FlatZipperInstance.FlatZipper

-- XIII. Trie stack — byte-indexed trie formalization (970 lines, 0 sorries)
-- CTrie: coalgebraic trie (List UInt8 → Option V), canonical semantics
#check @Mettapedia.OSLF.PathMap.Trie.CTrie
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.Bisim
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.AcceptsBisim
-- CTrie algebraic laws (up to Bisim)
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.union_idem
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.union_assoc
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.inter_idem
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.inter_assoc
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.absorption
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.inter_union_distrib
-- CTrie Brzozowski derivatives
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.deriv_union
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.deriv_inter
#check @Mettapedia.OSLF.PathMap.Trie.CTrie.deriv_diff
-- FTrie: inductive trie with sorted child lists
#check @Mettapedia.OSLF.PathMap.Trie.FTrie
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.lookup
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.entries
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.join
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.meet
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.subtract
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.restrict
-- FTrie → CTrie refinement homomorphism
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.toCTrie
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.Sorted
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.join_lookup
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.toCTrie_join
-- FTrie PathMapQuantale instance (via beqFTrie identity detection)
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.beqFTrie
#check @Mettapedia.OSLF.PathMap.Trie.FTrie.beqFTrie_refl
-- SimpleTrieZipper: ZipperIterationSound for FTrie
#check @Mettapedia.OSLF.PathMap.Trie.SimpleTrieZipper

-- XIV. ZAM Optimization Contracts (trie backend transfer of OptimizationTheorems)
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_relEnv_eq
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_diamond_false_early_termination
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_box_memoization_safe
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_deterministic_diamond_collapse
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_deterministic_box_collapse
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_diamond_mono
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_box_contra
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.zam_substitution_reduction_fusion
#check @Mettapedia.OSLF.PathMap.Trie.ZamContracts.trieZipperSpace

-- PeTTa OSLF instance (PeTTa → OSLF → mettail-rust pipeline)
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaOSLF
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaGalois
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaDiamond_spec
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaBox_spec
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaOSLF_lp_sound
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaRenderRust
#check @Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance.pettaWriteRust
-- PeTTa GSLT fiber
#check @Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex.pettaIdMorphism
#check @Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex.pettaForwardFiber
#check @Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex.pettaForwardFiber_oslf

-- LP Kernel (unified semantic core; Datalog retired to _archive/Datalog/)
-- LP-M1: Core syntax (generalizes Datalog with function symbols)
#check @Mettapedia.Logic.LP.LPSignature
#check @Mettapedia.Logic.LP.GroundAtom
#check @Mettapedia.Logic.LP.KnowledgeBase
-- LP-M2: Substitution/grounding
#check @Mettapedia.Logic.LP.Grounding.groundAtom
-- LP-M3: Semantics
#check @Mettapedia.Logic.LP.T_P_LP
#check @Mettapedia.Logic.LP.leastHerbrandModel
#check @Mettapedia.Logic.LP.leastHerbrandModel_fixpoint
#check @Mettapedia.Logic.LP.leastHerbrandModel_least
-- LP-M3b: SLD resolution
#check @Mettapedia.Logic.LP.SLDTree
#check @Mettapedia.Logic.LP.SLDTree_sound
-- LP-M3c: Executable SLD
#check @Mettapedia.Logic.LP.sldSearch
#check @Mettapedia.Logic.LP.sldSearch_sound
-- LP-M4: Function-free fragment + evaluation
#check @Mettapedia.Logic.LP.GroundTerm.equivConst
#check @Mettapedia.Logic.LP.HerbrandBase
#check @Mettapedia.Logic.LP.leastHerbrandModel_finite
#check @Mettapedia.Logic.LP.leastHerbrandModel_eq_iter_sup
-- LP-M4b: CertifyingDatalog bridge
#check @Mettapedia.Logic.LP.CDLGroundAtom
#check @Mettapedia.Logic.LP.GroundAtom.equivCDL
-- LP-M5: Provenance
#check @Mettapedia.Logic.LP.SemiringWithMonus
#check @Mettapedia.Logic.LP.T_P_K_LP
#check @Mettapedia.Logic.LP.T_P_K_LP_hom
-- LP-M6: PathMapBridge
#check @Mettapedia.Logic.LP.LPQuery
#check @Mettapedia.Logic.LP.positiveEvidence
#check @Mettapedia.Logic.LP.evidence_total
#check @Mettapedia.Logic.LP.leastHerbrandModel_monotone_in_rules
-- LP-M7: OSLFBridge
#check @Mettapedia.Logic.LP.lpToRelEnv
#check @Mettapedia.Logic.LP.mem_lpToRelEnv
#check @Mettapedia.Logic.LP.leastHerbrandModelRelEnv
-- LP-M8: WorldModelBridge
#check @Mettapedia.Logic.LP.lpModelEvidence
#check @Mettapedia.Logic.LP.lpLeastModelEvidence
#check @Mettapedia.Logic.LP.lpEvidence_monotone
#check @Mettapedia.Logic.LP.lpEDB_posEvidence

end Mettapedia.OSLF.SpecIndex
