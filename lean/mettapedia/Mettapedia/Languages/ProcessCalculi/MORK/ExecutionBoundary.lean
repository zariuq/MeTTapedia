import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge
import Mettapedia.Languages.ProcessCalculi.MORK.Conformance
import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.CollectionBridge

/-!
# MORK Execution Boundary

Packages the proven MORK execution boundary for the `morkTranslatable` fragment
of MeTTaIL. This file is a documentation surface — it re-exports the key theorems
from `MeTTaILBridge.lean` and states precisely what MORK can and cannot execute.

## What MORK executes

The `morkTranslatable` predicate (a decidable `Bool` function) defines the fragment:
- **IN scope**: variables (`.fvar`, `.bvar`), applications (`.apply`), lambdas,
  multi-lambdas, ground collections without rest-variables
- **OUT of scope**: `.subst` nodes (beta-redex evaluation requires reduction, not
  pattern matching) and `.collection _ _ (some _)` (rest-variable expansion requires
  runtime arity inspection)

## Bridge theorems

1. `applySubst_commutes`: For `morkTranslatable` patterns, substitution commutes
   with the `morkPatternToAtom` translation. This is the key algebraic property.

2. `declReduces_implies_mork_fire_full`: Full `DeclReduces` bridge handling both
   `topRule` and `congElem`. Direction: MeTTaIL reduction → MORK firing exists.

3. `congElem_implies_mork_zipper_fire`: Collection congruence bridge. When `congElem`
   rewrites an element inside a collection, the update factors through `LensRel`
   (principled zipper-based focus/replacement) and a MORK exec rule fires.
   Direction: MeTTaIL congElem → LensRel ∧ MORK firing exists.

5. The PeTTa/LP soundness chain (`petta_ruleApp_lp_sound` in LPSoundness.lean)
   builds on this boundary via `pettaRuleSafe` = `lpTranslatable`, which requires
   `morkTranslatable` on both rule sides.

## What is NOT claimed

- No completeness (MORK firing → DeclReduces): MORK's scheduler is more expressive
  than the declarative reduction relation
- For `congElem`: collection congruence is bridged via `congElem_implies_mork_zipper_fire`
  (zipper/lens factorization) and source-aware bridges use `languageDefToSourceExecRulesWithCongr`
  which extends the base rule set with `collectionReplaceSourceRule`.
- No beta-redex evaluation: `.subst` nodes are translated symbolically, not reduced
- No rest-variable expansion: `.collection _ _ (some _)` is rejected
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Re-exported boundary surface

These are the key definitions and theorems that constitute the MORK execution
boundary. They are defined in `MeTTaILBridge.lean`; this section makes
them visible as a coherent package. -/

namespace ExecutionBoundary

/-- The fragment predicate: which MeTTaIL patterns MORK can handle. -/
abbrev fragmentPredicate := @morkTranslatable

/-- Substitution commutation: the algebraic foundation of the bridge. -/
abbrev substCommutation := @applySubst_commutes

/-- Fire correspondence: DeclReduces → MORK fireRule (handles both topRule and congElem). -/
abbrev fireCorrespondence := @declReduces_implies_mork_fire_full

/-- Pattern translation: MeTTaIL Pattern → MORK Atom. -/
abbrev patternTranslation := @morkPatternToAtom

/-- Space injection: single-atom space from a pattern. -/
abbrev spaceInjection := @patternToSpace

/-- Rule translation: MeTTaIL RewriteRule → MORK ExecRule. -/
abbrev ruleTranslation := @rewriteRuleToExecRule

/-- Aggregator consistency: fold assembled result matches aggregator semantics. -/
abbrev aggregatorConsistency := @AggregatorConsistent

/-- Substitution extension: matchAtom preserves existing bindings. -/
abbrev substExtension := @matchAtom_extends

/-- Computable sinks = spec sinks (no-remove templates). -/
abbrev sinksCorrespondence := @Conformance.capplySinks_toFinset_no_remove

/-- Consumed atoms are from the input space. -/
abbrev consumedSoundness := @Conformance.cmatchPattern_consumed_subset

/-- Output substitution extends input substitution. -/
abbrev substSoundness := @Conformance.cmatchPattern_subst_extends

/-- Forward soundness: cmatchPattern results appear in matchPattern. -/
abbrev matchPatternSoundness := @Conformance.cmatchPattern_toFinset_sound

/-- Sinks composition with NodupSafe (generalizes no-remove). -/
abbrev sinksSafeCorrespondence := @Conformance.capplySinks_toFinset_safe

/-- Forward soundness: cfireRule results appear in fireRule. -/
abbrev fireRuleSoundness := @Conformance.cfireRule_toFinset_sound

/-- Backward completeness: matchPattern results have cmatchPattern preimages. -/
abbrev matchPatternCompleteness := @Conformance.matchPattern_toFinset_complete

/-- Backward completeness: fireRule results have cfireRule preimages. -/
abbrev fireRuleCompleteness := @Conformance.fireRule_toFinset_complete

/-- Scheduler permutation invariance: selectNextExec under KeyInjective. -/
abbrev schedulerPermInvariance := @selectNextExec_perm

/-- Exec-fact extraction: computable ↔ spec under Nodup. -/
abbrev execFactsPerm := @cExecFacts_perm_execFacts

/-- Scheduler step: computable selects same exec fact as spec under Nodup + KeyInjective. -/
abbrev schedulerSelectEq := @cWorkQueueStep_selectExec_eq

/-- List erase = Finset erase (consumed exec fact). -/
abbrev consumeExecCorrespondence := @cConsumeExec_toFinset

/-- Computable read copy = spec read copy under Nodup. -/
abbrev readCopyCorrespondence := @cReadCopy_toFinset

/-- Single-match fireExecFact correspondence: computable = spec under Nodup. -/
abbrev fireExecFactSingleMatch := @cFireExecFact_toFinset_single

/-- No-match fireExecFact correspondence: both reduce to consuming the exec fact. -/
abbrev fireExecFactEmpty := @cFireExecFact_toFinset_empty

/-- ExecFact extraction preserves the original atom. -/
abbrev extractPreservesAtom := @extractExecFact_atom

/-- ExecFact extraction is injective on atoms. -/
abbrev extractInjective := @extractExecFact_injective

/-- Consuming an exec fact strictly decreases cardinality. -/
abbrev consumeCardDecrease := @consumeExec_card_lt

/-- lexLt agrees with Mathlib's List.Lex. -/
abbrev lexLtBridge := @lexLt_iff_lex

/-- lexLt is irreflexive. -/
abbrev lexLtIrrefl := @lexLt_irrefl

/-- fireExecFact simplifies when exec fact is in the space. -/
abbrev fireExecFactSimplify := @fireExecFact_readCopy_simplify

/-- General multi-match cFireExecFact correspondence. -/
abbrev fireExecFactGeneral := @cFireExecFact_toFinset

/-- Foldl correspondence for multi-match sink application. -/
abbrev foldlSinksCorrespondence := @Conformance.foldl_capplySinks_toFinset

/-- Work-queue step correspondence (computable = spec under invariant). -/
abbrev workQueueStepCorrespondence := @cWorkQueueStep_toFinset

/-- Work-queue bounded-run correspondence (computable = spec under reachable invariant). -/
abbrev workQueueRunCorrespondence := @cWorkQueueRunN_toFinset

/-- Work-queue invariant bundle. -/
abbrev workQueueInvariant := @WorkQueueInvariant

/-- Source-aware exec fact extraction (compat + explicit modes). -/
abbrev sourceExecFactExtraction := @extractSourceExecFact

/-- Source-aware firing: matchInputSpec pipeline. -/
noncomputable abbrev sourceExecFactFiring := @fireSourceExecFact

/-! ### Hybrid source extension (generator/resource-backed factors) -/

/-- Compat-mode source firing agrees with regular fireRule. -/
abbrev sourceRuleCompat := @fireSourceRule_compat

/-- Computable source-aware firing. -/
abbrev cSourceExecFactFiring := @WQComputable.cFireSourceExecFact

/-- Source correspondence: cfireSourceRule → fireSourceRule (forward soundness). -/
abbrev sourceRuleSoundness := @Conformance.cfireSourceRule_toFinset_sound

/-- Source backward: fireSourceRule → cfireSourceRule (backward completeness). -/
abbrev sourceRuleCompleteness := @Conformance.fireSourceRule_toFinset_complete

/-- Termination: remove-only templates → cardinality strictly decreases. -/
abbrev terminationRemoveOnly := @fireExecFact_card_lt_of_removeOnly

/-- Fuel bound: scheduler takes at most fuel steps. -/
abbrev fuelBound := @workQueueRunN_steps_le_fuel

/-- Premise-to-source translation: MeTTaIL relationQuery → btm factor. -/
abbrev premiseTranslation := @premiseToSourceFactor

/-- Source-rule translation: MeTTaIL RewriteRule → MORK SourceExecRule. -/
abbrev sourceRuleTranslation := @rewriteRuleToSourceExecRule

/-- Premise translatability: all premises map to source factors. -/
abbrev premiseTranslatability := @allPremisesTranslatable

/-- Bindings translation: MeTTaIL Bindings → MORK Subst. -/
abbrev bindingsTranslation := @bindingsToSubst

/-- Workspace representation predicate for a single premise. -/
abbrev workspaceRepresentsPremise := @WorkspaceRepresentsPremise

/-- Workspace representation predicate for a list of premises. -/
abbrev workspaceRepresentsPremises := @WorkspaceRepresentsPremises

/-- Language def to source exec rules (filtered by premise translatability). -/
abbrev sourceRuleSetTranslation := @languageDefToSourceExecRules

/-- Per-rule bridge: zero premises, fvar LHS → fireSourceRule. -/
abbrev noPremiseBridge := @declReducesWithPremises_noPremise_fvar_mork_fireSourceRule

/-- Per-rule bridge: single relationQuery premise, fvar LHS → fireSourceRule. -/
abbrev singlePremiseBridge := @declReducesWithPremises_singlePremise_fvar_mork_fireSourceRule

/-- Full bridge: DeclReducesWithPremises (single premise) → ∃ source rule fires. -/
abbrev declReducesWithPremisesBridge := @declReducesWithPremises_single_implies_mork_fireSourceRule

/-- PremiseChain: step-by-step premise-witness correspondence. -/
abbrev premiseChainType := @PremiseChain

/-- PremiseChain → bindings reachable via applyPremisesWithEnv. -/
abbrev premiseChainImpliesApply := @premiseChain_implies_applyPremises

/-- PremiseChain → membership in matchSourceFactors. -/
abbrev premiseChainMatchFactors := @premiseChain_matchSourceFactors

/-- Per-rule bridge: N premises via PremiseChain, fvar LHS → fireSourceRule. -/
abbrev multiPremiseBridge := @declReducesWithPremises_multiPremise_fvar_mork_fireSourceRule

/-- Full bridge: DeclReducesWithPremises (N premises) → ∃ source rule fires. -/
abbrev declReducesWithPremisesMultiBridge := @declReducesWithPremises_multi_implies_mork_fireSourceRule

/-! ### Source guards (freshness premises) -/

/-- Source guard type: substitution-level conditions (separate from workspace-facing SourceFactor). -/
abbrev sourceGuardType := @SourceGuard

/-- Single guard matching: check a SourceGuard against a substitution. -/
abbrev matchSourceGuardDef := @matchSourceGuard

/-- All guards matching: check a list of SourceGuards against a substitution. -/
abbrev matchSourceGuardsDef := @matchSourceGuards

/-- Free variables of an atom (MORK-side). -/
abbrev atomFreeVarsDef := @atomFreeVars

/-- Freshness check on an atom (MORK-side). -/
abbrev isAtomFreshDef := @isAtomFresh

/-- Backward compat: fireSourceRule with no guards = unfiltered. -/
abbrev fireSourceRuleNoGuards := @fireSourceRule_no_guards

/-- Freshness correspondence: MeTTaIL freshness premise ↔ MORK SourceGuard.freshness. -/
abbrev freshnessCorrespondence := @freshness_premise_correspond

/-- Free-variable correspondence: morkPatternToAtom preserves free variables. -/
abbrev freeVarsCorrespondence := @morkPatternToAtom_freeVars

/-- isFresh ↔ isAtomFresh: freshness checks correspond across the bridge. -/
abbrev isFreshCorrespondence := @isFresh_iff_isAtomFresh

/-- Extended premise classification: premise → SourceFactor or SourceGuard. -/
abbrev premiseClassification := @premiseToFactorOrGuard

/-- Extended translatability: accepts relationQuery AND freshness premises. -/
abbrev extendedTranslatability := @allPremisesTranslatableExt

/-- Extended source factor extraction (from mixed premise lists). -/
abbrev extendedSourceFactors := @premisesToSourceFactorsExt

/-- Source guard extraction from premise lists. -/
abbrev sourceGuardExtraction := @premisesToSourceGuards

/-- Extended rule translation: MeTTaIL RewriteRule → MORK SourceExecRule (with guards). -/
abbrev extendedRuleTranslation := @rewriteRuleToSourceExecRuleExt

/-! ### mergeBindings ↔ matchAtom correspondence -/

/-- New variable binding: matchAtom agrees with mergeBindings (none case). -/
abbrev matchAtomNewBinding := @matchAtom_var_bindingsToSubst_new

/-- Existing variable binding: matchAtom agrees with mergeBindings (some case). -/
abbrev matchAtomExistingBinding := @matchAtom_var_bindingsToSubst_existing

/-- Single-step correspondence: mergeBindings step ↔ matchAtom on .var. -/
abbrev mergeBindingsStepCorrespondence := @mergeBindings_step_matchAtom_correspond

/-- Full correspondence: mergeBindings ↔ matchAtomList on .var patterns. -/
abbrev mergeBindingsCorrespondence := @mergeBindings_matchAtomList_correspond

/-! ### Multi-step closure -/

/-- Multi-step reduction closure. -/
abbrev multiStepClosure := @DeclReducesWithPremisesStar

/-- Per-step MORK source-rule firing (same guarantee as single-step bridge). -/
abbrev eachStepFires := @declReducesStar_each_step_fires

/-! ### Extended bridge (mixed relationQuery + freshness premises) -/

/-- Extended factor matching: PremiseChain → matchSourceFactors (for ext-translatable premises). -/
abbrev premiseChainMatchFactorsExt := @premiseChain_matchSourceFactorsExt

/-- Extended language def → source exec rules (filtering by ext-translatability). -/
abbrev languageDefSourceRulesExt := @languageDefToSourceExecRulesExt

/-- Per-rule ext bridge: PremiseChain + guards → fireSourceRule (with ext-translatable premises). -/
abbrev multiPremiseExtBridge := @declReducesWithPremises_multiPremise_fvar_mork_fireSourceRuleExt

/-- Full ext bridge: DeclReducesWithPremises → ∃ source rule fires (with ext-translatable premises). -/
abbrev fullExtBridge := @declReducesWithPremises_ext_implies_mork_fireSourceRule

/-! ### Collection congruence via zipper/lens

The canonical congruence surface. `congElem` (sub-collection element rewriting) is
modeled as focused sub-expression replacement via `AtomZipper` and `LensRel`.

Three theorem levels:
- **Structural**: `collection_lensRel` — element update satisfies `LensRel`
- **Semantic**: `congElem_implies_mork_zipper_fire` — LensRel + exec rule fires
- **Full DeclReduces**: `declReduces_implies_mork_fire_full` — handles both topRule and congElem

Source-aware bridges (`declReducesWithPremises_*`) use `languageDefToSourceExecRulesWithCongr`
which extends the base rule set with `collectionReplaceSourceRule`. -/

-- Zipper infrastructure

/-- Atom zipper type (Huet one-hole context). -/
abbrev atomZipperType := @AtomZipper

/-- Atom zipper reconstruction. -/
abbrev zipperRebuild := @rebuild

/-- Atom zipper focused replacement. -/
abbrev zipperReplaceFocus := @replaceFocus

/-- Navigate to i-th child of expression. -/
abbrev zipperDescendChild := @descendExprChild?

/-- Navigate back to parent. -/
abbrev zipperAscend := @ascend?

/-- Focus at a path of child indices. -/
abbrev zipperFocusAtPath := @focusAtPath?

/-- Replace sub-expression at a path and rebuild. -/
abbrev zipperReplaceAtPath := @replaceAtPath?

/-- Round-trip: focus then rebuild = original. -/
abbrev zipperFocusRebuild := @focusAtPath_rebuild

-- Lens relation + laws

/-- Lens relation: sub-expression focus + replacement. -/
abbrev zipperLensRel := @LensRel

/-- Get-Put lens law. -/
abbrev zipperGetPut := @lensRel_get_put

/-- Put-Get lens law. -/
abbrev zipperPutGet := @lensRel_put_get

/-- Put-Put lens law. -/
abbrev zipperPutPut := @lensRel_put_put

-- Collection specialization

/-- Collection element focus via zipper. -/
abbrev zipperCollectionFocus := @focusAtPath_collection

/-- Collection element replacement via zipper. -/
abbrev zipperCollectionReplace := @replaceAtPath_collection

/-- Collection element update satisfies LensRel. -/
abbrev collectionLensRel := @collection_lensRel

-- Primary congruence bridge

/-- **Canonical congruence bridge**: LensRel + fireRule (primary theorem). -/
abbrev congElemZipperBridge := @congElem_implies_mork_zipper_fire

/-- **Full DeclReduces bridge**: handles both topRule and congElem. -/
abbrev declReducesFullBridge := @declReduces_implies_mork_fire_full

-- Operational core (secondary)

/-- Translation commutation: `morkPatternToAtomList` is `List.map morkPatternToAtom`. -/
abbrev atomListEqMap := @morkPatternToAtomList_eq_map

/-- Translation commutation with `List.set`. -/
abbrev atomListSet := @morkPatternToAtomList_set

/-- Collection translation with element replacement. -/
abbrev collectionSet := @morkPatternToAtom_collection_set

/-- MORK-side collection element replacement. -/
abbrev collectionAtomReplace := @replaceElemInCollectionAtom

/-- Round-trip: MORK replacement ↔ MeTTaIL `List.set`. -/
abbrev collectionRoundtrip := @replaceElemInCollectionAtom_roundtrip

/-- Ground atoms are identity under `applySubst`. -/
abbrev groundSubstIdentity := @applySubst_ground

/-- Ground atoms match themselves. -/
abbrev groundSelfMatch := @matchAtom_ground_self

/-- Ad-hoc exec rule for collection element replacement. -/
abbrev collectionReplace := @collectionReplaceRule

/-- Firing the collection-replace rule. -/
abbrev collectionReplaceFires := @fireRule_collectionReplace

/-- Semantic-only congElem bridge (without LensRel factorization). -/
abbrev congElemBridge := @congElem_implies_mork_fire

-- Source-level congruence bridge (Layer G)

/-- Source-level encoding of collection replacement as a SourceExecRule. -/
abbrev collectionReplaceSource := @collectionReplaceSourceRule

/-- Source-level collection replace rule fires via fireSourceRule. -/
abbrev collectionReplaceSourceFires := @fireSourceRule_collectionReplaceSource

/-- Extended source-rule set with congruence rules. -/
abbrev sourceRulesWithCongr := @languageDefToSourceExecRulesWithCongr

/-- **Source-aware bridge**: DeclReduces → fireSourceRule with
    congruence-extended rule set. Handles both topRule and congElem. -/
abbrev declReducesSourceBridge := @declReduces_implies_mork_fireSourceRule

/-- Rest-irrelevance for morkPatternToAtom. -/
abbrev morkPatternToAtom_rest := @morkPatternToAtom_rest_irrelevant

/-- Extended source-rule set (ext) with congruence rules. -/
abbrev sourceRulesExtWithCongr := @languageDefToSourceExecRulesExtWithCongr

/-! ### Scheduler lift (Task A)

Sink commutation with exec-fact consumption, and the scheduler-to-source bridge. -/

/-- No sink produces a given atom via addition after substitution. -/
abbrev sinksDontProduce := @SinksDontProduce

/-- `applySinks` commutes with `\ {a}` when no sink produces `a`. -/
abbrev sinksSdiffComm := @applySinks_sdiff_comm

/-- Single-match fireExecFact = source-level applySinks minus exec atom. -/
abbrev fireExecFactSourceBridge := @fireExecFact_eq_applySinks_sdiff

/-- Scheduler makes progress when an exec fact is selected. -/
abbrev schedulerProgress := @scheduler_progress

/-- Base phase exactness. -/
abbrev baseStepExactness := @base_step_exactness

/-- Unfold phase exactness. -/
abbrev unfoldStepExactness := @unfold_step_exactness

/-- Fold phase exactness. -/
abbrev foldStepExactness := @fold_step_exactness

end ExecutionBoundary

/-! ## Canary theorems -/

section Canaries

#check @morkTranslatable
#check @applySubst_commutes
#check @declReduces_implies_mork_fire_full
#check @declReduces_implies_mork_fireSourceRule
#check @morkPatternToAtom
#check @morkPatternToAtom_rest_irrelevant
#check @declReducesWithPremises_single_implies_mork_fireSourceRule
#check @declReducesWithPremises_multi_implies_mork_fireSourceRule
#check @declReducesStar_each_step_fires
#check @declReducesWithPremises_ext_implies_mork_fireSourceRule
#check @languageDefToSourceExecRulesWithCongr
#check @languageDefToSourceExecRulesExtWithCongr
#check @patternToSpace
#check @rewriteRuleToExecRule
#check @languageDefToExecRules
#check @applySinks_sdiff_comm
#check @fireExecFact_eq_applySinks_sdiff
#check @scheduler_progress

end Canaries

/-! ## Axiom Audit

The MORK formalization uses only Lean's core axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (via Finset operations)
- `Quot.sound` (quotient soundness)

No custom axioms, no sorry, no native_decide.
14 noncomputable defs (all from Finset.toList); computable reference evaluators
provide kernel-checked conformance via rfl. -/

section AxiomAudit
#print axioms congElem_implies_mork_zipper_fire
#print axioms declReduces_implies_mork_fireSourceRule
#print axioms fireSourceRule_collectionReplaceSource
#print axioms declReduces_implies_mork_fire_full
#print axioms morkPatternToAtom_rest_irrelevant
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK
