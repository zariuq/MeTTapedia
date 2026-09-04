import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- On a scope-safe source subframe, a sealed environment's pulled-back key
is independent of both keyed-canonicalizer depths. -/
theorem CostStaticRegionNode.sourceSemanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (supportNil : ∀ slot,
      (environment.atomValue slot).key.targetSupport = [])
    {safetyDepth : Nat} (availableDepth scopeDepth : Nat) (pattern : Pattern)
    (safe : binderSafeAt rhoReflectivePresentation.quoteConstructor
      safetyDepth pattern = true)
    (depthOrder : safetyDepth ≤ scopeDepth) :
    sourceSemanticPatternKeyAt node environment availableDepth scopeDepth
        pattern =
      Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
        environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern) := by
  have mappedSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      safetyDepth (mapPattern (color.symbols rhoCIGSLT) pattern) = true := by
    rw [CostStaticColor.binderSafeAt_mapPattern_symbols]
    exact safe
  unfold sourceSemanticPatternKeyAt
  rw [node.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_le
    ((color.symbols rhoCIGSLT).constructor
      rhoReflectivePresentation.quoteConstructor) mappedSafe depthOrder]
  exact Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
    environment supportNil availableDepth 0 _

/-- A scope-safe frame canonicalizes identically with its pulled-back sealed
key and the corresponding depth-free target key. -/
theorem CostStaticRegionNode.canonicalizeByDepths_sourceSemanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (supportNil : ∀ slot,
      (environment.atomValue slot).key.targetSupport = []) :
    ∀ (availableDepth scopeDepth safetyDepth : Nat) (pattern : Pattern),
      binderSafeAt rhoReflectivePresentation.quoteConstructor safetyDepth
          pattern = true →
      safetyDepth ≤ scopeDepth →
      canonicalizeByDepths (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation availableDepth scopeDepth pattern =
        canonicalizeByDepths
          (fun _ _ pattern =>
            Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
              environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern))
          rhoReflectivePresentation availableDepth scopeDepth pattern := by
  intro availableDepth scopeDepth safetyDepth pattern safe depthOrder
  induction pattern using Pattern.inductionOn generalizing availableDepth
      scopeDepth safetyDepth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      let childSafetyDepth := match arguments with
        | [_] =>
            if constructor == rhoReflectivePresentation.quoteConstructor
              then 0 else safetyDepth
        | _ => safetyDepth
      have argumentsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor childSafetyDepth
          arguments = true := by
        cases arguments with
        | nil => simp [binderSafeListAt]
        | cons argument arguments =>
            cases arguments with
            | nil =>
                by_cases quoted :
                    constructor = rhoReflectivePresentation.quoteConstructor
                · have quotedDecision :
                      (constructor ==
                        rhoReflectivePresentation.quoteConstructor) = true :=
                    beq_iff_eq.mpr quoted
                  simpa [childSafetyDepth, binderSafeAt, quotedDecision,
                    binderSafeListAt] using safe
                · have quotedDecision :
                      (constructor ==
                        rhoReflectivePresentation.quoteConstructor) = false :=
                    beq_eq_false_iff_ne.mpr quoted
                  simpa [childSafetyDepth, binderSafeAt, quotedDecision,
                    binderSafeListAt] using safe
            | cons second remainder =>
                simpa [childSafetyDepth, binderSafeAt] using safe
      have childDepthOrder : childSafetyDepth ≤ scopeDepth := by
        cases arguments with
        | nil => simpa [childSafetyDepth] using depthOrder
        | cons argument arguments =>
            cases arguments with
            | nil =>
                by_cases quoted :
                    constructor = rhoReflectivePresentation.quoteConstructor
                · simp [childSafetyDepth, quoted]
                · simpa [childSafetyDepth, quoted] using depthOrder
            | cons second remainder =>
                simpa [childSafetyDepth] using depthOrder
      simp only [canonicalizeByDepths]
      apply congrArg
      rw [canonicalizeListByDepths_eq_map,
        canonicalizeListByDepths_eq_map]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership _ _ _
        ((binderSafeListAt_eq_true_iff _ _ _).mp argumentsSafe argument
          membership) childDepthOrder
  | hlambda binder body inductionHypothesis =>
      have bodySafe : binderSafeAt rhoReflectivePresentation.quoteConstructor
          (safetyDepth + 1) body = true := by
        simpa [binderSafeAt] using safe
      simp only [canonicalizeByDepths, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis _ _ _ bodySafe
        (Nat.add_le_add_right depthOrder 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      have bodySafe : binderSafeAt rhoReflectivePresentation.quoteConstructor
          (safetyDepth + arity) body = true := by
        simpa [binderSafeAt] using safe
      simp only [canonicalizeByDepths, Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis _ _ _ bodySafe
        (Nat.add_le_add_right depthOrder arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [canonicalizeByDepths, Pattern.subst.injEq]
      exact ⟨
        bodyHypothesis _ _ _ safe.1
          (Nat.add_le_add_right depthOrder 1),
        replacementHypothesis _ _ _ safe.2 depthOrder⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor safetyDepth elements =
            true := by
        simpa [binderSafeAt] using safe
      have normalizedElementsEq :
          canonicalizeListByDepths
              (sourceSemanticPatternKeyAt node environment)
              rhoReflectivePresentation availableDepth scopeDepth elements =
            canonicalizeListByDepths
              (fun _ _ pattern =>
                Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
                  environment 0
                    (mapPattern (color.symbols rhoCIGSLT) pattern))
              rhoReflectivePresentation availableDepth scopeDepth elements := by
        rw [canonicalizeListByDepths_eq_map,
          canonicalizeListByDepths_eq_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership _ _ _
          ((binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe element
            membership) depthOrder
      have normalizedElementsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor safetyDepth
          (canonicalizeListByDepths
            (sourceSemanticPatternKeyAt node environment)
            rhoReflectivePresentation availableDepth scopeDepth elements) =
            true := by
        rw [canonicalizeListByDepths_eq_map,
          binderSafeListAt_eq_true_iff]
        intro normalizedElement normalizedMembership
        rw [List.mem_map] at normalizedMembership
        obtain ⟨element, membership, rfl⟩ := normalizedMembership
        exact canonicalizeByDepths_binderSafeAt
          (sourceSemanticPatternKeyAt node environment)
          rhoReflectivePresentation rhoReflectivePresentation.quoteConstructor
          availableDepth scopeDepth safetyDepth element
          ((binderSafeListAt_eq_true_iff _ _ _).mp elementsSafe element
            membership)
      have stableNormalizedElementsSafe : binderSafeListAt
          rhoReflectivePresentation.quoteConstructor safetyDepth
          (canonicalizeListByDepths
            (fun _ _ pattern =>
              Mettapedia.GSLT.LanguageDef.CostStaticRegionNode.semanticPatternKeyAt
                environment 0 (mapPattern (color.symbols rhoCIGSLT) pattern))
            rhoReflectivePresentation availableDepth scopeDepth elements) =
              true := by
        rw [← normalizedElementsEq]
        exact normalizedElementsSafe
      cases rest with
      | some restName =>
          simpa [canonicalizeByDepths] using normalizedElementsEq
      | none =>
          by_cases parallel :
              collectionType = rhoReflectivePresentation.parallelCollection
          · subst collectionType
            simp only [canonicalizeByDepths, beq_self_eq_true, if_true]
            rw [normalizedElementsEq]
            apply congrArg (collapseParallel rhoReflectivePresentation)
            unfold normalizeParallelElementsBy
            apply CostStaticAtomKeyCospan.sortPatternsBy_eq_of_keys_eq_on
            intro member memberMembership
            have retainedMembership := List.mem_of_mem_filter memberMembership
            rw [List.mem_flatMap] at retainedMembership
            obtain ⟨sourcePattern, sourceMembership, memberSource⟩ :=
              retainedMembership
            have sourceSafe :=
              (binderSafeListAt_eq_true_iff _ _ _).mp
                stableNormalizedElementsSafe
                sourcePattern sourceMembership
            have memberSafe : binderSafeAt
                rhoReflectivePresentation.quoteConstructor safetyDepth
                member = true := by
              exact (binderSafeListAt_eq_true_iff _ _ _).mp
                (parallelSplice_binderSafeListAt rhoReflectivePresentation
                  rhoReflectivePresentation.quoteConstructor safetyDepth
                    sourceSafe) member memberSource
            exact
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.sourceSemanticPatternKeyAt_eq_of_atomTargetSupport_eq_nil
                node environment supportNil availableDepth scopeDepth member
                  memberSafe depthOrder
          · have notParallel :
                (collectionType ==
                  rhoReflectivePresentation.parallelCollection) = false :=
              beq_eq_false_iff_ne.mpr parallel
            simpa [canonicalizeByDepths, notParallel] using
              congrArg
                (fun normalized =>
                  Pattern.collection collectionType normalized none)
                normalizedElementsEq

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
