import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignResidualSpine
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableLeafRoutes
import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalFreeRenaming

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Reifying only free variables preserves a canonical bound-variable
terminal. -/
theorem canonicalize_environmentReify_eq_bvar_of_eq
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {pattern : Pattern} {index : Nat}
    (canonical : canonicalize rhoReflectivePresentation pattern =
      .bvar index) :
    canonicalize rhoReflectivePresentation (environment.reify pattern) =
      .bvar index := by
  rw [environment.reify_eq_renameFVars,
    canonicalize_renameFVars_factor rhoReflectivePresentation (by decide),
    canonical]
  simp [Pattern.renameFVars, canonicalize]

/-- Reifying free variables transports a canonical free-variable terminal to
the environment's selected source name. -/
theorem canonicalize_environmentReify_eq_fvar_of_eq
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      occurrences}
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {pattern : Pattern} {name : String}
    (canonical : canonicalize rhoReflectivePresentation pattern =
      .fvar name) :
    canonicalize rhoReflectivePresentation (environment.reify pattern) =
      .fvar (environment.reifyName name) := by
  rw [environment.reify_eq_renameFVars,
    canonicalize_renameFVars_factor rhoReflectivePresentation (by decide),
    canonical]
  simp [Pattern.renameFVars, canonicalize]

/-- Heterogeneously equal thinning witnesses act identically on indices. -/
theorem CostStaticBinderThinning.embedIndexAt_eq_of_eq_heq
    {source : CIGSLT} {color : CostStaticColor}
    {leftSourceBound leftTargetBound rightSourceBound rightTargetBound :
      List TypeExpr}
    {leftThinning : CostStaticBinderThinning source color leftSourceBound
      leftTargetBound}
    {rightThinning : CostStaticBinderThinning source color rightSourceBound
      rightTargetBound}
    (sourceBoundEq : leftSourceBound = rightSourceBound)
    (targetBoundEq : leftTargetBound = rightTargetBound)
    (equal : HEq leftThinning rightThinning) (depth index : Nat) :
    leftThinning.embedIndexAt depth index =
      rightThinning.embedIndexAt depth index := by
  subst rightSourceBound
  subst rightTargetBound
  cases equal
  rfl

/-- Two same-colour reached plans which canonically expose the same bound
variable have an exact apex in every enclosing semantic cospan. -/
noncomputable def rho_reachedPlanPairCommonApex_of_sameColorBVar
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (index : Nat)
    (leftCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload = .bvar index)
    (rightCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload = .bvar index) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  obtain ⟨leftSource⟩ := rhoBVarTowerSource_sameColor
    (sizeOf leftPayload) leftReached.plan 0 index (by omega) leftCanonical
  obtain ⟨rightSource⟩ := rhoBVarTowerSource_sameColor
    (sizeOf rightPayload) rightReached.plan 0 index (by omega) rightCanonical
  have sourceIndexEq : leftSource.sourceIndex = rightSource.sourceIndex := by
    apply leftReached.thinning.embedIndexAt_injective 0
    calc
      leftReached.thinning.embedIndexAt 0 leftSource.sourceIndex = index :=
        leftSource.index_eq
      _ = rightReached.thinning.embedIndexAt 0 rightSource.sourceIndex :=
        rightSource.index_eq.symm
      _ = leftReached.thinning.embedIndexAt 0 rightSource.sourceIndex :=
        (CostStaticBinderThinning.embedIndexAt_eq_of_eq_heq sourceBoundEq
          targetBoundEq thinningEq 0 rightSource.sourceIndex).symm
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment rightValues).1
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have leftReified : canonicalize rhoReflectivePresentation
      (leftEnvironment.reify leftReached.plan.abstractPattern) =
        .bvar leftSource.sourceIndex :=
    canonicalize_environmentReify_eq_bvar_of_eq leftEnvironment
      leftSource.abstractCanonical
  have rightReified : canonicalize rhoReflectivePresentation
      (rightEnvironment.reify rightReached.plan.abstractPattern) =
        .bvar rightSource.sourceIndex :=
    canonicalize_environmentReify_eq_bvar_of_eq rightEnvironment
      rightSource.abstractCanonical
  have leftKeyed : canonicalizeByDepths
      (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
        leftEnvironment)
      rhoReflectivePresentation callbackAvailable callbackScope
      (leftEnvironment.reify leftReached.plan.abstractPattern) =
        .bvar leftSource.sourceIndex :=
    canonicalizeByDepths_eq_bvar_of_canonicalize_eq _ _ _ _ leftReified
  have rightKeyed : canonicalizeByDepths
      (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
        rightEnvironment)
      rhoReflectivePresentation callbackAvailable callbackScope
      (rightEnvironment.reify rightReached.plan.abstractPattern) =
        .bvar rightSource.sourceIndex :=
    canonicalizeByDepths_eq_bvar_of_canonicalize_eq _ _ _ _ rightReified
  have parentThinningEq (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars callbackScope pattern =
        rightView.node.thinning.thickenAmbientBVars callbackScope pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars callbackScope pattern)
      (leftView.targetBound_eq_targetBound rightView)
  let endpoint := Pattern.bvar
    (leftView.node.thinning.embedIndexAt callbackScope leftSource.sourceIndex)
  have leftEndpoint :
      cospan.reifyLeft leftEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars callbackScope
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
                  leftEnvironment)
                rhoReflectivePresentation callbackAvailable callbackScope
                (leftEnvironment.reify leftReached.plan.abstractPattern)))) =
        endpoint := by
    rw [leftKeyed]
    simp [endpoint, Pattern.renameFVars, mapPattern,
      CostStaticBinderThinning.thickenAmbientBVars,
      CostStaticAtomKeyCospan.reifyLeft]
  have rightEndpoint :
      cospan.reifyRight rightEnvironment.lookupAtom?
          (rightView.node.thinning.thickenAmbientBVars callbackScope
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
                  rightEnvironment)
                rhoReflectivePresentation callbackAvailable callbackScope
                (rightEnvironment.reify rightReached.plan.abstractPattern)))) =
        endpoint := by
    rw [rightKeyed, ← sourceIndexEq, ← parentThinningEq]
    simp [endpoint, Pattern.renameFVars, mapPattern,
      CostStaticBinderThinning.thickenAmbientBVars,
      CostStaticAtomKeyCospan.reifyRight]
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    targetDeclaration callbackRoot _ _
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftEndpoint.symm rightEndpoint.symm
      (CostStaticAtomKeyCospan.CommonRestorationApex.refl cospan
        targetDeclaration callbackRoot endpoint)

/-- Two same-colour reached plans which canonically expose the same authored
free variable meet at the corresponding common semantic atom. -/
noncomputable def rho_reachedPlanPairCommonApex_of_sameColorFVar
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (name : String)
    (leftCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload = .fvar name)
    (rightCanonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload = .fvar name) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  obtain ⟨leftSource⟩ := rhoFVarTowerSource_sameColor
    (sizeOf leftPayload) leftReached.plan 0 name (by omega) leftCanonical
  obtain ⟨rightSource⟩ := rhoFVarTowerSource_sameColor
    (sizeOf rightPayload) rightReached.plan 0 name (by omega) rightCanonical
  let sourceName := costRegionSourceVariableName name
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment rightValues).1
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  have leftReified : canonicalize rhoReflectivePresentation
      (leftEnvironment.reify leftReached.plan.abstractPattern) =
        .fvar (leftEnvironment.reifyName sourceName) :=
    canonicalize_environmentReify_eq_fvar_of_eq leftEnvironment
      leftSource.abstractCanonical
  have rightReified : canonicalize rhoReflectivePresentation
      (rightEnvironment.reify rightReached.plan.abstractPattern) =
        .fvar (rightEnvironment.reifyName sourceName) :=
    canonicalize_environmentReify_eq_fvar_of_eq rightEnvironment
      rightSource.abstractCanonical
  have leftKeyed : canonicalizeByDepths
      (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
        leftEnvironment)
      rhoReflectivePresentation callbackAvailable callbackScope
      (leftEnvironment.reify leftReached.plan.abstractPattern) =
        .fvar (leftEnvironment.reifyName sourceName) :=
    canonicalizeByDepths_eq_fvar_of_canonicalize_eq _ _ _ _ leftReified
  have rightKeyed : canonicalizeByDepths
      (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
        rightEnvironment)
      rhoReflectivePresentation callbackAvailable callbackScope
      (rightEnvironment.reify rightReached.plan.abstractPattern) =
        .fvar (rightEnvironment.reifyName sourceName) :=
    canonicalizeByDepths_eq_fvar_of_canonicalize_eq _ _ _ _ rightReified
  have leftAbstractMembership : sourceName ∈
      leftReached.plan.abstractPattern.freeFvarNames := by
    rw [← mem_freeFvarNames_canonicalize_iff rhoReflectivePresentation,
      leftSource.abstractCanonical]
    simp [sourceName, iterDrop, Pattern.freeFvarNames]
  have rightAbstractMembership : sourceName ∈
      rightReached.plan.abstractPattern.freeFvarNames := by
    rw [← mem_freeFvarNames_canonicalize_iff rhoReflectivePresentation,
      rightSource.abstractCanonical]
    simp [sourceName, iterDrop, Pattern.freeFvarNames]
  have leftRootMembership : sourceName ∈
      leftView.node.skeleton.1.freeFvarNames := by
    rw [leftView.node.skeleton_pattern, leftReached.abstract_eq]
    exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
      leftReached.skeletonContext leftAbstractMembership
  have rightRootMembership : sourceName ∈
      rightView.node.skeleton.1.freeFvarNames := by
    rw [rightView.node.skeleton_pattern, rightReached.abstract_eq]
    exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
      rightReached.skeletonContext rightAbstractMembership
  have atomApex := memberFVar_commonRestorationApex leftView.node
    rightView.node leftView.children rightView.children leftEnvironment
    rightEnvironment sourceName leftRootMembership rightRootMembership
    targetDeclaration callbackRoot
  have leftEndpoint :
      cospan.reifyLeft leftEnvironment.lookupAtom?
          (leftView.node.thinning.thickenAmbientBVars callbackScope
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
                  leftEnvironment)
                rhoReflectivePresentation callbackAvailable callbackScope
                (leftEnvironment.reify leftReached.plan.abstractPattern)))) =
        cospan.reifyLeft leftEnvironment.lookupAtom?
          (.fvar (leftEnvironment.reifyName sourceName)) := by
    rw [leftKeyed]
    simp only [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]
  have rightEndpoint :
      cospan.reifyRight rightEnvironment.lookupAtom?
          (rightView.node.thinning.thickenAmbientBVars callbackScope
            (mapPattern (color.symbols rhoCIGSLT)
              (canonicalizeByDepths
                (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
                  rightEnvironment)
                rhoReflectivePresentation callbackAvailable callbackScope
                (rightEnvironment.reify rightReached.plan.abstractPattern)))) =
        cospan.reifyRight rightEnvironment.lookupAtom?
          (.fvar (rightEnvironment.reifyName sourceName)) := by
    rw [rightKeyed]
    simp only [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    targetDeclaration callbackRoot _ _
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftEndpoint.symm rightEndpoint.symm atomApex

/-- Same-colour reached plans whose common canonical result is a variable
admit the exact parent-cospan apex at arbitrary canonicalization, scope, and
restoration depths.  The premise concerns the surviving canonical result, so
it also covers quotation and parallel shells whose noncontributing positions
collapse to units. -/
noncomputable def rho_reachedPlanPairCommonApex_of_sameColorVariable
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) rightPayload)
    (canonicalIsVariable :
      (∃ index, canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) leftPayload = .bvar index) ∨
      ∃ name, canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) leftPayload = .fvar name) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  rcases canonicalIsVariable with ⟨index, leftCanonical⟩ | ⟨name, leftCanonical⟩
  · exact rho_reachedPlanPairCommonApex_of_sameColorBVar leftView rightView
      callbackAvailable callbackScope callbackRoot leftReached rightReached
      sourceBoundEq targetBoundEq thinningEq index leftCanonical
      (canonical.symm.trans leftCanonical)
  · exact rho_reachedPlanPairCommonApex_of_sameColorFVar leftView rightView
      callbackAvailable callbackScope callbackRoot leftReached rightReached
      name leftCanonical (canonical.symm.trans leftCanonical)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
