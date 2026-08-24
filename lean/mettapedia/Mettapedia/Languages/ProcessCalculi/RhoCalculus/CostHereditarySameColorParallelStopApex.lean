import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryNodeCommonAssignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCommonRestorationApex

namespace ParallelFrontier

/-- Same-colour canonical equality preserves the multiset of recursively
flattened parallel leaves, classified by their ordinary canonical forms. -/
theorem rhoProc_parallelLeaves_map_perm_of_sameColor_canonical_eq
    {Key : Type} [LinearOrder Key]
    (key : Nat → Pattern → Key) (color : CostStaticColor)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {left right : Pattern}
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage free bound left
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage free bound right
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) left =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl) right)
    (depth : Nat) :
    List.Perm
      ((parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        left).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)))
      ((parallelLeaves
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        right).map
          (canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl))) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftFrontier := rhoProc_parallelLeaves_keyed_frontier_perm key color
    color free bound leftTyped depth
  have rightFrontier := rhoProc_parallelLeaves_keyed_frontier_perm key color
    color free bound rightTyped depth
  have wrappedCanonical : canonicalize declaration
        (.collection declaration.parallelCollection [left] none) =
      canonicalize declaration
        (.collection declaration.parallelCollection [right] none) := by
    simpa only [canonicalize_parallel_singleton] using canonical
  have outer := canonicalize_parallelContents_keyed_perm_of_equal key
    declaration depth wrappedCanonical
  have leftToLeaves : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth left]).map
          (canonicalize declaration))
      ((parallelLeaves declaration left).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        leftFrontier.map (canonicalize declaration)
  have rightToLeaves : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth right]).map
          (canonicalize declaration))
      ((parallelLeaves declaration right).map
          (canonicalize declaration)) := by
    simpa [declaration, canonicalizeListByAt_eq_map, List.map_map,
      Function.comp_def, canonicalize_canonicalizeByAt_unconditional] using
        rightFrontier.map (canonicalize declaration)
  have outerSingleton : List.Perm
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth left]).map
          (canonicalize declaration))
      ((parallelContents declaration
        [canonicalizeByAt key declaration depth right]).map
          (canonicalize declaration)) := by
    simpa [canonicalizeListByAt] using outer
  exact leftToLeaves.symm.trans (outerSingleton.trans rightToLeaves)

/-- Same-colour canonical equality lifts through two admitted process plans
to an occurrence-preserving restoration permutation of their abstract
parallel frontiers. -/
noncomputable def
    parallelLeaves_abstractPattern_permutation_of_sameColor_canonical_eq
    {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter :
      Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (targetDeclaration : ReflectivePresentationDecl) (depth : Nat)
    (leftFrame rightFrame : Pattern → Pattern)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          leftRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          leftFrame leftAbstract = leftEndpoint) →
      (∃ rightAbstract,
          rightRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          rightFrame rightAbstract = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration depth leftEndpoint rightEndpoint) :
    CostStaticAtomKeyCospan.CommonRestorationApex.Permutation
      (source := rhoCIGSLT) cospan targetDeclaration depth
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        leftPlan.abstractPattern).map leftFrame)
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        rightPlan.abstractPattern).map rightFrame) := by
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftTraversal :=
    parallelLeaves_map_abstractPattern_forall2_with_membership leftPlan
      leftAdmission leftFrame
  have rightTraversal :=
    parallelLeaves_map_abstractPattern_forall2_with_membership rightPlan
      rightAdmission rightFrame
  have leftTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable leftPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact leftAdmission.wellSorted.1.1
  have rightTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable rightPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact rightAdmission.wellSorted.1.1
  have permutation :=
    rhoProc_parallelLeaves_map_perm_of_sameColor_canonical_eq
      (fun _ pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      color leftTyped rightTyped canonical depth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_related_map_perm
    cospan targetDeclaration depth (canonicalize rawDeclaration)
      (canonicalize rawDeclaration) leftTraversal rightTraversal permutation
      close

/-- Reconstruct two same-colour process-plan frames from restoration evidence
on their canonically paired parallel leaves. -/
noncomputable def processPlans_commonRestorationApex_of_sameColorCanonical
    {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin leftEnvironment.atomCount → Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEnvironment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (targetDeclaration : ReflectivePresentationDecl)
    (targetDeclaration_eq : targetDeclaration =
      costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
    (scopeDepth depth : Nat)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          leftRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration depth
            (cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
          rightRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration depth
            (cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration depth leftEndpoint rightEndpoint) :
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftFrame := fun pattern =>
      cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify pattern)))
    let rightFrame := fun pattern =>
      cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify pattern)))
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration depth
      (canonicalizeByAt key targetDeclaration depth
        (leftFrame leftPlan.abstractPattern))
      (canonicalizeByAt key targetDeclaration depth
        (rightFrame rightPlan.abstractPattern)) := by
  subst targetDeclaration
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftFrame := fun pattern =>
    cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify pattern)))
  let rightFrame := fun pattern =>
    cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify pattern)))
  let leftEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration depth (leftFrame pattern)
  let rightEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration depth (rightFrame pattern)
  have aligned :=
    parallelLeaves_abstractPattern_permutation_of_sameColor_canonical_eq
      leftPlan rightPlan leftAdmission rightAdmission canonical cospan
      targetDeclaration depth leftEndpoint rightEndpoint close
  have leftPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan leftAdmission scopeDepth depth
  have rightPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan rightAdmission scopeDepth depth
  have wrapped : CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      cospan targetDeclaration depth
      (canonicalizeByAt key targetDeclaration depth
        (.collection targetDeclaration.parallelCollection
          [leftFrame leftPlan.abstractPattern] none))
      (canonicalizeByAt key targetDeclaration depth
        (.collection targetDeclaration.parallelCollection
          [rightFrame rightPlan.abstractPattern] none)) :=
    CostStaticAtomKeyCospan.CommonRestorationApex.parallel_of_permutation
      cospan targetDeclaration depth
        (CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_endpoint_perms
          aligned
          (by simpa only [canonicalizeListByAt, leftEndpoint, leftFrame, key]
            using leftPermutation)
          (by simpa only [canonicalizeListByAt, rightEndpoint, rightFrame, key]
            using rightPermutation))
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (processPlan_commonFrame_parallelSingleton_absorbed leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan scopeDepth depth)
    (processPlan_commonFrame_parallelSingleton_absorbed rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan scopeDepth depth)
    wrapped

/-- Same-colour process-plan reconstruction with independent keying and
restoration depths. -/
noncomputable def
    processPlans_commonRestorationApex_at_independentDepths_of_sameColorCanonical
    {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftFrameSourceBound leftFrameTargetBound : List TypeExpr}
    {rightFrameSourceBound rightFrameTargetBound : List TypeExpr}
    (leftFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      leftFrameSourceBound leftFrameTargetBound)
    (rightFrameThinning : CostStaticBinderThinning rhoCIGSLT color
      rightFrameSourceBound rightFrameTargetBound)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftLeg : Fin leftEnvironment.atomCount → Fin cospan.commonKeys.length)
    (rightLeg : Fin rightEnvironment.atomCount → Fin cospan.commonKeys.length)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (targetDeclaration : ReflectivePresentationDecl)
    (targetDeclaration_eq : targetDeclaration =
      costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
    (scopeDepth keyDepth restorationDepth : Nat)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          leftRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            leftPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration keyDepth
            (cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
              (leftFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
          rightRaw ∈ parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rightPayload ∧
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            targetDeclaration keyDepth
            (cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
              (rightFrameThinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols rhoCIGSLT)
                  (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
        cospan targetDeclaration depth leftEndpoint rightEndpoint)
    (crossTies :
      let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
      let leftFrame := fun pattern =>
        cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
          (leftFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (leftEnvironment.reify pattern)))
      let rightFrame := fun pattern =>
        cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
          (rightFrameThinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (rightEnvironment.reify pattern)))
      ∀ {leftEndpoint rightEndpoint},
        leftEndpoint ∈ parallelContents targetDeclaration
          (canonicalizeListByAt key targetDeclaration keyDepth
            [leftFrame leftPlan.abstractPattern]) →
        rightEndpoint ∈ parallelContents targetDeclaration
          (canonicalizeListByAt key targetDeclaration keyDepth
            [rightFrame rightPlan.abstractPattern]) →
        key keyDepth leftEndpoint = key keyDepth rightEndpoint →
        ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
          cospan targetDeclaration depth leftEndpoint rightEndpoint) :
    let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
    let leftFrame := fun pattern =>
      cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
        (leftFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (leftEnvironment.reify pattern)))
    let rightFrame := fun pattern =>
      cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
        (rightFrameThinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (rightEnvironment.reify pattern)))
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      targetDeclaration restorationDepth
      (canonicalizeByAt key targetDeclaration keyDepth
        (leftFrame leftPlan.abstractPattern))
      (canonicalizeByAt key targetDeclaration keyDepth
        (rightFrame rightPlan.abstractPattern)) := by
  subst targetDeclaration
  dsimp only
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation.toReflectivePresentationDecl
  let key := cospan.commonSemanticPatternKeyAt rhoCIGSLT
  let leftFrame := fun pattern =>
    cospan.reifyWith leftEnvironment.lookupAtom? leftLeg
      (leftFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (leftEnvironment.reify pattern)))
  let rightFrame := fun pattern =>
    cospan.reifyWith rightEnvironment.lookupAtom? rightLeg
      (rightFrameThinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (rightEnvironment.reify pattern)))
  let leftEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration keyDepth (leftFrame pattern)
  let rightEndpoint := fun pattern =>
    canonicalizeByAt key targetDeclaration keyDepth (rightFrame pattern)
  have aligned :=
    parallelLeaves_abstractPattern_permutation_of_sameColor_canonical_eq
      leftPlan rightPlan leftAdmission rightAdmission canonical cospan
      targetDeclaration keyDepth leftEndpoint rightEndpoint (by
        intro leftRaw leftResult rightRaw rightResult leftWitness rightWitness
          rawCanonical
        exact close leftWitness rightWitness rawCanonical keyDepth)
  have leftPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan leftAdmission scopeDepth keyDepth
  have rightPermutation :=
    processPlan_commonReifiedMappedThickened_frontier_perm rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan rightAdmission scopeDepth
        keyDepth
  have frontierAlignment :=
    CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_endpoint_perms
      aligned
      (by simpa only [canonicalizeListByAt, leftEndpoint, leftFrame, key]
        using leftPermutation)
      (by simpa only [canonicalizeListByAt, rightEndpoint, rightFrame, key]
        using rightPermutation)
  have wrapped :=
    CostStaticAtomKeyCospan.CommonRestorationApex.parallel_at_keyDepth_of_key_perm_of_cross_ties
      cospan targetDeclaration keyDepth restorationDepth
        frontierAlignment.semanticKey_perm (by
          intro leftResult rightResult leftMembership rightMembership keyEq
          exact CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
            (crossTies leftMembership rightMembership keyEq))
  apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (processPlan_commonFrame_parallelSingleton_absorbed leftEnvironment
      leftFrameThinning cospan leftLeg leftPlan scopeDepth keyDepth)
    (processPlan_commonFrame_parallelSingleton_absorbed rightEnvironment
      rightFrameThinning cospan rightLeg rightPlan scopeDepth keyDepth)
    wrapped

end ParallelFrontier

/-- Reconstruct a reached same-colour process pair in the semantic cospan of
its enclosing static roots, with independent keying and restoration depths. -/
noncomputable def rho_reachedPlanPairCommonApex_of_sameColorCanonical
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
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftProcess : leftReached.sourceType = .base "Proc")
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (close :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
        leftRaw ∈ RhoCommonRestorationApex.parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPayload ∧
        ParallelFrontier.LeafWitness leftReached.sourceBound
          leftReached.targetBound leftReached.thinning
          leftReached.sourceAvailable leftReached.plan.abstractPattern
          leftReached.plan.boundaryTable.entries leftRaw leftAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
        rightRaw ∈ RhoCommonRestorationApex.parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPayload ∧
        ParallelFrontier.LeafWitness rightReached.sourceBound
          rightReached.targetBound rightReached.thinning
          rightReached.sourceAvailable rightReached.plan.abstractPattern
          rightReached.plan.boundaryTable.entries rightRaw rightAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl) rightRaw →
      ∀ depth, CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
        cospan
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        depth leftEndpoint rightEndpoint) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftNaturality :=
    ParallelFrontier.reached_parentCanonicalFrame_commonReify leftView.node
      leftEnvironment cospan cospan.leftSlot cospan.leftCommutes leftReached
        callbackAvailable callbackScope
  have rightNaturality :=
    ParallelFrontier.reached_parentCanonicalFrame_commonReify rightView.node
      rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
        rightReached callbackAvailable callbackScope
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨lsb, ltb, lth, lsa, lo, lst, lp, lsc, lae⟩ := leftReached
  obtain ⟨rsb, rtb, rth, rsa, ro, rst, rp, rsc, rae⟩ := rightReached
  cases sourceBoundEq
  cases targetBoundEq
  cases sourceAvailableEq
  cases thinningEq
  have rightProcess : rst = .base "Proc" := sourceTypeEq.symm.trans leftProcess
  subst leftProcess
  subst rightProcess
  have sameParentTargetBound : leftView.node.targetBound =
      rightView.node.targetBound :=
    leftView.targetBound_eq_targetBound rightView
  have apex :=
    ParallelFrontier.processPlans_commonRestorationApex_at_independentDepths_of_sameColorCanonical
      leftEnvironment rightEnvironment leftView.node.thinning
      rightView.node.thinning cospan cospan.leftSlot cospan.rightSlot lp rp
      leftAdmission rightAdmission canonical targetDeclaration rfl
      callbackScope callbackAvailable callbackRoot (by
        intro leftRaw leftEndpoint rightRaw rightEndpoint leftWitness
          rightWitness rawCanonical depth
        simpa only [leftEnvironment, rightEnvironment, cospan,
          targetDeclaration, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using
            (close (leftRaw := leftRaw) (leftEndpoint := leftEndpoint)
              (rightRaw := rightRaw) (rightEndpoint := rightEndpoint)
              leftWitness rightWitness rawCanonical depth))
      (by
        dsimp only
        intro leftEndpoint rightEndpoint leftMembership rightMembership keyEq
          depth
        exact rho_processPlan_frontier_crossTies leftView.node rightView.node
          leftView.children rightView.children leftInventory rightInventory
          sameParentTargetBound leftView.node.thinning
          rightView.node.thinning lp rp leftAdmission rightAdmission
          leftParentEmbedding rightParentEmbedding callbackScope
          callbackAvailable leftMembership rightMembership keyEq depth)
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftNaturality.symm rightNaturality.symm apex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
