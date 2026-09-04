import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostTypedMixedColorApexCounterexample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

/-!
# Same-view foreign-shell ordering canary

This places the typed depth-sensitive parallel from the mixed-colour apex
counterexample below two base-colour static roots.  The wrapped Quote/Drop
shell occurs only on the left, so wrapped canonicalization identifies the
raw endpoints while base planning remains the common parent decomposition.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignSupportMismatchOrderCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostTypedMixedColorApexCounterexample

def nameType : TypeExpr := .base (costBaseSortName "Name")
def processType : TypeExpr := .base (costBaseSortName "Proc")
def available : List TypeExpr := [processType, processType, processType]

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

def foreignQuote : Pattern := typedApexForeignQuote

def selectedShell : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [foreignQuote]]

def leftPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [selectedShell]

def rightPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [foreignQuote]

private theorem rule_mem (index : Nat) (inBounds : index < 6) :
    rhoCalc.terms[index]'(by simp [rhoCalc]; omega) ∈ rhoCalc.terms :=
  List.getElem_mem _

private theorem leftTyped :
    HasType rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] leftPattern processType := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rule_mem 1 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseDropConstructor_params]
    exact .cons (by trivial) rfl typedApexSelectedQuoteDrop_typed .nil

private theorem rightTyped :
    HasType rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] rightPattern processType := by
  apply HasType.constructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[1])
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _
      (rule_mem 1 (by omega))
  · rw [usesBareCollection_costBaseConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costBaseDropConstructor_params]
    exact .cons (by trivial) rfl typedApexForeignQuote_typed .nil

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext available processType
        leftPattern := by
  have zero : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] processType leftPattern := by
    refine ⟨⟨leftTyped, rfl, rfl, leftTyped.isWellScopedAt⟩, ?_⟩
    intro reflected _membership
    simp [leftPattern, selectedShell, foreignQuote, typedApexForeignQuote,
      typedApexRaw, typedApexFirstAtom, typedApexSecondAtom,
      binderSafeAt, binderSafeListAt]
  simpa only [List.nil_append] using zero.extendOuter available

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext available processType
        rightPattern := by
  have zero : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] processType rightPattern := by
    refine ⟨⟨rightTyped, rfl, rfl, rightTyped.isWellScopedAt⟩, ?_⟩
    intro reflected _membership
    simp [rightPattern, foreignQuote, typedApexForeignQuote, typedApexRaw,
      typedApexFirstAtom, typedApexSecondAtom,
      binderSafeAt, binderSafeListAt]
  simpa only [List.nil_append] using zero.extendOuter available

theorem canonical_eq :
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern := by
  have inner := typedApexMixedColor_canonical_eq
  unfold leftPattern rightPattern
  rw [canonicalize_apply_of_ne_quote declaration (by decide),
    canonicalize_apply_of_ne_quote declaration (by decide)]
  exact congrArg (Pattern.apply (costBaseConstructorName "PDrop"))
    (congrArg List.singleton inner)

noncomputable def leftTree :
    CostRegionTree rhoCIGSLT typedApexCospan.commonTargetFreeContext available []
      leftPattern processType :=
  (CostRegionTree.build? available [] leftPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT typedApexCospan.commonTargetFreeContext available []
      rightPattern processType :=
  (CostRegionTree.build? available [] rightPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted)

private def baseDropDeclared : rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.base ⟨rhoCalc.terms[1], rule_mem 1 (by omega)⟩, True.intro⟩

private theorem baseDropRole :
    rhoCIGSLT.declaredCostConstructorRole baseDropDeclared = .static .base :=
  rfl

private theorem baseDropDecoded :
    rhoCIGSLT.decodeDeclaredCostConstructor (costBaseConstructorName "PDrop") =
      some baseDropDeclared := by
  simpa [baseDropDeclared, CIGSLT.renderDeclaredCostConstructor,
    CIGSLT.renderGeneratedCostConstructor, CostConstructor.render, rhoCalc]
    using rhoCIGSLT.decodeDeclaredCostConstructor_render baseDropDeclared

private def leftStaticShape : CostStaticRootShape rhoCIGSLT leftPattern
    processType := by
  apply CostStaticRootShape.application .base baseDropDeclared
  · exact baseDropDecoded
  · exact baseDropRole

private def rightStaticShape : CostStaticRootShape rhoCIGSLT rightPattern
    processType := by
  apply CostStaticRootShape.application .base baseDropDeclared
  · exact baseDropDecoded
  · exact baseDropRole

theorem leftTree_rootIsStatic : leftTree.rootIsStatic = true := by
  exact leftStaticShape.rootIsStatic leftTree

theorem rightTree_rootIsStatic : rightTree.rootIsStatic = true := by
  exact rightStaticShape.rootIsStatic rightTree

noncomputable def leftRootColor :
    CostRegionTree.StaticRootColor rhoCIGSLT
      typedApexCospan.commonTargetFreeContext leftTree .base :=
  Classical.choice (leftTree.nonempty_staticRootColor_of_static_application
    .base baseDropDeclared baseDropDecoded baseDropRole)

noncomputable def rightRootColor :
    CostRegionTree.StaticRootColor rhoCIGSLT
      typedApexCospan.commonTargetFreeContext rightTree .base :=
  Classical.choice (rightTree.nonempty_staticRootColor_of_static_application
    .base baseDropDeclared baseDropDecoded baseDropRole)

noncomputable def leftView : leftTree.StaticRootView .base :=
  leftRootColor.toView

noncomputable def rightView : rightTree.StaticRootView .base :=
  rightRootColor.toView

theorem left_targetDepth : leftView.node.targetBound.length = 3 := by
  simpa [available] using leftView.targetBound_length_eq

theorem right_targetDepth : rightView.node.targetBound.length = 3 := by
  simpa [available] using rightView.targetBound_length_eq

/-- Select one exact argument plan from a certified static application root. -/
theorem applicationArgument_reached
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer pattern sourceType)
    (rootStatic : plan.isStaticRoot = true)
    {wireName : String} {before : List Pattern} {middle : Pattern}
    {after : List Pattern}
    (shape : pattern = .apply wireName (before ++ middle :: after)) :
    ∃ reached : CostStaticPlanReached source color targetFree middle
        plan.abstractPattern,
      Nonempty (CostStaticPlanEntryEmbedding source color targetFree
        reached.plan.boundaryTable.entries plan.boundaryTable.entries) := by
  cases plan with
  | bvar | fvar | boundaryApplication | lambda | multiLambda |
      boundaryCollection =>
      simp [CostStaticRegionPlan.isStaticRoot] at rootStatic
  | collection choice selected children =>
      cases shape
  | application constructor rendered current preimage notBare children =>
      obtain ⟨_wireEq, argumentsEq⟩ := Pattern.apply.inj shape
      obtain ⟨active⟩ :=
        CostStaticArgumentPlan.nonempty_activeAt children argumentsEq
      let frame : OneHoleContext :=
        .apply preimage.sourceConstructor.1.label active.beforeAbstracts .hole
          active.afterAbstracts
      let reached : CostStaticPlanReached source color targetFree middle
          (.apply preimage.sourceConstructor.1.label
            children.abstractPatterns) :=
        { sourceBound := _
          targetBound := _
          thinning := _
          sourceAvailable := _
          outer := _
          sourceType := _
          plan := active.head
          skeletonContext := frame
          abstract_eq := by
            rw [active.abstracts_eq]
            rfl }
      exact ⟨reached, ⟨active.entryEmbedding⟩⟩

theorem left_selected_reached :
    ∃ reached : CostStaticPlanReached rhoCIGSLT .base
        typedApexCospan.commonTargetFreeContext selectedShell
        leftView.node.plan.abstractPattern,
      Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT .base
        typedApexCospan.commonTargetFreeContext
        reached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries) := by
  refine applicationArgument_reached leftView.node.plan
    leftView.node.rootStatic (wireName := costBaseConstructorName "PDrop")
      (before := []) (after := []) ?_
  simpa [leftPattern] using leftView.patternEq

theorem right_selected_reached :
    ∃ reached : CostStaticPlanReached rhoCIGSLT .base
        typedApexCospan.commonTargetFreeContext foreignQuote
        rightView.node.plan.abstractPattern,
      Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT .base
        typedApexCospan.commonTargetFreeContext
        reached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries) := by
  refine applicationArgument_reached rightView.node.plan
    rightView.node.rootStatic (wireName := costBaseConstructorName "PDrop")
      (before := []) (after := []) ?_
  simpa [rightPattern] using rightView.patternEq

end ForeignSupportMismatchOrderCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
