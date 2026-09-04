import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticProcessBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- The opposite colour cannot read this colour's tagging of the interacting
sort.  Flipped instance of `rho_decodeCostStaticTypeExpr_flip_process_eq_none`. -/
theorem rho_decode_flipProcess_eq_none (color : CostStaticColor) :
    decodeCostStaticTypeExpr rhoCIGSLT color
        (.base
          (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).processSort) = none := by
  have flipped := rho_decodeCostStaticTypeExpr_flip_process_eq_none color.flip
  simpa [CostStaticColor.flip_flip] using flipped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- **The opposite colour's image of the interacting sort is never this
colour's image of anything.**  This is the whole content of the cross-colour
boundary gate: `Proc` is the one sort the two static fibres tag differently,
so a type written in one colour's namespace can never be read by the other as
the interacting sort. -/
theorem mapTypeExpr_flipProc_ne (color : CostStaticColor) (sourceType : TypeExpr) :
    mapTypeExpr (color.flip.symbols rhoCIGSLT) (.base "Proc") ≠
      mapTypeExpr (color.symbols rhoCIGSLT) sourceType := by
  intro equation
  have decoded := congrArg (decodeCostStaticTypeExpr rhoCIGSLT color) equation
  rw [decodeCostStaticTypeExpr_mapTypeExpr] at decoded
  rw [show mapTypeExpr (color.flip.symbols rhoCIGSLT) (TypeExpr.base "Proc") =
      .base (costStaticReflectivePresentationDecl rhoCIGSLT color.flip
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort from
      by cases color <;> rfl] at decoded
  rw [rho_decode_flipProcess_eq_none] at decoded
  simp at decoded

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- **rho declares one bare collection, at `Proc`.**  So an authored-rule
collection choice can only be offered at the interacting sort. -/
theorem rho_bareChoices_eq_nil_of_ne_proc (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern) {sort : String}
    (notProc : sort ≠ "Proc") :
    bareCostStaticCollectionTypingChoices rhoCIGSLT color targetFree targetBound
        collectionType elements (.base sort)
        rhoCIGSLT.theory.presentation.presentation.language.terms = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro rule membership
  have shape : WellSorted.bareCollectionElementType? rule collectionType
      (.base sort) = none := by
    revert membership
    simp only [show rhoCIGSLT.theory.presentation.presentation.language =
      rhoCalc from rfl, rhoCalc, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [WellSorted.bareCollectionElementType?, TypeExpr.name, TypeExpr.proc,
        TypeExpr.bag, TypeExpr.funType, TypeExpr.baseType,
        Ne.symm notProc]
  simp [shape]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Authored bare-collection choices are offered only at a base sort. -/
theorem rho_bareChoices_eq_nil_of_not_base (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern) {expected : TypeExpr}
    (notBase : ∀ sort, expected ≠ .base sort) :
    bareCostStaticCollectionTypingChoices rhoCIGSLT color targetFree targetBound
        collectionType elements expected
        rhoCIGSLT.theory.presentation.presentation.language.terms = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro rule _membership
  have shape : WellSorted.bareCollectionElementType? rule collectionType
      expected = none := by
    cases expected with
    | base sort => exact absurd rfl (notBase sort)
    | arrow _ _ => rfl
    | multiBinder _ => rfl
    | collection _ _ => rfl
  simp [shape]

/-- **The cross-colour boundary-collection gate is empty.**

A cell rejected by its own static colour and accepted by the opposite one, at
a type written in its own colour's namespace, does not exist.  The authored
route needs the interacting sort, which the opposite colour cannot read; the
direct route reads the same element type in both colours, so acceptance
there transfers back. -/
theorem rho_boundaryCollection_choices_absurd (color : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) (targetBound : List TypeExpr)
    (collectionType : CollType) (elements : List Pattern) (sourceType : TypeExpr)
    {oppositeChoice : CostCollectionTypingChoice}
    (oppositeSelected : oppositeChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT color.flip targetFree
        targetBound collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT) sourceType))
    (currentRejected :
      costStaticCollectionTypingChoices rhoCIGSLT color targetFree targetBound
        collectionType elements
        (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) = []) :
    False := by
  unfold costStaticCollectionTypingChoices at oppositeSelected currentRejected
  rw [decodeCostStaticTypeExpr_mapTypeExpr] at currentRejected
  cases flipDecoded : decodeCostStaticTypeExpr rhoCIGSLT color.flip
      (mapTypeExpr (color.symbols rhoCIGSLT) sourceType) with
  | none =>
      rw [flipDecoded] at oppositeSelected
      simp at oppositeSelected
  | some flipExpected =>
      rw [flipDecoded] at oppositeSelected
      have back := mapTypeExpr_decodeCostStaticTypeExpr rhoCIGSLT color.flip
        flipDecoded
      cases flipExpected with
      | base sort =>
          dsimp only at oppositeSelected
          by_cases procSort : sort = "Proc"
          · subst procSort
            exact mapTypeExpr_flipProc_ne color sourceType back
          · rw [rho_bareChoices_eq_nil_of_ne_proc color.flip targetFree
              targetBound collectionType elements procSort] at oppositeSelected
            simp at oppositeSelected
      | arrow domain codomain =>
          dsimp only at oppositeSelected
          rw [rho_bareChoices_eq_nil_of_not_base color.flip targetFree
            targetBound collectionType elements (by intro s; simp)]
            at oppositeSelected
          simp at oppositeSelected
      | multiBinder body =>
          dsimp only at oppositeSelected
          rw [rho_bareChoices_eq_nil_of_not_base color.flip targetFree
            targetBound collectionType elements (by intro s; simp)]
            at oppositeSelected
          simp at oppositeSelected
      | collection actual element =>
          dsimp only at oppositeSelected
          rw [rho_bareChoices_eq_nil_of_not_base color.flip targetFree
            targetBound collectionType elements (by intro s; simp)]
            at oppositeSelected
          cases sourceType with
          | base _ => simp [mapTypeExpr] at back
          | arrow _ _ => simp [mapTypeExpr] at back
          | multiBinder _ => simp [mapTypeExpr] at back
          | collection currentActual currentElement =>
              simp only [mapTypeExpr, TypeExpr.collection.injEq] at back
              obtain ⟨actualEq, elementEq⟩ := back
              subst actualEq
              rw [elementEq] at oppositeSelected
              dsimp only at currentRejected
              by_cases fires : actual = collectionType ∧
                  WellSorted.checkElementsHaveType rhoCIGSLT.costWholeLanguage
                    targetFree targetBound elements
                    (mapTypeExpr (color.symbols rhoCIGSLT) currentElement) = true
              · rw [if_pos (by simp [fires.1, fires.2])] at currentRejected
                simp at currentRejected
              · rw [if_neg (by simpa using fires)] at oppositeSelected
                simp at oppositeSelected

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- **rho never stops at a collection boundary.**  The foreign-boundary
collection plan is uninhabited, so every rho collection plan is a static
root. -/
theorem rho_collectionPlan_isStaticRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern} {rest : Option String}
    {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer
      (.collection collectionType elements rest) sourceType) :
    plan.isStaticRoot = true := by
  cases plan with
  | collection choice selected children => rfl
  | boundaryCollection currentRejected oppositeChoice oppositeSelected
      certified certifies =>
      exact absurd oppositeSelected (fun selected =>
        rho_boundaryCollection_choices_absurd _ _ _ _ _ _ selected
          currentRejected)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
