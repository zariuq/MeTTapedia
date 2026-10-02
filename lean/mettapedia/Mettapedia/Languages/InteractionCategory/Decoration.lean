import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecoration
import Mettapedia.Languages.InteractionCategory.Interaction

/-!
# Visible interface composition preserves continuation decoration

The contractum rebuilds an action prefix around the composed continuations.
An independent constructor closure can include that prefix: its wrapped
copy preserves the label surfaces and consumes a wrapped continuation.
Excluding the prefix from the closure gives a different, strictly narrower
sorting problem. Neither result asserts the stronger Cost activation laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.InteractionCategory

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The actual finite authored signature supplies the constructor closure.
Both primary continuation slots are already part of the cut. -/
def visibleDecoration : ContinuationDecorationProfile (cut .visible) where
  constructorClosure := (interactionCategory .visible).terms.attach

/-- The same slots with the old non-principal closure exclude rebuilding Act. -/
def visibleNonPrincipalDecoration : ContinuationDecorationProfile (cut .visible) where
  constructorClosure := continuationConstructors (cut .visible)

theorem visibleDecoration_comp_parameters :
    (visibleDecoration.baseConstructor terms[4]).params =
      [.simple "first" (.base (costBaseSortName "Proc")),
        .simple "second" (.base (costBaseSortName "Proc"))] := by
  decide +kernel

theorem visibleDecoration_act_parameters :
    (visibleDecoration.baseConstructor terms[3]).params =
      [.simple "left" (.base (costBaseSortName "Label")),
        .simple "right" (.base (costBaseSortName "Label")),
        .simple "next" (.base costWrappedSortName)] := by
  decide +kernel

/-- The two introductions still accept decorated continuation slots while
their interacting outputs are in the base fibre. -/
theorem visibleDecoration_redexRetypable : visibleDecoration.RedexRetypable := by
  unfold ContinuationDecorationProfile.RedexRetypable
  change HasType visibleDecoration.generatedLanguage visibleDecoration.generatedFreeContext []
    (.apply (costBaseConstructorName "Comp")
      [.apply (costBaseConstructorName "Act") [.fvar "a", .fvar "b", .fvar "p"],
        .apply (costBaseConstructorName "Act") [.fvar "b", .fvar "c", .fvar "q"]])
    (.base (costBaseSortName "Proc"))
  have actTyped : ∀ left right next : String,
      visibleDecoration.generatedFreeContext left = some (.base (costBaseSortName "Label")) →
      visibleDecoration.generatedFreeContext right = some (.base (costBaseSortName "Label")) →
      visibleDecoration.generatedFreeContext next = some (.base costWrappedSortName) →
      HasType visibleDecoration.generatedLanguage visibleDecoration.generatedFreeContext []
        (.apply (costBaseConstructorName "Act") [.fvar left, .fvar right, .fvar next])
        (.base (costBaseSortName "Proc")) := by
    intro left right next leftType rightType nextType
    apply HasType.constructor (rule := visibleDecoration.baseConstructor terms[3])
    · exact visibleDecoration.baseConstructor_mem _ (List.getElem_mem (by decide))
    · simp [UsesBareCollection, visibleDecoration_act_parameters]
    · rw [visibleDecoration_act_parameters]
      exact .cons trivial rfl (HasType.fvar leftType)
        (.cons trivial rfl (HasType.fvar rightType)
          (.cons trivial rfl (HasType.fvar nextType) .nil))
  apply HasType.constructor (rule := visibleDecoration.baseConstructor terms[4])
  · exact visibleDecoration.baseConstructor_mem _ (List.getElem_mem (by decide))
  · simp [UsesBareCollection, visibleDecoration_comp_parameters]
  · rw [visibleDecoration_comp_parameters]
    exact .cons trivial rfl (actTyped "a" "b" "p" rfl rfl rfl)
      (.cons trivial rfl (actTyped "b" "c" "q" rfl rfl rfl) .nil)

theorem visibleDecoration_contractum :
    visibleDecoration.mapContractum (composeRule .visible).right =
      .apply (costWrappedConstructorName "Act")
        [.fvar "a", .fvar "c", .apply (costWrappedConstructorName "Comp")
          [.fvar "p", .fvar "q"]] := by
  have actIncluded : "Act" ∈ visibleDecoration.wrappedLabels := by decide +kernel
  have compIncluded : "Comp" ∈ visibleDecoration.wrappedLabels := by decide +kernel
  simp only [composeRule, composite, act, comp, ContinuationDecorationProfile.mapContractum,
    mapPattern, mapPatternList_eq_map, ContinuationDecorationProfile.contractumSymbols,
    actIncluded, compIncluded, if_true, List.map_cons, List.map_nil]

/-- Rebuilding an introduction around untouched decorated continuations is
well sorted once that constructor belongs to the independent closure. -/
theorem visibleDecoration_wrappable : visibleDecoration.Wrappable := by
  unfold ContinuationDecorationProfile.Wrappable
  change HasType visibleDecoration.generatedLanguage visibleDecoration.generatedFreeContext []
    (visibleDecoration.mapContractum (composeRule .visible).right) (.base costWrappedSortName)
  rw [visibleDecoration_contractum]
  have composed : HasType visibleDecoration.generatedLanguage
      visibleDecoration.generatedFreeContext []
      (.apply (costWrappedConstructorName "Comp") [.fvar "p", .fvar "q"])
      (.base costWrappedSortName) := by
    apply HasType.constructor
      (rule := costWrappedConstructor (theory := theory .visible) terms[4])
    · exact visibleDecoration.wrappedConstructor_mem (presentation .visible).contactConstructor
        (List.mem_attach _ _)
    · simp [UsesBareCollection, costWrappedConstructor, terms, mapParameterType,
        costWrappedTypeExpr]
    · change ArgumentsHaveTypes _ _ [] [.fvar "p", .fvar "q"]
        [.simple "first" (.base costWrappedSortName),
          .simple "second" (.base costWrappedSortName)]
      exact .cons trivial rfl (HasType.fvar rfl)
        (.cons trivial rfl (HasType.fvar rfl) .nil)
  apply HasType.constructor
    (rule := costWrappedConstructor (theory := theory .visible) terms[3])
  · exact visibleDecoration.wrappedConstructor_mem (actConstructor .visible)
      (List.mem_attach _ _)
  · simp [UsesBareCollection, costWrappedConstructor, terms, mapParameterType,
      costWrappedTypeExpr]
  · change ArgumentsHaveTypes _ _ []
      [.fvar "a", .fvar "c", .apply (costWrappedConstructorName "Comp") [.fvar "p", .fvar "q"]]
      [.simple "left" (.base (costBaseSortName "Label")),
        .simple "right" (.base (costBaseSortName "Label")),
        .simple "next" (.base costWrappedSortName)]
    exact .cons trivial rfl (HasType.fvar rfl)
      (.cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl composed .nil))

/-- Keeping the old closure leaves the rebuilt action in the base fibre,
so it still fails the wrapped-result obligation. -/
theorem visibleNonPrincipalDecoration_not_wrappable :
    ¬ visibleNonPrincipalDecoration.Wrappable := by
  have excluded : "Act" ∉ visibleNonPrincipalDecoration.wrappedLabels := by decide +kernel
  have included : "Comp" ∈ visibleNonPrincipalDecoration.wrappedLabels := by decide +kernel
  have contractum : visibleNonPrincipalDecoration.mapContractum (composeRule .visible).right =
      .apply (costBaseConstructorName "Act")
        [.fvar "a", .fvar "c", .apply (costWrappedConstructorName "Comp")
          [.fvar "p", .fvar "q"]] := by
    simp only [composeRule, composite, act, comp, ContinuationDecorationProfile.mapContractum,
      mapPattern, mapPatternList_eq_map, ContinuationDecorationProfile.contractumSymbols,
      excluded, included, if_true, if_false, List.map_cons, List.map_nil]
  intro typed
  unfold ContinuationDecorationProfile.Wrappable at typed
  change HasType _ _ []
    (visibleNonPrincipalDecoration.mapContractum (composeRule .visible).right)
    (.base costWrappedSortName) at typed
  rw [contractum] at typed
  exact visibleNonPrincipalDecoration.baseHead_not_wrapped "Act" _ typed

theorem decoration_separates_constructor_closure :
    visibleDecoration.RedexRetypable ∧ visibleDecoration.Wrappable ∧
      ¬ visibleNonPrincipalDecoration.Wrappable :=
  ⟨visibleDecoration_redexRetypable, visibleDecoration_wrappable,
    visibleNonPrincipalDecoration_not_wrappable⟩

end Mettapedia.Languages.InteractionCategory
