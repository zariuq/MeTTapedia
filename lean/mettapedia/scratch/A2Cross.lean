import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingRestoration

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

theorem CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available leftOuter rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {leftTree : CostRegionTree source targetFree available leftOuter
      leftPattern type}
    {rightTree : CostRegionTree source targetFree available rightOuter
      rightPattern type}
    {leftColor rightColor : CostStaticColor}
    (leftView : leftTree.StaticRootView leftColor)
    (rightView : rightTree.StaticRootView rightColor)
    (different : leftColor ≠ rightColor) :
    leftView.node.sourceSort.1 = rightView.node.sourceSort.1 ∧
      leftView.node.sourceSort.1 ≠
        source.theory.presentation.interactingSort.1.name := by
  have nameEq :
      (leftColor.symbols source).sort leftView.node.sourceSort.1 =
        (rightColor.symbols source).sort rightView.node.sourceSort.1 :=
    TypeExpr.base.inj (leftView.typeEq.trans rightView.typeEq.symm)
  cases leftColor <;> cases rightColor
  · exact absurd rfl different
  · simp only [CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols, costWrappedStaticSymbols] at nameEq
    split_ifs at nameEq with interacting
    · exact absurd nameEq (costBaseSortName_ne_wrapped _)
    · have sortEq := costBaseSortName_injective nameEq
      exact ⟨sortEq, by rw [sortEq]; exact interacting⟩
  · simp only [CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols, costWrappedStaticSymbols] at nameEq
    split_ifs at nameEq with interacting
    · exact absurd nameEq.symm (costBaseSortName_ne_wrapped _)
    · have sortEq := costBaseSortName_injective nameEq
      exact ⟨sortEq, interacting⟩
  · exact absurd rfl different

end Mettapedia.GSLT.LanguageDef
