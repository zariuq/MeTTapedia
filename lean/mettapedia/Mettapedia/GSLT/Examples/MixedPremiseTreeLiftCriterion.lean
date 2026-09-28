import Mettapedia.GSLT.Examples.MixedPremiseSortedTree
import Mettapedia.OSLF.Syntax.ResultSortedScopedTreeLiftCriterion

/-!
# A selected mixed authored firing satisfies the local tree-lift criterion

The root relation query supplies an event but no recursive branch. Its
binder-local step supplies one child, whose result sort differs from what a
root-only typing argument can assume. This theorem applies the general
cartesian tree criterion to an actual selected execution and retains its
complete decoded history.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.MixedPremiseTreeLiftCriterion

open Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
open Mettapedia.GSLT.Examples.TypedPartialSpinePremise (wrapped expected)
open Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion
open Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedHistory
open Mettapedia.OSLF.Binding.ResultSortedScopedTreeLiftCriterion
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation

private def term : TypeExpr := .base "Term"

private def root :
    Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.Judgment :=
  ⟨2, [], term, wrapped, expected⟩

/-- Every selected mixed execution with the authored mixed-rule label has
an exact raw firing tree whose local result-sort admission is established.
The selected child and its parent history remain in their source order. -/
theorem selected_mixed_firing_has_local_certificate
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ raw :
      (Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage).Derivation () root.eraseResult,
      LocallyResultSorted RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty root raw ∧
      Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty recursiveLanguage root.eraseResult.depth
          ((depthPolynomialMap RelationEnv.empty recursiveLanguage).mapFix
            () root.eraseResult raw) = some history := by
  obtain ⟨sorted, decoded⟩ :=
    mixed_sorted_tree_decodes_execution history selected observedIndex
  let raw := (erasePolynomialMap RelationEnv.empty recursiveLanguage
      FreeTypeContext.empty).mapFix () root sorted
  refine ⟨raw, ?_, ?_⟩
  · exact mapFix_liftable
      (erasePolynomialMap RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty) () root sorted
  · rw [decodeSorted_eq_mapFix] at decoded
    rw [show eraseToDepthMap RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty =
          Hom.comp
            (erasePolynomialMap RelationEnv.empty recursiveLanguage
              FreeTypeContext.empty)
            (depthPolynomialMap RelationEnv.empty recursiveLanguage)
          from rfl, Hom.mapFix_comp] at decoded
    exact decoded

#print axioms selected_mixed_firing_has_local_certificate

end Mettapedia.GSLT.Examples.MixedPremiseTreeLiftCriterion
