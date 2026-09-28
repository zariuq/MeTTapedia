import Mettapedia.GSLT.Examples.MixedPremiseSortedTree
import Mettapedia.OSLF.Syntax.ResultSortedScopedAdmission

/-!
# All-node typing for the authored mixed firing

The selected relation-query and scoped-step execution has a complete
result-sorted firing tree with its exact history. Erasing the result-sort
annotations yields a raw scoped tree for which every recursive occurrence,
not just the root, has an authored common endpoint sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.MixedPremiseAllNodesAdmission

open Mettapedia.GSLT.Examples.TypedMixedPremiseHistory
open Mettapedia.GSLT.Examples.TypedPartialSpinePremise (wrapped expected)
open Mettapedia.GSLT.Examples.MixedPremiseSortedClassifier
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation
open Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel
open Mettapedia.OSLF.Binding.ResultSortedScopedHistory
open Mettapedia.OSLF.Binding.ResultSortedScopedAdmission

private def term : TypeExpr := .base "Term"

/-- The exact authored execution produces a complete sorted tree whose
erasure has endpoint typing at every recursive premise occurrence. -/
theorem mixed_execution_all_nodes_typed
    (history : RuleHistory)
    (selected : (history, expected) ∈
      rewriteAt RelationEnv.empty recursiveLanguage 2 0 wrapped)
    (observedIndex : historyRuleIndex history = 1) :
    ∃ tree :
      (Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation.presentation
        RelationEnv.empty recursiveLanguage FreeTypeContext.empty).Derivation
          () ⟨2, [], term, wrapped, expected⟩,
      decodeSorted? RelationEnv.empty recursiveLanguage
        FreeTypeContext.empty ⟨2, [], term, wrapped, expected⟩ tree =
          some history ∧
      AllNodesAdmitted
        (Mettapedia.OSLF.Binding.SortIndexedScopedFreeModel.authoredRules
          RelationEnv.empty recursiveLanguage)
        (fun _ child => SomeEndpointsHaveType recursiveLanguage
          FreeTypeContext.empty child)
        () ⟨2, [], wrapped, expected⟩
        ((toContextSortedFree RelationEnv.empty recursiveLanguage
          FreeTypeContext.empty).toFun ()
            ⟨2, [], term, wrapped, expected⟩ tree) := by
  obtain ⟨tree, exactHistory⟩ :=
    mixed_sorted_tree_decodes_execution history selected observedIndex
  exact ⟨tree, exactHistory,
    eraseTree_allNodesHaveType RelationEnv.empty recursiveLanguage
      FreeTypeContext.empty ⟨2, [], term, wrapped, expected⟩ tree⟩

#print axioms mixed_execution_all_nodes_typed

end Mettapedia.GSLT.Examples.MixedPremiseAllNodesAdmission
