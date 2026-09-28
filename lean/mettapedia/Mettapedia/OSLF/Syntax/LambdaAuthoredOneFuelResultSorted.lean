import Mettapedia.OSLF.Syntax.CanonicalCompiledOneFuelAdmission
import Mettapedia.OSLF.Syntax.LambdaAuthoredTypingComparison

/-!
# The authored beta execution is a result-sorted firing tree

The actual four-rule executor selects beta at fuel one. Canonical
whole-language compilation and the authored typing judgment lift the
complete free firing to the result-sorted operational model. Erasure
returns the same selected tree and its decoded history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredOneFuelResultSorted

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.Binding.LambdaAuthoredAppCongExecutionComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredCanonicalFreeComparison
open Mettapedia.OSLF.Binding.LambdaAuthoredTypingComparison
open Mettapedia.OSLF.Binding.CanonicalCompiledOneFuelAdmission
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory rewriteAt)
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalCertification
open Mettapedia.OSLF.Binding.ResultSortedScopedFreeModel
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)

private abbrev termType : TypeExpr := .base "Term"

/-- The selected one-fuel beta event in the actual authored evaluator has a
complete result-sorted free firing above it. The same depth-indexed tree
decodes to the beta history, and erasing the new result-sort certificates
gives exactly its sort-context lift. -/
theorem beta_result_sorted_with_history {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    ∃ rawTree :
        (presentation RelationEnv.empty language).Derivation ()
          ⟨1, (contextTypes Γ).length,
            encodeTerm (appT (lamT body) argument),
            encodeTerm (inst body argument)⟩,
      ∃ sortedTree :
        (ResultSortedScopedOperationalPresentation.presentation
          RelationEnv.empty language FreeTypeContext.empty).Derivation ()
          ⟨1, contextTypes Γ, termType,
            encodeTerm (appT (lamT body) argument),
            encodeTerm (inst body argument)⟩,
        (toContextSortedFree RelationEnv.empty language
          FreeTypeContext.empty).toFun ()
            ⟨1, contextTypes Γ, termType,
              encodeTerm (appT (lamT body) argument),
              encodeTerm (inst body argument)⟩ sortedTree =
          Mettapedia.OSLF.Binding.SortIndexedScopedTreeLifting.liftTreeAt
            RelationEnv.empty language
            ⟨1, contextTypes Γ,
              encodeTerm (appT (lamT body) argument),
              encodeTerm (inst body argument)⟩ rawTree ∧
        Mettapedia.OSLF.Binding.ScopedOperationalHistory.decodeHistory?
          RelationEnv.empty language _ rawTree = some (.fire 0 []) := by
  have hlen : (contextTypes Γ).length = Γ.length := by
    simp [contextTypes]
  have executed :
      (.fire 0 [], encodeTerm (inst body argument)) ∈
        rewriteAt RelationEnv.empty language 1 (contextTypes Γ).length
          (encodeTerm (appT (lamT body) argument)) := by
    rw [hlen]
    rw [full_beta_one_step body argument]
    simp
  obtain ⟨rawTree, typedTree, _, history, erasure⟩ :=
    runtime_oneFuel_resultSorted RelationEnv.empty language
      FreeTypeContext.empty (contextTypes Γ) termType _
      (all_rules_compile (contextTypes Γ)) (.fire 0 []) executed
      (encodeTerm_hasType (appT (lamT body) argument))
      (encodeTerm_hasType (inst body argument))
  exact ⟨rawTree, typedTree, erasure, history⟩

#print axioms beta_result_sorted_with_history

end Mettapedia.OSLF.Binding.LambdaAuthoredOneFuelResultSorted
