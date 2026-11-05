import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement

/-!
# Actual clause compiler results realize the world observation comparison

An injective capture frame provides model coverage in both directions.
All conditional observations and the exposed environment travel through
that same frame. The concrete instance uses the independently constructed
source update and the actual compiler target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows ContextualPrefixModels

variable {S : Signature} {Public Left Right O : Type} {Γ : Ctx S} {sort : S.Srt}
    {exposed : Public → MetaArity S} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}

theorem equivalent_of_frame
    (left : ContextualClauseSourceState.World lefts O Γ sort) (leftEnv : Assignment exposed left.declarations)
    (right : ContextualClauseSourceState.World rights O Γ sort) (rightEnv : Assignment exposed right.declarations)
    (name : left.Names → right.Names) (injective : Function.Injective name)
    (preserves : ∀ identity, right.declarations (name identity) = left.declarations identity)
    (physical : left.present = right.present)
    (information : right.equations = ContextualResidual.mapProblem (reindex name preserves) left.equations)
    (bindings : rightEnv = Assignment.compose (reindex name preserves) leftEnv)
    (observations : ∀ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment right.declarations future) (pattern : Term (signature S future) Γ sort)
      (occurrence : O) (_present : occurrence ∈ left.present),
      Matches lefts left.declarations (Assignment.compose candidate (reindex name preserves)) pattern (left.rows occurrence) ↔
        Matches rights right.declarations candidate pattern (right.rows occurrence)) :
    Equivalent left leftEnv right rightEnv := by
  let frame : Extension left.declarations := ⟨right.Names, right.declarations, name, injective, preserves⟩
  have related : ∀ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment right.declarations future), ContextualResidual.Models candidate right.equations →
      Related left leftEnv right rightEnv (Assignment.compose candidate frame.assignment) candidate := by
    intro Future future candidate model
    refine ⟨?_, model, ?_, ?_⟩
    · rw [information, ContextualResidual.models_mapProblem] at model
      exact model
    · rw [bindings, Assignment.compose_associative]
      rfl
    · intro later pattern occurrence member
      have observed := observations _ _ (Assignment.compose later.assignment candidate) pattern occurrence member
      erw [← Assignment.compose_associative] at observed
      exact observed
  refine ⟨physical, ?_, ?_⟩
  · intro Future future candidate model
    have lifted : ContextualResidual.Models (frame.liftModel candidate) right.equations := by
      rw [information]
      exact (ContextualConditionalNaturality.models_liftModel_iff frame candidate left.equations).mpr model
    have pair := related _ _ (frame.liftModel candidate) lifted
    rw [frame.liftModel_square] at pair
    exact ⟨Extension.withLocals frame.complementDeclarations future, frame.liftModel candidate, pair⟩
  · intro Future future candidate model
    refine ⟨Extension.identity future, Assignment.compose candidate frame.assignment, ?_⟩
    have unit : (Extension.identity future).assignment = generator future := rfl
    erw [unit, Assignment.compose_identity_left]
    exact related Future future candidate model

def nativeWorld (locals : Left → MetaArity S) (state : ContextualConditionalExecution.State locals O Γ sort) :
    ContextualClauseSourceState.World locals O Γ sort :=
  ⟨state.Names, state.equality, state.declarations, state.equations, state.present, state.rows⟩

variable {Local Query : Type} {locals : Local → MetaArity S} {queries : Query → MetaArity S}
    [DecidableEq Local] [DecidableEq Query] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {before : ContextualClauseSourceState.World locals O Γ sort} {occupied : Finset Nat}
    {plan : ContextualPublication.Plan
      (Term (signature S (ContextualConjunctiveQueries.queryFamily queries before.declarations)) Γ sort)}
    {picked : Selection O}

theorem actual_compiler_result
    (compiled : ContextualConditionalClauses.Compiled queries locals (before := before.native occupied) plan picked) :
    Equivalent (ContextualClauseSourceState.target queries locals before plan picked)
      (ContextualClauseSourceState.continuationEnv queries locals before)
      (nativeWorld _ compiled.firing.target) compiled.continuationEnv := by
  exact equivalent_of_frame _ _ _ _ compiled.sourceFrame.name compiled.sourceFrame.injective
    compiled.sourceFrame.preserves (ContextualClauseStateRefinement.physical_exact compiled).symm
    (ContextualClauseStateRefinement.information_exact compiled) rfl
    (fun _ next candidate pattern occurrence _ =>
      ContextualClauseStateRefinement.all_row_observations compiled occurrence next candidate pattern)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
