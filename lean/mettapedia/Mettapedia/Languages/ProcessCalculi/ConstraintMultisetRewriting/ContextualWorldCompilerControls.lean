import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequencingControls

/-!
# The computed program retains a reusable source/native comparison

The first actual firing computes and publishes 7. The second uses that
binding and reads its schema twice. The state comparison is preserved
after that actual second firing. Replacing the exposed answer by 9 is
not an equivalent representation, even when the physical world is equal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualWorldComparison
open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries origin symbol)
open ContextualComputedJoinControls (world plan picked model source_model)
open ContextualClauseSequencingControls (afterFirst rowLocals nextPlan selection source_next_admitted)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance

local instance : DecidableEq world.Names := world.equality

theorem first_result_comparison
    (first : ContextualConditionalClauses.Compiled queries locals (before := world.native ∅) plan picked) :
    Equivalent afterFirst (generator origin) (nativeWorld _ first.firing.target) first.sourceFrame.assignment := by
  exact equivalent_of_frame _ _ _ _ first.sourceFrame.name first.sourceFrame.injective first.sourceFrame.preserves
    (ContextualClauseStateRefinement.physical_exact (before := world) (occupied := ∅) first).symm
    (ContextualClauseStateRefinement.information_exact (before := world) (occupied := ∅) first)
    (Assignment.compose_identity_right first.sourceFrame.assignment).symm
    (fun _ next candidate pattern occurrence _ =>
      ContextualClauseStateRefinement.all_row_observations (before := world) (occupied := ∅)
        first occurrence next candidate pattern)

theorem prepared_source_plan : preparedPlan captures (generator origin) nextPlan = nextPlan := by
  with_unfolding_all rfl

abbrev afterSecond := ContextualClauseSourceState.target captures rowLocals afterFirst nextPlan selection

theorem the_actual_second_firing_retains_the_state_comparison
    (first : ContextualConditionalClauses.Compiled queries locals (before := world.native ∅) plan picked) (fuel : Nat) :
    let _ : DecidableEq first.firing.update.Variables := first.firing.update.equality
    ∃ following : ContextualConditionalClauses.Compiled captures
        (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) first.firing.update.declaration)
        (before := first.firing.target) (preparedPlan captures first.sourceFrame.assignment nextPlan) selection,
      following.firing.fuel = fuel ∧
      Equivalent afterSecond (resultEnv captures rowLocals origin (generator origin))
        (nativeWorld _ following.firing.target)
        (compilerResultEnv (right := first.firing.target) (rightEnv := first.sourceFrame.assignment)
          captures nextPlan selection following) := by
  let _ := first.firing.update.equality
  dsimp only
  have source : ContextualClauseSourceState.Admitted captures rowLocals afterFirst
      (preparedPlan captures (generator origin) nextPlan) selection := by
    erw [prepared_source_plan]
    exact source_next_admitted
  obtain ⟨following, budget, after⟩ :=
    (first_result_comparison first).realize_step (right := first.firing.target) captures nextPlan selection source fuel
  erw [prepared_source_plan] at after
  exact ⟨following, budget, after⟩

def wrongEnvironment : Assignment origin origin
  | .inl false => generator origin (.inl false)
  | .inl true => symbol 9
  | .inr (.inl ⟨_, impossible⟩) => nomatch impossible
  | .inr (.inr impossible) => nomatch impossible

theorem a_wrong_returned_binding_is_not_a_world_comparison :
    ¬ Equivalent afterFirst (generator origin) afterFirst wrongEnvironment := by
  intro equivalent
  obtain ⟨extension, other, related⟩ := equivalent.forward Empty captures (model captures) (source_model captures)
  have fixed := congrFun related.bindings (.inl true)
  change symbol (decl := extension.declarations) 7 = symbol 9 at fixed
  have impossible : (7 : Nat) = 9 := DataOperator.symbol.inj
    (Sum.inl.inj (Sum.inl.inj (Term.op.inj fixed).1))
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerControls
