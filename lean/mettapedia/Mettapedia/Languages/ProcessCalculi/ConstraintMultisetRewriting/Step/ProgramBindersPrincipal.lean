import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStep

/-!
# Principal answers of the binder-bearing equation core on the step

A store is in the pattern fragment when every retained equation and the current call are Miller
patterns (`PatternState`). The initial state of a call is, and a firing of an equation whose two
sides are Miller patterns keeps it so.

`principal_firing`: at such a state, the actual worklist run on the whole firing problem of an
admitted Miller-pattern equation completes (through `solves_principally_of_model`). Its answer is
principal: the readings of the firing's result are exactly the instances of the made right-hand side
under that answer.

`principal_answers_on_step`: at a call that every solution reads the same way, the answers of the
equation's branch are exactly those instances.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern ProblemPattern generator_pattern instantiate_preserves map_patterns)

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type} {program : ι → Equation S Γ sort}

/-- The firing problem of equation `index` at `state`: the retained store and `lhs ≐ call`. -/
abbrev firingProblem (state : State program) (index : ι) :=
  ContextualResidual.observeProblem
    (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
      (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration)

/-- Every retained equation and the current call are Miller patterns. -/
def PatternState (state : State program) : Prop :=
  ProblemPattern (ContextualResidual.observeProblem state.1.inventory.configuration.equations) ∧
    ∃ value, Holds program state value ∧ Pattern S state.1.declarations value

theorem problem_pattern_append {V : Type} {source : V → MetaArity S} (first second : ContextualResidual.Problem source)
    (left : ProblemPattern first) (right : ProblemPattern second) : ProblemPattern (first ++ second) := by
  intro equation member
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact left equation inFirst
  · exact right equation inSecond

theorem firing_problem_pattern (state : State program) (index : ι) (patterned : PatternState state)
    (lhsPattern : Pattern S (program index).arity (program index).lhs) :
    ProblemPattern (firingProblem state index) := by
  obtain ⟨storePattern, value, holds, valuePattern⟩ := patterned
  unfold firingProblem
  rw [actual_problem program state index value holds.2, ContextualResidual.observeProblem, List.map_append]
  apply problem_pattern_append
  · rw [← ContextualResidual.observeProblem, ContextualResidual.observeProblem_mapProblem]
    exact map_patterns _ (fun _ => generator_pattern _) _ storePattern
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    exact ⟨instantiate_preserves _ (fun _ => generator_pattern _) _ lhsPattern,
      instantiate_preserves _ (fun _ => generator_pattern _) _ valuePattern⟩

theorem initial_pattern (call : Term S Γ sort) : PatternState (initial (program := program) call) := by
  refine ⟨?_, _, initial_holds call, ContextualPatternFragment.rigid_inclusion_pattern _ call⟩
  intro equation member
  cases member

variable [DecidableEq ι]

theorem destination_pattern (state : State program) (index : ι) (valid : Admitted program state index)
    (patterned : PatternState state) (lhsPattern : Pattern S (program index).arity (program index).lhs)
    (rhsPattern : Pattern S (program index).arity (program index).rhs) :
    PatternState (destination program state index valid) := by
  refine ⟨firing_problem_pattern state index patterned lhsPattern, ?_⟩
  obtain ⟨_, value, holds, _⟩ := patterned
  exact ⟨_, destination_holds state index valid holds.1,
    instantiate_preserves _ (fun _ => generator_pattern _) _ rhsPattern⟩

/-- Runs of a program whose equations are Miller patterns on both sides stay in the fragment. -/
theorem reachable_pattern
    (patterns : ∀ index, Pattern S (program index).arity (program index).lhs ∧
      Pattern S (program index).arity (program index).rhs)
    {call : Term S Γ sort} {state : State program}
    (path : Relation.ReflTransGen (Transition program) (initial call) state) : PatternState state := by
  induction path with
  | refl => exact initial_pattern call
  | tail _ transition ih =>
      obtain ⟨index, valid, rfl⟩ := transition
      exact destination_pattern _ index valid ih (patterns index).1 (patterns index).2

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **Principal answers on the step.** For a Miller-pattern equation at a state in the fragment,
the actual worklist completes on the whole firing problem, and the result of the firing reads
exactly as the instances of the made right-hand side under the computed answer. -/
theorem principal_firing (state : State program) (index : ι) (valid : Admitted program state index)
    (patterned : PatternState state) (lhsPattern : Pattern S (program index).arity (program index).lhs) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem state index)),
      (letI := (destination program state index valid).1.equality;
        ContextualFrameWorklist.run fuel (active program state.1.declarations) (firingProblem state index)) =
          .residual update ∧
        update.remaining = [] ∧
        ∀ answer, Reads program (destination program state index valid) answer ↔
          ∃ (Future : Type) (future : Future → MetaArity S) (factor : Assignment update.declaration future),
            instantiate factor (instantiate update.answer
              (output program state.1.declarations index state.1.occupied state.2)) =
                Rigid.includeTerm future answer := by
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Local program) ⊕ state.1.Names) :=
    (destination program state index valid).1.equality
  obtain ⟨Later, later, candidate, solved⟩ := valid.solvable
  obtain ⟨fuel, update, computed, empty, answerSolves, factors⟩ :=
    ContextualPatternCompleteness.solves_principally_of_model later (firingProblem state index)
      (firing_problem_pattern state index patterned lhsPattern) candidate
      ((ContextualResidual.models_observeProblem _ _).mpr solved)
  obtain ⟨_, value, holds, _⟩ := patterned
  refine ⟨fuel, update, computed, empty, fun answer => ⟨?_, ?_⟩⟩
  · rintro ⟨Future, future, solution, made, ⟨_, madeShared⟩, solutionSolves, observed⟩
    have same : made = output program state.1.declarations index state.1.occupied state.2 :=
      ContextualStoredRows.Row.shared.inj (madeShared.symm.trans (destination_holds state index valid holds.1).2)
    subst same
    obtain ⟨factor, components⟩ := factors future solution
      ((ContextualResidual.models_observeProblem _ _).mpr solutionSolves)
    exact ⟨Future, future, factor,
      (ContextualFrameUnifier.factor_terms _ _ factor components _).symm.trans observed⟩
  · rintro ⟨Future, future, factor, read⟩
    refine ⟨Future, future, Assignment.compose factor update.answer, _,
      destination_holds state index valid holds.1, ?_, ?_⟩
    · exact (ContextualResidual.models_observeProblem _ _).mp
        (ContextualResidual.models_compose answerSolves factor)
    · rw [Assignment.instantiate_compose]
      exact read

/-- At a call that every solution reads the same way, the answers of a Miller-pattern equation are
exactly the instances of the principal answer computed on the step. -/
theorem principal_answers_on_step [ClosedTerms S] (state : State program) (call : Term S Γ sort)
    (determined : Determines program state call) (index : ι) (valid : Admitted program state index)
    (patterned : PatternState state) (lhsPattern : Pattern S (program index).arity (program index).lhs) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem state index)),
      (letI := (destination program state index valid).1.equality;
        ContextualFrameWorklist.run fuel (active program state.1.declarations) (firingProblem state index)) =
          .residual update ∧
        update.remaining = [] ∧
        ∀ answer, Answers (program index) call answer ↔
          ∃ (Future : Type) (future : Future → MetaArity S) (factor : Assignment update.declaration future),
            instantiate factor (instantiate update.answer
              (output program state.1.declarations index state.1.occupied state.2)) =
                Rigid.includeTerm future answer := by
  obtain ⟨fuel, update, computed, empty, readings⟩ := principal_firing state index valid patterned lhsPattern
  exact ⟨fuel, update, computed, empty, fun answer =>
    (reads_iff state call determined index valid answer).symm.trans (readings answer)⟩

#print axioms firing_problem_pattern
#print axioms initial_pattern
#print axioms reachable_pattern
#print axioms principal_firing
#print axioms principal_answers_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
