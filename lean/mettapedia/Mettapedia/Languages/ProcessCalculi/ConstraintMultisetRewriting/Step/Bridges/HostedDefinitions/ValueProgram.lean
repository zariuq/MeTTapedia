import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueProgramGuards

/-!
# The value stage inside the actual compiled program

Literal phase checks rule out the other fixed clauses, the substitution
helper, and generated native rows. Thus the full program can only take a
worker step or its actual finish rule while the worker invariant holds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open SourceLanguage.Elaboration
open RuleBuilder ValueContinuation
open NativeTypesOnTheStep.Computing

def finishRule : Rule := ContextRules.driver[3]

theorem finish_cases {call answer : MClosed} (answered : ProgramBinders.Answers finishRule call answer) :
    ∃ datum, call = resumeC datum finishContinuation ∧ answer = doneC datum := by
  change ProgramBinders.Answers
    (equation (n := 1)
      (ContextRules.active "hd-resume" [slot 0, node "hd-main-finish" []])
      (node doneTag [slot 0])) call answer at answered
  obtain ⟨environment, lhs, rhs⟩ := (RuleBuilder.answers_iff _ _ call answer).mp answered
  simp only [ContextRules.active, materialize_node, materialize_slot,
    List.map_cons, List.map_nil] at lhs rhs
  exact ⟨environment 0, lhs.symm, rhs.symm⟩

theorem of_member {rule : Rule} (member : rule ∈ rules) {call answer : MClosed}
    (answered : ProgramBinders.Answers rule call answer) : Step call answer := by
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  refine ⟨index, ?_⟩
  rw [selected]
  exact answered

theorem program_step_cases {dev : Definitions.Development} (built : Compiled dev)
    {original current next : MClosed} (invariant : Invariant original current)
    (step : ProgramBinders.Rewrites built.rules.get current next) :
    Step current next ∨ ∃ datum, current = resumeC datum finishContinuation ∧ next = doneC datum := by
  obtain ⟨index, answered⟩ := step
  let rule := built.rules.get index
  have member : rule ∈ built.rules := List.get_mem _ _
  have answers : ProgramBinders.Answers rule current next := answered
  change rule ∈ (ContextRules.fixed ++ RuntimeSubstitution.rules) ++ built.authored at member
  rcases List.mem_append.mp member with fixedOrHelper | authored
  · rcases List.mem_append.mp fixedOrHelper with fixed | helper
    · change rule ∈ (ContextRules.traversal ++ ContextRules.primitive) ++ ContextRules.driver at fixed
      rcases List.mem_append.mp fixed with traversalOrPrimitive | driver
      · rcases List.mem_append.mp traversalOrPrimitive with traversal | primitive
        · exact False.elim (avoiding_cannot_invariant
            (List.all_eq_true.mp traversal_avoids rule traversal) invariant answers)
        · exact False.elim (avoiding_cannot_invariant
            (List.all_eq_true.mp primitive_avoids rule primitive) invariant answers)
      · have partition := List.take_append_drop 3 ContextRules.driver
        rw [← partition] at driver
        rcases List.mem_append.mp driver with early | suffix
        · exact False.elim (avoiding_cannot_invariant
            (List.all_eq_true.mp driver_prefix_avoids rule early) invariant answers)
        · change rule ∈ finishRule :: rules at suffix
          rcases List.mem_cons.mp suffix with same | worker
          · exact .inr (finish_cases (same ▸ answers))
          · exact .inl (of_member worker answers)
    · exact False.elim (avoiding_cannot_invariant
        (List.all_eq_true.mp helpers_avoid rule helper) invariant answers)
  · exact False.elim (avoiding_cannot_invariant
      (root_avoids (RowPhases.authored_phase built authored)) invariant answers)

theorem program_step_preserves {dev : Definitions.Development} (built : Compiled dev)
    {original current next : MClosed} (invariant : Invariant original current)
    (step : ProgramBinders.Rewrites built.rules.get current next) :
    Invariant original next ∨ ∃ value : Presentation.Tower.Tm 0,
      DirectedAnswers.Value value ∧ original = encodeTm value ∧ next = doneC (encodeTm value) := by
  rcases program_step_cases built invariant step with worker | finished
  · exact .inl (step_preserves worker invariant)
  · obtain ⟨datum, sameCurrent, rfl⟩ := finished
    rcases invariant with checking | returning
    · obtain ⟨term, stack, same, _, _⟩ := checking
      exact False.elim (value_ne_resume _ _ _ _ (same.symm.trans sameCurrent))
    · obtain ⟨term, stack, isValue, same, _, restored⟩ := returning
      have compared := (resume_eq_iff _ _ _ _).mp (sameCurrent.symm.trans same)
      obtain ⟨sameDatum, sameStack⟩ := compared
      have stackBase := (base_iff stack).mp sameStack.symm
      subst stack
      exact .inr ⟨term, isValue, restored.symm, congrArg doneC sameDatum⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorker.program_step_preserves
