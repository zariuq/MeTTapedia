import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PublicProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.GroundControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerProgress

/-!
# The actual seven-rule worker has a terminating source evaluator instance

Every dependency certificate is checked on the real worker equation. The
source program is the existing binder-core embedding, not a new evaluator.
An actual zero execution supplies the positive run. The uncovered-answer
counterexample demonstrates why the dependency licence is substantive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.SourceProgressControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

private theorem grounding_of_paths {slots : Nat} (lhs rhs : Template slots)
    (paths : Fin slots → List Nat)
    (checked : ∀ index, LiteralPaths.part lhs (paths index) = some (slot index)) :
    GroundRead.Grounding (equation lhs rhs) := by
  intro X target assignment environment matched
  change instantiate assignment lhs = instantiate (GroundRead.valuesAt target environment) lhs at matched
  change instantiate assignment rhs = instantiate (GroundRead.valuesAt target environment) rhs
  apply instantiate_congr assignment (GroundRead.valuesAt target environment) rhs
  intro index _
  exact GroundRead.recover_in_target lhs index (paths index) (checked index) assignment environment
    (matched.trans (GroundRead.include_materialize_at target environment lhs).symm)

theorem actual_worker_grounding : ∀ rule ∈ ValueWorker.rules, GroundRead.Grounding rule := by
  intro rule member
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  rw [← selected]
  fin_cases index
  · exact grounding_of_paths _ _ ![[1, 2]] (by intro index; fin_cases index; rfl)
  · exact grounding_of_paths _ _ ![[1, 2]] (by intro index; fin_cases index; rfl)
  · exact grounding_of_paths _ _ ![[1, 1, 2], [1, 2]] (by intro index; fin_cases index <;> rfl)
  · exact grounding_of_paths _ _ ![[1, 1], [1, 2, 1]] (by intro index; fin_cases index <;> rfl)
  · exact grounding_of_paths _ _ ![[1, 1, 1], [1, 1, 2], [1, 2]] (by intro index; fin_cases index <;> rfl)
  · exact grounding_of_paths _ _ ![[1, 1], [1, 2, 1], [1, 2, 2]] (by intro index; fin_cases index <;> rfl)
  · exact grounding_of_paths _ _ ![[1, 1], [1, 2, 1], [1, 2, 2]] (by intro index; fin_cases index <;> rfl)

theorem actual_source_worker_normalizes (datum : MClosed) (D : Discipline MSig [] ())
    (supply : Nat → MClosed) :
    Acc (fun after before => SourceLanguage.Step D (BinderCore.program ValueWorker.rules) supply before after)
      (BinderCore.start ValueWorker.rules (valueC datum finishContinuation)) :=
  ConfigProgress.initial_normalizes ValueWorker.rules D supply actual_worker_grounding _
    (ValueWorkerRank.initialized_normalizes datum)

theorem actual_zero_source_run (D : Discipline MSig [] ()) (supply : Nat → MClosed) :
    ∃ configuration, Runs D (BinderCore.program ValueWorker.rules) supply
      (BinderCore.start ValueWorker.rules (valueC ValueWorker.zero finishContinuation)) configuration ∧
      ∃ branch ∈ configuration.branches,
        BinderCore.Shows ValueWorker.rules branch (resumeC ValueWorker.zero finishContinuation) := by
  have edge := RuleInstances.template (rows := ValueWorker.rules)
    (ContextRules.active (n := 1) "hd-value" [literal ValueWorker.zero, slot 0])
    (ContextRules.active "hd-resume" [literal ValueWorker.zero, slot 0])
    (List.get_mem ValueWorker.rules ⟨0, by decide⟩) ![finishContinuation]
  have rewritten : ProgramBinders.Rewrites ValueWorker.rules.get
      (valueC ValueWorker.zero finishContinuation) (resumeC ValueWorker.zero finishContinuation) := by
    simpa [ContextRules.active, valueC, resumeC, activeC] using edge
  exact (BinderCore.execution_iff ValueWorker.rules D supply _ _).mp (.single rewritten)

theorem ambient_uncovered_answers_are_not_grounded :
    ¬ GroundRead.Grounding RuntimeSubstitution.uncovered := GroundControls.uncovered_not_grounding

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.SourceProgressControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.SourceProgressControls.actual_source_worker_normalizes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.SourceProgressControls.actual_zero_source_run
