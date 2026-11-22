import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls

/-!
# Empty-body completion and the read-gate repetition counterexample

A read gate permits arbitrarily many resource executions without changing
the store. The actual compiled empty body instead consumes its invocation
control, changes its private state and cannot be admitted again without
another control production. Its decoded public result still agrees with
the empty source body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeInvocationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission ContextualSourceSchedules
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace ReadGate

def label (_ : Option Nat) : Unit := ()
def gate : Commit (Option Nat) Unit := ⟨∅, {none}, ∅, []⟩

theorem enabled : Enabled label {none} gate := by decide +kernel
theorem unchanged : fire {none} gate = {none} := by decide +kernel

/-- Keeping a request does not by itself bound how often it is served. -/
theorem arbitrarily_many_resource_repeats (count : Nat) :
    Executable label {none} (List.replicate count gate) ∧ fireList {none} (List.replicate count gate) = {none} := by
  induction count with
  | zero => exact ⟨.nil _, rfl⟩
  | succ count prior =>
      rw [List.replicate_succ]
      constructor
      · exact .cons enabled (by rw [unchanged]; exact prior.1)
      · change fireList (fire {none} gate) (List.replicate count gate) = _
        rw [unchanged]
        exact prior.2

end ReadGate

namespace EmptyBody

open ContextualPrefixPublicationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

def body : Schedule base Nat [] () initial initial := .nil initial

theorem source_admitted : body.Admitted := by
  refine ⟨Unit, captures, generator captures, ?_⟩
  intro equation member
  cases member

theorem the_actual_empty_body_finishes_once (fuel : Nat) :
    ∃ observed : WithQueries body.native.guardNativeBank (body.native.nativeBindingState ∅),
      observed.firing.rule = body.producer.rule ∧ observed.firing.selection = body.native.bindingSelection ∧
        observed.firing.outputs = body.producer.outputs ∅ ∧ observed.firing.reusable = body.producerReusable ∧
        observed.firing.fuel = fuel ∧ observed.queries = body.producer.queries ∅ ∧
        ContextualWorldComparison.Equivalent initial (generator initial.declarations)
          (body.native.producerProjection ∅ observed.firing) (body.native.producerCaller ∅ observed.firing) ∧
        observed.firing.target.present = ∅ ∧
        (body.native.nativeBindingState ∅).present = {Option.none} ∧
        ContextualNativeBodies.invocationPending observed.firing.target.present = 0 ∧
        ¬ Enabled (fun _ => ()) observed.firing.target.present (body.native.bindingSelection.commit (T := Unit)) := by
  obtain ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent⟩ :=
    (body.source_iff_native_body ∅ fuel).mp source_admitted
  refine ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent, ?_, rfl, ?_, ?_⟩
  · rw [body.native.producer_result_physical ∅ observed.firing (.nil _) selection]
    rfl
  · have missing := body.native.completed_control_absent ∅ observed.firing selection
    exact if_neg missing
  · exact body.native.no_immediate_resource_replay ∅ observed.firing selection body.native.bindingSelection body.native.invocation_control_taken

theorem completed_empty_body_cannot_replay_after_data
    (firing : ContextualConditionalExecution.Firing body.native.guardNativeBank (body.native.nativeBindingState ∅))
    (selection : firing.selection = body.native.bindingSelection)
    (dataSteps : List (Commit (ContextualNativeBodies.GuardPhysical Nat) Unit))
    (quiet : ∀ commit ∈ dataSteps, Option.none ∉ commit.made) :
    ¬ Enabled (fun _ => ()) (fireList firing.target.present dataSteps) (body.native.bindingSelection.commit (T := Unit)) :=
  body.native.no_resource_replay_after_data ∅ firing selection dataSteps quiet body.native.bindingSelection body.native.invocation_control_taken

end EmptyBody

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeInvocationControls
