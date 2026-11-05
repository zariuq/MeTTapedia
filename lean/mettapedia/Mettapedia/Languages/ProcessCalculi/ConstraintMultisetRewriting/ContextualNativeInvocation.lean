import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramResult

/-!
# Completion consumes the selected invocation's control occurrence

The invocation control is the last take, after the authored data takes.
It is never produced by that invocation. A successful actual firing
therefore completes the invocation even when its visible body has no
outputs or effects. Another step requiring this control cannot be admitted
unless some intervening action produces a new control occurrence.

Standing-rule installation and fresh invocation creation remain separate
resource policies. This result introduces no occurrence lifetime or new
interaction primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

private theorem absent_after_no_make {N : Type} [DecidableEq N] (key : N) (world : Finset N)
    (missing : key ∉ world) (code : List (Commit N Unit))
    (quiet : ∀ commit ∈ code, key ∉ commit.made) : key ∉ fireList world code := by
  induction code generalizing world with
  | nil => exact missing
  | cons first rest prior =>
      apply prior
      · intro member
        rcases mem_fire.mp member with retained | made
        · exact missing retained.1
        · exact quiet first (List.mem_cons_self ..) made
      · intro commit member
        exact quiet commit (List.mem_cons_of_mem _ member)

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem invocation_control_taken (schedule : Schedule S O Γ sort before after) :
    none ∈ schedule.bindingSelection.taken :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem invocation_control_not_read (schedule : Schedule S O Γ sort before after) :
    none ∉ schedule.bindingSelection.read := by simp [bindingSelection]

theorem invocation_control_not_made (schedule : Schedule S O Γ sort before after) :
    none ∉ schedule.bindingSelection.made := by simp [bindingSelection]

/-- The control's last-take ordinal is the former first-read ordinal.
The actual data takes and reads keep their opening ordinals. -/
theorem invocation_control_scope (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :
    ContextualActivationScopes.scopeAt occupied
        (ContextualActivationScopes.takePort schedule.bindingSelection
          ⟨schedule.net.effect.taken.toList.length, by
            simp only [bindingSelection, List.length_append, List.length_map, List.length_singleton]
            omega⟩) =
      ContextualActivationScopes.start occupied + (1 + schedule.net.effect.taken.toList.length) := rfl

theorem invocation_data_take_scope (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (port : Fin schedule.net.effect.taken.toList.length) :
    ContextualActivationScopes.scopeAt occupied
        (ContextualActivationScopes.takePort schedule.bindingSelection
          ⟨port.val, by simp only [bindingSelection, List.length_append, List.length_map, List.length_singleton]; omega⟩) =
      ContextualActivationScopes.start occupied + (1 + port.val) := rfl

theorem invocation_data_read_scope (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (port : Fin schedule.net.effect.kept.toList.length) :
    ContextualActivationScopes.scopeAt occupied
        (ContextualActivationScopes.readPort schedule.bindingSelection
          ⟨port.val, by simpa only [bindingSelection, List.length_map] using port.isLt⟩) =
      ContextualActivationScopes.start occupied + (1 + schedule.net.effect.taken.toList.length + (1 + port.val)) := by
  simp only [ContextualActivationScopes.scopeAt, ContextualActivationScopes.readPort, bindingSelection,
    List.length_append, List.length_map, List.length_singleton]
  omega

def invocationPending (world : Finset (GuardPhysical O)) : Nat := if none ∈ world then 1 else 0

section Firing

variable [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing schedule.guardNativeBank (schedule.nativeBindingState occupied))
    (selection : firing.selection = schedule.bindingSelection)

include selection

theorem completed_control_absent : none ∉ firing.target.present := by
  rw [firing.physical_result, selection]
  intro member
  rcases mem_fire.mp member with old | created
  · exact old.2 (List.mem_toFinset.mpr schedule.invocation_control_taken)
  · exact schedule.invocation_control_not_made (List.mem_toFinset.mp created)

theorem completed_changes_private_state : firing.target.present ≠ (schedule.nativeBindingState occupied).present := by
  intro same
  have missing := schedule.completed_control_absent occupied firing selection
  rw [same] at missing
  exact missing (Finset.mem_insert_self _ _)

theorem invocation_pending_decreases :
    invocationPending firing.target.present < invocationPending (schedule.nativeBindingState occupied).present := by
  have missing := schedule.completed_control_absent occupied firing selection
  have present : (none : GuardPhysical O) ∈ (schedule.nativeBindingState occupied).present := Finset.mem_insert_self _ _
  simp only [invocationPending, if_neg missing, if_pos present]
  exact Nat.zero_lt_one

theorem no_immediate_resource_replay (next : Selection (GuardPhysical O)) (requested : none ∈ next.taken) :
    ¬ Enabled (fun _ => ()) firing.target.present (next.commit (T := Unit)) := by
  intro enabled
  exact schedule.completed_control_absent occupied firing selection
    (enabled.taken_subset (List.mem_toFinset.mpr requested))

/-- This covers every actual second firing requiring the control through
its admission record, independently of its declaration family or guards. -/
theorem no_immediate_admitted_replay
    (rule : RuleInstance (Term (signature S
      (ContextualActivatedStep.source (ContextualPublication.privateFamily schedule.guardNativeBank firing.update.declaration)
        firing.target.declarations)) Γ sort))
    (next : Selection (GuardPhysical O))
    (outputs : GuardPhysical O → Term (signature S
      (ContextualActivatedStep.target (ContextualPublication.privateFamily schedule.guardNativeBank firing.update.declaration)
        firing.target.declarations)) Γ sort)
    (requested : none ∈ next.taken) :
    ¬ ContextualConditionalExecution.Admitted
      (ContextualPublication.privateFamily schedule.guardNativeBank firing.update.declaration) firing.target rule next outputs := by
  intro admitted
  exact schedule.completed_control_absent occupied firing selection
    (admitted.taken_present (List.mem_toFinset.mpr requested))

theorem no_control_after_intervening_data (code : List (Commit (GuardPhysical O) Unit))
    (quiet : ∀ commit ∈ code, none ∉ commit.made) : none ∉ fireList firing.target.present code :=
  absent_after_no_make none firing.target.present (schedule.completed_control_absent occupied firing selection) code quiet

theorem no_resource_replay_after_data (code : List (Commit (GuardPhysical O) Unit))
    (quiet : ∀ commit ∈ code, none ∉ commit.made)
    (next : Selection (GuardPhysical O)) (requested : none ∈ next.taken) :
    ¬ Enabled (fun _ => ()) (fireList firing.target.present code) (next.commit (T := Unit)) := by
  intro enabled
  exact schedule.no_control_after_intervening_data occupied firing selection code quiet
    (enabled.taken_subset (List.mem_toFinset.mpr requested))

end Firing

/-- The constructed invocation includes both the source/result comparison
and actual control consumption, even for a source body with no effects. -/
theorem source_iff_completed_invocation (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : ContextualPredicateQueryAdmission.WithQueries schedule.guardNativeBank (schedule.nativeBindingState occupied),
        observed.firing.rule = schedule.producerRule ∧ observed.firing.selection = schedule.bindingSelection ∧
          observed.firing.outputs = schedule.producerOutputs occupied ∧ observed.firing.reusable = schedule.producerReusable ∧
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producerQueries occupied ∧
          ContextualWorldComparison.Equivalent after (generator after.declarations)
            (schedule.producerProjection occupied observed.firing) (schedule.producerCaller occupied observed.firing) ∧
          none ∉ observed.firing.target.present ∧
          invocationPending observed.firing.target.present < invocationPending (schedule.nativeBindingState occupied).present := by
  constructor
  · intro source
    obtain ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent⟩ :=
      (schedule.source_iff_native_body occupied fuel).mp source
    exact ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent,
      schedule.completed_control_absent occupied observed.firing selection,
      schedule.invocation_pending_decreases occupied observed.firing selection⟩
  · rintro ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent, _completed, _progress⟩
    exact (schedule.source_iff_native_body occupied fuel).mpr
      ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
