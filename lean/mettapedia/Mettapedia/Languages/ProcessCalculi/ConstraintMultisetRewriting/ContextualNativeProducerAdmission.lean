import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProducerProgram

/-!
# The constructed native producer has an actual bounded solver execution

Source shapes, the whole resource schedule and terminal consistency supply
the binding/resource admission of the computed producer. Source guard
queries must additionally be attached before this is a source-admission
comparison. No complete-body guard claim follows from this stage alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits


variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem binding_selection_sets (schedule : Schedule S O Γ sort before after) :
    schedule.bindingSelection.taken.toFinset = insert none (schedule.net.effect.taken.image some) ∧
    schedule.bindingSelection.read.toFinset = schedule.net.effect.kept.image some ∧
    schedule.bindingSelection.made.toFinset = schedule.net.effect.made.image some := by
  have mapped (set : Finset (OccurrenceAllocationRenaming.Name O)) :
      (set.toList.map some).toFinset = set.image some := by
    ext physical
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList, Finset.mem_image]
  change (schedule.net.effect.taken.toList.map some ++ [none]).toFinset = _ ∧
    (schedule.net.effect.kept.toList.map some).toFinset = _ ∧
    (schedule.net.effect.made.toList.map some).toFinset = _
  rw [List.toFinset_append, mapped, mapped, mapped]
  change schedule.net.effect.taken.image some ∪ {none} = _ ∧ _
  rw [Finset.union_singleton]
  exact ⟨rfl, rfl, rfl⟩

theorem native_store_with_control (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :
    (schedule.nativeBindingState occupied).present = insert none ((before.present.image Sum.inl).image some) := by
  change insert none (before.present.image (fun occurrence => some (Sum.inl occurrence))) = _
  rw [Finset.image_image]
  rfl

theorem binding_selection_enabled (schedule : Schedule S O Γ sort before after)
    (resources : Executable unitLabel before.present schedule.commits) (occupied : Finset Nat) :
    Enabled (fun _ => ()) (schedule.nativeBindingState occupied).present (schedule.bindingSelection.commit (T := Unit)) := by
  have allocated := (schedule.allocated_resources_of_executable resources).1
  have netEnabled := ((CompiledSchedule.compile_correct OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) (before.present.image Sum.inl)).2
    ((CompiledSchedule.compile_condition_iff _ _ _).mpr allocated)).1
  have lifted := OccurrenceAllocationRenaming.enabled_with_control netEnabled
  have sets := schedule.binding_selection_sets
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change schedule.bindingSelection.taken.toFinset ⊆ _
    rw [sets.1, schedule.native_store_with_control occupied]
    exact lifted.taken_subset
  · change schedule.bindingSelection.read.toFinset ⊆ _
    rw [sets.2.1, schedule.native_store_with_control occupied]
    exact lifted.kept_subset
  · change Disjoint schedule.bindingSelection.taken.toFinset schedule.bindingSelection.read.toFinset
    rw [sets.1, sets.2.1]
    exact lifted.apart
  · change Disjoint schedule.bindingSelection.made.toFinset _
    rw [sets.2.2, schedule.native_store_with_control occupied]
    exact lifted.fresh
  · intro query member
    cases member

theorem producer_taken_distinct (schedule : Schedule S O Γ sort before after) : schedule.bindingSelection.taken.Nodup := by
  change (schedule.net.effect.taken.toList.map some ++ [none]).Nodup
  have distinct : (schedule.net.effect.taken.toList.map some).Nodup :=
    (Finset.nodup_toList _).map (fun _ _ same => Option.some.inj same)
  have missing : (none : Option (OccurrenceAllocationRenaming.Name O)) ∉ schedule.net.effect.taken.toList.map some := by simp
  simpa only [List.concat_eq_append] using List.Nodup.concat missing distinct

theorem producer_binding_admitted (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) :
    ContextualConditionalExecution.Admitted
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied)
      schedule.producerRule schedule.bindingSelection (schedule.producerOutputs occupied) := by
  have enabled := schedule.binding_selection_enabled resources occupied
  refine ⟨schedule.producer_taken_distinct, schedule.producer_made_distinct, ?_, ?_, ?_,
    enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, ?_, ?_⟩
  · change ((schedule.bindingSelection.taken.map schedule.bindingPattern).map
      (instantiate (ContextualClauseFrames.actor schedule.bindingLocals schedule.bindingLocals schedule.guardFamily))).length = _
    simp only [List.length_map]
  · change ((schedule.bindingSelection.read.map schedule.bindingPattern).map
      (instantiate (ContextualClauseFrames.actor schedule.bindingLocals schedule.bindingLocals schedule.guardFamily))).length = _
    simp only [List.length_map]
  · exact ContextualClauseAdmission.output_shape schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
      occupied schedule.bindingSelection (schedule.bindingRule schedule.producerValues [])
      (fun occurrence => (schedule.bindingRows occurrence).value) schedule.producer_made_distinct
      (by change _ = schedule.producerValues.length; simp only [producerValues, List.length_map])
  · exact (schedule.native_binding_solvable_iff shapes resources occupied schedule.producerValues []).mpr consistent
  · intro check member
    erw [ContextualConditionalSourceAdmission.prepared_rule] at member
    change check ∈ [] at member
    cases member

theorem realize_native_producer (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) (fuel : Nat) :
    ∃ firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied),
      firing.rule = schedule.producerRule ∧ firing.selection = schedule.bindingSelection ∧
        firing.outputs = schedule.producerOutputs occupied ∧ firing.reusable = schedule.producerReusable ∧ firing.fuel = fuel :=
  ContextualConditionalExecution.realize_at_fuel
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied)
    schedule.producerRule schedule.bindingSelection (schedule.producerOutputs occupied) schedule.producerReusable
    (schedule.producer_binding_admitted shapes resources consistent occupied) fuel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
