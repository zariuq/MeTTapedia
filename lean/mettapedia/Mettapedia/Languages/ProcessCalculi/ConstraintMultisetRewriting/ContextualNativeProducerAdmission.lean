import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationInputs

/-!
# One native producer firing for every compiled body

A producer gives every physical net output its native code and its
publication flag; each clause kind supplies its own producer. Source
shapes, the whole resource schedule and terminal consistency supply the
binding/resource admission of the constructed rule, so an actual bounded
solver firing exists at every budget. Source guard queries must
additionally be attached before this is a source-admission comparison.
No complete-body guard claim follows from this stage alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

/-- Native code and publication flag for each physical output of a body. -/
structure Producer (body : Body S O Γ sort before after) where
  code : Option (OccurrenceAllocationRenaming.Name O) →
    Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort
  reusable : Option (OccurrenceAllocationRenaming.Name O) → Bool

namespace Producer

variable {body : Body S O Γ sort before after} (producer : body.Producer)

noncomputable def values := body.bindingSelection.made.map producer.code

noncomputable def rule := body.nativeBindingRule producer.values []

noncomputable def outputs (occupied : Finset Nat) :=
  ContextualConditionalSourceAdmission.outputs body.bindingLocals body.bindingLocals body.guardFamily
    occupied body.bindingSelection (body.bindingRule producer.values []) body.bindingRows

end Producer

theorem binding_selection_sets (body : Body S O Γ sort before after) :
    body.bindingSelection.taken.toFinset = insert none (body.net.effect.taken.image some) ∧
    body.bindingSelection.read.toFinset = body.net.effect.kept.image some ∧
    body.bindingSelection.made.toFinset = body.net.effect.made.image some := by
  have mapped (set : Finset (OccurrenceAllocationRenaming.Name O)) :
      (set.toList.map some).toFinset = set.image some := by
    ext physical
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList, Finset.mem_image]
  change (body.net.effect.taken.toList.map some ++ [none]).toFinset = _ ∧
    (body.net.effect.kept.toList.map some).toFinset = _ ∧
    (body.net.effect.made.toList.map some).toFinset = _
  rw [List.toFinset_append, mapped, mapped, mapped]
  change body.net.effect.taken.image some ∪ {none} = _ ∧ _
  rw [Finset.union_singleton]
  exact ⟨rfl, rfl, rfl⟩

theorem native_store_with_control (body : Body S O Γ sort before after) (occupied : Finset Nat) :
    (body.nativeBindingState occupied).present = insert none ((before.present.image Sum.inl).image some) := by
  change insert none (before.present.image (fun occurrence => some (Sum.inl occurrence))) = _
  rw [Finset.image_image]
  rfl

theorem binding_selection_enabled (body : Body S O Γ sort before after)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (occupied : Finset Nat) :
    Enabled (fun _ => ()) (body.nativeBindingState occupied).present (body.bindingSelection.commit (T := Unit)) := by
  have allocated := (body.allocated_resources_of_executable resources).1
  have netEnabled := ((CompiledSchedule.compile_correct OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits body.allocated) (before.present.image Sum.inl)).2
    ((CompiledSchedule.compile_condition_iff _ _ _).mpr allocated)).1
  have lifted := OccurrenceAllocationRenaming.enabled_with_control netEnabled
  have sets := body.binding_selection_sets
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change body.bindingSelection.taken.toFinset ⊆ _
    rw [sets.1, body.native_store_with_control occupied]
    exact lifted.taken_subset
  · change body.bindingSelection.read.toFinset ⊆ _
    rw [sets.2.1, body.native_store_with_control occupied]
    exact lifted.kept_subset
  · change Disjoint body.bindingSelection.taken.toFinset body.bindingSelection.read.toFinset
    rw [sets.1, sets.2.1]
    exact lifted.apart
  · change Disjoint body.bindingSelection.made.toFinset _
    rw [sets.2.2, body.native_store_with_control occupied]
    exact lifted.fresh
  · intro query member
    cases member

theorem producer_taken_distinct (body : Body S O Γ sort before after) : body.bindingSelection.taken.Nodup := by
  change (body.net.effect.taken.toList.map some ++ [none]).Nodup
  have distinct : (body.net.effect.taken.toList.map some).Nodup :=
    (Finset.nodup_toList _).map (fun _ _ same => Option.some.inj same)
  have missing : (none : Option (OccurrenceAllocationRenaming.Name O)) ∉ body.net.effect.taken.toList.map some := by simp
  simpa only [List.concat_eq_append] using List.Nodup.concat missing distinct

theorem producer_made_distinct (body : Body S O Γ sort before after) : body.bindingSelection.made.Nodup :=
  (Finset.nodup_toList _).map (fun _ _ same => Option.some.inj same)

namespace Producer

variable {body : Body S O Γ sort before after} (producer : body.Producer)

theorem outputs_at (occupied : Finset Nat)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ body.bindingSelection.made) :
    producer.outputs occupied physical =
      instantiate (ContextualClauseFrames.frame body.bindingLocals body.bindingLocals body.guardFamily occupied).assignment
        (queryView body.bindingLocals body.bindingLocals body.guardFamily (producer.code physical)) := by
  let values := (ContextualActivatedStep.prepared
    (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily occupied
    body.bindingSelection producer.rule
    (fun occurrence => (body.nativeBindingState occupied).rows occurrence |>.value)).rule.produce
  have compiled : values = body.bindingSelection.made.map (fun occurrence =>
      instantiate (ContextualClauseFrames.frame body.bindingLocals body.bindingLocals body.guardFamily occupied).assignment
        (queryView body.bindingLocals body.bindingLocals body.guardFamily (producer.code occurrence))) := by
    dsimp only [values, rule, nativeBindingRule]
    erw [ContextualConditionalSourceAdmission.prepared_rule]
    change (producer.values.map _).map _ = _
    simp only [Producer.values, List.map_map, Function.comp_def]
  obtain ⟨port, equal⟩ := List.mem_iff_get.mp made
  have lengths : body.bindingSelection.made.length = values.length := by rw [compiled, List.length_map]
  have assigned := ContextualTemplateSource.assign_get body.bindingSelection.made values
    body.producer_made_distinct lengths port
  rw [equal] at assigned
  change (ContextualTemplateSource.assign body.bindingSelection.made values physical).getD _ = _
  rw [assigned]
  change values[port.val]'(by omega) = _
  have indexed := congrArg (fun list => list[port.val]?) compiled
  have bound : port.val < values.length := by omega
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem port.isLt, Option.map_some] at indexed
  exact (Option.some.inj indexed).trans (congrArg (fun occurrence =>
    instantiate (ContextualClauseFrames.frame body.bindingLocals body.bindingLocals body.guardFamily occupied).assignment
      (queryView body.bindingLocals body.bindingLocals body.guardFamily (producer.code occurrence))) equal)

theorem binding_admitted [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) :
    ContextualConditionalExecution.Admitted
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied)
      producer.rule body.bindingSelection (producer.outputs occupied) := by
  have enabled := body.binding_selection_enabled resources occupied
  refine ⟨body.producer_taken_distinct, body.producer_made_distinct, ?_, ?_, ?_,
    enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, ?_, ?_⟩
  · change ((body.bindingSelection.taken.map body.bindingPattern).map
      (instantiate (ContextualClauseFrames.actor body.bindingLocals body.bindingLocals body.guardFamily))).length = _
    simp only [List.length_map]
  · change ((body.bindingSelection.read.map body.bindingPattern).map
      (instantiate (ContextualClauseFrames.actor body.bindingLocals body.bindingLocals body.guardFamily))).length = _
    simp only [List.length_map]
  · exact ContextualClauseAdmission.output_shape body.bindingLocals body.bindingLocals body.guardFamily
      occupied body.bindingSelection (body.bindingRule producer.values [])
      (fun occurrence => (body.bindingRows occurrence).value) body.producer_made_distinct
      (by change _ = producer.values.length; simp only [Producer.values, List.length_map])
  · exact (body.native_binding_solvable_iff shapes resources occupied producer.values []).mpr consistent
  · intro check member
    erw [ContextualConditionalSourceAdmission.prepared_rule] at member
    change check ∈ [] at member
    cases member

/-- An actual bounded firing of the constructed producer at every budget. -/
theorem realize [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) (fuel : Nat) :
    ∃ firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied),
      firing.rule = producer.rule ∧ firing.selection = body.bindingSelection ∧
        firing.outputs = producer.outputs occupied ∧ firing.reusable = producer.reusable ∧ firing.fuel = fuel :=
  ContextualConditionalExecution.realize_at_fuel
    (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied)
    producer.rule body.bindingSelection (producer.outputs occupied) producer.reusable
    (producer.binding_admitted shapes resources consistent occupied) fuel

end Producer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
