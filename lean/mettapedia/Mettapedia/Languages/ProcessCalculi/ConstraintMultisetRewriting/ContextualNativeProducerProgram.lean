import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBirthPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProductionAllocation

/-!
# Producer syntax computed from authored surviving births

Each physical net output selects the authored birth of its logical source
occurrence. Ordinary productions use that birth's independent information
block; shared productions use its transport into the current caller block.
The rule's output list, native values and publication flags are constructed
from these descriptors, without reading the final source row store.
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

def producerBirth (schedule : Schedule S O Γ sort before after) :
    Option (OccurrenceAllocationRenaming.Name O) → Option schedule.BirthIndex
  | none => none
  | some physical => schedule.productionIndex (OccurrenceAllocationRenaming.erase physical)

def producerBirthValue (schedule : Schedule S O Γ sort before after) (index : schedule.BirthIndex) :
    Term (signature S schedule.guardFamily) Γ sort :=
  let birth := schedule.births.get index
  if birth.reusable then
    instantiate (ContextualIndependentProblems.inclusion schedule.guardVariables schedule.guardDeclarations (.inl (some index)))
      birth.value
  else instantiate schedule.bindingCurrent (instantiate birth.transport birth.value)

def producerCode (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort :=
  match schedule.producerBirth physical with
  | some index => instantiate (ContextualSelectionViews.capturedSource schedule.bindingLocals schedule.guardFamily)
      (schedule.producerBirthValue index)
  | none => schedule.bindingPattern physical

def producerReusable (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) : Bool :=
  ((schedule.producerBirth physical).map fun index => (schedule.births.get index).reusable).getD false

noncomputable def producerValues (schedule : Schedule S O Γ sort before after) :=
  schedule.bindingSelection.made.map schedule.producerCode

noncomputable def producerRule (schedule : Schedule S O Γ sort before after) :=
  schedule.nativeBindingRule schedule.producerValues []

noncomputable def producerOutputs (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :=
  ContextualConditionalSourceAdmission.outputs schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
    occupied schedule.bindingSelection (schedule.bindingRule schedule.producerValues []) schedule.bindingRows

theorem native_captured_production (schedule : Schedule S O Γ sort before after)
    (occupied : Finset Nat) (value : Term (signature S schedule.guardFamily) Γ sort) :
    instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
        (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
          (instantiate (ContextualSelectionViews.capturedSource schedule.bindingLocals schedule.guardFamily) value)) =
      schedule.nativeBindingValue value := by
  unfold queryView nativeBindingValue
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
  apply congrArg (fun assignment => instantiate assignment value)
  funext name
  simp only [Assignment.compose, ContextualSelectionViews.capturedSource]
  erw [instantiate_generator]
  change instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
    (generator (family schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) (.inr (.inr name))) = _
  erw [instantiate_generator]
  rfl

theorem producer_birth_exists (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ schedule.bindingSelection.made) :
    ∃ index, schedule.producerBirth physical = some index := by
  obtain ⟨name, inside, rfl⟩ := List.mem_map.mp made
  have original : name ∈ schedule.net.effect.made := Finset.mem_toList.mp inside
  obtain ⟨occurrence, _present, index, _current, selected, erased⟩ :=
    schedule.net_output_has_production_of_resources shapes resources name original
  exact ⟨index, by simpa only [producerBirth, erased] using selected⟩

theorem producer_made_distinct (schedule : Schedule S O Γ sort before after) : schedule.bindingSelection.made.Nodup :=
  (Finset.nodup_toList _).map (fun _ _ same => Option.some.inj same)

theorem producer_outputs_at (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ schedule.bindingSelection.made) :
    schedule.producerOutputs occupied physical =
      instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
        (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily (schedule.producerCode physical)) := by
  let values := (ContextualActivatedStep.prepared
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily occupied
    schedule.bindingSelection schedule.producerRule
    (fun occurrence => (schedule.nativeBindingState occupied).rows occurrence |>.value)).rule.produce
  have compiled : values = schedule.bindingSelection.made.map (fun occurrence =>
      instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
        (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily (schedule.producerCode occurrence))) := by
    dsimp only [values, producerRule, nativeBindingRule]
    erw [ContextualConditionalSourceAdmission.prepared_rule]
    change (schedule.producerValues.map _).map _ = _
    simp only [producerValues, List.map_map, Function.comp_def]
  obtain ⟨port, equal⟩ := List.mem_iff_get.mp made
  have lengths : schedule.bindingSelection.made.length = values.length := by rw [compiled, List.length_map]
  have assigned := ContextualTemplateSource.assign_get schedule.bindingSelection.made values
    schedule.producer_made_distinct lengths port
  rw [equal] at assigned
  change (ContextualTemplateSource.assign schedule.bindingSelection.made values physical).getD _ = _
  rw [assigned]
  change values[port.val]'(by omega) = _
  have indexed := congrArg (fun list => list[port.val]?) compiled
  have bound : port.val < values.length := by omega
  simp only [List.getElem?_map, List.getElem?_eq_getElem bound,
    List.getElem?_eq_getElem port.isLt, Option.map_some] at indexed
  exact (Option.some.inj indexed).trans (congrArg (fun occurrence =>
    instantiate (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
      (queryView schedule.bindingLocals schedule.bindingLocals schedule.guardFamily (schedule.producerCode occurrence))) equal)

theorem producer_output_birth (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ schedule.bindingSelection.made)
    (index : schedule.BirthIndex) (selected : schedule.producerBirth physical = some index) :
    schedule.producerOutputs occupied physical = schedule.nativeBindingValue (schedule.producerBirthValue index) := by
  rw [schedule.producer_outputs_at occupied physical made, producerCode, selected]
  exact schedule.native_captured_production occupied (schedule.producerBirthValue index)

theorem producer_flag_birth (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (index : schedule.BirthIndex)
    (selected : schedule.producerBirth physical = some index) :
    schedule.producerReusable physical = (schedule.births.get index).reusable := by
  rw [producerReusable, selected]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
