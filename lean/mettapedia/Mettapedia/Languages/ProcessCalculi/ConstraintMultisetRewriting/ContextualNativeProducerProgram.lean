import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBirthPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProducerAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProductionAllocation

/-!
# Producer syntax computed from authored surviving births

Each physical net output selects the authored birth of its logical source
occurrence. Ordinary productions use that birth's independent information
block; shared productions use its transport into the current caller block.
The body producer's code and publication flags are constructed from these
descriptors, without reading the final source row store.
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
    Term (signature S schedule.native.guardFamily) Γ sort :=
  let birth := schedule.births.get index
  if birth.reusable then
    instantiate (ContextualIndependentProblems.inclusion schedule.native.guardVariables schedule.native.guardDeclarations (.inl (some index)))
      birth.value
  else instantiate schedule.native.bindingCurrent (instantiate birth.transport birth.value)

def producerCode (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Term (signature S (queryFamily schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort :=
  match schedule.producerBirth physical with
  | some index => instantiate (ContextualSelectionViews.capturedSource schedule.native.bindingLocals schedule.native.guardFamily)
      (schedule.producerBirthValue index)
  | none => schedule.native.bindingPattern physical

def producerReusable (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) : Bool :=
  ((schedule.producerBirth physical).map fun index => (schedule.births.get index).reusable).getD false

/-- The ordinary/shared producer of the compiled body. -/
def producer (schedule : Schedule S O Γ sort before after) : schedule.native.Producer :=
  ⟨schedule.producerCode, schedule.producerReusable⟩

theorem native_captured_production (schedule : Schedule S O Γ sort before after)
    (occupied : Finset Nat) (value : Term (signature S schedule.native.guardFamily) Γ sort) :
    instantiate (ContextualClauseFrames.frame schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily occupied).assignment
        (queryView schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily
          (instantiate (ContextualSelectionViews.capturedSource schedule.native.bindingLocals schedule.native.guardFamily) value)) =
      schedule.native.nativeBindingValue value := by
  unfold queryView ContextualNativeBodies.Body.nativeBindingValue
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
  apply congrArg (fun assignment => instantiate assignment value)
  funext name
  simp only [Assignment.compose, ContextualSelectionViews.capturedSource]
  erw [instantiate_generator]
  change instantiate (ContextualClauseFrames.frame schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily occupied).assignment
    (generator (family schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily) (.inr (.inr name))) = _
  erw [instantiate_generator]
  rfl

theorem producer_birth_exists (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ schedule.native.bindingSelection.made) :
    ∃ index, schedule.producerBirth physical = some index := by
  obtain ⟨name, inside, rfl⟩ := List.mem_map.mp made
  have original : name ∈ schedule.net.effect.made := Finset.mem_toList.mp inside
  obtain ⟨occurrence, _present, index, _current, selected, erased⟩ :=
    schedule.net_output_has_production_of_resources shapes resources name original
  exact ⟨index, by simpa only [producerBirth, erased] using selected⟩

theorem producer_output_birth (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (made : physical ∈ schedule.native.bindingSelection.made)
    (index : schedule.BirthIndex) (selected : schedule.producerBirth physical = some index) :
    schedule.producer.outputs occupied physical = schedule.native.nativeBindingValue (schedule.producerBirthValue index) := by
  rw [schedule.producer.outputs_at occupied physical made]
  change instantiate _ (queryView _ _ _ (schedule.producerCode physical)) = _
  rw [producerCode, selected]
  exact schedule.native_captured_production occupied (schedule.producerBirthValue index)

theorem producer_flag_birth (schedule : Schedule S O Γ sort before after)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (index : schedule.BirthIndex)
    (selected : schedule.producerBirth physical = some index) :
    schedule.producerReusable physical = (schedule.births.get index).reusable := by
  rw [producerReusable, selected]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
