import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeAdmission

/-!
# Actual native producer results carry their conditional row metadata

The record pins the constructed rule, physical selection and output syntax
of an actual bounded conditional firing. Saved row descriptions provide
publication metadata. Resource effects and global information remain those
of that same execution; row conditions are not asserted globally.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

local instance : DecidableEq (OccurrenceAllocationRenaming.Name O) :=
  inferInstanceAs (DecidableEq (O ⊕ (Nat × O)))
local instance : DecidableEq (Option (OccurrenceAllocationRenaming.Name O)) := inferInstance
local instance : BEq (Option (OccurrenceAllocationRenaming.Name O)) where
  beq left right := decide (left = right)
local instance : LawfulBEq (Option (OccurrenceAllocationRenaming.Name O)) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

structure NativePublication (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) where
  firing : ContextualConditionalExecution.Firing
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied)
  compiled : firing.rule = schedule.producerRule
  selected : firing.selection = schedule.bindingSelection
  values : firing.outputs = schedule.producerOutputs occupied
  flags : firing.reusable = schedule.producerReusable

namespace NativePublication

variable {schedule : Schedule S O Γ sort before after} {occupied : Finset Nat}

def returnGuard (publication : NativePublication schedule occupied) :
    Assignment schedule.guardFamily publication.firing.target.declarations :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource publication.firing.update)
    (ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals)
      schedule.guardFamily)

def returnCurrent (publication : NativePublication schedule occupied) :
    Assignment after.declarations publication.firing.target.declarations :=
  Assignment.compose publication.returnGuard schedule.bindingCurrent

abbrev PrivateNames (publication : NativePublication schedule occupied) : Option O → Type
  | none => (ContextualAnswerFamilies.Names schedule.bindingVariables ⊕ ContextualAnswerFamilies.Names schedule.bindingVariables) ⊕
      publication.firing.update.Variables
  | some occurrence => schedule.outputVariables occurrence

abbrev privateDeclarations (publication : NativePublication schedule occupied) : ∀ index, publication.PrivateNames index → MetaArity S
  | none => ContextualPublication.privateFamily (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals)
      publication.firing.update.declaration
  | some occurrence => schedule.outputDeclarations occurrence

abbrev resultLocals (publication : NativePublication schedule occupied) :=
  ContextualConditionalRowPacking.family publication.PrivateNames publication.privateDeclarations

noncomputable def rows (publication : NativePublication schedule occupied)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Row publication.resultLocals publication.firing.target.declarations Γ sort :=
  if physical ∈ schedule.bindingSelection.made then
    match physical with
    | some name =>
        match schedule.outputRow (OccurrenceAllocationRenaming.erase name) with
        | some row => ContextualConditionalRowPacking.pack publication.PrivateNames publication.privateDeclarations
            publication.firing.target.declarations (some (OccurrenceAllocationRenaming.erase name))
            (row.map _ _ publication.returnCurrent)
        | none => ContextualConditionalRowPacking.pack publication.PrivateNames publication.privateDeclarations
            publication.firing.target.declarations none (publication.firing.target.rows physical)
    | none => ContextualConditionalRowPacking.pack publication.PrivateNames publication.privateDeclarations
        publication.firing.target.declarations none (publication.firing.target.rows physical)
  else ContextualConditionalRowPacking.pack publication.PrivateNames publication.privateDeclarations
    publication.firing.target.declarations none (publication.firing.target.rows physical)

noncomputable def target (publication : NativePublication schedule occupied) :
    ContextualConditionalExecution.State publication.resultLocals (Option (OccurrenceAllocationRenaming.Name O)) Γ sort where
  Names := publication.firing.target.Names
  equality := publication.firing.target.equality
  declarations := publication.firing.target.declarations
  occupied := publication.firing.target.occupied
  equations := publication.firing.target.equations
  present := publication.firing.target.present
  rows := publication.rows

theorem output_matches (publication : NativePublication schedule occupied) (physical : OccurrenceAllocationRenaming.Name O)
    (made : some physical ∈ schedule.bindingSelection.made)
    (row : Row (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations Γ sort)
    (selectedRow : schedule.outputRow (OccurrenceAllocationRenaming.erase physical) = some row)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern
        (publication.target.rows (some physical)) ↔
      Matches (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations
        (Assignment.compose candidate publication.returnCurrent) pattern row := by
  change Matches _ _ candidate pattern (publication.rows (some physical)) ↔ _
  simp only [rows, if_pos made, selectedRow]
  exact (ContextualConditionalRowPacking.matches_iff publication.PrivateNames publication.privateDeclarations
    publication.firing.target.declarations (some (OccurrenceAllocationRenaming.erase physical)) _ candidate pattern).trans
      (matches_map_iff (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations
        publication.returnCurrent candidate pattern row)

theorem retained_matches (publication : NativePublication schedule occupied)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (notMade : physical ∉ publication.firing.selection.made)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern (publication.target.rows physical) ↔
      Matches (publication.privateDeclarations none) publication.firing.target.declarations candidate pattern
        (publication.firing.target.rows physical) := by
  change Matches _ _ candidate pattern (publication.rows physical) ↔ _
  have missing : physical ∉ schedule.bindingSelection.made := by rw [← publication.selected]; exact notMade
  simp only [rows, if_neg missing]
  exact ContextualConditionalRowPacking.matches_iff publication.PrivateNames publication.privateDeclarations
    publication.firing.target.declarations none _ candidate pattern

theorem physical_result (publication : NativePublication schedule occupied) :
    publication.target.present = fire (schedule.nativeBindingState occupied).present (schedule.bindingSelection.commit (T := Unit)) := by
  rw [target, publication.firing.physical_result, publication.selected]

end NativePublication

theorem realize_native_publication (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : NativePublication schedule occupied, publication.firing.fuel = fuel := by
  obtain ⟨firing, compiled, selected, values, flags, budget⟩ := schedule.realize_native_producer shapes resources consistent occupied fuel
  exact ⟨⟨firing, compiled, selected, values, flags⟩, budget⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
