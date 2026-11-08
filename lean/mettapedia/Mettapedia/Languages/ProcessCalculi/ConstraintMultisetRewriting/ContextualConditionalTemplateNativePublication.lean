import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativeProducer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeResults

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

abbrev NativePublication (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat) :=
  ContextualConditionalExecution.Published
    (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
    (schedule.native.nativeBindingState occupied) schedule.producer.rule schedule.native.bindingSelection
    (schedule.producer.outputs occupied) (.all schedule.producerReusable)

namespace NativePublication

variable {schedule : Schedule S O Γ sort before after} {occupied : Finset Nat}

def returnGuard (publication : NativePublication schedule occupied) :
    Assignment schedule.native.guardFamily publication.firing.target.declarations :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource publication.firing.update)
    (ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
      schedule.native.guardFamily)

abbrev producerCaller (publication : NativePublication schedule occupied) :
    Assignment after.declarations publication.firing.target.declarations :=
  schedule.native.producerCaller occupied publication.firing

abbrev PrivateNames (publication : NativePublication schedule occupied) : Option O → Type :=
  ContextualConditionalRowPacking.WithFallback schedule.outputVariables
    (Raw := (ContextualAnswerFamilies.Names schedule.native.bindingVariables ⊕
      ContextualAnswerFamilies.Names schedule.native.bindingVariables) ⊕ publication.firing.update.Variables)

abbrev privateDeclarations (publication : NativePublication schedule occupied) : ∀ index, publication.PrivateNames index → MetaArity S :=
  ContextualConditionalRowPacking.fallbackDeclarations schedule.outputVariables schedule.outputDeclarations
    (ContextualPublication.privateFamily (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
      publication.firing.update.declaration)

abbrev resultLocals (publication : NativePublication schedule occupied) :=
  ContextualConditionalRowPacking.family publication.PrivateNames publication.privateDeclarations

/-- The recipe's private names enter the output block of the shared bank;
the raw firing's private/helper names occupy its retained block. -/
def embedRecipe (publication : NativePublication schedule occupied)
    (recipe : ContextualConditionalPublication.Recipe schedule.producerLocals
      (ContextualClauseFrames.nativeActive schedule.native.bindingLocals
        schedule.native.bindingLocals schedule.native.guardFamily)) :
    ContextualConditionalPublication.Recipe publication.resultLocals
      (ContextualClauseFrames.nativeActive schedule.native.bindingLocals
        schedule.native.bindingLocals schedule.native.guardFamily) :=
  ContextualConditionalRowPacking.includeRecipe schedule.outputVariables schedule.outputDeclarations
    (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)
    (ContextualPublication.privateFamily (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
      publication.firing.update.declaration) recipe

noncomputable def recipes (publication : NativePublication schedule occupied)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :=
  (schedule.producerRecipes physical).map publication.embedRecipe

noncomputable def rows (publication : NativePublication schedule occupied)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) :
    Row publication.resultLocals publication.firing.target.declarations Γ sort :=
  ContextualConditionalRowPacking.publishWithFallback schedule.outputVariables schedule.outputDeclarations
    (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)
    (ContextualPublication.privateFamily (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
      publication.firing.update.declaration)
    schedule.producerRecipes (ContextualComputedFreshFrame.includeSource publication.firing.update)
    publication.firing.outputs publication.firing.target.rows physical

noncomputable def target (publication : NativePublication schedule occupied) :
    ContextualConditionalExecution.State publication.resultLocals (Option (OccurrenceAllocationRenaming.Name O)) Γ sort :=
  publication.firing.target.withRows publication.resultLocals publication.rows

theorem retained_matches (publication : NativePublication schedule occupied)
    (physical : Option (OccurrenceAllocationRenaming.Name O)) (notMade : physical ∉ publication.firing.selection.made)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern (publication.target.rows physical) ↔
      Matches (publication.privateDeclarations none) publication.firing.target.declarations candidate pattern
        (publication.firing.target.rows physical) := by
  change Matches _ _ candidate pattern (publication.rows physical) ↔ _
  have missing : physical ∉ schedule.native.bindingSelection.made := by rw [← publication.selected]; exact notMade
  exact ContextualConditionalRowPacking.publishWithFallback_none_matches
    schedule.outputVariables schedule.outputDeclarations
    (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)
    (ContextualPublication.privateFamily (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals)
      publication.firing.update.declaration)
    schedule.producerRecipes (ContextualComputedFreshFrame.includeSource publication.firing.update)
    publication.firing.outputs publication.firing.target.rows physical
    (schedule.producerRecipes_none_of_not_made physical missing) candidate pattern

theorem physical_result (publication : NativePublication schedule occupied) :
    publication.target.present = fire (schedule.native.nativeBindingState occupied).present (schedule.native.bindingSelection.commit (T := Unit)) := by
  change publication.firing.target.present = _
  exact publication.firing.physical_result.trans
    (congrArg (fun selection => fire (schedule.native.nativeBindingState occupied).present
      (selection.commit (T := Unit))) publication.selected)

end NativePublication

theorem realize_native_publication (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat) (fuel : Nat) :
    ∃ publication : NativePublication schedule occupied, publication.firing.fuel = fuel := by
  obtain ⟨firing, compiled, selected, values, flags, budget⟩ := schedule.producer.realize shapes resources consistent occupied fuel
  exact ⟨⟨firing, compiled, selected, values, flags⟩, budget⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
