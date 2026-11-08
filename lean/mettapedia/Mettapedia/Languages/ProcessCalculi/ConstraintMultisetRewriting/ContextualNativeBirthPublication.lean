import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeResults
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSurvivingProductions

/-!
# Ordinary outputs retain independent creation-time instances

The native port equations preserve every given compiled information model
(`ContextualNativeResults`). Consequently they neither add nor remove
instances of a value in any saved creation block of an ordinary/shared body.
This comparison uses actual native information, including
the selected rows' latent conditions, without assuming successful guards.

The ordinary-output theorem applies the existing conditional producer's
row semantics to that comparison. The compiled firing and its world
comparison are joined in `ContextualNativeProgramResult`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def nativeBirthValue (schedule : Schedule S O Γ sort before after) (index : schedule.BirthIndex) :
    Term (signature S (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort :=
  schedule.native.nativeBindingValue
    (instantiate (ContextualIndependentProblems.inclusion schedule.native.guardVariables schedule.native.guardDeclarations (.inl (some index)))
      (schedule.births.get index).value)

/-- Other creation blocks, later caller information and selected input
conditions do not narrow this ordinary output's original instances. -/
theorem native_birth_instances (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort)))
    (index : schedule.BirthIndex) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (schedule.native.nativeBindingInformation occupied produced guards)
        (schedule.nativeBirthValue index) next pattern ↔
      ContextualPublication.SourceInstances (schedule.births.get index).problem (schedule.births.get index).value next pattern :=
  (schedule.native.native_binding_value_instances shapes resources occupied produced guards _ pattern).trans
    (ContextualIndependentProblems.instances_iff schedule.native.guardVariables schedule.native.guardDeclarations schedule.native.guardConditions
      (schedule.native.guard_blocks_solvable consistent) schedule.native.guardIndices (.inl (some index))
      (schedule.native_birth_listed index) (schedule.births.get index).value pattern)

instance bindingVariableEquality (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] (index : Option O) : DecidableEq (schedule.native.bindingVariables index) := by
  cases index <;> dsimp only [ContextualNativeBodies.Body.bindingVariables] <;> infer_instance

theorem ordinary_native_row_matches_birth (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort)))
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) (schedule.native.nativeBindingState occupied))
    (rule : firing.rule = schedule.native.nativeBindingRule produced guards)
    (selection : firing.selection = schedule.native.bindingSelection)
    (occurrence : Option (OccurrenceAllocationRenaming.Name O)) (made : occurrence ∈ firing.selection.made)
    (ordinary : firing.reusable occurrence = true) (index : schedule.BirthIndex)
    (output : firing.outputs occurrence = schedule.nativeBirthValue index)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches
        (ContextualPublication.privateFamily
          (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      ContextualPublication.SourceInstances (schedule.births.get index).problem (schedule.births.get index).value next pattern := by
  rw [firing.ordinary_matches_source occurrence made ordinary next candidate pattern, rule, selection, output]
  exact schedule.native_birth_instances shapes resources consistent occupied produced guards index pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
