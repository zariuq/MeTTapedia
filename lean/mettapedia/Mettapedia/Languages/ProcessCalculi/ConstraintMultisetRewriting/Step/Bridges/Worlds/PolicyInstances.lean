import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Local
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.EmptyBag
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.PolicyControls

/-!
# Existing unique and every steps as local world event families

These adapters use the existing restrictions of bagStep. Their choices keep
the actual bag, opening, selections and admission proof. Their action is the
ordered list of existing match keys. The nonempty convention of bagStep is
retained: an empty complete bag at quiescence is not a local event.

The actual program-extension controls refute ProgramMonotone for both families.
They do not refute adding a world while leaving the shared space unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.PolicyInstances

open RuleSyntax RuleSyntax.JointFirings

universe uO uT uH uE uOcc

section Families

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

def uniqueEvents (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
    (E : Extensions.{uO,uH,uE} Hom) (program : Program Tm) :=
  (StepWeb.uniqueStep X O E program program).eventSystem
    (Action := List (Rule Tm × List O × List O)) (fun {_} bag => bag.members.map Member.key)

def everyEvents (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
    (E : Extensions.{uO,uH,uE} Hom) (program : Program Tm) :=
  (StepWeb.everyStep X O E program program).eventSystem
    (Action := List (Rule Tm × List O × List O)) (fun {_} bag => bag.members.map Member.key)

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
    (E : Extensions.{uO,uH,uE} Hom) (program : Program Tm)

theorem unique_admission {before : State Tm O} (bag : JointFirings.Bag O E program before.frame) :
    (StepWeb.uniqueStep X O E program program).Admits bag ↔ bag.AdmitsUnique X before program := by
  change ((bag.members ≠ [] ∧ bag.Admits X before) ∧ bag.AdmitsUnique X before program) ↔ _
  refine ⟨fun admitted => admitted.2, fun unique => ⟨⟨?_, unique.1.admits⟩, unique⟩⟩
  intro empty
  have one := unique.2
  rw [empty] at one
  simp at one

theorem every_admission {before : State Tm O} (bag : JointFirings.Bag O E program before.frame) :
    (StepWeb.everyStep X O E program program).Admits bag ↔
      bag.members ≠ [] ∧ bag.AdmitsEvery X before program := by
  change ((bag.members ≠ [] ∧ bag.Admits X before) ∧ bag.AdmitsEvery X before program) ↔ _
  exact ⟨fun admitted => ⟨admitted.1.1, admitted.2⟩,
    fun admitted => ⟨⟨admitted.1, admitted.2.admits⟩, admitted.2⟩⟩

theorem unique_advances_iff (before after : State Tm O) :
    RuleSyntax.Worlds.Advances (uniqueEvents X O E) program before after ↔
      ∃ bag : JointFirings.Bag O E program before.frame,
        bag.AdmitsUnique X before program ∧ bag.result X before = after := by
  constructor
  · rintro ⟨⟨bag, admitted⟩, result⟩
    exact ⟨bag, (unique_admission X O E program bag).mp admitted, result⟩
  · rintro ⟨bag, admitted, result⟩
    exact ⟨⟨bag, (unique_admission X O E program bag).mpr admitted⟩, result⟩

theorem every_advances_iff (before after : State Tm O) :
    RuleSyntax.Worlds.Advances (everyEvents X O E) program before after ↔
      ∃ bag : JointFirings.Bag O E program before.frame,
        bag.members ≠ [] ∧ bag.AdmitsEvery X before program ∧ bag.result X before = after := by
  constructor
  · rintro ⟨⟨bag, admitted⟩, result⟩
    obtain ⟨nonempty, every⟩ := (every_admission X O E program bag).mp admitted
    exact ⟨bag, nonempty, every, result⟩
  · rintro ⟨bag, nonempty, every, result⟩
    exact ⟨⟨bag, (every_admission X O E program bag).mpr ⟨nonempty, every⟩⟩, result⟩

/-- Actual completeness earns nonemptiness when a match really is admitted. -/
theorem every_advances_iff_of_match (before after : State Tm O)
    (available : ∃ firing : Firing O E program before.frame, firing.Admits X before) :
    RuleSyntax.Worlds.Advances (everyEvents X O E) program before after ↔
      ∃ bag : JointFirings.Bag O E program before.frame,
        bag.AdmitsEvery X before program ∧ bag.result X before = after := by
  rw [every_advances_iff]
  constructor
  · rintro ⟨bag, _, every, result⟩
    exact ⟨bag, every, result⟩
  · rintro ⟨bag, every, result⟩
    refine ⟨bag, ?_, every, result⟩
    intro empty
    obtain ⟨firing, admitted⟩ := available
    have listed := every.2.2.2 firing firing.member admitted
    rw [empty, List.map_nil] at listed
    exact List.not_mem_nil listed

theorem unique_action {before : State Tm O} (choice : (uniqueEvents X O E program).Choice before) :
    (uniqueEvents X O E program).action before choice = choice.val.members.map Member.key := rfl

theorem every_action {before : State Tm O} (choice : (everyEvents X O E program).Choice before) :
    (everyEvents X O E program).action before choice = choice.val.members.map Member.key := rfl

theorem every_choice_nonempty {before : State Tm O} (choice : (everyEvents X O E program).Choice before) :
    choice.val.members ≠ [] := (every_admission X O E program choice.val).mp choice.property |>.1

theorem unique_choice_nonempty {before : State Tm O} (choice : (uniqueEvents X O E program).Choice before) :
    choice.val.members ≠ [] := choice.property.1.1

theorem unique_no_events_at_inconsistent :
    RuleSyntax.Worlds.NoEventsAtInconsistent X (uniqueEvents X O E) := by
  intro program state inconsistent
  refine ⟨fun choice => inconsistent ?_⟩
  exact (bagStep X O E program).toStep.solvable_knowledge choice.property.1

theorem every_no_events_at_inconsistent :
    RuleSyntax.Worlds.NoEventsAtInconsistent X (everyEvents X O E) := by
  intro program state inconsistent
  refine ⟨fun choice => inconsistent ?_⟩
  exact (bagStep X O E program).toStep.solvable_knowledge choice.property.1

end Families

namespace Controls

open RuleSyntax.Examples (Tm X E)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)
open Mettapedia.Logic.LP

theorem unique_controls_iff (program : Program Tm) (before after : State Tm Nat) :
    RuleSyntax.Worlds.Advances (uniqueEvents X Nat E) program before after ↔
      PolicyControls.uniqueMove program before after := unique_advances_iff X Nat E program before after

theorem original_unique_advances : RuleSyntax.Worlds.Advances (uniqueEvents X Nat E)
    PolicyControls.originalProgram PolicyControls.tokenState
      (MaximalControls.lone.result X PolicyControls.tokenState) :=
  (unique_controls_iff _ _ _).mpr PolicyControls.original_unique

theorem extended_no_unique_advances :
    ¬ ∃ after, RuleSyntax.Worlds.Advances (uniqueEvents X Nat E)
      PolicyControls.extendedProgram PolicyControls.tokenState after := by
  rintro ⟨after, advanced⟩
  exact PolicyControls.extended_no_unique_move ⟨after, (unique_controls_iff _ _ _).mp advanced⟩

theorem unique_not_program_monotone : ¬ RuleSyntax.Worlds.ProgramMonotone (uniqueEvents X Nat E) := by
  intro monotone
  exact extended_no_unique_advances ⟨_, monotone _ _ PolicyControls.program_extension _ _ original_unique_advances⟩

theorem original_every_controls_iff (after : State Tm Nat) :
    RuleSyntax.Worlds.Advances (everyEvents X Nat E) PolicyControls.originalProgram PolicyControls.tokenState after ↔
      PolicyControls.everyMove PolicyControls.originalProgram PolicyControls.tokenState after :=
  every_advances_iff_of_match X Nat E _ _ _
    ⟨(EveryControls.takeAt 0 10).firing, EveryControls.takeAt_admitted (by decide) (by decide)⟩

theorem extended_every_controls_iff (after : State Tm Nat) :
    RuleSyntax.Worlds.Advances (everyEvents X Nat E) PolicyControls.extendedProgram PolicyControls.tokenState after ↔
      PolicyControls.everyMove PolicyControls.extendedProgram PolicyControls.tokenState after :=
  every_advances_iff_of_match X Nat E _ _ _ ⟨ReadTake.taker.firing, ReadTake.taker_admitted⟩

theorem original_every_advances : RuleSyntax.Worlds.Advances (everyEvents X Nat E)
    PolicyControls.originalProgram PolicyControls.tokenState
      (MaximalControls.lone.result X PolicyControls.tokenState) :=
  (original_every_controls_iff _).mpr PolicyControls.original_every

theorem extended_no_every_advances :
    ¬ ∃ after, RuleSyntax.Worlds.Advances (everyEvents X Nat E)
      PolicyControls.extendedProgram PolicyControls.tokenState after := by
  rintro ⟨after, advanced⟩
  exact PolicyControls.extended_no_every_move ⟨after, (extended_every_controls_iff _).mp advanced⟩

theorem every_not_program_monotone : ¬ RuleSyntax.Worlds.ProgramMonotone (everyEvents X Nat E) := by
  intro monotone
  exact extended_no_every_advances ⟨_, monotone _ _ PolicyControls.program_extension _ _ original_every_advances⟩

def quiet : State Tm Nat := EveryControls.tokensAt ∅
def emptyComplete : JointFirings.Bag Nat E EveryControls.tokens PUnit.unit := bagOf action []

theorem quiet_has_no_match (firing : Firing Nat E EveryControls.tokens PUnit.unit) :
    ¬ firing.Admits X quiet := by
  intro admitted
  obtain ⟨occurrence, _, present, _, _⟩ := EveryControls.firing_shape firing admitted
  exact Finset.notMem_empty occurrence present

theorem raw_empty_every : emptyComplete.AdmitsEvery X quiet EveryControls.tokens := by
  apply (nil_every_iff action quiet EveryControls.tokens).mpr
  refine ⟨⟨Subst.id atoms, ?_⟩, fun firing _ => quiet_has_no_match firing⟩
  intro equation member
  cases member

theorem quiet_has_no_every_advance :
    ¬ ∃ after, RuleSyntax.Worlds.Advances (everyEvents X Nat E) EveryControls.tokens quiet after := by
  rintro ⟨after, advanced⟩
  obtain ⟨bag, nonempty, every, _⟩ := (every_advances_iff X Nat E _ _ _).mp advanced
  obtain ⟨member, present⟩ := List.exists_mem_of_ne_nil bag.members nonempty
  have admitted := JointFirings.Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) every.1 present
  exact quiet_has_no_match member.firing admitted

theorem quiet_every_choices_empty : IsEmpty ((everyEvents X Nat E EveryControls.tokens).Choice quiet) :=
  ⟨fun choice => quiet_has_no_every_advance ⟨_, choice, rfl⟩⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.PolicyInstances
