import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceRenaming

/-!
# Original guard cuts follow their own private allocation context

Each source cut uses the allocation map at that point in the private body,
not the body's final map. Later declaration extensions retain the saved
cut's equations and rows without adding later information. The compiled
cut list therefore preserves and reflects all original all-future asks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries

variable {S : Signature} {O P V : Type} {declaration : V → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def Cut.rename [DecidableEq P] (name : O → P) (back : P → O) (cut : Cut declaration O Γ sort) :
    Cut declaration P Γ sort :=
  ⟨cut.LocalNames, cut.locals, cut.problem, (fun physical => cut.rows (back physical)),
    cut.world.image name, cut.checks⟩

theorem Cut.rename_iff [DecidableEq P] (cut : Cut declaration O Γ sort) (name : O → P)
    (injective : Function.Injective name) (back : P → O)
    (projects : ∀ occurrence ∈ cut.world, back (name occurrence) = occurrence) :
    (cut.rename name back).Holds ↔ cut.Holds := by
  simp only [Cut.Holds, Cut.rename]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact ContextualOccurrenceRenaming.ask_iff cut.locals name injective cut.problem cut.rows
    (fun physical => cut.rows (back physical)) cut.world (by
      intro occurrence present
      rw [projects occurrence present]) check

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def allocatedCuts : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → List (Cut after.declarations (OccurrenceAllocationRenaming.Name O) Γ sort)
  | _, _, _, .nil _ => []
  | _, _, _, @Schedule.snoc _ _ _ _ _ _ _ _ _ middle _ _ _ mid past queries plan picked =>
      past.allocatedCuts.map (Cut.map (captureFrame queries middle mid.declarations).assignment) ++
        [(originalCut mid queries plan picked).rename
          (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial past.selections).current
          OccurrenceAllocationRenaming.erase]

def AllocatedCutsHold (schedule : Schedule S O Γ sort before after) : Prop :=
  ∀ cut ∈ schedule.allocatedCuts, cut.Holds

theorem allocated_cuts_snoc {Middle Query : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query] {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort))
    (picked : Selection O) :
    (Schedule.snoc past queries plan picked).AllocatedCutsHold ↔
      past.AllocatedCutsHold ∧ (originalCut mid queries plan picked).Holds := by
  change (∀ cut ∈ past.allocatedCuts.map (Cut.map (captureFrame queries middle mid.declarations).assignment) ++
    [(originalCut mid queries plan picked).rename
      (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial past.selections).current
      OccurrenceAllocationRenaming.erase], cut.Holds) ↔ _
  rw [List.forall_mem_append, List.forall_mem_singleton]
  apply and_congr
  · simp only [List.forall_mem_map]
    apply forall_congr'
    intro cut
    apply forall_congr'
    intro _member
    exact cut.extension_iff (captureFrame queries middle mid.declarations)
  · exact (originalCut mid queries plan picked).rename_iff _
      (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial past.selections).injective
      _ (by intro occurrence _present; exact
        (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial past.selections).projects occurrence)

/-- Renaming private creations preserves and reflects every guard at its original cut. -/
theorem allocated_cuts_iff (schedule : Schedule S O Γ sort before after) :
    schedule.AllocatedCutsHold ↔ schedule.CutsHold := by
  induction schedule with
  | nil _ => simp [AllocatedCutsHold, allocatedCuts, CutsHold, cuts]
  | snoc past queries plan picked prior =>
      rw [allocated_cuts_snoc, cuts_snoc, prior]

theorem allocated_cuts_count (schedule : Schedule S O Γ sort before after) :
    schedule.allocatedCuts.length = schedule.selections.length := by
  induction schedule with
  | nil _ => rfl
  | snoc _ _ _ _ prior =>
      change (_ ++ [_]).length = (_ ++ [_]).length
      simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil] using
        congrArg (fun count => count + 1) prior

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
