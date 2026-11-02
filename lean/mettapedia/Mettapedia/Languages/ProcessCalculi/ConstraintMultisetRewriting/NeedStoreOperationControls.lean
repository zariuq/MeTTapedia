import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedStoreOperations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedSnapshotControls
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructionControls

/-!
# Retained snapshot editing controls

The input is the actual completed three-cell copy from NeedSnapshotControls.
Four ordinary firings edit that world in sequence, comparing the result to
the independently defined Store operations. The original source snapshot
remains unchanged throughout.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedStoreOperations.Controls

open SnapshotCopy
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
open NeedSnapshots.Controls (cached pending store finished finished_snapshot)

def changed : Suspension := {cached with memo := .done (.sym 42)}
def newCell : Suspension := ⟨.ret (.sym 88),[.need 0],.pending⟩
def memoEvent : Event := .memo 0 cached (.done (.sym 42))
def emitEvent : Event := .emit 3 [9,9,3] 9
def allocateEvent : Event := .allocate 3 [9,9,3,9] (.ret (.sym 88)) [.need 0]
def outsideEvent : Event := .memoOutside 9 4 [9,9,3,9] (by decide) (.done (.sym 99))

def memoSelection : Selection (Occurrence Suspension) :=
  ⟨[(17,.reply 5 1),(10,.cell 1 0 cached)],[(16,.ready 1)],[(18,.reply 5 1),(19,.cell 1 0 changed)]⟩
def emitSelection : Selection (Occurrence Suspension) :=
  ⟨[(18,.reply 5 1),(8,.metadata 1 3 [9,9,3])],[(16,.ready 1)],
    [(20,.reply 5 1),(21,.metadata 1 3 [9,9,3,9])]⟩
def allocateSelection : Selection (Occurrence Suspension) :=
  ⟨[(20,.reply 5 1),(21,.metadata 1 3 [9,9,3,9])],[(16,.ready 1)],
    [(22,.reply 5 1),(23,.metadata 1 4 [9,9,3,9]),(24,.cell 1 3 newCell)]⟩
def outsideSelection : Selection (Occurrence Suspension) :=
  ⟨[(22,.reply 5 1)],[(16,.ready 1),(23,.metadata 1 4 [9,9,3,9])],[(25,.reply 5 1)]⟩

def afterMemo := memoSelection.result label (memoEvent.rule 5 1) finished
def afterEmit := emitSelection.result label (emitEvent.rule 5 1) afterMemo
def afterAllocate := allocateSelection.result label (allocateEvent.rule 5 1) afterEmit
def afterOutside := outsideSelection.result label (outsideEvent.rule 5 1) afterAllocate

theorem memo_valid : memoSelection.Valid action label (memoEvent.rule 5 1) finished := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ memoSelection.problem label (memoEvent.rule 5 1) finished, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem emit_valid : emitSelection.Valid action label (emitEvent.rule 5 1) afterMemo := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ emitSelection.problem label (emitEvent.rule 5 1) afterMemo, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem allocate_valid : allocateSelection.Valid action label (allocateEvent.rule 5 1) afterEmit := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ allocateSelection.problem label (allocateEvent.rule 5 1) afterEmit, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem outside_valid : outsideSelection.Valid action label (outsideEvent.rule 5 1) afterAllocate := by
  refine ⟨by decide,by decide,rfl,rfl,rfl,?_,⟨(),?_⟩,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,by intro query member; cases member⟩
  · change ∀ equation ∈ outsideSelection.problem label (outsideEvent.rule 5 1) afterAllocate, equation.1 = equation.2
    decide +kernel
  · intro check member; cases member

theorem memo_step : Step action label (memoEvent.rule 5 1) finished afterMemo := ⟨memoSelection,memo_valid,rfl⟩
theorem emit_step : Step action label (emitEvent.rule 5 1) afterMemo afterEmit := ⟨emitSelection,emit_valid,rfl⟩
theorem allocate_step : Step action label (allocateEvent.rule 5 1) afterEmit afterAllocate := ⟨allocateSelection,allocate_valid,rfl⟩
theorem outside_step : Step action label (outsideEvent.rule 5 1) afterAllocate afterOutside := ⟨outsideSelection,outside_valid,rfl⟩

def memoedStore := store.setMemo 0 (.done (.sym 42))
def emittedStore := memoedStore.emit 9
def allocatedStore := emittedStore.alloc (.ret (.sym 88)) [.need 0]

theorem afterMemo_represents : Editable afterMemo.present 5 1 memoedStore :=
  preserves (editable_of_completed finished_snapshot) memoEvent memo_step
theorem afterEmit_represents : Editable afterEmit.present 5 1 emittedStore :=
  preserves afterMemo_represents emitEvent emit_step
theorem afterAllocate_represents : Editable afterAllocate.present 5 1 allocatedStore :=
  preserves afterEmit_represents allocateEvent allocate_step
theorem afterOutside_represents : Editable afterOutside.present 5 1 allocatedStore := by
  have result := preserves afterAllocate_represents outsideEvent outside_step
  have unchanged : outsideEvent.operation.apply allocatedStore = allocatedStore := by decide +kernel
  exact unchanged ▸ result

theorem copied_source_stays_unchanged : Snapshot afterOutside.present 0 store.cells store.trace := by
  have first := preserves_other (editable_of_completed finished_snapshot) memoEvent memo_step
    (by decide : 0 ≠ 1) finished_snapshot.sourceSnapshot
  have second := preserves_other afterMemo_represents emitEvent emit_step (by decide : 0 ≠ 1) first
  have third := preserves_other afterEmit_represents allocateEvent allocate_step (by decide : 0 ≠ 1) second
  exact preserves_other afterAllocate_represents outsideEvent outside_step (by decide : 0 ≠ 1) third

theorem only_the_selected_memo_changes :
    (19,.cell 1 0 changed) ∈ afterOutside.present ∧ (12,.cell 1 1 cached) ∈ afterOutside.present ∧
      (14,.cell 1 2 pending) ∈ afterOutside.present := by decide +kernel

theorem allocation_preserves_the_captured_reference :
    (24,.cell 1 3 newCell) ∈ afterOutside.present := by decide +kernel

theorem emission_appends_without_deduplicating :
    (23,.metadata 1 4 [9,9,3,9]) ∈ afterOutside.present := by decide +kernel

theorem old_command_occurrences_are_consumed :
    (17,.reply 5 1) ∉ afterOutside.present ∧ (18,.reply 5 1) ∉ afterOutside.present ∧
      (20,.reply 5 1) ∉ afterOutside.present ∧ (22,.reply 5 1) ∉ afterOutside.present ∧
      (25,.reply 5 1) ∈ afterOutside.present := by decide +kernel

theorem all_previous_equations_remain : finished.equations.IsPrefix afterOutside.equations ∧
    afterOutside.equations.length = 28 := by decide +kernel

theorem stale_command_refuses_replay : ¬ memoSelection.Valid action label (memoEvent.rule 5 1) afterMemo := by
  intro valid
  have old := valid.occurrences.taken_subset (by decide : (17,.reply 5 1) ∈ memoSelection.commit.taken)
  exact (by decide : (17,.reply 5 1) ∉ afterMemo.present) old

theorem old_memo_value_refuses_a_new_edit :
    ¬ ∃ after, Step action label ((Event.memo 0 cached .pending).rule 5 1) afterMemo after := by
  rintro ⟨after,step⟩
  have matched := matches_of_step afterMemo_represents (.memo 0 cached .pending) step
  exact (by unfold Event.Matches; decide +kernel : ¬ (Event.memo 0 cached .pending).Matches memoedStore) matched

theorem stale_allocation_count_is_refused :
    ¬ ∃ after, Step action label ((Event.allocate 3 [9,9,3,9] (.ret (.sym 0)) []).rule 5 1) afterAllocate after := by
  rintro ⟨after,step⟩
  have matched := matches_of_step afterAllocate_represents (.allocate 3 [9,9,3,9] (.ret (.sym 0)) []) step
  exact (by unfold Event.Matches; decide +kernel : ¬ (Event.allocate 3 [9,9,3,9] (.ret (.sym 0)) []).Matches allocatedStore) matched

theorem an_existing_cell_cannot_take_the_outside_case :
    ¬ ∃ after, Step action label ((Event.memoOutside 0 0 [9,9,3,9] (Nat.le_refl 0) .pending).rule 5 1) afterAllocate after := by
  rintro ⟨after,step⟩
  have matched := matches_of_step afterAllocate_represents (.memoOutside 0 0 [9,9,3,9] (Nat.le_refl 0) .pending) step
  exact (by unfold Event.Matches; decide +kernel : ¬ (Event.memoOutside 0 0 [9,9,3,9] (Nat.le_refl 0) .pending).Matches allocatedStore) matched

/-- An independent source consumer follows the undemanded cell's captured
reference. This tests the two represented stores; it is not an assertion
that the source instruction runner has already been lowered to CMR. -/
def demandCaptured (source : Store) :=
  Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.Controls.observations
    (Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions.runFuel [] 50
      (.task (.forceVal source (.need 2)) []))

theorem captured_reference_resolves_in_its_own_branch :
    demandCaptured store = some [(.ok (.sym 7),[9,9,3,5])] ∧
      demandCaptured allocatedStore = some [(.ok (.sym 42),[9,9,3,9,5])] := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedStoreOperations.Controls
