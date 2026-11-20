import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SplitPhaseRuns

/-!
# Delivery does not determine the atomicity boundary

Two independent takes have the same net effect as their batch. An observer
inserted between the takes can nevertheless see an intermediate store that
is unavailable at either boundary of the batch. All controls use the existing
occurrence-commit run relation, not an alternative definition of firing.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.AtomicObservation

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

def label (occurrence : Nat) : Nat := occurrence
def takeFirst : Commit Nat Nat := Commit.takeOne 0
def takeSecond : Commit Nat Nat := Commit.takeOne 1
def middleQuery : Commit Nat Nat := ⟨∅, ∅, ∅, [⟨fun _ => true, {1}⟩]⟩
def start : RunState Nat Nat := RunState.start {0, 1}

theorem sequential_is_valid :
    RunValid label start [.fire takeFirst, .observe middleQuery, .fire takeSecond] := by
  simp only [RunValid, Valid]
  decide

theorem batch_is_valid : Valid label start (.batch [takeFirst, takeSecond]) := by
  refine ⟨?_, by decide, ?_, ?_⟩
  · intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · simp [List.pairwise_cons, Clash, takeFirst, takeSecond, Commit.takeOne]
  · exact .cons (by decide) (.cons (by decide) (.nil _))

theorem same_final_store :
    (final start [.fire takeFirst, .observe middleQuery, .fire takeSecond]).store =
      (next start (.batch [takeFirst, takeSecond])).store := by decide

theorem observer_cannot_run_before_batch : ¬ Valid label start (.observe middleQuery) := by
  simp only [Valid]
  decide

theorem observer_cannot_run_after_batch :
    ¬ Valid label (next start (.batch [takeFirst, takeSecond])) (.observe middleQuery) := by
  simp only [Valid]
  decide

/-- Final-store equality therefore does not justify removing the gap. -/
theorem collection_is_not_an_atomicity_proof :
    RunValid label start [.fire takeFirst, .observe middleQuery, .fire takeSecond] ∧
      ¬ Valid label start (.observe middleQuery) ∧
      ¬ Valid label (next start (.batch [takeFirst, takeSecond])) (.observe middleQuery) :=
  ⟨sequential_is_valid, observer_cannot_run_before_batch, observer_cannot_run_after_batch⟩

end Mettapedia.Machines.StoreInteraction.AtomicObservation
