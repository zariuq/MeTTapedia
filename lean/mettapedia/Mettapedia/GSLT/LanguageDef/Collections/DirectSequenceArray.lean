import Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

/-!
# Direct backing-array operations implement the sequence reference view

The reference array semantics uses extraction to describe a slice. Its
semantic equations do not require constructing that extraction at runtime.
This implementation checks the logical bound and loads the retained backing
array at the translated offset. It neither extracts the slice nor enumerates
its preceding elements.

The equivalence is at the existing GSLT observation. Counting one declared
array operation is still distinct from counting native instructions or time.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.DirectSequenceArray

open CArray0SequenceHosting
open Mettapedia.GSLT.LanguageDef.ObservationRefinement
open Mettapedia.GSLT.LanguageDef.GSLTHosting

variable {α : Type}

def load (slice : StackSlice α) (index : Nat) : Option α :=
  if inside : index < slice.count then
    some (slice.cells[slice.start + index]'(by have := slice.inBounds; omega))
  else none

theorem load_eq_reference (slice : StackSlice α) (index : Nat) :
    load slice index = slice.toArray[index]? := by
  unfold StackSlice.toArray
  rw [Array.getElem?_extract, Nat.min_eq_left slice.inBounds, Nat.add_sub_cancel_left]
  by_cases inside : index < slice.count
  · have safe : slice.start + index < slice.cells.size := by have := slice.inBounds; omega
    simp [load, inside, Array.getElem?_eq_getElem safe]
  · simp [load, inside]

def run : ArrayInstruction → StackSlice α → ArrayOutcome α
  | .count, slice => .count slice.count
  | .loadFirst, slice =>
      match load slice 0 with
      | some value => .element value
      | none => .declined
  | .advance, slice =>
      if nonempty : 0 < slice.count then .slice (slice.advance nonempty) else .declined
  | .loadAt index, slice =>
      match load slice index with
      | some value => .element value
      | none => .declined

theorem run_eq_reference (instruction : ArrayInstruction) (slice : StackSlice α) :
    run instruction slice = arraySem instruction slice := by
  cases instruction with
  | count => rfl
  | advance => rfl
  | loadFirst =>
      simp only [run, arraySem, load_eq_reference]
      cases slice.toArray[0]? <;> rfl
  | loadAt index =>
      simp only [run, arraySem, load_eq_reference]
      cases slice.toArray[index]? <;> rfl

def observe : ArrayTerm α → Option (SequenceObservation α)
  | .start _ _ => none
  | .halted instruction slice => some (arrayOutcomeObservation (run instruction slice))

theorem observe_eq_reference (term : ArrayTerm α) : observe term = arrayObserve term := by
  cases term <;> simp [observe, arrayObserve, run_eq_reference]

def target (α : Type) : ObservedOperationalObject (SequenceObservation α) where
  operational := (targetObject α).operational
  observe := fun {_ last} _ => observe last

/-- The direct operations have the same two-sided GSLT hosting theorem as
the independent reference view. This retains the original source calculus. -/
theorem hosting_exact (initial : SequenceTerm α) (value : SequenceObservation α) :
    ProducesObservation (target α) (compileTerm initial) value ↔
      ProducesObservation (sourceObject α) initial value := by
  constructor
  · rintro ⟨⟨last, path, observed⟩⟩
    change ArrayTerm α at last
    apply (CArray0SequenceHosting.hosting_exact initial value).mp
    change observe last = some value at observed
    rw [observe_eq_reference] at observed
    exact ⟨⟨last, path, observed⟩⟩
  · intro produced
    obtain ⟨⟨last, path, observed⟩⟩ :=
      (CArray0SequenceHosting.hosting_exact initial value).mpr produced
    change ArrayTerm α at last
    refine ⟨⟨last, path, ?_⟩⟩
    change observe last = some value
    rw [observe_eq_reference]
    exact observed

namespace Controls

def middle : StackSlice Nat := ⟨#[7, 8, 9, 10], 1, 2, by decide⟩

theorem offset_and_bound : load middle 0 = some 8 ∧ load middle 1 = some 9 ∧
    load middle 2 = none := by decide

theorem wrong_offset_changes_value : middle.cells[0]? = some 7 ∧ load middle 0 = some 8 := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.DirectSequenceArray
