import Mathlib.Tactic

/-!
# Publishing capacity for parallel arrays

A shared capacity licenses indexing both arrays. Growing the first array
does not license publishing that capacity before the second growth succeeds.
On refusal the first private allocation may remain larger; retaining the old
published bound is sufficient for safe retry. This models capacities, not
native pointer validity, contents, ownership, allocator liveness or overflow.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PairedArrayAdmission

structure State where
  live : Nat
  published : Nat
  valuesCapacity : Nat
  framesCapacity : Nat
  deriving DecidableEq

def Valid (s : State) : Prop :=
  s.live ≤ s.published ∧ s.published ≤ s.valuesCapacity ∧ s.published ≤ s.framesCapacity

/-- Allocations are allowed to grow independently. The shared bound is
published only after both success reports; failure retains the old bound. -/
def reserve (requested : Nat) (valuesOK framesOK : Bool) (s : State) : Bool × State :=
  let values := if valuesOK then max requested s.valuesCapacity else s.valuesCapacity
  let frames := if valuesOK && framesOK then max requested s.framesCapacity else s.framesCapacity
  let success := valuesOK && framesOK
  (success, { s with
    valuesCapacity := values
    framesCapacity := frames
    published := if success then max requested s.published else s.published })

theorem reserve_valid (requested : Nat) (valuesOK framesOK : Bool) (s : State) (valid : Valid s) :
    Valid (reserve requested valuesOK framesOK s).2 := by
  rcases valid with ⟨live, values, frames⟩
  cases valuesOK <;> cases framesOK <;> simp only [reserve, Valid, Bool.false_and,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem refusal_preserves_public_bound (requested : Nat) (valuesOK framesOK : Bool) (s : State)
    (refused : (reserve requested valuesOK framesOK s).1 = false) :
    (reserve requested valuesOK framesOK s).2.published = s.published ∧
    (reserve requested valuesOK framesOK s).2.live = s.live := by
  cases valuesOK <;> cases framesOK <;> simp_all [reserve]

theorem success_has_room (requested : Nat) (s : State) :
    requested ≤ (reserve requested true true s).2.published := by
  simp [reserve]

def allocate (s : State) : Option (Nat × State) :=
  if s.live < s.published then some (s.live, { s with live := s.live + 1 }) else none

theorem allocated_index_safe (before after : State) (index : Nat) (valid : Valid before)
    (accepted : allocate before = some (index, after)) :
    index < before.valuesCapacity ∧ index < before.framesCapacity ∧ Valid after := by
  unfold allocate at accepted
  split at accepted <;> try contradiction
  rename_i room
  cases accepted
  rcases valid with ⟨live, values, frames⟩
  simp only [Valid]
  omega

namespace Controls

def full : State := ⟨16, 16, 16, 16⟩

theorem original_valid : Valid full := by simp [Valid, full]

theorem early_capacity_publication_is_unsafe :
    let bad : State := ⟨16, 32, 32, 16⟩
    ¬ Valid bad ∧ allocate bad = some (16, ⟨17, 32, 32, 16⟩) ∧
      ¬ 16 < bad.framesCapacity := by simp [Valid, allocate]

theorem partial_growth_can_safely_survive_refusal :
    reserve 32 true false full = (false, ⟨16, 16, 32, 16⟩) ∧
    allocate (reserve 32 true false full).2 = none ∧
    (reserve 32 true true (reserve 32 true false full).2).2 = ⟨16, 32, 32, 32⟩ := by decide

end Controls

#print axioms reserve_valid
#print axioms allocated_index_safe

end Mettapedia.Machines.PairedArrayAdmission
