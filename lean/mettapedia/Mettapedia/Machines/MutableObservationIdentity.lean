import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Reference equality under future permitted writes

Current contents are not a sufficient identity for retained mutable values.
The observer reads a cell now or after any permitted write. Equality for all
those contexts is exactly identity, or equal contents in two cells neither
of which the observer can ever write. The permissions here are fixed; this
does not justify assuming that a currently absent write capability can never
be acquired later.

The final control distinguishes clearing an interning table from repairing
a representative already retained by a caller. This is a content/write
observation model, not a native allocator, state-cell codec or pointer-identity
semantics. The separate ResourceWeakInterning theory assumes immutable content.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MutableObservationIdentity

variable {Ref : Type} [DecidableEq Ref]

def SameObservations (heap : Ref → Nat) (writable : Ref → Prop) (left right : Ref) : Prop :=
  heap left = heap right ∧
    ∀ written, writable written → ∀ value,
      Function.update heap written value left = Function.update heap written value right

theorem same_observations_iff (heap : Ref → Nat) (writable : Ref → Prop) (left right : Ref) :
    SameObservations heap writable left right ↔
      left = right ∨ (¬ writable left ∧ ¬ writable right ∧ heap left = heap right) := by
  constructor
  · rintro ⟨now, later⟩
    by_cases equal : left = right
    · exact Or.inl equal
    · refine Or.inr ⟨?_, ?_, now⟩
      · intro canWrite
        have changed := later left canWrite (heap right + 1)
        simp [Function.update, Ne.symm equal] at changed
      · intro canWrite
        have changed := later right canWrite (heap left + 1)
        simp [Function.update, equal] at changed
  · rintro (rfl | ⟨leftReadOnly, rightReadOnly, now⟩)
    · exact ⟨rfl, fun _ _ _ => rfl⟩
    · refine ⟨now, ?_⟩
      intro written permitted value
      have leftApart : left ≠ written := by rintro rfl; exact leftReadOnly permitted
      have rightApart : right ≠ written := by rintro rfl; exact rightReadOnly permitted
      simpa [Function.update, leftApart, rightApart] using now

/-- With unrestricted mutation, equal observations force equal references.
An interner based only on current contents cannot establish this law. -/
theorem unrestricted_iff_identity (heap : Ref → Nat) (left right : Ref) :
    SameObservations heap (fun _ => True) left right ↔ left = right := by
  rw [same_observations_iff]
  simp

def writes (heap : Ref → Nat) : List (Ref × Nat) → Ref → Nat
  | [] => heap
  | (address, value) :: rest => writes (Function.update heap address value) rest

theorem protected_read_unchanged (heap : Ref → Nat) (history : List (Ref × Nat)) (address : Ref)
    (apart : ∀ event ∈ history, event.1 ≠ address) : writes heap history address = heap address := by
  induction history generalizing heap with
  | nil => rfl
  | cons event history ih =>
      rw [writes, ih _ (fun other member => apart other (List.mem_cons_of_mem _ member))]
      exact Function.update_of_ne (Ne.symm (apart event (List.mem_cons_self))) _ _

/-- The one-write characterization is also sufficient for every finite
history of writes under the same fixed permission policy. -/
theorem same_observations_history (heap : Ref → Nat) (writable : Ref → Prop)
    {left right : Ref} (same : SameObservations heap writable left right)
    (history : List (Ref × Nat)) (permitted : ∀ event ∈ history, writable event.1) :
    writes heap history left = writes heap history right := by
  rcases (same_observations_iff heap writable left right).mp same with rfl | ⟨l, r, now⟩
  · rfl
  · rw [protected_read_unchanged heap history left (fun event member equal =>
        l (equal ▸ permitted event member)),
      protected_read_unchanged heap history right (fun event member equal =>
        r (equal ▸ permitted event member))]
    exact now

namespace Controls

def before : Nat → Nat := fun _ => 1
def after : Nat → Nat := Function.update before 0 2

theorem equal_contents_do_not_authorize_representative_change :
    before 0 = before 1 ∧ after 0 ≠ after 1 ∧
      ¬ SameObservations before (fun _ => True) 0 1 := by
  constructor
  · rfl
  constructor
  · decide +kernel
  · rw [unrestricted_iff_identity]
    decide

theorem permanently_readonly_equal_cells_can_share_content_observation :
    SameObservations before (fun address => address = 2) 0 1 := by
  rw [same_observations_iff]
  exact Or.inr ⟨by decide, by decide, rfl⟩

structure Caller where
  expected : Nat
  cache : List Nat
  deriving DecidableEq

def clearCache (caller : Caller) : Caller := {caller with cache := []}
def accepts (heap : Nat → Nat) (caller : Caller) (candidate : Nat) : Bool :=
  heap caller.expected == heap candidate

def original : Caller := ⟨1, [0, 1]⟩
def substituted : Caller := ⟨0, [0, 1]⟩

/-- Both representatives looked equal when returned. Clearing the table
does not repair the different reference already retained by the caller. -/
theorem clearing_cache_does_not_repair_published_reference :
    accepts before original 1 = accepts before substituted 1 ∧
      accepts after (clearCache original) 1 = true ∧
      accepts after (clearCache substituted) 1 = false := by decide +kernel

end Controls

end Mettapedia.Machines.MutableObservationIdentity
