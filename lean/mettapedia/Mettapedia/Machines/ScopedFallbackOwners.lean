import Mathlib.Tactic
import Mettapedia.Machines.NestedSafePoints

/-!
# Owners of pointer-backed stored values

The term store can own an opaque value without placing that value in an
arena retained for the whole session. A live entry owns its image. An arena
that borrows the image acquires a separate hold; retiring the entry therefore
does not invalidate the borrower. Dropping the final hold permits reclamation.

This model concerns image lifetime, not the encoding or copying of its value,
nor permission to transport an opaque resource to a different host context.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedFallbackOwners

variable {Owner : Type} [DecidableEq Owner]

structure State (Owner : Type) where
  entries : Finset Owner
  readers : Finset (ℕ × Owner)
  storage : Finset Owner

def readersOf (s : State Owner) : Finset Owner := s.readers.image Prod.snd

def held (s : State Owner) : Finset Owner := s.entries ∪ readersOf s

def Inv (s : State Owner) : Prop := held s ⊆ s.storage

def store (s : State Owner) (owner : Owner) : State Owner :=
  { s with entries := insert owner s.entries, storage := insert owner s.storage }

def borrow (s : State Owner) (arena : ℕ) (owner : Owner) : State Owner :=
  if owner ∈ s.entries then { s with readers := insert (arena, owner) s.readers } else s

def retire (s : State Owner) (owner : Owner) : State Owner :=
  { s with entries := s.entries.erase owner }

def release (s : State Owner) (arena : ℕ) (owner : Owner) : State Owner :=
  { s with readers := s.readers.erase (arena, owner) }

def collect (s : State Owner) : State Owner :=
  { s with storage := s.storage ∩ held s }

theorem store_inv (s : State Owner) (safe : Inv s) (owner : Owner) :
    Inv (store s owner) := by
  intro o ho
  simp only [store, held, readersOf, Finset.mem_union, Finset.mem_insert] at ho ⊢
  rcases ho with (rfl | old) | reader
  · exact Or.inl rfl
  · exact Or.inr (safe (Finset.mem_union_left _ old))
  · exact Or.inr (safe (Finset.mem_union_right _ reader))

theorem borrow_inv (s : State Owner) (safe : Inv s) (arena : ℕ) (owner : Owner) :
    Inv (borrow s arena owner) := by
  by_cases source : owner ∈ s.entries
  · rw [borrow, if_pos source]
    intro o ho
    simp only [held, readersOf,
      Finset.image_insert, Finset.mem_union, Finset.mem_insert] at ho
    rcases ho with entry | (rfl | reader)
    · exact safe (Finset.mem_union_left _ entry)
    · exact safe (Finset.mem_union_left _ source)
    · exact safe (Finset.mem_union_right _ reader)
  · simpa [borrow, source] using safe

theorem retire_inv (s : State Owner) (safe : Inv s) (owner : Owner) :
    Inv (retire s owner) := by
  intro o ho
  rcases Finset.mem_union.mp ho with entry | reader
  · exact safe (Finset.mem_union_left _ (Finset.mem_erase.mp entry).2)
  · exact safe (Finset.mem_union_right _ reader)

theorem release_inv (s : State Owner) (safe : Inv s) (arena : ℕ) (owner : Owner) :
    Inv (release s arena owner) := by
  intro o ho
  rcases Finset.mem_union.mp ho with entry | reader
  · exact safe (Finset.mem_union_left _ entry)
  · obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp reader
    exact safe (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨pair, (Finset.mem_erase.mp hp).2, rfl⟩))

theorem collect_inv (s : State Owner) (safe : Inv s) : Inv (collect s) := by
  intro owner member
  exact Finset.mem_inter.mpr ⟨safe member, member⟩

theorem borrowed_image_survives_retirement (s : State Owner) (safe : Inv s)
    (arena : ℕ) (owner : Owner) (source : owner ∈ s.entries) :
    owner ∈ (collect (retire (borrow s arena owner) owner)).storage := by
  rw [borrow, if_pos source]
  refine Finset.mem_inter.mpr ⟨safe (Finset.mem_union_left _ source), ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(arena, owner), Finset.mem_insert_self .., rfl⟩)

theorem no_holders_reclaims (s : State Owner) (owner : Owner)
    (no_entry : owner ∉ s.entries) (no_reader : owner ∉ readersOf s) :
    owner ∉ (collect s).storage := by
  simp [collect, held, no_entry, no_reader]

theorem missing_entry_cannot_borrow (s : State Owner) (arena : ℕ) (owner : Owner)
    (absent : owner ∉ s.entries) : borrow s arena owner = s := by
  simp [borrow, absent]

/-- A process-lifetime arena retains each fresh image, even after its row
has been removed. This is the leaking loop's allocation history. -/
def permanentLoop : ℕ → List ℕ
  | 0 => []
  | n + 1 => n :: permanentLoop n

theorem permanentLoop_length (n : ℕ) : (permanentLoop n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [permanentLoop, ih]

/-- The same allocation history is reclaimable when no entry or receiving
arena still owns it. The heap's contents, not its history, determine retention. -/
theorem retired_batch_reclaims (images : Finset Owner) :
    (collect (State.mk ∅ ∅ images)).storage = ∅ := by
  simp [collect, held, readersOf]

/-- Each step creates and retires one entry. Collection runs every `window`
steps, using the actual owner-set collector with no remaining borrowers. -/
def pacedLoop (window steps : ℕ) : Finset ℕ :=
  (NestedSafePoints.run window (fun n => {n})
    (fun _ s => (collect (State.mk ∅ ∅ s)).storage) ∅ steps).1

theorem pacedLoop_bound (window steps : ℕ) (positive : 0 < window) :
    (pacedLoop window steps).card ≤ window - 1 := by
  have bound := NestedSafePoints.run_card_le window 0 1 positive
    (fun n => ({n} : Finset ℕ))
    (fun _ s => (collect (State.mk ∅ ∅ s)).storage) ∅
    (by simp)
    (by intro _ s; simp [retired_batch_reclaims])
    (by intro _; simp) steps
  simpa [pacedLoop] using bound

example :
    7 ∈ (collect (retire (borrow (store (State.mk ∅ ∅ ∅) 7) 3 7) 7)).storage := by
  decide

example :
    (collect (release (retire (borrow (store (State.mk ∅ ∅ ∅) 7) 3 7) 7) 3 7)).storage =
      (∅ : Finset ℕ) := by
  decide

end Mettapedia.Machines.ScopedFallbackOwners
