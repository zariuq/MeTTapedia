import Mettapedia.Machines.CMemory.Array

/-!
# Positive and negative examples for the C memory model

**Positive.**

* Two arrays in separate blocks each take an append, and both appends are
  visible afterwards (`disjoint_arrays_both_append`).  This is the shape of
  CeTTa's publisher, which writes `importer->deps[...]` and
  `dependency->importers[...]` for each link.
* After a moving `realloc`, the same contents are found through the new
  pointer (`moved_contents_reachable_through_new_pointer`).

**Negative.**  Each of these is a program that C leaves undefined, and the
model has no safe execution for it:

* an interior pointer cached across a moving `realloc` dangles: loading
  through it, or even comparing it, is undefined
  (`interior_pointer_dangles_after_move`);
* double free (`double_free_undefined`);
* use after free (`use_after_free_undefined`);
* comparing a pointer into a freed block (`compare_after_free_undefined`);
* reading a fresh cell before writing it (`fresh_cell_read_undefined`);
* `realloc` of a live block to size zero (`realloc_zero_undefined`).

Aliasing: the precondition of the two-array write cannot hold when the two
arrays share a block (`aliased_arrays_unsatisfiable`), nor when two points-to
facts name one cell (`aliased_cells_unsatisfiable`).  The precondition is not
a formality: when two stores go through aliasing pointers, the first write is
lost (`aliased_stores_lose_first_write`).

Provenance: a block id is never reused, so `malloc` never returns a pointer
into a block whose death the caller holds (`malloc_never_reuses_dead_block`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.Examples

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open CellPermission

universe u

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-! ## Positive -/

/-- **Two arrays in separate blocks both take an append.** -/
theorem disjoint_arrays_both_append (p q : Ptr) (n m : ℕ) (xs ys : List V) (v w : V)
    (roomP : xs.length < n) (roomQ : ys.length < m) :
    CTriple (L := L) (DynArray (some p) n xs ∗ DynArray (some q) m ys)
      (CProg.store (p + xs.length) v >>= fun _ => CProg.store (q + ys.length) w)
      (fun _ => DynArray (some p) n (xs ++ [v]) ∗ DynArray (some q) m (ys ++ [w])) :=
  triple_bind _ (frame (store_append p n xs v roomP) _)
    fun _ => frame_left (store_append q m ys w roomQ) _

/-! ## The realloc hazard -/

section Move

variable (b : BlockId) (cs : List (Option V)) (n : ℕ)

/-- The memory of one live block holding `cs`. -/
abbrev blockMemory : Heap L := atBlock b (.own ⟨cs.length, true⟩, segment 0 (cs.map whole))

theorem next_block_ne (b : BlockId) : b ≠ b + 1 := Nat.ne_of_lt (Nat.lt_succ_self b)

/-- From one live block, `realloc` may move it to the next block id. -/
theorem realloc_may_move :
    (CProg.realloc (some ⟨b, 0⟩) n).Runs act (blockMemory (L := L) b cs) (some ⟨b + 1, 0⟩)
      ((blockMemory (L := L) b cs).move b cs.length (b + 1) n) :=
  prim_runs (Or.inr ⟨cs.length, b + 1, by simp, atBlock_other _ (next_block_ne b).symm, rfl, rfl⟩)

theorem moved_old_cell (k : ℕ) (inside : k < cs.length) :
    (((blockMemory (L := L) b cs).move b cs.length (b + 1) n) b).2 k = 0 := by
  simp only [Heap.move, Function.update_of_ne (next_block_ne b), Heap.kill,
    Function.update_self, Heap.killedBlock, if_pos inside]

theorem moved_old_header :
    (((blockMemory (L := L) b cs).move b cs.length (b + 1) n) b).1 =
      .own ⟨cs.length, false⟩ := by
  simp only [Heap.move, Function.update_of_ne (next_block_ne b), Heap.kill,
    Function.update_self, Heap.killedBlock]

/-- **Negative control: an interior pointer cached across a moving `realloc`
dangles.**  Loading through it is undefined, and so is comparing it, even with
null. -/
theorem interior_pointer_dangles_after_move (k : ℕ)
    (inside : k < cs.length) :
    ¬ (CProg.realloc (some ⟨b, 0⟩) n >>= fun _ => CProg.load (V := V) ⟨b, k⟩).Safe act
        (blockMemory (L := L) b cs) ∧
      ¬ (CProg.realloc (some ⟨b, 0⟩) n >>= fun _ =>
          CProg.ptrEq (V := V) (some ⟨b, k⟩) none).Safe act (blockMemory (L := L) b cs) := by
  constructor
  · refine not_safe_bind (realloc_may_move b cs n) ?_
    rintro ⟨⟨v, readV⟩, -⟩
    rw [moved_old_cell b cs n k inside, read_zero] at readV
    cases readV
  · refine not_safe_bind (realloc_may_move b cs n) ?_
    rintro ⟨⟨(⟨size, header, -⟩ | held), -⟩, -⟩
    · rw [moved_old_header] at header
      cases header
    · exact held (moved_old_cell b cs n k inside)

/-- **Positive control**: after the move, the contents are reachable through
the new pointer. -/
theorem moved_contents_reachable_through_new_pointer (k : ℕ) (inside : k < cs.length)
    (fits : k < n) :
    read ((((blockMemory (L := L) b cs).move b cs.length (b + 1) n) (b + 1)).2 k) =
      some cs[k] := by
  have atCell := segment_at (L := L) 0 (cs.map whole) (k := k) (by simpa using inside)
  simp only [Nat.zero_add, List.getElem_map] at atCell
  simp only [Heap.move, Function.update_self, Heap.grownBlock, atBlock_same,
    if_pos (And.intro inside fits), atCell, read_whole]

end Move

/-! ## Freeing -/

section Free

variable (b : BlockId) (n : ℕ)

theorem free_runs_to_dead {σ : Heap L} (holds : (LiveBlock b n ∗ CellsAny (V := V) ⟨b, 0⟩ n) σ) :
    ∃ σ', (CProg.free (V := V) (some ⟨b, 0⟩)).Runs act σ () σ' ∧ DeadBlock b n σ' := by
  obtain ⟨safe, post⟩ := free_spec (L := L) (V := V) b n σ holds
  obtain ⟨u, σ', runs⟩ := exists_runs _ σ safe
  exact ⟨σ', runs, post u σ' runs⟩

/-- **Negative control: double free is undefined.** -/
theorem double_free_undefined {σ : Heap L}
    (holds : (LiveBlock b n ∗ CellsAny (V := V) ⟨b, 0⟩ n) σ) :
    ¬ (CProg.free (V := V) (some ⟨b, 0⟩) >>= fun _ =>
        CProg.free (V := V) (some ⟨b, 0⟩)).Safe act σ := by
  obtain ⟨σ', runs, dead⟩ := free_runs_to_dead b n holds
  refine not_safe_bind runs ?_
  rintro ⟨⟨-, m, header, -⟩, -⟩
  rw [dead] at header
  simp only [atBlock_same] at header
  cases header

/-- **Negative control: use after free is undefined.** -/
theorem use_after_free_undefined {σ : Heap L} (k : ℕ)
    (holds : (LiveBlock b n ∗ CellsAny (V := V) ⟨b, 0⟩ n) σ) :
    ¬ (CProg.free (V := V) (some ⟨b, 0⟩) >>= fun _ => CProg.load (V := V) ⟨b, k⟩).Safe act σ := by
  obtain ⟨σ', runs, dead⟩ := free_runs_to_dead b n holds
  refine not_safe_bind runs ?_
  rintro ⟨⟨v, readV⟩, -⟩
  rw [dead] at readV
  simp only [atBlock_same] at readV
  rw [show ((0 : ℕ → L) k) = 0 from rfl, read_zero] at readV
  cases readV

/-- **Negative control: a pointer into a freed block cannot even be
compared.** -/
theorem compare_after_free_undefined {σ : Heap L} (k : ℕ)
    (holds : (LiveBlock b n ∗ CellsAny (V := V) ⟨b, 0⟩ n) σ) :
    ¬ (CProg.free (V := V) (some ⟨b, 0⟩) >>= fun _ =>
        CProg.ptrEq (V := V) (some ⟨b, k⟩) none).Safe act σ := by
  obtain ⟨σ', runs, dead⟩ := free_runs_to_dead b n holds
  refine not_safe_bind runs ?_
  rintro ⟨⟨(⟨size, header, -⟩ | held), -⟩, -⟩
  · rw [dead] at header
    simp only [atBlock_same] at header
    cases header
  · rw [dead] at held
    exact held (by simp)

/-- **Provenance: a dead block id is never reused.**  Whoever holds the dead
header of `b` never receives a pointer into `b` from `malloc`. -/
theorem malloc_never_reuses_dead_block (m : ℕ) {F : Heap L → Prop} {σ σ' : Heap L}
    {r : Option Ptr} (holds : (DeadBlock b n ∗ F) σ)
    (runs : (CProg.malloc (V := V) m).Runs act σ r σ') : ∀ p, r = some p → p.block ≠ b := by
  obtain ⟨r', σ₁, step, rfl, rfl⟩ := runs
  rintro p same rfl
  rcases step with ⟨rfl, -⟩ | ⟨b', fresh, rfl, -⟩
  · cases same
  · cases same
    obtain ⟨x, y, separate, rfl, rfl, -⟩ := holds
    have header := congrArg Prod.fst fresh
    simp only [heap_add_header, atBlock_same, Prod.fst_zero] at header
    cases header

end Free

/-! ## Indeterminate values and size zero -/

/-- **Negative control: a fresh cell holds an indeterminate value, and reading
it is undefined.** -/
theorem fresh_cell_read_undefined (n : ℕ) (positive : 0 < n) :
    ¬ (CProg.malloc (V := V) n >>= fun r => match r with
        | none => pure ()
        | some p => CProg.load (V := V) p >>= fun _ => pure ()).Safe act (0 : Heap L) := by
  have runs : (CProg.malloc (V := V) n).Runs act (0 : Heap L) (some ⟨0, 0⟩)
      (Function.update 0 0 (freshBlock n)) :=
    prim_runs (Or.inr ⟨0, rfl, rfl, rfl⟩)
  refine not_safe_bind runs ?_
  rintro ⟨⟨v, readV⟩, -⟩
  simp only [Function.update_self, freshBlock, if_pos positive, read_whole] at readV
  cases readV

/-- **Negative control: `realloc` of a live block to size zero is undefined**
(C23 7.24.3.7). -/
theorem realloc_zero_undefined (p : Ptr) (σ : Heap L) :
    ¬ (CProg.realloc (V := V) (some p) 0).Safe act σ :=
  fun ⟨⟨positive, _⟩, _⟩ => Nat.lt_irrefl 0 positive

/-! ## Aliasing -/

/-- **Negative control**: two arrays in one block cannot be held separately. -/
theorem aliased_arrays_unsatisfiable (p : Ptr) (n m : ℕ) (xs ys : List V) (σ : Heap L) :
    ¬ (DynArray (some p) n xs ∗ DynArray (some p) m ys) σ :=
  dynArray_sepConj_self_false p n m xs ys σ

/-- **Negative control**: two points-to facts never name one cell. -/
theorem aliased_cells_unsatisfiable (p : Ptr) (v w : V) (σ : Heap L) :
    ¬ (PointsTo (L := L) p v ∗ PointsTo p w) σ :=
  pointsTo_sepConj_self_false p v w σ

/-- **Negative control: two stores through aliasing pointers lose the first
write.**  Reading the cell afterwards returns the second value, so a
specification promising both writes needs the separate precondition. -/
theorem aliased_stores_lose_first_write (p : Ptr) (v w : V) :
    CTriple (L := L) (PointsToAny p)
      (CProg.store p v >>= fun _ => CProg.store p w >>= fun _ => CProg.load p)
      (fun r σ => r = w ∧ PointsTo p w σ) := by
  refine triple_bind _ (store_spec p v) fun _ => ?_
  refine triple_bind _ (triple_pre _ (fun σ holds => ⟨some v, holds⟩) (store_spec p w))
    fun _ => ?_
  refine load_rule fun σ holds => ?_
  have framed : (PointsTo (L := L) p w ∗ emp) σ := by
    rw [sepConj_emp]
    exact holds
  exact read_of_pointsTo framed

end Mettapedia.Machines.CMemory.Examples
