import Mettapedia.Machines.CMemory.Array
import Mettapedia.GSLT.Logic.SymbolicHeap

/-!
# Weakest-precondition rules for C programs over block memory

The generic calculus (`GSLT.Logic.WeakestPrecondition`) and the symbolic-heap
judgments (`GSLT.Logic.SymbolicHeap`), instantiated for the seven C memory
primitives.  Every rule below is derived from the small axioms of
`CMemory.Assertions` and the frame rule `CMemory.frame`; none is assumed.

**Locality.**  `instLocalSignature`: the C signature is a signature of local
actions (`act_local`), so `wp_call_framed` and the tactic `sep_call` apply to
every C program.  `instWellFormedInvariant`: the well-formedness of the whole
of memory is a step invariant (`act_wellFormed`), so a proof that holds
`WellFormed σ` beside its separating conjunction keeps it across calls.

**Observations.**  `Reads p v`: the cell at `p` holds the initialized value
`v` for its holder.  `ValidAt p`: `p` is a valid pointer.  `HeldFrom p`: a
cell of `p`'s block at or after `p` is held, which in well-formed memory makes
`p` valid (`valid_of_wellFormed_heldFrom`), as for the base pointer of a struct
whose field is held.  All three survive framing, so they are read off any one
conjunct of the current state.

**Rules for the primitives.**

* `wp_load`: a load returns the value the state reads at its address;
* `wp_store`: a store needs the whole cell, `PointsToAny p`, split off the
  state, and leaves `PointsTo p v` beside the same frame;
* `wp_ptrEq`: a comparison needs both pointers valid or null, from a conjunct
  (`validOpt_some`) or, in well-formed memory, from a held cell of the block
  (`validOpt_some_wellFormed`);
* `wp_undefined`: undefined behaviour has no weakest precondition but `False`;
* `wp_free_none`: freeing null does nothing;
* allocation, `free` and `realloc` of a block are framed calls of their small
  axioms (`malloc_spec`, `free_spec`, `realloc_spec`, `realloc_dynArray`).

**Atom lemmas** for the assertions of `CMemory`: a points-to cell reads its
value, is valid, and is held for the pointers before it in its block; an
element of a dynamic array reads its value; a dynamic array's base pointer and
its live bounds are valid; and the pure facts of a dynamic array.
`CMemory.Tactic` registers them with the search tactics.

## Examples

* **Positive.**  Loads, stores and comparisons against cells beside a frame
  (`AutomationExamples.increment_spec`, `swap_spec`,
  `base_comparison_after_store`), and the re-proofs of `reserve_spec` and
  `publish_refines` in `CMemory.AutomationExamples`.
* **Negative.**  A load of an indeterminate cell has no weakest precondition
  (`Controls.load_indeterminate_not_wp`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

section Rules

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-- The C primitives are local actions. -/
instance instLocalSignature : LocalSignature (act (L := L) (V := V)) :=
  ⟨act_local⟩

/-- The well-formedness of the whole of memory is preserved by every
primitive step, so proofs may carry it beside the separating conjunction. -/
instance instWellFormedInvariant : StepInvariant (act (L := L) (V := V)) WellFormed :=
  ⟨fun o _ _ _ wellFormed safe step => act_wellFormed wellFormed o safe step⟩

/-! ## Observations -/

/-- **The cell at `p` holds the initialized value `v`**, for its holder. -/
def Reads (p : Ptr) (v : V) : Heap L → Prop :=
  fun σ => read ((σ p.block).2 p.offset) = some (some v)

/-- **`p` is a valid pointer**: comparison evidence. -/
def ValidAt (p : Ptr) : Heap L → Prop :=
  fun σ => Valid σ p

theorem reads_persistent (p : Ptr) (v : V) : Persistent (Reads (L := L) p v) := by
  intro x y separate holds
  change read (((x + y) p.block).2 p.offset) = some (some v)
  rw [heap_add_cell]
  exact read_add ((separate p.block).2 p.offset) holds

/-- **Some cell of `p`'s block, at or after `p`, is held.**  In well-formed
memory this makes `p` valid (`valid_of_wellFormed_heldFrom`): the block of a
held cell is live and larger than its offset.  It is how the base pointer of a
struct is valid to a holder of one of its fields. -/
def HeldFrom (p : Ptr) : Heap L → Prop :=
  fun σ => ∃ i, p.offset ≤ i ∧ (σ p.block).2 i ≠ 0

omit [CellPermission L (Option V)] in
theorem heldFrom_persistent (p : Ptr) [CellPermission L (Option V)] :
    Persistent (HeldFrom (L := L) p) := by
  rintro x y separate ⟨i, after, held⟩
  exact ⟨i, after, by
    rw [heap_add_cell]
    exact add_ne_zero_of_ne_zero (C' := Option V) ((separate p.block).2 i) held⟩

omit [Add L] [SepAlgebra L] [CellPermission L (Option V)] in
/-- In well-formed memory, a held cell at or after `p` in its block makes `p`
valid. -/
theorem valid_of_wellFormed_heldFrom {σ : Heap L} {p : Ptr} (wellFormed : WellFormed σ)
    (held : HeldFrom p σ) : Valid σ p := by
  obtain ⟨i, after, nonzero⟩ := held
  obtain ⟨n, header, inside⟩ := wellFormed p.block i nonzero
  exact Or.inl ⟨n, header, by omega⟩

omit [CellPermission L (Option V)] in
theorem validAt_persistent (p : Ptr) [CellPermission L (Option V)] :
    Persistent (ValidAt (L := L) p) :=
  fun _ _ separate valid => Valid.frame (C := Option V) separate valid

/-! ## Rules for the primitives -/

/-- **Load**: the result is the value the state reads at the address. -/
theorem wp_load {T : Heap L → Prop} {p : Ptr} {v : V} {Q : V → Heap L → Prop} {σ : Heap L}
    (holds : T σ) (reads : Ensures T (Reads p v)) (post : Q v σ) :
    (CProg.load p).wp act Q σ := by
  have readV : read ((σ p.block).2 p.offset) = some (some v) := reads.apply holds
  refine (wp_prim (act (L := L) (V := V)) (Op.load p) Q σ).mpr ⟨⟨v, readV⟩, ?_⟩
  rintro r σ' ⟨readR, rfl⟩
  rw [readV] at readR
  cases readR
  exact post

/-- **Store**: split the whole cell off the state; the frame is untouched. -/
theorem wp_store {T F : Heap L → Prop} {p : Ptr} {v : V} {Q : Unit → Heap L → Prop}
    {σ : Heap L} (holds : T σ) (split : Splits T (PointsToAny p) F)
    (post : ∀ σ', (PointsTo p v ∗ F) σ' → Q () σ') : (CProg.store p v).wp act Q σ :=
  wp_call_split act (store_spec p v) holds split fun _ σ' after => post σ' after

/-- **Pointer comparison** of pointers that are valid or null. -/
theorem wp_ptrEq {p q : Option Ptr} {Q : Bool → Heap L → Prop} {σ : Heap L}
    (validP : ValidOpt σ p) (validQ : ValidOpt σ q) (post : Q (decide (p = q)) σ) :
    (CProg.ptrEq (V := V) p q).wp act Q σ := by
  refine (wp_prim (act (L := L) (V := V)) (Op.ptrEq p q) Q σ).mpr ⟨⟨validP, validQ⟩, ?_⟩
  rintro r σ' ⟨rfl, rfl⟩
  exact post

/-- **Undefined behaviour** meets no postcondition from any state. -/
theorem wp_undefined {α : Type} (Q : α → Heap L → Prop) (σ : Heap L) :
    (CProg.undefined (V := V) : CProg V α).wp act Q σ ↔ False := by
  rw [CProg.undefined, wp_call]
  exact ⟨fun holds => holds.1, False.elim⟩

/-- Freeing null does nothing. -/
theorem wp_free_none (Q : Unit → Heap L → Prop) (σ : Heap L) :
    (CProg.free (V := V) none).wp act Q σ ↔ Q () σ := by
  refine (wp_prim (act (L := L) (V := V)) (Op.free none) Q σ).trans ?_
  constructor
  · rintro ⟨-, post⟩
    exact post () σ rfl
  · intro holds
    exact ⟨trivial, by rintro ⟨⟩ σ' rfl; exact holds⟩

omit [Add L] [SepAlgebra L] [CellPermission L (Option V)] in
theorem validOpt_none (σ : Heap L) : ValidOpt σ none :=
  trivial

omit [Add L] [SepAlgebra L] [CellPermission L (Option V)] in
theorem validOpt_some {T : Heap L → Prop} {p : Ptr} {σ : Heap L} (holds : T σ)
    (valid : Ensures T (ValidAt p)) : ValidOpt σ (some p) :=
  valid.apply holds

omit [Add L] [SepAlgebra L] [CellPermission L (Option V)] in
/-- A pointer is valid in well-formed memory when a cell at or after it in its
block is held. -/
theorem validOpt_some_wellFormed {T : Heap L → Prop} {p : Ptr} {σ : Heap L}
    (wellFormed : WellFormed σ) (holds : T σ) (held : Ensures T (HeldFrom p)) :
    ValidOpt σ (some p) :=
  valid_of_wellFormed_heldFrom wellFormed (held.apply holds)

/-! ## Atom lemmas -/

theorem ensures_reads_pointsTo (p : Ptr) (v : V) : Ensures (PointsTo (L := L) p v) (Reads p v) := by
  refine ⟨fun σ holds => ?_⟩
  have framed : (PointsTo (L := L) p v ∗ emp) σ := by rw [sepConj_emp]; exact holds
  exact read_of_pointsTo framed

theorem ensures_valid_pointsTo (p : Ptr) (v : V) :
    Ensures (PointsTo (L := L) p v) (ValidAt p) := by
  refine ⟨fun σ holds => ?_⟩
  have framed : (PointsTo (L := L) p v ∗ emp) σ := by rw [sepConj_emp]; exact holds
  exact valid_of_pointsTo framed

/-- A points-to cell is held, for every pointer at or before it in its block. -/
theorem ensures_heldFrom_pointsTo (q : Ptr) (v : V) (p : Ptr) (sameBlock : q.block = p.block)
    (after : p.offset ≤ q.offset) : Ensures (PointsTo (L := L) q v) (HeldFrom p) := by
  refine ⟨fun σ holds => ⟨q.offset, after, ?_⟩⟩
  have framed : (PointsTo (L := L) q v ∗ emp) σ := by rw [sepConj_emp]; exact holds
  have readV := read_of_pointsTo framed
  rw [← sameBlock]
  exact read_ne_zero readV

/-- An initialized cell of a range reads its value. -/
theorem ensures_reads_cells (p : Ptr) (xs : List V) (i : ℕ) (inside : i < xs.length) :
    Ensures (Cells (L := L) p (xs.map some)) (Reads (p + i) xs[i]) := by
  refine ⟨fun σ held => ?_⟩
  have framed : (Cells (L := L) p (xs.map some) ∗ emp) σ := by
    rw [sepConj_emp]
    exact held
  exact read_cells (by simpa using inside) (by simp) framed

/-- **An element of a dynamic array** reads its value. -/
theorem ensures_reads_dynArray (p : Ptr) (cap : ℕ) (xs : List V) (i : ℕ)
    (inside : i < xs.length) :
    Ensures (DynArray (L := L) (some p) cap xs) (Reads (p + i) xs[i]) := by
  refine ⟨?_⟩
  rintro σ ⟨-, -, held⟩
  refine (Ensures.right (reads_persistent _ _) (Ensures.left (reads_persistent _ _) ?_)).apply
    held
  exact ensures_reads_cells p xs i inside

theorem ptr_add_zero (p : Ptr) : p + 0 = p :=
  rfl

/-- The first element of a dynamic array, at its base pointer. -/
theorem ensures_reads_dynArray_base (p : Ptr) (cap : ℕ) (xs : List V) (nonempty : 0 < xs.length) :
    Ensures (DynArray (L := L) (some p) cap xs) (Reads p xs[0]) := by
  have element := ensures_reads_dynArray (L := L) p cap xs 0 nonempty
  rwa [ptr_add_zero] at element

omit [CellPermission L (Option V)] in
/-- A live block makes every pointer into it, or one past its end, valid. -/
theorem ensures_valid_liveBlock [CellPermission L (Option V)] (b : BlockId) (n k : ℕ)
    (inside : k ≤ n) : Ensures (LiveBlock (L := L) b n) (ValidAt ⟨b, k⟩) := by
  refine ⟨fun σ holds => ?_⟩
  have framed : (LiveBlock (L := L) b n ∗ emp) σ := by rw [sepConj_emp]; exact holds
  exact valid_of_liveBlock (C := Option V) framed inside

/-- Every pointer into a dynamic array, or one past its end, is valid. -/
theorem ensures_valid_dynArray (p : Ptr) (cap : ℕ) (xs : List V) (k : ℕ) (inside : k ≤ cap) :
    Ensures (DynArray (L := L) (some p) cap xs) (ValidAt (p + k)) := by
  refine ⟨?_⟩
  rintro σ ⟨base, -, held⟩
  obtain ⟨b, offset⟩ := p
  simp only at base
  subst base
  refine (Ensures.left (validAt_persistent (V := V) _) ?_).apply held
  have shifted : (⟨b, 0⟩ : Ptr) + k = ⟨b, k⟩ := by
    change (⟨b, 0 + k⟩ : Ptr) = ⟨b, k⟩
    rw [Nat.zero_add]
  rw [shifted]
  exact ensures_valid_liveBlock (L := L) (V := V) b cap k inside

/-- The base pointer of a dynamic array is valid. -/
theorem ensures_valid_dynArray_base (p : Ptr) (cap : ℕ) (xs : List V) :
    Ensures (DynArray (L := L) (some p) cap xs) (ValidAt p) := by
  have base := ensures_valid_dynArray (L := L) p cap xs 0 (Nat.zero_le _)
  rwa [ptr_add_zero] at base

theorem ensures_dynArray_offset (p : Ptr) (cap : ℕ) (xs : List V) :
    Ensures (DynArray (L := L) (some p) cap xs) (fun _ => p.offset = 0) :=
  ⟨fun _ holds => holds.1⟩

theorem ensures_dynArray_length (p : Ptr) (cap : ℕ) (xs : List V) :
    Ensures (DynArray (L := L) (some p) cap xs) (fun _ => xs.length ≤ cap) :=
  ⟨fun _ holds => holds.2.1⟩

theorem ensures_dynArray_none_contents (cap : ℕ) (xs : List V) :
    Ensures (DynArray (L := L) none cap xs) (fun _ => xs = []) :=
  ⟨fun _ holds => holds.2.1⟩

theorem ensures_dynArray_none_capacity (cap : ℕ) (xs : List V) :
    Ensures (DynArray (L := L) none cap xs) (fun _ => cap = 0) :=
  ⟨fun _ holds => holds.1⟩

/-- A cell with a value is a cell with any value. -/
theorem pointsTo_le_pointsToAny (p : Ptr) (v : V) : PointsTo (L := L) p v ≤ PointsToAny p :=
  fun _ holds => ⟨some v, holds⟩

end Rules

/-! ## Controls -/

namespace Controls

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-- **Negative control**: a load of an indeterminate cell has no weakest
precondition, whatever the postcondition: the cell is held, but it reads no
value. -/
theorem load_indeterminate_not_wp (p : Ptr) (Q : V → Heap L → Prop) (σ : Heap L)
    (holds : Cells (L := L) p [none] σ) : ¬ (CProg.load p).wp act Q σ := by
  rintro ⟨⟨⟨v, readV⟩, -⟩, -⟩
  subst holds
  have atCell := segment_at (L := L) p.offset [whole (none : Option V)] (k := 0) (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at atCell
  change read ((atBlock p.block (.empty, segment p.offset ([none].map whole)) p.block).2
    p.offset) = some (some v) at readV
  simp only [List.map_cons, List.map_nil, atBlock_same, atCell, read_whole] at readV
  cases readV

end Controls

end Mettapedia.Machines.CMemory
