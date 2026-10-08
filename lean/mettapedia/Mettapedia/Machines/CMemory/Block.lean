import Mettapedia.GSLT.Logic.SeparationProduct

/-!
# Block memory as a separation algebra

C memory is a collection of blocks.  A block is what one call of `malloc`
returns: it has a size, a liveness bit and cells.  A pointer names a block and
a cell offset inside it; the block is the pointer's provenance.  Block ids are
never reused, so a pointer into a dead block stays dangling forever, and two
pointers into blocks of different lifetimes are never confused.

A cell holds one scalar object.  Offsets count cells, not bytes: the model has
no byte representation and no layout, and it serves programs that access every
object at its own type (the effective-type rule, C11 6.5p7).  A cell's content
is `Option V`: `none` is the indeterminate value of fresh storage.

## The heap is a resource

Ownership of memory is a separation algebra, assembled from Mettapedia's own
instances:

* a block resource is a header slot (`Excl Header`) beside a family of cell
  slots (`ℕ → L`), joined by the product instance;
* a heap is a block resource at every block id, by `instPi`.

The cell algebra `L` is any `CellPermission`: it says which content a holder
reads and which permission is *whole* (may write and free).  Exclusive cells
(`Excl`) are one instance; fractional permissions for shared reading are
another (`CMemory.Fractional`).  The header is always exclusive: whoever holds
it may free the block.

A dead block keeps its header, marked dead, and loses its cells.  The dead
header is a resource too: it records that the block is gone, which is how a
specification says "the old block is dead".

## Examples

* **Positive.**  A header and a cell of the same block are separate resources,
  so a struct field can be owned without the block's header
  (`Controls.header_separate_cell`).
* **Negative.**  Two whole permissions on one cell are never separate
  (`Controls.whole_not_separate_whole`); neither are two headers of one block.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v

/-- Block identifiers.  A block id names at most one allocation, ever. -/
abbrev BlockId := ℕ

/-- **A pointer**: a block, which is its provenance, and a cell offset. -/
structure Ptr where
  block : BlockId
  offset : ℕ
  deriving DecidableEq, Repr

/-- Pointer arithmetic stays in the pointer's block.  Forming a pointer outside
its block's bounds is already undefined in ISO C (6.5.6p8); this model checks
bounds where a pointer is used (load, store, free, realloc, comparison), not
where it is formed. -/
instance : HAdd Ptr ℕ Ptr := ⟨fun p k => ⟨p.block, p.offset + k⟩⟩

@[simp] theorem Ptr.add_block (p : Ptr) (k : ℕ) : (p + k).block = p.block := rfl
@[simp] theorem Ptr.add_offset (p : Ptr) (k : ℕ) : (p + k).offset = p.offset + k := rfl

/-- What a block records besides its cells: its size in cells and whether it
is alive. -/
structure Header where
  size : ℕ
  live : Bool
  deriving DecidableEq, Repr

/-! ## Permissions on one cell -/

/-- **A permission algebra for one cell.**  A holder of a permission reads a
content; the whole permission on a content may also write and free.  The laws
are the ones local reasoning about loads, stores and allocation needs:

* a content read with some permission is still read when a separate
  permission is added (`read_add`);
* nothing is separate from a whole permission except the empty one;
* only empty permissions add up to the empty one. -/
class CellPermission (L : Type u) (C : outParam (Type v)) [Zero L] [Add L]
    [SepAlgebra L] where
  /-- The content seen by a holder of this permission, if any. -/
  read : L → Option C
  /-- The whole permission on a cell holding this content. -/
  whole : C → L
  read_whole (c : C) : read (whole c) = some c
  read_zero : read 0 = none
  read_add {x y : L} {c : C} : x ## y → read x = some c → read (x + y) = some c
  eq_zero_of_whole_separate {c : C} {y : L} : whole c ## y → y = 0
  eq_zero_of_add_eq_zero {x y : L} : x ## y → x + y = 0 → x = 0

namespace CellPermission

variable {L : Type u} {C : Type v} [Zero L] [Add L] [SepAlgebra L] [CellPermission L C]

theorem whole_ne_zero (c : C) : (whole c : L) ≠ 0 := by
  intro equal
  have readWhole := read_whole (L := L) c
  rw [equal, read_zero] at readWhole
  cases readWhole

theorem whole_add_of_separate {c : C} {y : L} (separate : whole c ## y) :
    whole c + y = whole c := by
  rw [eq_zero_of_whole_separate separate, SepAlgebra.add_zero]

omit [CellPermission L C] in
theorem eq_zero_of_add_eq_zero_right {C' : Type v} [CellPermission L C'] {x y : L}
    (separate : x ## y) (sum : x + y = 0) : y = 0 :=
  eq_zero_of_add_eq_zero (SepAlgebra.separate_symm separate)
    (by rw [← SepAlgebra.add_comm separate]; exact sum)

omit [CellPermission L C] in
theorem add_ne_zero_of_ne_zero {C' : Type v} [CellPermission L C'] {x y : L}
    (separate : x ## y) (nonzero : x ≠ 0) : x + y ≠ 0 :=
  fun sum => nonzero (eq_zero_of_add_eq_zero separate sum)

end CellPermission

open CellPermission

/-- Exclusive cells: the only permission is the whole one. -/
instance Excl.instCellPermission (C : Type v) : CellPermission (Excl C) C where
  read cell := match cell with
    | .empty => none
    | .own c => some c
  whole := .own
  read_whole _ := rfl
  read_zero := rfl
  read_add := by
    rintro (_ | x) y c - read
    · cases read
    · exact read
  eq_zero_of_whole_separate := by
    rintro c y (owned | empty)
    · cases owned
    · exact empty
  eq_zero_of_add_eq_zero := fun _ sum => (Excl.add_eq_empty sum).1

/-! ## Blocks and heaps -/

/-- **A block resource**: the header slot and the cell slots of one block. -/
abbrev BlockRes (L : Type u) := Excl Header × (ℕ → L)

/-- **A heap**: a block resource at every block id.  The separation algebra is
`instPi` over block ids of the product of `Excl` headers and `instPi` cells. -/
abbrev Heap (L : Type u) := BlockId → BlockRes L

section Heap

variable {L : Type u}

@[simp] theorem heap_add_header [Add L] (σ τ : Heap L) (b : BlockId) :
    ((σ + τ) b).1 = (σ b).1 + (τ b).1 := rfl

@[simp] theorem heap_add_cell [Add L] (σ τ : Heap L) (b : BlockId) (i : ℕ) :
    ((σ + τ) b).2 i = (σ b).2 i + (τ b).2 i := rfl

@[simp] theorem heap_zero_header [Zero L] (b : BlockId) :
    ((0 : Heap L) b).1 = Excl.empty := rfl

@[simp] theorem heap_zero_cell [Zero L] (b : BlockId) (i : ℕ) : ((0 : Heap L) b).2 i = 0 := rfl

theorem blockRes_ext {r r' : BlockRes L} (header : r.1 = r'.1) (cells : ∀ i, r.2 i = r'.2 i) :
    r = r' :=
  Prod.ext header (funext cells)

/-- Changing one block of a heap and adding a frame: the frame's block is
added to the new block. -/
theorem update_add [Add L] (σ τ : Heap L) (b : BlockId) (r : BlockRes L) :
    Function.update σ b r + τ = Function.update (σ + τ) b (r + τ b) := by
  funext x
  by_cases same : x = b
  · subst x
    simp only [Pi.add_apply, Function.update_self]
  · simp only [Pi.add_apply, Function.update_of_ne same]

variable [Zero L] [Add L] [SepAlgebra L]

example : SepAlgebra (Heap L) := inferInstance

theorem separate_heap_iff {σ τ : Heap L} :
    σ ## τ ↔ ∀ b, (σ b).1 ## (τ b).1 ∧ ∀ i, (σ b).2 i ## (τ b).2 i :=
  Iff.rfl

theorem separate_block_iff {r r' : BlockRes L} :
    r ## r' ↔ r.1 ## r'.1 ∧ ∀ i, r.2 i ## r'.2 i :=
  Iff.rfl

theorem update_separate {σ τ : Heap L} (separate : σ ## τ) {b : BlockId} {r : BlockRes L}
    (separateBlock : r ## τ b) : Function.update σ b r ## τ := by
  intro x
  by_cases same : x = b
  · subst x
    simpa only [Function.update_self] using separateBlock
  · simpa only [Function.update_of_ne same] using separate x

/-- Two separate block resources whose sum is empty are both empty. -/
theorem blockRes_eq_zero_of_add_eq_zero {C : Type v} [CellPermission L C]
    {r r' : BlockRes L} (separate : r ## r') (sum : r + r' = 0) : r = 0 ∧ r' = 0 := by
  have header : r.1 + r'.1 = Excl.empty := congrArg Prod.fst sum
  have cells : ∀ i, r.2 i + r'.2 i = 0 := fun i => congrFun (congrArg Prod.snd sum) i
  obtain ⟨header₁, header₂⟩ := Excl.add_eq_empty header
  refine ⟨blockRes_ext header₁ fun i => eq_zero_of_add_eq_zero (separate.2 i) (cells i),
    blockRes_ext header₂ fun i => eq_zero_of_add_eq_zero_right (separate.2 i) (cells i)⟩

end Heap

/-! ## Validity and well-formedness -/

section Validity

variable {L : Type u} [Zero L]

/-- **Evidence that a pointer is valid**, held in a heap: the holder owns the
header of a live block that `p` points into or one past the end of, or holds
some permission on the cell `p` itself.  Comparing pointers needs this
evidence, because the value of a pointer into a dead block is indeterminate
(C11 6.2.4p2). -/
def Valid (σ : Heap L) (p : Ptr) : Prop :=
  (∃ n, (σ p.block).1 = .own ⟨n, true⟩ ∧ p.offset ≤ n) ∨ (σ p.block).2 p.offset ≠ 0

/-- Null is always comparable; a pointer needs evidence. -/
def ValidOpt (σ : Heap L) : Option Ptr → Prop
  | none => True
  | some p => Valid σ p

/-- Evidence survives the addition of a separate frame. -/
theorem Valid.frame [Add L] [SepAlgebra L] {C : Type v} [CellPermission L C] {σ τ : Heap L}
    (separate : σ ## τ) {p : Ptr} : Valid σ p → Valid (σ + τ) p := by
  rintro (⟨n, header, inside⟩ | cell)
  · exact Or.inl ⟨n, by rw [heap_add_header, header]; rfl, inside⟩
  · exact Or.inr (by rw [heap_add_cell]; exact add_ne_zero_of_ne_zero ((separate _).2 _) cell)

theorem ValidOpt.frame [Add L] [SepAlgebra L] {C : Type v} [CellPermission L C]
    {σ τ : Heap L} (separate : σ ## τ) : ∀ {p : Option Ptr}, ValidOpt σ p → ValidOpt (σ + τ) p
  | none, _ => trivial
  | some _, valid => Valid.frame separate valid

/-- **A heap that describes C memory**: every cell held lies inside a live
block whose header is held.  The whole state of a running program has this
form; a part of it, such as a precondition's footprint, need not. -/
def WellFormed (σ : Heap L) : Prop :=
  ∀ b i, (σ b).2 i ≠ 0 → ∃ n, (σ b).1 = .own ⟨n, true⟩ ∧ i < n

/-- In memory, a held cell is a cell of a live block, inside its bounds. -/
theorem WellFormed.live {σ : Heap L} (wellFormed : WellFormed σ) {p : Ptr}
    (held : (σ p.block).2 p.offset ≠ 0) :
    ∃ n, (σ p.block).1 = .own ⟨n, true⟩ ∧ p.offset < n :=
  wellFormed p.block p.offset held

end Validity

/-! ## Controls -/

namespace Controls

variable {V : Type v}

/-- The heap holding one cell `p` with content `c`, exclusively. -/
def cellOnly (p : Ptr) (c : Option V) : Heap (Excl (Option V)) :=
  Function.update 0 p.block (Excl.empty, Function.update 0 p.offset (Excl.own c))

/-- The heap holding only the header of block `b`. -/
def headerOnly (b : BlockId) (header : Header) : Heap (Excl (Option V)) :=
  Function.update 0 b (Excl.own header, 0)

/-- **Positive control**: the header of a block and one of its cells are
separate resources. -/
theorem header_separate_cell (b : BlockId) (header : Header) (offset : ℕ) (c : Option V) :
    headerOnly b header ## cellOnly ⟨b, offset⟩ c := by
  intro x
  by_cases same : x = b
  · subst x
    refine ⟨Or.inr ?_, fun _ => Or.inl ?_⟩
    · simp [cellOnly]
    · simp [headerOnly, Excl.zero_def]
  · refine ⟨Or.inl ?_, fun _ => Or.inl ?_⟩
    · simp [headerOnly, Function.update_of_ne same, Excl.zero_def]
    · simp [headerOnly, Function.update_of_ne same, Excl.zero_def]

/-- **Negative control**: two whole permissions on one cell are not separate,
whatever their contents. -/
theorem whole_not_separate_whole (p : Ptr) (c c' : Option V) :
    ¬ cellOnly p c ## cellOnly p c' := by
  intro separate
  have atCell := (separate p.block).2 p.offset
  simp only [cellOnly, Function.update_self] at atCell
  exact Excl.not_separate_own c c' atCell

/-- **Negative control**: two headers of one block are not separate. -/
theorem header_not_separate_header (b : BlockId) (header header' : Header) :
    ¬ headerOnly (V := V) b header ## headerOnly b header' := by
  intro separate
  have atHeader := (separate b).1
  simp only [headerOnly, Function.update_self] at atHeader
  exact Excl.not_separate_own header header' atHeader

end Controls

end Mettapedia.Machines.CMemory
