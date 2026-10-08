import Mettapedia.Machines.CMemory.Primitives

/-!
# Assertions about block memory and the small axioms

The assertions describe exact pieces of memory:

* `Cells p cs`: the whole permissions on the cells from `p` onward, holding
  the contents `cs` (`none` is indeterminate);
* `PointsTo p v`: one whole initialized cell, `Cells p [some v]`;
* `PointsToPerm p x`: exactly the permission `x` on the cell `p`;
* `LiveBlock b n` and `DeadBlock b n`: the header of block `b`, alive with `n`
  cells or dead.

Cell ranges split along any boundary (`cells_append`), so a block is its
header beside its cells, and an array is a block whose cells are split into a
used prefix and spare capacity.

Each primitive has a small specification that mentions only its footprint.
With the frame rule (`CMemory.frame`), these are all the reasoning about memory
a program needs:

* `load_rule`: a load reads a cell that the precondition holds with content;
* `store_spec`: `{p ↦ _} store p v {p ↦ v}`;
* `malloc_spec`: `{emp} malloc n {null, or a live block of n indeterminate cells}`;
* `free_spec`: `{live block b n ∗ its cells} free b {dead block b n}`;
* `realloc_spec`: `{live block b m ∗ cells cs} realloc b n
  {unchanged, or dead block b m ∗ a live block b' of n cells holding the
  moved prefix of cs, then indeterminate cells}`;
* `ptrEq_rule`: comparison of pointers the precondition shows valid;
* `undefined_spec`: undefined behaviour meets no satisfiable precondition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

/-! ## Exact heaps -/

section Exact

variable {L : Type u}

/-- The heap holding the block resource `r` at block `b` and nothing else. -/
def atBlock [Zero L] (b : BlockId) (r : BlockRes L) : Heap L := Function.update 0 b r

/-- Permissions `xs` on the consecutive cells from offset `start`. -/
def segment [Zero L] (start : ℕ) (xs : List L) : ℕ → L :=
  fun i => if start ≤ i then (xs[i - start]?).getD 0 else 0

section ZeroOnly

variable [Zero L]

@[simp] theorem atBlock_same (b : BlockId) (r : BlockRes L) : atBlock b r b = r :=
  Function.update_self _ _ _

theorem atBlock_other {b x : BlockId} (r : BlockRes L) (different : x ≠ b) :
    atBlock b r x = 0 :=
  Function.update_of_ne different _ _

theorem segment_of_lt {start i : ℕ} (xs : List L) (before : i < start) :
    segment start xs i = 0 := by
  simp [segment, Nat.not_le.mpr before]

theorem segment_of_le {start i : ℕ} (xs : List L) (after : start + xs.length ≤ i) :
    segment start xs i = 0 := by
  have outside : xs.length ≤ i - start := by omega
  simp [segment, show start ≤ i by omega, List.getElem?_eq_none outside]

theorem segment_at (start : ℕ) (xs : List L) {k : ℕ} (inside : k < xs.length) :
    segment start xs (start + k) = xs[k] := by
  simp [segment, List.getElem?_eq_getElem inside]

theorem segment_nil (start : ℕ) : segment start ([] : List L) = 0 := by
  funext i
  simp [segment]

theorem segment_singleton (start : ℕ) (x : L) :
    segment start [x] = Function.update (0 : ℕ → L) start x := by
  funext i
  by_cases same : i = start
  · subst i
    simpa using segment_at start [x] (k := 0) (by simp)
  · rw [Function.update_of_ne same]
    rcases Nat.lt_or_gt_of_ne same with before | after
    · exact segment_of_lt [x] before
    · exact segment_of_le (start := start) (i := i) [x] (by simp; omega)

theorem segment_replicate (start n : ℕ) (x : L) (i : ℕ) :
    segment start (List.replicate n x) i = if start ≤ i ∧ i < start + n then x else 0 := by
  by_cases inside : start ≤ i ∧ i < start + n
  · rw [if_pos inside]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le inside.1
    rw [segment_at start _ (by simp; omega)]
    simp
  · rw [if_neg inside]
    rcases Nat.lt_or_ge i start with before | after
    · exact segment_of_lt _ before
    · exact segment_of_le (start := start) (i := i) _ (by simp; omega)

theorem atBlock_zero (b : BlockId) : atBlock b (0 : BlockRes L) = 0 :=
  Function.update_eq_self_iff.mpr rfl

end ZeroOnly

variable [Zero L] [Add L] [SepAlgebra L]

/-- Two pieces of one block add inside that block. -/
theorem atBlock_add (b : BlockId) (r r' : BlockRes L) :
    atBlock b r + atBlock b r' = atBlock b (r + r') := by
  funext x
  by_cases same : x = b
  · subst x
    simp
  · simp only [Pi.add_apply, atBlock_other _ same]
    exact SepAlgebra.add_zero 0

theorem atBlock_separate_iff (b : BlockId) (r r' : BlockRes L) :
    atBlock b r ## atBlock b r' ↔ r ## r' := by
  constructor
  · intro separate
    simpa using separate b
  · intro separate x
    by_cases same : x = b
    · subst x
      simpa using separate
    · simpa only [atBlock_other _ same] using SepAlgebra.separate_zero (0 : BlockRes L)

/-- Pieces of different blocks are always separate. -/
theorem atBlock_separate_of_ne {b b' : BlockId} (different : b ≠ b') (r r' : BlockRes L) :
    atBlock b r ## atBlock b' r' := by
  intro x
  by_cases same : x = b
  · subst x
    simpa only [atBlock_other _ different] using SepAlgebra.separate_zero (atBlock b r b)
  · simpa only [atBlock_other _ same] using SepAlgebra.zero_separate (atBlock b' r' x)

/-- Splitting one block's resource is splitting the heap. -/
theorem sepConj_atBlock_iff (b : BlockId) (r r' : BlockRes L) (σ : Heap L) :
    ((fun σ => σ = atBlock b r) ∗ (fun σ => σ = atBlock b r')) σ ↔
      r ## r' ∧ σ = atBlock b (r + r') := by
  constructor
  · rintro ⟨_, _, separate, rfl, rfl, rfl⟩
    exact ⟨(atBlock_separate_iff b r r').mp separate, atBlock_add b r r'⟩
  · rintro ⟨separate, rfl⟩
    exact ⟨_, _, (atBlock_separate_iff b r r').mpr separate, (atBlock_add b r r').symm,
      rfl, rfl⟩

/-- Pieces of two different blocks: their sum. -/
theorem sepConj_atBlock_ne_iff {b b' : BlockId} (different : b ≠ b') (r r' : BlockRes L)
    (σ : Heap L) :
    ((fun σ => σ = atBlock b r) ∗ (fun σ => σ = atBlock b' r')) σ ↔
      σ = atBlock b r + atBlock b' r' := by
  constructor
  · rintro ⟨_, _, -, rfl, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨_, _, atBlock_separate_of_ne different r r', rfl, rfl, rfl⟩

/-- Consecutive cell ranges are disjoint, and together they are the
concatenated range. -/
theorem segment_append (start : ℕ) (xs ys : List L) :
    segment start xs ## segment (start + xs.length) ys ∧
      segment start (xs ++ ys) = segment start xs + segment (start + xs.length) ys := by
  constructor
  · intro i
    by_cases early : i < start + xs.length
    · rw [segment_of_lt ys early]
      exact SepAlgebra.separate_zero _
    · rw [segment_of_le xs (Nat.not_lt.mp early)]
      exact SepAlgebra.zero_separate _
  · funext i
    simp only [Pi.add_apply]
    by_cases early : i < start + xs.length
    · rw [segment_of_lt ys early, SepAlgebra.add_zero]
      by_cases before : i < start
      · rw [segment_of_lt _ before, segment_of_lt _ before]
      · have offset : i - start < xs.length := by omega
        simp only [segment, Nat.not_lt.mp before, if_true,
          List.getElem?_append_left offset]
    · rw [segment_of_le xs (Nat.not_lt.mp early), SepAlgebra.zero_add]
      have offset : xs.length ≤ i - start := by omega
      simp only [segment, show start ≤ i by omega, show start + xs.length ≤ i by omega,
        if_true, List.getElem?_append_right offset, Nat.sub_sub]

end Exact

/-! ## Assertions -/

section Assertions

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-- `Cells p cs`: the whole permissions on the cells from `p` onward, holding
the contents `cs`. -/
def Cells (p : Ptr) (cs : List (Option V)) : Heap L → Prop :=
  fun σ => σ = atBlock p.block (.empty, segment p.offset (cs.map whole))

/-- `p ↦ v`: one whole initialized cell. -/
def PointsTo (p : Ptr) (v : V) : Heap L → Prop := Cells p [some v]

/-- `p ↦ _`: one whole cell with any content, possibly indeterminate. -/
def PointsToAny (p : Ptr) : Heap L → Prop := fun σ => ∃ c : Option V, Cells p [c] σ

/-- `n` whole cells from `p`, with any contents. -/
def CellsAny (p : Ptr) (n : ℕ) : Heap L → Prop :=
  fun σ => ∃ cs : List (Option V), cs.length = n ∧ Cells p cs σ

/-- Exactly the permission `x` on the cell `p`. -/
def PointsToPerm (p : Ptr) (x : L) : Heap L → Prop :=
  fun σ => σ = atBlock p.block (.empty, segment p.offset [x])

/-- The header of block `b`. -/
def HeaderIs (b : BlockId) (header : Header) : Heap L → Prop :=
  fun σ => σ = atBlock b (.own header, 0)

/-- Block `b` is alive, with `n` cells. -/
def LiveBlock (b : BlockId) (n : ℕ) : Heap L → Prop := HeaderIs b ⟨n, true⟩

/-- Block `b`, of `n` cells, is dead. -/
def DeadBlock (b : BlockId) (n : ℕ) : Heap L → Prop := HeaderIs b ⟨n, false⟩

theorem pointsTo_eq_pointsToPerm (p : Ptr) (v : V) :
    PointsTo (L := L) p v = PointsToPerm p (whole (some v)) := rfl

theorem cells_nil (p : Ptr) : Cells (L := L) (V := V) p [] = emp := by
  funext σ
  have empty : atBlock (L := L) p.block (.empty, segment p.offset ([] : List L)) = 0 := by
    rw [segment_nil]
    exact atBlock_zero p.block
  simp only [Cells, List.map_nil, empty]
  rfl

/-- **Cell ranges split along any boundary.** -/
theorem cells_append (p : Ptr) (cs ds : List (Option V)) :
    Cells (L := L) p (cs ++ ds) = (Cells p cs ∗ Cells (p + cs.length) ds) := by
  funext σ
  apply propext
  obtain ⟨separate, sum⟩ := segment_append (L := L) p.offset (cs.map whole) (ds.map whole)
  rw [List.length_map] at separate sum
  have headers : (Excl.empty : Excl Header) ## Excl.empty := Or.inl rfl
  have left : Cells (L := L) p cs =
      fun σ => σ = atBlock p.block (.empty, segment p.offset (cs.map whole)) := rfl
  have right : Cells (L := L) (p + cs.length) ds =
      fun σ => σ = atBlock p.block (.empty, segment (p.offset + cs.length) (ds.map whole)) :=
    rfl
  rw [left, right, sepConj_atBlock_iff]
  simp only [Cells, List.map_append]
  constructor
  · rintro rfl
    exact ⟨⟨headers, separate⟩, by rw [sum]; rfl⟩
  · rintro ⟨-, rfl⟩
    rw [sum]
    rfl

theorem cells_cons (p : Ptr) (c : Option V) (cs : List (Option V)) :
    Cells (L := L) p (c :: cs) = (Cells p [c] ∗ Cells (p + 1) cs) :=
  cells_append p [c] cs

/-- A live block with its cells is one block resource. -/
theorem liveBlock_cells_iff (b : BlockId) (cs : List (Option V)) (n : ℕ) (σ : Heap L) :
    (LiveBlock b n ∗ Cells ⟨b, 0⟩ cs) σ ↔
      σ = atBlock b (.own ⟨n, true⟩, segment 0 (cs.map whole)) := by
  have header : LiveBlock (L := L) b n = fun σ => σ = atBlock b (.own ⟨n, true⟩, 0) := rfl
  have cells : Cells (L := L) ⟨b, 0⟩ cs =
      fun σ => σ = atBlock b (.empty, segment 0 (cs.map whole)) := rfl
  rw [header, cells, sepConj_atBlock_iff]
  constructor
  · rintro ⟨-, rfl⟩
    congr 1
    refine blockRes_ext rfl fun i => ?_
    exact SepAlgebra.zero_add _
  · rintro rfl
    refine ⟨⟨Or.inr rfl, fun i => SepAlgebra.zero_separate _⟩, ?_⟩
    congr 1
    refine blockRes_ext rfl fun i => ?_
    exact (SepAlgebra.zero_add _).symm

/-- **Two points-to facts never name one cell.** -/
theorem pointsTo_sepConj_self_false (p : Ptr) (v w : V) (σ : Heap L) :
    ¬ (PointsTo (L := L) p v ∗ PointsTo p w) σ := by
  rintro ⟨x, y, separate, -, rfl, rfl⟩
  have atCell := (separate p.block).2 p.offset
  have cell : ∀ u : V, ((atBlock (L := L) p.block (.empty,
      segment p.offset ([some u].map whole))) p.block).2 p.offset = whole (some u) := by
    intro u
    simpa using segment_at (L := L) p.offset [whole (some u)] (k := 0) (by simp)
  rw [cell v, cell w] at atCell
  exact whole_ne_zero _ (eq_zero_of_whole_separate atCell)

omit [CellPermission L (Option V)] in
/-- An owned header is the header of the whole heap, whatever is beside it. -/
theorem header_of_sepConj_right {P Q : Heap L → Prop} {σ : Heap L} {b : BlockId}
    {header : Header} (holds : (P ∗ Q) σ) (owned : ∀ τ, Q τ → (τ b).1 = .own header) :
    (σ b).1 = .own header := by
  obtain ⟨x, y, separate, rfl, -, holdsQ⟩ := holds
  have right := owned y holdsQ
  rcases (separate b).1 with empty | empty
  · rw [heap_add_header, empty, right]
    rfl
  · rw [right] at empty
    cases empty

omit [CellPermission L (Option V)] in
theorem header_of_sepConj_left {P Q : Heap L → Prop} {σ : Heap L} {b : BlockId}
    {header : Header} (holds : (P ∗ Q) σ) (owned : ∀ τ, P τ → (τ b).1 = .own header) :
    (σ b).1 = .own header := by
  rw [sepConj_comm] at holds
  exact header_of_sepConj_right holds owned

/-! ## Validity from assertions -/

omit [CellPermission L (Option V)] in
/-- A live block's header makes every pointer into it, or one past its end,
valid. -/
theorem valid_of_liveBlock {C : Type} [CellPermission L C] {b : BlockId} {n k : ℕ}
    {F : Heap L → Prop} {σ : Heap L}
    (holds : (LiveBlock b n ∗ F) σ) (inside : k ≤ n) : Valid σ ⟨b, k⟩ := by
  obtain ⟨x, y, separate, rfl, rfl, -⟩ := holds
  exact Valid.frame separate (Or.inl ⟨n, by simp, inside⟩)

/-- Exclusive ownership makes an initialized or indeterminate cell a valid
pointer. This grants no right to read an indeterminate value. -/
theorem valid_of_pointsToAny {p : Ptr} {F : Heap L → Prop} {heap : Heap L}
    (held : (PointsToAny (V := V) p ∗ F) heap) : Valid heap p := by
  obtain ⟨left, right, separate, rfl, ⟨cell, rfl⟩, -⟩ := held
  refine Valid.frame separate (Or.inr ?_)
  have selected := segment_at (L := L) p.offset [whole cell] (k := 0) (by simp)
  simp only [Nat.add_zero] at selected
  simp only [atBlock_same, List.map_cons, List.map_nil, selected]
  exact whole_ne_zero _


/-- A held initialized cell is a valid pointer. -/
theorem valid_of_pointsTo {p : Ptr} {v : V} {F : Heap L → Prop} {σ : Heap L}
    (holds : (PointsTo p v ∗ F) σ) : Valid σ p := by
  obtain ⟨left, right, separate, total, cell, rest⟩ := holds
  exact valid_of_pointsToAny (V := V) (p := p) (F := F)
    ⟨left, right, separate, total, ⟨some v, cell⟩, rest⟩

/-! ## The small axioms -/

/-- **Load**: a load from a cell the precondition holds with content `v`
returns `v` and changes nothing. -/
theorem load_rule {P : Heap L → Prop} {p : Ptr} {v : V}
    (reads : ∀ σ, P σ → read ((σ p.block).2 p.offset) = some (some v)) :
    CTriple P (CProg.load p) (fun r σ => r = v ∧ P σ) := by
  apply triple_prim
  intro σ holds
  refine ⟨⟨v, reads σ holds⟩, ?_⟩
  rintro r σ' ⟨readR, rfl⟩
  rw [reads _ holds] at readR
  cases readR
  exact ⟨rfl, holds⟩

/-- The content of a cell held in a separating conjunction. -/
theorem read_of_pointsTo {p : Ptr} {v : V} {F : Heap L → Prop} {σ : Heap L}
    (holds : (PointsTo p v ∗ F) σ) : read ((σ p.block).2 p.offset) = some (some v) := by
  obtain ⟨x, y, separate, rfl, rfl, -⟩ := holds
  have atCell := segment_at (L := L) p.offset [whole (some v)] (k := 0) (by simp)
  simp only [Nat.add_zero] at atCell
  rw [heap_add_cell]
  apply read_add ((separate p.block).2 p.offset)
  simp only [atBlock_same, List.map_cons, List.map_nil, atCell]
  exact read_whole _

/-- The same, with the cell on the right. -/
theorem read_of_pointsTo_right {p : Ptr} {v : V} {F : Heap L → Prop} {σ : Heap L}
    (holds : (F ∗ PointsTo p v) σ) : read ((σ p.block).2 p.offset) = some (some v) := by
  rw [sepConj_comm] at holds
  exact read_of_pointsTo holds

/-- A current cell read is retained when a separate frame is added. -/
theorem read_framed {P F : Heap L → Prop} {p : Ptr} {v : V} {σ : Heap L}
    (holds : (P ∗ F) σ)
    (reads : ∀ τ, P τ → read ((τ p.block).2 p.offset) = some (some v)) :
    read ((σ p.block).2 p.offset) = some (some v) := by
  obtain ⟨x, y, separate, rfl, holdsX, -⟩ := holds
  rw [heap_add_cell]
  exact read_add ((separate p.block).2 p.offset) (reads x holdsX)

theorem read_framed_right {P F : Heap L → Prop} {p : Ptr} {v : V} {σ : Heap L}
    (holds : (F ∗ P) σ)
    (reads : ∀ τ, P τ → read ((τ p.block).2 p.offset) = some (some v)) :
    read ((σ p.block).2 p.offset) = some (some v) := by
  rw [sepConj_comm] at holds
  exact read_framed holds reads

/-- An initialized cell is read at its checked index in the held range. -/
theorem read_cells {p : Ptr} {cs : List (Option V)} {i : Nat} {v : V}
    {F : Heap L → Prop} {σ : Heap L} (inside : i < cs.length)
    (value : cs[i] = some v) (holds : (Cells p cs ∗ F) σ) :
    read ((σ (p + i).block).2 (p + i).offset) = some (some v) := by
  apply read_framed holds
  rintro τ rfl
  simp only [Ptr.add_block, Ptr.add_offset, atBlock_same]
  rw [segment_at p.offset (cs.map whole) (by simpa using inside), List.getElem_map, value]
  exact read_whole _


/-- **Store**: `{p ↦ _} store p v {p ↦ v}`. -/
theorem store_spec (p : Ptr) (v : V) :
    CTriple (L := L) (PointsToAny p) (CProg.store p v) (fun _ => PointsTo p v) := by
  apply triple_prim
  rintro σ ⟨c, rfl⟩
  have atCell : ∀ x : L, segment p.offset [x] p.offset = x := fun x => by
    simpa using segment_at (L := L) p.offset [x] (k := 0) (by simp)
  refine ⟨⟨c, by simp [atCell]⟩, ?_⟩
  rintro - σ' rfl
  simp only [PointsTo, Cells, Heap.setCell, atBlock_same, List.map_cons, List.map_nil]
  unfold atBlock
  rw [Function.update_idem]
  congr 2
  rw [segment_singleton, segment_singleton, Function.update_idem]

/-- **Allocation**: `malloc n` from nothing returns null and nothing, or a live
block of `n` indeterminate cells. -/
theorem malloc_spec (n : ℕ) :
    CTriple (L := L) (V := V) emp (CProg.malloc n)
      (fun r σ => (r = none ∧ σ = 0) ∨
        ∃ b, r = some ⟨b, 0⟩ ∧ (LiveBlock b n ∗ Cells ⟨b, 0⟩ (List.replicate n none)) σ) := by
  apply triple_prim
  rintro σ rfl
  refine ⟨trivial, ?_⟩
  rintro r σ' (⟨rfl, rfl⟩ | ⟨b, -, rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨b, rfl, (liveBlock_cells_iff b _ n _).mpr ?_⟩
    change Function.update (0 : Heap L) b (freshBlock n) = atBlock b _
    unfold atBlock freshBlock
    congr 2
    funext i
    rw [List.map_replicate, segment_replicate]
    simp

/-- `realloc` of null is `malloc`. -/
theorem realloc_null_spec (n : ℕ) :
    CTriple (L := L) (V := V) emp (CProg.realloc none n)
      (fun r σ => (r = none ∧ σ = 0) ∨
        ∃ b, r = some ⟨b, 0⟩ ∧ (LiveBlock b n ∗ Cells ⟨b, 0⟩ (List.replicate n none)) σ) :=
  malloc_spec n

/-- Killing a whole block leaves only its dead header. -/
theorem kill_atBlock (b : BlockId) (cs : List (Option V)) (live : Bool) :
    (atBlock (L := L) b (.own ⟨cs.length, live⟩, segment 0 (cs.map whole))).kill b cs.length =
      atBlock b (.own ⟨cs.length, false⟩, 0) := by
  simp only [Heap.kill, Heap.killedBlock, atBlock_same]
  unfold atBlock
  rw [Function.update_idem]
  congr 2
  funext i
  split
  · rfl
  · exact segment_of_le _ (by simp; omega)

/-- The block `realloc` grows from a whole block: the moved prefix, then
indeterminate cells. -/
theorem grownBlock_atBlock (b : BlockId) (cs : List (Option V)) (live : Bool) (n : ℕ) :
    (atBlock (L := L) b (.own ⟨cs.length, live⟩, segment 0 (cs.map whole))).grownBlock b
        cs.length n =
      (.own ⟨n, true⟩,
        segment 0 ((cs.take n ++ List.replicate (n - cs.length) none).map whole)) := by
  simp only [Heap.grownBlock, atBlock_same]
  congr 1
  funext i
  simp only [segment, Nat.zero_le, if_true, Nat.sub_zero, List.map_append]
  by_cases moved : i < cs.length ∧ i < n
  · rw [if_pos moved, List.getElem?_append_left (by simp; omega)]
    simp [moved.2]
  · rw [if_neg moved]
    by_cases fresh : i < n
    · rw [if_pos fresh, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_take, List.getElem?_map, List.getElem?_replicate]
      rw [if_pos (by omega)]
      rfl
    · rw [if_neg fresh, List.getElem?_eq_none (by simp; omega)]
      rfl

/-- Changing a block other than the only one held adds a separate block. -/
theorem update_atBlock_of_ne {b b' : BlockId} (different : b' ≠ b) (r r' : BlockRes L) :
    Function.update (atBlock b r) b' r' = atBlock b r + atBlock b' r' := by
  funext x
  by_cases atNew : x = b'
  · subst x
    simp only [Function.update_self, Pi.add_apply, atBlock_other _ different, atBlock_same]
    exact (SepAlgebra.zero_add r').symm
  · rw [Function.update_of_ne atNew, Pi.add_apply, atBlock_other _ atNew]
    exact (SepAlgebra.add_zero _).symm

theorem holdsBlock_of_cells {b : BlockId} {cs : List (Option V)} {n : ℕ} {σ : Heap L}
    (holds : σ = atBlock b (.own ⟨n, true⟩, segment 0 (cs.map whole)))
    (length : cs.length = n) : HoldsBlock σ b n := by
  subst holds
  refine ⟨by simp, fun i inside => ⟨cs[i]'(length ▸ inside), ?_⟩⟩
  have := segment_at (L := L) 0 (cs.map whole) (k := i) (by simpa [length] using inside)
  simpa using this

/-- **Free**: `{live block b n ∗ n cells} free b {dead block b n}`. -/
theorem free_spec (b : BlockId) (n : ℕ) :
    CTriple (L := L) (V := V) (LiveBlock b n ∗ CellsAny ⟨b, 0⟩ n) (CProg.free (some ⟨b, 0⟩))
      (fun _ => DeadBlock b n) := by
  apply triple_prim
  rintro σ ⟨x, y, separate, rfl, holdsX, cs, length, holdsY⟩
  have whole_block := (liveBlock_cells_iff b cs n (x + y)).mp
    ⟨x, y, separate, rfl, holdsX, holdsY⟩
  refine ⟨⟨rfl, n, holdsBlock_of_cells whole_block length⟩, ?_⟩
  rintro - σ' ⟨n', header, rfl⟩
  rw [whole_block] at header ⊢
  simp only [atBlock_same] at header
  cases header
  subst length
  exact kill_atBlock b cs true

/-- **Reallocation** of a live block to `n > 0` cells: it fails and changes
nothing, or the old block dies and a different, fresh block of `n` cells
holds the moved prefix followed by indeterminate cells. -/
theorem realloc_spec (b : BlockId) (cs : List (Option V)) (n : ℕ) (positive : 0 < n) :
    CTriple (L := L) (LiveBlock b cs.length ∗ Cells ⟨b, 0⟩ cs) (CProg.realloc (some ⟨b, 0⟩) n)
      (fun r σ => (r = none ∧ (LiveBlock b cs.length ∗ Cells ⟨b, 0⟩ cs) σ) ∨
        ∃ b', r = some ⟨b', 0⟩ ∧ (DeadBlock b cs.length ∗ (LiveBlock b' n ∗
          Cells ⟨b', 0⟩ (cs.take n ++ List.replicate (n - cs.length) none))) σ) := by
  apply triple_prim
  intro σ holds
  have whole_block := (liveBlock_cells_iff b cs cs.length σ).mp holds
  refine ⟨⟨positive, rfl, cs.length, holdsBlock_of_cells whole_block rfl⟩, ?_⟩
  rintro r σ' (⟨rfl, rfl⟩ | ⟨m, b', header, fresh, rfl, rfl⟩)
  · exact Or.inl ⟨rfl, holds⟩
  · subst whole_block
    simp only [atBlock_same] at header
    cases header
    have different : b' ≠ b := by
      rintro rfl
      have := congrArg Prod.fst fresh
      simp at this
    refine Or.inr ⟨b', rfl, ?_⟩
    have block : (LiveBlock (L := L) b' n ∗
        Cells ⟨b', 0⟩ (cs.take n ++ List.replicate (n - cs.length) none)) =
        fun σ => σ = atBlock b' (.own ⟨n, true⟩,
          segment 0 ((cs.take n ++ List.replicate (n - cs.length) none).map whole)) :=
      funext fun σ => propext (liveBlock_cells_iff b' _ n σ)
    rw [block]
    refine (sepConj_atBlock_ne_iff (Ne.symm different) _ _ _).mpr ?_
    rw [Heap.move, kill_atBlock, grownBlock_atBlock, update_atBlock_of_ne different]

/-- **Pointer comparison** of pointers the precondition shows valid (or null). -/
theorem ptrEq_rule {P : Heap L → Prop} {p q : Option Ptr}
    (valid : ∀ σ, P σ → ValidOpt σ p ∧ ValidOpt σ q) :
    CTriple P (CProg.ptrEq (V := V) p q) (fun r σ => r = decide (p = q) ∧ P σ) := by
  apply triple_prim
  intro σ holds
  refine ⟨valid σ holds, ?_⟩
  rintro r σ' ⟨rfl, rfl⟩
  exact ⟨rfl, holds⟩

/-- **Undefined behaviour** is safe from no state: its triples are exactly the
ones with an unsatisfiable precondition. -/
theorem undefined_spec {α : Type} {P : Heap L → Prop} {Q : α → Heap L → Prop} :
    CTriple P (CProg.undefined (V := V)) Q ↔ ∀ σ, ¬ P σ := by
  constructor
  · intro spec σ holds
    exact (spec σ holds).1.1
  · intro impossible σ holds
    exact absurd holds (impossible σ)

end Assertions

end Mettapedia.Machines.CMemory
