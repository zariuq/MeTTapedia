import Mettapedia.Machines.CMemory.Values
import Mettapedia.Machines.OrderedDependencyCapacity

/-!
# Dynamic arrays and the specification of `reserve`

`DynArray a cap xs` is the array of the B1 plan, `Array a cap xs`: either `a`
is null, the capacity is zero and there are no contents, or `a` is the base of
a live block of exactly `cap` cells whose first `|xs|` cells hold `xs` and whose
remaining cells are allocated with arbitrary contents.  (It is not named
`Array`, which is Lean's own array type.)

`reserve` is the C helper `space_module_link_reserve` of CeTTa's `space.c`,
written in the command language over block memory:

```c
static bool space_module_link_reserve(Space ***items, uint32_t *capacity,
                                       uint32_t required) {
    if (required <= *capacity) return true;
    uint32_t next = *capacity ? *capacity : 4u;
    while (next < required) { ... next *= 2u; ... }   // Co5's growth loop
    if ((uint64_t)next * sizeof(**items) > SIZE_MAX) return false;
    Space **grown = realloc(*items, sizeof(**items) * (size_t)next);
    if (!grown) return false;
    *items = grown;
    *capacity = next;
    return true;
}
```

The growth loop is replaced by its value, `OrderedDependencyCapacity.grow`:
Co5 proved that the retained C loop computes exactly that function
(`OrderedDependencyCReserveGrowth.executed_growth_supplies_allocator_request`).
Cells count elements, so the byte size `sizeof(**items) * next` is `next`
cells; the size guard keeps its byte arithmetic through `pointerBytes`.

**The specification** (`reserve_spec`), from the two fields and the array:

* success without moving: `required ≤ cap`, and nothing changed;
* success after moving: some pointer `p` and capacity `c` with
  `required ≤ c` and `cap ≤ c`; the fields now hold `p` and `c`, the array at
  `p` has the same contents `xs`, and the old block is dead
  (`DeadStorage a cap`), hence different from the new one
  (`moved_array_is_fresh`);
* failure: nothing changed.

Addresses may change only on success, and when they change the old address is
dead: an interior pointer cached across a successful `reserve` dangles
(`CMemory.Examples`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

section DynArray

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-- **A dynamic array** at `a` with capacity `cap` and contents `xs`. -/
def DynArray : Option Ptr → ℕ → List V → Heap L → Prop
  | none, cap, xs => fun σ => cap = 0 ∧ xs = [] ∧ σ = 0
  | some p, cap, xs => fun σ => p.offset = 0 ∧ xs.length ≤ cap ∧
      (LiveBlock p.block cap ∗
        (Cells p (xs.map some) ∗ CellsAny (p + xs.length) (cap - xs.length))) σ

/-- The storage an array leaves behind when it moves: nothing for a null
array, its dead block otherwise. -/
def DeadStorage : Option Ptr → ℕ → Heap L → Prop
  | none, _ => emp
  | some p, cap => DeadBlock p.block cap

theorem dynArray_none_iff (cap : ℕ) (xs : List V) (σ : Heap L) :
    DynArray none cap xs σ ↔ cap = 0 ∧ xs = [] ∧ σ = 0 := Iff.rfl

/-- A non-null array is one live block whose cells hold the contents followed
by the spare cells. -/
theorem dynArray_some_iff (p : Ptr) (cap : ℕ) (xs : List V) (σ : Heap L) :
    DynArray (some p) cap xs σ ↔ p.offset = 0 ∧ xs.length ≤ cap ∧
      ∃ spare : List (Option V), spare.length = cap - xs.length ∧
        (LiveBlock p.block cap ∗ Cells p (xs.map some ++ spare)) σ := by
  simp only [DynArray]
  constructor
  · rintro ⟨base, size, x, y, separate, rfl, header, z, w, separate', rfl, used, spare,
      length, rest⟩
    refine ⟨base, size, spare, length, x, z + w, separate, rfl, header, ?_⟩
    rw [cells_append, List.length_map]
    exact ⟨z, w, separate', rfl, used, rest⟩
  · rintro ⟨base, size, spare, length, x, y, separate, rfl, header, cells⟩
    rw [cells_append, List.length_map] at cells
    obtain ⟨z, w, separate', rfl, used, rest⟩ := cells
    exact ⟨base, size, x, z + w, separate, rfl, header, z, w, separate', rfl, used, spare,
      length, rest⟩

/-- A non-null array holds the live header of its block. -/
theorem header_of_dynArray {p : Ptr} {cap : ℕ} {xs : List V} {σ : Heap L}
    (holds : DynArray (some p) cap xs σ) : (σ p.block).1 = .own ⟨cap, true⟩ := by
  obtain ⟨-, -, x, y, -, rfl, rfl, -⟩ := holds
  simp only [heap_add_header, atBlock_same]
  rfl

/-- **Reallocating an array** to `n ≥ cap` cells: it fails and changes nothing,
or the array moves to a fresh block with the same contents and the old storage
is dead. -/
theorem realloc_dynArray (a : Option Ptr) (cap n : ℕ) (xs : List V) (positive : 0 < n)
    (grows : cap ≤ n) :
    CTriple (L := L) (DynArray a cap xs) (CProg.realloc a n)
      (fun g σ => (g = none ∧ DynArray a cap xs σ) ∨
        ∃ b, g = some ⟨b, 0⟩ ∧ (DynArray (some ⟨b, 0⟩) n xs ∗ DeadStorage a cap) σ) := by
  cases a with
  | none =>
    refine triple_pre _ (P := fun σ => (cap = 0 ∧ xs = []) ∧ emp σ)
      (fun σ holds => ⟨⟨holds.1, holds.2.1⟩, holds.2.2⟩) ?_
    apply triple_pure
    rintro ⟨rfl, rfl⟩
    refine triple_post _ (realloc_null_spec n) ?_
    rintro g σ (⟨rfl, rfl⟩ | ⟨b, rfl, holds⟩)
    · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · refine Or.inr ⟨b, rfl, ?_⟩
      rw [DeadStorage, sepConj_emp]
      refine (dynArray_some_iff _ _ _ _).mpr ⟨rfl, Nat.zero_le _, List.replicate n none,
        by simp, ?_⟩
      simpa using holds
  | some p =>
    refine triple_pre _ (P := fun σ => (p.offset = 0 ∧ xs.length ≤ cap) ∧
        ∃ spare : List (Option V), spare.length = cap - xs.length ∧
          (LiveBlock p.block cap ∗ Cells p (xs.map some ++ spare)) σ)
      (fun σ holds => by
        obtain ⟨base, size, rest⟩ := (dynArray_some_iff p cap xs σ).mp holds
        exact ⟨⟨base, size⟩, rest⟩) ?_
    apply triple_pure
    rintro ⟨base, size⟩
    apply triple_exists
    intro spare
    apply triple_pure
    intro spareLength
    obtain ⟨b, offset⟩ := p
    simp only at base
    subst base
    have length : (xs.map some ++ spare).length = cap := by
      simp only [List.length_append, List.length_map, spareLength]
      omega
    have spec := realloc_spec (L := L) b (xs.map some ++ spare) n positive
    rw [length] at spec
    refine triple_post _ spec ?_
    rintro g σ (⟨rfl, holds⟩ | ⟨b', rfl, holds⟩)
    · exact Or.inl ⟨rfl, (dynArray_some_iff _ _ _ _).mpr ⟨rfl, size, spare, spareLength, holds⟩⟩
    · refine Or.inr ⟨b', rfl, ?_⟩
      rw [sepConj_comm] at holds
      refine sepConj_mono (fun τ moved => ?_) le_rfl σ holds
      have spareLength' : (spare ++ List.replicate (n - cap) none).length =
          n - xs.length := by
        simp only [List.length_append, List.length_replicate, spareLength]
        omega
      refine (dynArray_some_iff _ _ _ _).mpr ⟨rfl, (by omega),
        spare ++ List.replicate (n - cap) none, spareLength', ?_⟩
      have whole : (xs.map some ++ spare).take n = xs.map some ++ spare :=
        List.take_of_length_le (by omega)
      rw [whole, List.append_assoc] at moved
      exact moved

theorem Ptr.add_add (p : Ptr) (a b : ℕ) : p + a + b = p + (a + b) := by
  show (⟨p.block, p.offset + a + b⟩ : Ptr) = ⟨p.block, p.offset + (a + b)⟩
  rw [Nat.add_assoc]

/-- **Element update**: a store into the `k`-th of the cells `cs` replaces that
content and keeps the others. -/
theorem store_cells (p : Ptr) (cs : List (Option V)) {k : ℕ} (inside : k < cs.length) (v : V) :
    CTriple (L := L) (Cells p cs) (CProg.store (p + k) v)
      (fun _ => Cells p (cs.set k (some v))) := by
  have prefixLength : (cs.take k).length = k := by
    rw [List.length_take]
    omega
  have shape : Cells (L := L) p cs = (Cells p (cs.take k) ∗
      (Cells (p + k) [cs[k]] ∗ Cells (p + (k + 1)) (cs.drop (k + 1)))) := by
    have split : cs = cs.take k ++ (cs[k] :: cs.drop (k + 1)) := by
      rw [← List.drop_eq_getElem_cons inside, List.take_append_drop]
    conv_lhs => rw [split]
    rw [cells_append, prefixLength, cells_cons, Ptr.add_add]
  have result : Cells (L := L) p (cs.set k (some v)) = (Cells p (cs.take k) ∗
      (Cells (p + k) [some v] ∗ Cells (p + (k + 1)) (cs.drop (k + 1)))) := by
    rw [List.set_eq_take_append_cons_drop, if_pos inside, cells_append, prefixLength,
      cells_cons, Ptr.add_add]
  rw [shape, result]
  apply frame_left
  apply frame
  exact triple_pre _ (fun σ holds => ⟨cs[k], holds⟩) (store_spec (p + k) v)

namespace CProg

/-- Initialize supplied, already owned cells. This executes stores only;
allocation, automatic-storage admission and the end of its lifetime remain
the enclosing region's obligations. -/
def initializeCells (p : Ptr) : List V → CProg V Unit
  | [] => pure ()
  | value :: rest => do
      CProg.store p value
      initializeCells (p + 1) rest


/-- Read the complete typed-cell sequence before any subsequent publication.
Each value, including a nullable pointer, is retained without narrowing or
deep-copying its referenced storage. This is not a native byte-copy model. -/
def loadCells (p : Ptr) : Nat → CProg V (List V)
  | 0 => pure []
  | count + 1 => do
      let first ← CProg.load p
      let rest ← loadCells (p + 1) count
      pure (first :: rest)

/-- A typed aggregate transfer snapshots its source cells before writing its
destination. The ownership proof supplies separate initialized source and
writable destination ranges; storage allocation and ABI layout are separate. -/
def copyCells (source destination : Ptr) (count : Nat) : CProg V Unit := do
  let values ← loadCells source count
  initializeCells destination values

end CProg

/-- Initialization keeps all declared elements and their order, under the
existing cell ownership and frame rules. It neither adds allocator failure
nor treats a temporary C array as a heap allocation. -/
theorem initialize_cells (p : Ptr) (old : List (Option V)) (values : List V)
    (lengths : old.length = values.length) :
    CTriple (L := L) (Cells p old) (CProg.initializeCells p values)
      (fun _ => Cells p (values.map some)) := by
  induction values generalizing p old with
  | nil =>
      have vacant : old = [] := by simpa using lengths
      subst old
      simpa only [CProg.initializeCells, List.map_nil, Prog.pure_eq] using
        (triple_ret act () (fun _ : Unit => Cells (L := L) p ([] : List (Option V))))
  | cons value rest ih =>
      cases old with
      | nil => simp at lengths
      | cons previous tail =>
          have tailLength : tail.length = rest.length := by simpa using lengths
          rw [CProg.initializeCells, cells_cons p previous tail, List.map_cons,
            cells_cons p (some value) (rest.map some)]
          have first : CTriple (L := L) (Cells p [previous]) (CProg.store p value)
              (fun _ => Cells p [some value]) :=
            triple_pre _ (fun _ held => ⟨previous, held⟩) (store_spec p value)
          refine triple_bind _ (frame first (Cells (p + 1) tail)) fun _ => ?_
          exact frame_left (ih (p + 1) tail tailLength) (Cells p [some value])

theorem empty_initialization_has_no_memory_action (p : Ptr) :
    CProg.initializeCells (V := V) p [] = pure () := rfl

theorem two_initializers_keep_both_stores (p : Ptr) (first second : V) :
    CProg.initializeCells p [first, second] =
      (CProg.store p first >>= fun _ => CProg.store (p + 1) second >>= fun _ => pure ()) := rfl

/-- Complete reads preserve the source range and return its entire ordered
value sequence. Uninitialized cells do not satisfy this precondition. -/
theorem load_cells (p : Ptr) (values : List V) :
    CTriple (L := L) (Cells p (values.map some)) (CProg.loadCells p values.length)
      (fun actual σ => actual = values ∧ Cells p (values.map some) σ) := by
  induction values generalizing p with
  | nil =>
      exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
        (triple_ret act [] (fun actual σ => actual = [] ∧ Cells p ([] : List (Option V)) σ))
  | cons value rest ih =>
      rw [List.length_cons, CProg.loadCells]
      have first : CTriple (L := L) (Cells p ((value :: rest).map some))
          (CProg.load p) (fun actual σ => actual = value ∧ Cells p ((value :: rest).map some) σ) := by
        apply load_rule
        intro σ held
        rw [List.map_cons, cells_cons] at held
        exact read_of_pointsTo held
      refine triple_bind _ first fun actual => ?_
      apply triple_pure
      intro actualValue
      subst actual
      have tail := frame_left (ih (p + 1)) (Cells p [some value])
      simp only [sepConj_pure_right] at tail
      rw [List.map_cons, cells_cons]
      refine triple_bind _ tail fun actualRest => ?_
      apply triple_pure
      intro restValue
      subst actualRest
      exact triple_pre _ (fun _ held => ⟨rfl, held⟩)
        (triple_ret act (value :: rest) (fun actual σ => actual = value :: rest ∧
          (Cells p [some value] ∗ Cells (p + 1) (rest.map some)) σ))

/-- Separately owned ranges justify complete aggregate transfer. The source
contents and all pointer identities remain intact, and every destination cell
receives its corresponding source value. -/
theorem copy_cells (source destination : Ptr) (old : List (Option V)) (values : List V)
    (lengths : old.length = values.length) :
    CTriple (L := L) (Cells source (values.map some) ∗ Cells destination old)
      (CProg.copyCells source destination values.length)
      (fun _ => Cells source (values.map some) ∗ Cells destination (values.map some)) := by
  unfold CProg.copyCells
  have loaded := frame (load_cells (L := L) source values) (Cells destination old)
  simp only [sepConj_pure_left] at loaded
  refine triple_bind _ loaded fun actual => ?_
  apply triple_pure
  intro valuesMatch
  subst actual
  exact frame_left (initialize_cells (L := L) destination old values lengths)
    (Cells source (values.map some))

theorem empty_copy_has_no_memory_action (source destination : Ptr) :
    CProg.copyCells (V := V) source destination 0 = pure () := rfl

/-- Two-cell transfer retains both source loads before either destination
store, even when the supplied values contain shared pointers. -/
theorem two_cell_copy_reads_before_writes (source destination : Ptr) :
    CProg.copyCells (V := V) source destination 2 =
      (CProg.load source >>= fun first => CProg.load (source + 1) >>= fun second =>
        CProg.store destination first >>= fun _ =>
        CProg.store (destination + 1) second >>= fun _ => pure ()) := by
  simp only [CProg.copyCells, CProg.loadCells, CProg.initializeCells,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]

/-- A complete transfer cannot repair an uninitialized first source cell
or skip it to reach a later field. -/
theorem copy_uninitialized_first_is_unsafe (source destination : Ptr) (count : Nat)
    (σ : Heap L) (uninitialized : read ((σ source.block).2 source.offset) = some none) :
    ¬ (CProg.copyCells (V := V) source destination (count + 1)).Safe act σ := by
  intro safe
  simp only [CProg.copyCells, CProg.loadCells, Prog.bind_eq, Prog.bind_assoc] at safe
  have first := (Prog.safe_bind act _ _ σ).mp safe
  obtain ⟨value, loaded⟩ := first.1.1
  rw [uninitialized] at loaded
  cases loaded

/-- A one-cell source and destination cannot each own the same cell. Exact
self-copy is outside this separate-range contract. -/
theorem overlapping_owned_copy_precondition_is_false (address : Ptr) (left right : V)
    (σ : Heap L) :
    ¬ (Cells (L := L) address [some left] ∗ Cells address [some right]) σ :=
  pointsTo_sepConj_self_false address left right σ

/-- **Append into spare capacity**: storing into the first spare cell of an
array extends its contents.  This is the memory effect of `a[n++] = v`. -/
theorem store_append (p : Ptr) (cap : ℕ) (xs : List V) (v : V) (room : xs.length < cap) :
    CTriple (L := L) (DynArray (some p) cap xs) (CProg.store (p + xs.length) v)
      (fun _ => DynArray (some p) cap (xs ++ [v])) := by
  refine triple_pre _ (P := fun σ => p.offset = 0 ∧ ∃ spare : List (Option V),
      spare.length = cap - xs.length ∧ (LiveBlock p.block cap ∗ Cells p (xs.map some ++ spare)) σ)
    (fun σ holds => by
      obtain ⟨base, -, rest⟩ := (dynArray_some_iff p cap xs σ).mp holds
      exact ⟨base, rest⟩) ?_
  apply triple_pure
  intro base
  apply triple_exists
  intro spare
  apply triple_pure
  intro spareLength
  cases spare with
  | nil =>
    simp only [List.length_nil] at spareLength
    omega
  | cons c rest =>
    have inside : xs.length < (xs.map some ++ c :: rest).length := by simp
    have stored := frame_left (store_cells (L := L) p (xs.map some ++ c :: rest)
      (k := xs.length) inside v) (LiveBlock p.block cap)
    refine triple_post _ stored fun _ σ holds => ?_
    have set : (xs.map some ++ c :: rest).set xs.length (some v) =
        (xs ++ [v]).map some ++ rest := by
      rw [List.set_append_right _ _ (by simp)]
      simp
    rw [set] at holds
    refine (dynArray_some_iff p cap (xs ++ [v]) σ).mpr ⟨base, ?_, rest, ?_, holds⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [List.length_cons] at spareLength
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- After a move, the new block is not the old one: each holds its own header. -/
theorem moved_array_is_fresh {p q : Ptr} {n m : ℕ} {xs : List V} {σ : Heap L}
    (holds : (DynArray (some p) n xs ∗ DeadStorage (some q) m) σ) : p.block ≠ q.block := by
  obtain ⟨x, y, separate, -, array, rfl⟩ := holds
  intro same
  have live := header_of_dynArray array
  have headers := (separate p.block).1
  rw [live, same] at headers
  simp only [atBlock_same] at headers
  exact Excl.not_separate_own _ _ headers

/-- **Two arrays in one block are never held separately.** -/
theorem dynArray_sepConj_self_false (p : Ptr) (n m : ℕ) (xs ys : List V) (σ : Heap L) :
    ¬ (DynArray (some p) n xs ∗ DynArray (some p) m ys) σ := by
  rintro ⟨x, y, separate, -, first, second⟩
  have headers := (separate p.block).1
  rw [header_of_dynArray first, header_of_dynArray second] at headers
  exact Excl.not_separate_own _ _ headers

end DynArray

/-! ## The `reserve` helper -/

/-- The capacity `reserve` requests when `required` exceeds the current
capacity `cap`: the growth function started at `cap`, or at 4 when `cap` is
zero. -/
def nextCapacity (required cap : UInt32) : ℕ :=
  OrderedDependencyCapacity.grow required.toNat (if cap.toNat = 0 then 4 else cap.toNat)

theorem nextCapacity_covers (required cap : UInt32) :
    required.toNat ≤ nextCapacity required cap :=
  OrderedDependencyCapacity.grow_covers_request _ _

theorem nextCapacity_preserves (required cap : UInt32) :
    cap.toNat ≤ nextCapacity required cap := by
  have grown := OrderedDependencyCapacity.grow_preserves_capacity required.toNat
    (if cap.toNat = 0 then 4 else cap.toNat)
  unfold nextCapacity
  by_cases zero : cap.toNat = 0
  · rw [zero]
    exact Nat.zero_le _
  · simp only [zero, if_false] at grown ⊢
    exact grown

theorem nextCapacity_bounded (required cap : UInt32) :
    nextCapacity required cap ≤ OrderedDependencyCapacity.maximum := by
  apply OrderedDependencyCapacity.grow_bounded
  · have := required.toNat_lt
    simp only [OrderedDependencyCapacity.maximum]
    omega
  · split
    · simp [OrderedDependencyCapacity.maximum]
    · have := cap.toNat_lt
      simp only [OrderedDependencyCapacity.maximum]
      omega

/-- The requested capacity fits in a `uint32_t`, so storing it is exact. -/
theorem nextCapacity_toNat (required cap : UInt32) :
    (UInt32.ofNat (nextCapacity required cap)).toNat = nextCapacity required cap := by
  apply UInt32.toNat_ofNat_of_lt'
  have := nextCapacity_bounded required cap
  simp only [OrderedDependencyCapacity.maximum] at this
  change nextCapacity required cap < 4294967296
  omega

/-- **`space_module_link_reserve`** over block memory: `items` is the address of
the array pointer field and `capacity` the address of the capacity field. -/
def reserve (pointerBytes sizeMaximum : ℕ) (items capacity : Ptr) (required : UInt32) :
    CProg CVal Bool := do
  let cap ← CProg.loadU32 capacity
  if required ≤ cap then
    pure true
  else if sizeMaximum < nextCapacity required cap * pointerBytes then
    pure false
  else
    let old ← CProg.loadPtr items
    match ← CProg.realloc old (nextCapacity required cap) with
    | none => pure false
    | some grown => do
      CProg.store items (.ptr (some grown))
      CProg.store capacity (.u32 (UInt32.ofNat (nextCapacity required cap)))
      pure true

section Reserve

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- The two fields of a C struct that describe a dynamic array, and the array:
`items ↦ a ∗ capacity ↦ cap ∗ DynArray a cap xs`. -/
def ArrayFields (items capacity : Ptr) (a : Option Ptr) (cap : UInt32) (xs : List CVal) :
    Heap L → Prop :=
  PointsTo items (.ptr a) ∗ (PointsTo capacity (.u32 cap) ∗ DynArray a cap.toNat xs)

theorem pointsTo_le_any (p : Ptr) (v : CVal) :
    PointsTo (L := L) p v ≤ PointsToAny p := fun _ holds => ⟨some v, holds⟩

/-- **The specification of `reserve`.** -/
theorem reserve_spec (pointerBytes sizeMaximum : ℕ) (items capacity : Ptr) (required : UInt32)
    (a : Option Ptr) (cap : UInt32) (xs : List CVal) :
    CTriple (L := L) (ArrayFields items capacity a cap xs)
      (reserve pointerBytes sizeMaximum items capacity required)
      (fun ok σ =>
        (ok = true ∧ required ≤ cap ∧ ArrayFields items capacity a cap xs σ) ∨
        (ok = true ∧ ∃ (p : Ptr) (c : UInt32), required.toNat ≤ c.toNat ∧
          cap.toNat ≤ c.toNat ∧ (ArrayFields items capacity (some p) c xs ∗
            DeadStorage a cap.toNat) σ) ∨
        (ok = false ∧ ArrayFields items capacity a cap xs σ)) := by
  unfold reserve
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := cap) fun σ holds => ?_) fun c => ?_
  · rw [ArrayFields, sepConj_left_comm] at holds
    exact read_of_pointsTo holds
  apply triple_pure
  intro same
  subst same
  by_cases fits : required ≤ c
  · rw [if_pos fits]
    refine triple_pre _ ?_ (triple_ret _ true _)
    intro σ holds
    exact Or.inl ⟨rfl, fits, holds⟩
  rw [if_neg fits]
  by_cases tooLarge : sizeMaximum < nextCapacity required c * pointerBytes
  · rw [if_pos tooLarge]
    refine triple_pre _ ?_ (triple_ret _ false _)
    intro σ holds
    exact Or.inr (Or.inr ⟨rfl, holds⟩)
  rw [if_neg tooLarge]
  refine triple_bind _ (loadPtr_rule (q := a) fun σ holds => read_of_pointsTo holds)
    fun old => ?_
  apply triple_pure
  intro same
  subst same
  have positive : 0 < nextCapacity required c := by
    have covers := nextCapacity_covers required c
    have grows : c < required := Nat.not_le.mp fits
    have := UInt32.lt_iff_toNat_lt.mp grows
    omega
  set fields := PointsTo (L := L) items (.ptr old) ∗ PointsTo capacity (.u32 c) with fieldsDef
  have moved := frame_left (realloc_dynArray (L := L) old c.toNat (nextCapacity required c) xs
    positive (nextCapacity_preserves required c)) fields
  refine triple_bind _ (triple_pre _ (fun σ holds => ?_) moved) fun g => ?_
  · rwa [ArrayFields, ← sepConj_assoc] at holds
  cases g with
  | none =>
    refine triple_pre _ (fun σ holds => ?_) (triple_ret _ false _)
    refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    rw [ArrayFields, ← sepConj_assoc]
    refine sepConj_mono le_rfl (fun τ unchanged => ?_) σ holds
    rcases unchanged with ⟨-, array⟩ | ⟨b, impossible, -⟩
    · exact array
    · cases impossible
  | some grown =>
    simp only
    set next := nextCapacity required c
    set rest := DynArray (L := L) (some grown) next xs ∗ DeadStorage old c.toNat with restDef
    have arrived : ∀ σ, (fields ∗ fun σ => (some grown = none ∧ DynArray old c.toNat xs σ) ∨
        ∃ b, some grown = some ⟨b, 0⟩ ∧
          (DynArray (some ⟨b, 0⟩) next xs ∗ DeadStorage old c.toNat) σ) σ →
        (PointsToAny items ∗ (PointsTo capacity (.u32 c) ∗ rest)) σ := by
      intro σ holds
      rw [fieldsDef, sepConj_assoc] at holds
      refine sepConj_mono (pointsTo_le_any items _) (sepConj_mono le_rfl ?_) σ holds
      rintro τ (⟨impossible, -⟩ | ⟨b, same, moved⟩)
      · cases impossible
      · cases same
        exact moved
    refine triple_bind _ (triple_pre _ arrived
      (frame (store_spec items (CVal.ptr (some grown))) _)) fun _ => ?_
    refine triple_bind _ (triple_pre _ (fun σ holds => ?_)
      (frame_left (frame (store_spec capacity (CVal.u32 (UInt32.ofNat next))) rest)
        (PointsTo items (.ptr (some grown))))) fun _ => ?_
    · exact sepConj_mono le_rfl (sepConj_mono (pointsTo_le_any capacity _) le_rfl) σ holds
    refine triple_pre _ (fun σ holds => ?_) (triple_ret _ true _)
    refine Or.inr (Or.inl ⟨rfl, grown, UInt32.ofNat next, ?_, ?_, ?_⟩)
    · rw [nextCapacity_toNat]
      exact nextCapacity_covers required c
    · rw [nextCapacity_toNat]
      exact nextCapacity_preserves required c
    · rw [ArrayFields, nextCapacity_toNat, sepConj_assoc, sepConj_assoc]
      exact holds

end Reserve

end Mettapedia.Machines.CMemory
