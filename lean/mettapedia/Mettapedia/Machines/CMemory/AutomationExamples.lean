import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.Examples
import Mettapedia.Machines.CMemory.Lift

/-!
# Proof automation for C programs: examples, a re-proof and controls

**Positive.**

* `increment_spec`, `swap_spec`: loads and stores against cells beside a frame,
  proved by symbolic execution alone (`cmem_vcgen`, then `cmem_exact`).
* `overwrite_then_read_separate`: two stores into separate cells keep both
  values; the separating conjunction of the precondition is what makes the
  second store leave the first cell alone.
* `base_comparison_after_store`: comparing a struct's base pointer after a
  store into one of its fields.  Its validity comes from the well-formedness
  of the whole of memory, which the tactics carry across the store.
* `reserve_spec_by_vcgen`: CeTTa's `space_module_link_reserve` meets the
  specification of `CMemory.Array.reserve_spec`, the same statement, re-proved
  with the tactics.
* `publish_refines_by_vcgen`: the publisher loop of `CMemory.Lift`, the same
  statement as `publish_refines`, proved with a loop invariant (`cmem_loop`)
  rather than by induction.

**Negative.**  Each program below is undefined in C, and the tactics fail on
it rather than prove it.  The `#guard_msgs` tests record the failure: each
fails at the step that has no defined meaning, saying what is missing.  The
`_unprovable` theorems show that the claimed triples are false, so no proof
of them exists at all.

* use after free: a load from a freed block (`use_after_free_unprovable`);
* an out-of-bounds store, one past the end of an array
  (`store_past_end_unprovable`);
* a missing disjointness premise: two cells described by an ordinary
  conjunction may be one cell, and then the second store overwrites the first
  (`overwrite_then_read_aliased_unprovable`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.AutomationExamples

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-! ## Positive -/

/-- `*p += 1` on a `uint32_t`. -/
def increment (p : Ptr) : CProg CVal Unit := do
  let n ← CProg.loadU32 p
  CProg.store p (.u32 (n + 1))

theorem increment_spec (p q : Ptr) (n : UInt32) (w : CVal) :
    CTriple (L := L) (PointsTo q w ∗ PointsTo p (.u32 n)) (increment p)
      (fun _ => PointsTo p (.u32 (n + 1)) ∗ PointsTo q w) := by
  cmem_start σ h
  unfold increment
  cmem_vcgen
  cmem_exact

/-- Exchange two cells. -/
def swap (p q : Ptr) : CProg CVal Unit := do
  let a ← CProg.load p
  let b ← CProg.load q
  CProg.store p b
  CProg.store q a

theorem swap_spec (p q : Ptr) (a b : CVal) :
    CTriple (L := L) (PointsTo p a ∗ PointsTo q b) (swap p q)
      (fun _ => PointsTo p b ∗ PointsTo q a) := by
  cmem_start σ h
  unfold swap
  cmem_vcgen
  cmem_exact

/-- Store into `p`, then into `q`, then read `p` back. -/
def overwriteThenRead (p q : Ptr) : CProg CVal CVal :=
  CProg.store p (.u32 1) >>= fun _ => CProg.store q (.u32 2) >>= fun _ => CProg.load p

theorem overwrite_then_read_separate (p q : Ptr) :
    CTriple (L := L) (PointsToAny p ∗ PointsToAny q) (overwriteThenRead p q)
      (fun r σ => r = .u32 1 ∧ (PointsTo p (.u32 1) ∗ PointsTo q (.u32 2)) σ) := by
  cmem_start σ h
  unfold overwriteThenRead
  cmem_vcgen
  cmem_exact

/-- Store into the field at offset `k` of a struct, then test its base pointer
against null. -/
def storeThenTestBase (base : Ptr) (k : ℕ) (w : CVal) : CProg CVal Bool :=
  CProg.store (base + k) w >>= fun _ => CProg.ptrEq (some base) none

theorem base_comparison_after_store (base : Ptr) (k : ℕ) (v w : CVal) :
    CTriple (L := L) (fun σ => WellFormed σ ∧ PointsTo (base + k) v σ)
      (storeThenTestBase base k w)
      (fun r σ => r = false ∧ WellFormed σ ∧ PointsTo (base + k) w σ) := by
  cmem_start σ h
  obtain ⟨wf, h⟩ := h
  unfold storeThenTestBase
  cmem_vcgen
  exact ⟨wf, by cmem_exact⟩

/-! ## `space_module_link_reserve`, re-proved -/

/-- **The specification of `reserve`**, the statement of `reserve_spec`,
proved by symbolic execution. -/
theorem reserve_spec_by_vcgen (pointerBytes sizeMaximum : ℕ) (items capacity : Ptr)
    (required : UInt32) (a : Option Ptr) (cap : UInt32) (xs : List CVal) :
    CTriple (L := L) (ArrayFields items capacity a cap xs)
      (reserve pointerBytes sizeMaximum items capacity required)
      (fun ok σ =>
        (ok = true ∧ required ≤ cap ∧ ArrayFields items capacity a cap xs σ) ∨
        (ok = true ∧ ∃ (p : Ptr) (c : UInt32), required.toNat ≤ c.toNat ∧
          cap.toNat ≤ c.toNat ∧ (ArrayFields items capacity (some p) c xs ∗
            DeadStorage a cap.toNat) σ) ∨
        (ok = false ∧ ArrayFields items capacity a cap xs σ)) := by
  cmem_start σ h
  unfold reserve
  cmem_step
  split_ifs with fits tooLarge
  · exact Or.inl ⟨fits, h⟩
  · exact h
  cmem_step
  have positive : 0 < nextCapacity required cap := by
    have := nextCapacity_covers required cap
    have := UInt32.lt_iff_toNat_lt.mp (Nat.not_le.mp fits)
    omega
  cmem_call realloc_dynArray a cap.toNat _ xs positive (nextCapacity_preserves required cap)
    with g σ (⟨rfl, h⟩ | ⟨b, rfl, h⟩)
  · cmem_norm
    cmem_exact
  · cmem_vcgen
    refine Or.inr ⟨⟨b, 0⟩, UInt32.ofNat (nextCapacity required cap), ?_, ?_, ?_⟩
    · rw [nextCapacity_toNat]
      exact nextCapacity_covers required cap
    · rw [nextCapacity_toNat]
      exact nextCapacity_preserves required cap
    · rw [ArrayFields, nextCapacity_toNat]
      cmem_exact

/-- The re-proved statement is exactly that of `reserve_spec`. -/
example : type_of% @reserve_spec_by_vcgen.{0} = type_of% @reserve_spec.{0} := rfl

/-! ## The publisher loop, with an invariant -/

section Publish

open Mettapedia.Machines.CMemory.Lift

variable {Id : Type} (addr : Id → Ptr)

/-- **The publisher loop refines `writeBatch`**, the statement of
`Lift.publish_refines`, proved with the loop invariant: some split heap `H₁`
represents the store, its batch over the identities still pending is the
whole batch, and it is ready for them. -/
theorem publish_refines_by_vcgen [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (distinct : D.Nodup) {reader : Id} (readerIn : reader ∈ D) :
    ∀ (pending : List Id) (H : SplitHeap Id), (∀ s ∈ pending, s ∈ D) → reader ∉ pending →
      OrderedDependencyCArray.Ready H reader pending →
      CTriple (L := L) (StoreRep addr layout D H) (publishProg addr layout reader pending)
        (fun _ σ => ∃ H', OrderedDependencyCArray.writeBatch H reader pending = some H' ∧
          StoreRep addr layout D H' σ) := by
  intro pending H pendingIn notSelf ready
  cmem_start σ h
  unfold publishProg
  cmem_loop (fun rest _ σ => ∃ H₁, OrderedDependencyCArray.writeBatch H reader pending =
      OrderedDependencyCArray.writeBatch H₁ reader rest ∧ (∀ s ∈ rest, s ∈ D) ∧
      reader ∉ rest ∧ OrderedDependencyCArray.Ready H₁ reader rest ∧
      StoreRep addr layout D H₁ σ)
  case invariant => exact ⟨H, rfl, pendingIn, notSelf, ready, h⟩
  case post =>
    rintro - σ ⟨H₁, batch, -, -, -, h⟩
    exact ⟨H₁, batch, h⟩
  case step =>
    intro source rest _
    cmem_start σ h
    obtain ⟨H₁, batch, restIn, notSelf, ready, h⟩ := h
    have sourceIn := restIn source List.mem_cons_self
    have different : reader ≠ source := fun same => notSelf (same ▸ List.mem_cons_self)
    have forwardRoom : (H₁.forward reader).Room := by
      have capacity := ready.2.2.1
      simp only [List.length_cons] at capacity
      change (H₁.forward reader).count.toNat < (H₁.forward reader).slots.length
      omega
    cmem_call writeLink_refines addr layout H₁ reader source different ready.1 forwardRoom
      (ready.2.2.2 source List.mem_cons_self) with - σ ⟨H₂, linked, h⟩
    refine ⟨H₂, by rw [batch]; simp [OrderedDependencyCArray.writeBatch, linked],
      fun s member => restIn s (List.mem_cons_of_mem _ member),
      fun member => notSelf (List.mem_cons_of_mem _ member),
      OrderedDependencyCArray.ready_after_first ready linked, ?_⟩
    obtain ⟨forward, reverse, -, -, rfl⟩ := OrderedDependencyCArray.writeLink_fields linked
    rw [storeRep_split addr layout _ readerIn sourceIn different,
      storeRep_congr addr layout (H := H₁)]
    · exact h
    · intro i member
      rw [(List.Nodup.erase reader distinct).mem_erase_iff, distinct.mem_erase_iff] at member
      exact ⟨Function.update_of_ne member.2.1 _ _, Function.update_of_ne member.1 _ _⟩

/-- The re-proved statement is exactly that of `publish_refines`. -/
example : type_of% @publish_refines_by_vcgen.{0} = type_of% @publish_refines.{0} := rfl

end Publish

/-! ## Negative controls -/

/-! ### Use after free -/

/-- Free a block, then load from it. -/
def useAfterFree (b : BlockId) (k : ℕ) : CProg CVal CVal := do
  CProg.free (some ⟨b, 0⟩)
  CProg.load ⟨b, k⟩

/--
error: cmem_step: the load
  CProg.load { block := b, offset := k }
needs a conjunct that reads an initialized value at its address.
No hypothesis about the state `σ` provides it (1 tried).
-/
#guard_msgs in
example (b : BlockId) (n k : ℕ) (v : CVal) :
    CTriple (L := L) (LiveBlock b n ∗ CellsAny ⟨b, 0⟩ n) (useAfterFree b k)
      (fun r _ => r = v) := by
  cmem_start σ h
  unfold useAfterFree
  cmem_norm
  cmem_call free_spec b n with - σ h
  cmem_step

/-- The memory of one live block of `n` indeterminate cells. -/
abbrev freshMemory (b : BlockId) (n : ℕ) : Heap L :=
  atBlock b (.own ⟨n, true⟩, segment 0 ((List.replicate n (none : Option CVal)).map whole))

theorem freshMemory_holds (b : BlockId) (n : ℕ) :
    (LiveBlock (L := L) b n ∗ CellsAny (V := CVal) ⟨b, 0⟩ n) (freshMemory b n) := by
  have block := (liveBlock_cells_iff (L := L) b (List.replicate n (none : Option CVal)) n
    (freshMemory b n)).mpr rfl
  exact sepConj_mono le_rfl (fun τ cells => ⟨_, List.length_replicate, cells⟩) _ block

/-- **Negative control: use after free.**  No postcondition is met: from a
state that holds the live block, the load after `free` is undefined. -/
theorem use_after_free_unprovable (b : BlockId) (n k : ℕ) (Q : CVal → Heap L → Prop) :
    ¬ CTriple (L := L) (LiveBlock b n ∗ CellsAny ⟨b, 0⟩ n) (useAfterFree b k) Q := by
  intro spec
  exact Examples.use_after_free_undefined (L := L) (V := CVal) b n k (freshMemory_holds b n)
    (spec _ (freshMemory_holds b n)).1

/-! ### Out-of-bounds store -/

/-- Store one past the last cell of an array of `cap` cells. -/
def storePastEnd (p : Ptr) (cap : ℕ) (v : CVal) : CProg CVal Unit :=
  CProg.store (p + cap) v

/--
error: cmem_step: the store
  CProg.store (p + cap) v
needs a conjunct that holds the whole cell at its address.
No hypothesis about the state `σ` provides it (1 tried).
-/
#guard_msgs in
example (p : Ptr) (cap : ℕ) (xs : List CVal) (v : CVal) (Q : Unit → Heap L → Prop) :
    CTriple (L := L) (DynArray (some p) cap xs) (storePastEnd p cap v) Q := by
  cmem_start σ h
  unfold storePastEnd
  cmem_step

/-- The memory of an array of one cell. -/
abbrev singleMemory (b : BlockId) (v : CVal) : Heap L :=
  atBlock b (.own ⟨1, true⟩, segment 0 [whole (some v)])

theorem singleMemory_holds (b : BlockId) (v : CVal) :
    DynArray (L := L) (some ⟨b, 0⟩) 1 [v] (singleMemory b v) := by
  refine (dynArray_some_iff _ _ _ _).mpr ⟨rfl, by simp, [], by simp, ?_⟩
  exact (liveBlock_cells_iff (L := L) b _ 1 _).mpr (by simp)

/-- **Negative control: out-of-bounds store.**  From the memory of an array of
one cell, a store into its second cell is undefined. -/
theorem store_past_end_unprovable (b : BlockId) (v w : CVal) (Q : Unit → Heap L → Prop) :
    ¬ CTriple (L := L) (DynArray (some ⟨b, 0⟩) 1 [v]) (storePastEnd ⟨b, 0⟩ 1 w) Q := by
  intro spec
  obtain ⟨⟨⟨c, whole_at⟩, -⟩, -⟩ := spec _ (singleMemory_holds b v)
  have outside : (singleMemory (L := L) b v b).2 1 = 0 := by
    simp only [atBlock_same]
    exact segment_of_le _ (by simp)
  change ((singleMemory (L := L) b v) b).2 (0 + 1) = whole c at whole_at
  rw [Nat.zero_add, outside] at whole_at
  exact whole_ne_zero c whole_at.symm

/-! ### Missing disjointness premise -/

/--
error: cmem_step: the store
  CProg.store q (CVal.u32 2)
needs a conjunct that holds the whole cell at its address.
No hypothesis about the state `σ` provides it (1 tried).
-/
#guard_msgs in
example (p q : Ptr) :
    CTriple (L := L) (fun σ => PointsToAny p σ ∧ PointsToAny q σ) (overwriteThenRead p q)
      (fun r _ => r = .u32 1) := by
  cmem_start σ h
  obtain ⟨hp, hq⟩ := h
  unfold overwriteThenRead
  cmem_step
  cmem_step

/-- **Negative control: a missing disjointness premise.**  Described by an
ordinary conjunction, the two cells may be one cell; then the second store
overwrites the first, and the promised read is false. -/
theorem overwrite_then_read_aliased_unprovable (p : Ptr) :
    ¬ CTriple (L := L) (fun σ => PointsToAny p σ ∧ PointsToAny p σ) (overwriteThenRead p p)
      (fun r _ => r = .u32 1) := by
  intro spec
  let σ₀ : Heap L := atBlock p.block (.empty, segment p.offset [whole (none : Option CVal)])
  have cell : PointsToAny (L := L) (V := CVal) p σ₀ := ⟨none, rfl⟩
  obtain ⟨safe, returns⟩ :=
    Examples.aliased_stores_lose_first_write (L := L) p (CVal.u32 1) (CVal.u32 2) σ₀ cell
  obtain ⟨r, σ', runs⟩ := exists_runs _ σ₀ safe
  have promised := (spec σ₀ ⟨cell, cell⟩).2 r σ' runs
  rw [(returns r σ' runs).1] at promised
  simp at promised

end Mettapedia.Machines.CMemory.AutomationExamples
