import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.DependencyPublication

/-!
# Proof automation on the dependency fragments

Four results of the dependency modules, each re-proved with the tactics of
`CMemory.Tactic` under exactly its original statement (checked by the
`example`s that compare the two types).  The originals are imported, not
edited.

* `load_item_refines_by_vcgen`: the two loads of `items[i]` refine the
  counted array's `i`-th active identity (`DependencyReads.load_item_refines`).
* `store_count_load_by_vcgen`, `store_capacity_load_by_vcgen`: a module's
  counter and capacity are loaded from its cells inside the representation of
  the whole store (`DependencyReads.store_count_load`, `store_capacity_load`);
  the search finds the module's member of the iterated conjunction.
* `run_refines_remaining_by_vcgen`: the publisher loop, which loads the
  reservation's count at every condition and its pending identity at every
  iteration, refines the remaining ordered batch
  (`DependencyPublication.run_refines_remaining`).  The loop is an induction
  over the remaining identities whose hypothesis is called like any other
  specification.

What stays manual is what is not about memory: the arithmetic of indices and
capacities, the readiness of the split heap, and the order of the batch.

The lowered statement forms need no second calculus: every interpreter of
parsed C produces a `CProg`, so its equations go to `cmem_norm` beside the
facts about the local environment, and the memory steps are those of any other
program.  The publisher here is such a lowering (`publisherCode`, run by
`run`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.AutomationDependency

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.Lift
open Mettapedia.Machines.CMemory.DependencyReads
open Mettapedia.Machines.CMemory.DependencyPublication
open PostIndex (Array32)
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]
variable {Id : Type} (addr : Id → Ptr)

/-! ## A dependency read -/

/-- **The physical load of `items[i]`** returns the address of the counted
array's `i`-th active identity and keeps the whole representation. -/
theorem load_item_refines_by_vcgen {items count capacity : Ptr} (A : Array32 Id)
    (index : UInt32) (inside : index.toNat < A.active.length) (F : Heap L → Prop) :
    CTriple (CountedArray addr items count capacity A ∗ F) (loadItem items index)
      (fun r σ => r = some (addr A.active[index.toNat]) ∧
        (CountedArray addr items count capacity A ∗ F) σ) := by
  cmem_start σ h
  unfold CountedArray at h ⊢
  sep_norm at h ⊢
  obtain ⟨within, a, h⟩ := h
  unfold loadItem
  cmem_step
  cases a with
  | none =>
    cmem_norm
    have empty : A.active.map (spacePtr ∘ addr) = [] := by cmem_fact
    simp only [List.map_eq_nil_iff] at empty
    simp [empty] at inside
  | some p =>
    cmem_step [List.getElem_map, Function.comp_apply, spacePtr]
    exact ⟨within, some p, h⟩

example : type_of% @load_item_refines_by_vcgen.{0} = type_of% @load_item_refines.{0} := rfl

/-! ## Field loads from a store of modules -/

/-- **A module's counter is loaded from its block cell**, with the whole store
kept: the read is found in the member of the iterated conjunction. -/
theorem store_count_load_by_vcgen [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (CProg.loadU32 (addr owner + (arrayOffsets layout direction).2.1))
      (fun r σ => r = (selectedArray H owner direction).count ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  cmem_start σ h
  cases direction <;> cmem_step [arrayOffsets, selectedArray] <;> exact h

example : type_of% @store_count_load_by_vcgen.{0} = type_of% @store_count_load.{0} := rfl

/-- **A module's capacity is loaded from its block cell**, with the whole store
kept. -/
theorem store_capacity_load_by_vcgen [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (CProg.loadU32 (addr owner + (arrayOffsets layout direction).2.2))
      (fun r σ => r = UInt32.ofNat (selectedArray H owner direction).slots.length ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  cmem_start σ h
  cases direction <;> cmem_step [arrayOffsets, selectedArray] <;> exact h

example : type_of% @store_capacity_load_by_vcgen.{0} = type_of% @store_capacity_load.{0} :=
  rfl

/-! ## The publisher loop -/

/-- **The publisher loop refines the remaining ordered batch**: from position
`index`, with `remaining` still pending, the loop reads every pending identity
from the reservation and publishes its link. -/
theorem run_refines_remaining_by_vcgen [DecidableEq Id] (layout : SpaceLayout)
    (reservationLayout : ReservationLayout) {D : List Id} (distinct : D.Nodup)
    {reader : Id} (readerIn : reader ∈ D) (reservation : Ptr) (array : Option Ptr)
    (capacity : Nat) (added : UInt32) (remaining : List Id) :
    ∀ (prior : List Id) (index : UInt32) (fuel : Nat) (H : SplitHeap Id),
      index.toNat = prior.length → added.toNat = (prior ++ remaining).length →
      remaining.length ≤ fuel → (∀ s ∈ remaining, s ∈ D) → reader ∉ remaining →
      OrderedDependencyCArray.Ready H reader remaining →
      CTriple (L := L)
        (StoreRep addr layout D H ∗
          ReservationFields addr reservationLayout reservation array capacity added
            (prior ++ remaining))
        (run layout reservationLayout publisherCode (addr reader) reservation fuel index)
        (fun r σ => r = .finished ∧ ∃ H',
          OrderedDependencyCArray.writeBatch H reader remaining = some H' ∧
          (StoreRep addr layout D H' ∗
            ReservationFields addr reservationLayout reservation array capacity added
              (prior ++ remaining)) σ) := by
  induction remaining with
  | nil =>
    intro prior index fuel H position extent _ _ _ _
    have stopped : ¬ index < added := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.append_nil] at extent
      omega
    cmem_start σ h
    rw [run.eq_def]
    cmem_step [stopped]
    exact ⟨H, rfl, h⟩
  | cons source rest ih =>
    intro prior index fuel H position extent enough pendingIn notSelf ready
    have selected : index < added := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have increment : (index + 1).toNat = index.toNat + 1 := by
      rw [UInt32.toNat_add]
      apply Nat.mod_eq_of_lt
      have upper := added.toNat_lt
      have before := UInt32.lt_iff_toNat_lt.mp selected
      change index.toNat + 1 < 2 ^ 32
      omega
    have inside : index.toNat < (prior ++ source :: rest).length := by
      simp only [List.length_append, List.length_cons]
      omega
    have loaded : (prior ++ source :: rest)[index.toNat]'inside = source := by
      rw [List.getElem_append_right (by omega)]
      simp [position]
    have sourceIn := pendingIn source List.mem_cons_self
    have different : reader ≠ source := fun same => notSelf (same ▸ List.mem_cons_self)
    have oneReady : OrderedDependencyCArray.Ready H reader [source] := by
      refine ⟨ready.1, by simp, ?_, ?_⟩
      · have room := ready.2.2.1
        simp only [List.length_cons, List.length_nil] at room ⊢
        omega
      · simpa using ready.2.2.2 source List.mem_cons_self
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      cmem_start σ h
      rw [run.eq_def]
      cmem_step [selected, bodyProg]
      cmem_call reservation_item_load addr reservationLayout reservation array capacity added
        (prior ++ source :: rest) index inside (StoreRep addr layout D H) with - σ ⟨rfl, h⟩
      simp only [loaded, publisher_stores_use_loaded_pointer]
      cmem_call write_store_refines addr layout distinct readerIn sourceIn different H oneReady
        with - σ ⟨H', linked, h⟩
      have following := ih (prior ++ [source]) (index + 1) fuel H' (by simp [increment, position])
        (by simpa [List.append_assoc] using extent) (by simpa using enough)
        (fun s member => pendingIn s (List.mem_cons_of_mem _ member))
        (fun member => notSelf (List.mem_cons_of_mem _ member))
        (OrderedDependencyCArray.ready_after_first ready linked)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at following
      cmem_call following with r σ ⟨finished, H'', batch, h⟩
      exact ⟨finished, H'', by simp [OrderedDependencyCArray.writeBatch, linked, batch], h⟩

example : type_of% @run_refines_remaining_by_vcgen.{0} = type_of% @run_refines_remaining.{0} :=
  rfl

end Mettapedia.Machines.CMemory.AutomationDependency
