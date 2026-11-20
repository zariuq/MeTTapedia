import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.DependencyReads

/-!
# Proof automation on the dependency reads

Three results of `CMemory.DependencyReads`, each re-proved with the tactics of
`CMemory.Tactic` under exactly its original statement (checked by the
`example`s that compare the two types). The originals are imported, not
edited.

* `load_item_refines_by_vcgen`: the two loads of `items[i]` refine the
  counted array's `i`-th active identity (`DependencyReads.load_item_refines`).
* `store_count_load_by_vcgen`, `store_capacity_load_by_vcgen`: a module's
  counter and capacity are loaded from its cells inside the representation of
  the whole store (`DependencyReads.store_count_load`, `store_capacity_load`);
  the search finds the module's member of the iterated conjunction.

What stays manual is what is not about memory: the arithmetic of indices and
capacities.
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
    (direction : Direction) (F : Heap L → Prop) :
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
    (direction : Direction) (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (CProg.loadU32 (addr owner + (arrayOffsets layout direction).2.2))
      (fun r σ => r = UInt32.ofNat (selectedArray H owner direction).slots.length ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  cmem_start σ h
  cases direction <;> cmem_step [arrayOffsets, selectedArray] <;> exact h

example : type_of% @store_capacity_load_by_vcgen.{0} = type_of% @store_capacity_load.{0} :=
  rfl

end Mettapedia.Machines.CMemory.AutomationDependency
