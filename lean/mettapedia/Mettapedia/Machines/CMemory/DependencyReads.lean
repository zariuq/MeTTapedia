import Mettapedia.Machines.CMemory.Lift
import Mettapedia.Machines.OrderedDependencyCSource

/-!
# Block loads for dependency fields and indexed identity arrays

The split-array representation supplies actual typed loads, rather than a
caller-provided field oracle. The load specifications retain every framed
resource. Reading an active identity follows the pointer stored in the array
field and loads the indexed cell of that block; no list value is substituted
for a memory operation.

Offsets are the existing cell-granular layout, not a claim about a compiler's
byte ABI. Whole-runtime synchronization and the reserve/preparation programs
remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.DependencyReads

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.Lift
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open PostIndex (Array32)
open CellPermission

universe u

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

/-- A used element of a dynamic array is the value in its initialized prefix. -/
theorem read_dynArray {p : Ptr} {cap : Nat} {xs : List CVal} {i : Nat}
    {F : Heap L → Prop} {σ : Heap L} (inside : i < xs.length)
    (holds : (DynArray (some p) cap xs ∗ F) σ) :
    read ((σ (p + i).block).2 (p + i).offset) = some (some xs[i]) := by
  apply read_framed holds
  intro τ array
  obtain ⟨-, -, array⟩ := array
  rw [sepConj_comm, sepConj_assoc] at array
  exact read_cells (by simpa using inside) (by simp) array

variable {Id : Type} (addr : Id → Ptr)

/-- All three scalar field reads follow from the representation; neither
capacities nor pointers are guessed by the observer. -/
theorem counted_fields_reads {items count capacity : Ptr} {a : Option Ptr}
    {A : Array32 Id} {F : Heap L → Prop} {σ : Heap L}
    (holds : (CountedFields addr items count capacity a A ∗ F) σ) :
    read ((σ items.block).2 items.offset) = some (some (.ptr a)) ∧
    read ((σ count.block).2 count.offset) = some (some (.u32 A.count)) ∧
    read ((σ capacity.block).2 capacity.offset) =
      some (some (.u32 (UInt32.ofNat A.slots.length))) := by
  refine ⟨read_framed holds (fun _ fields => read_of_pointsTo fields), ?_, ?_⟩
  · exact read_framed holds fun _ fields =>
      read_framed_right fields fun _ rest => read_of_pointsTo rest
  · exact read_framed holds fun _ fields =>
      read_framed_right fields fun _ rest =>
        read_framed_right rest fun _ rest => read_of_pointsTo rest

theorem counted_count_read {items count capacity : Ptr} {A : Array32 Id}
    {F : Heap L → Prop} {σ : Heap L}
    (holds : (CountedArray addr items count capacity A ∗ F) σ) :
    read ((σ count.block).2 count.offset) = some (some (.u32 A.count)) := by
  obtain ⟨x, y, separate, rfl, ⟨-, a, fields⟩, frame⟩ := holds
  exact (counted_fields_reads addr ⟨x, y, separate, rfl, fields, frame⟩).2.1

theorem counted_capacity_read {items count capacity : Ptr} {A : Array32 Id}
    {F : Heap L → Prop} {σ : Heap L}
    (holds : (CountedArray addr items count capacity A ∗ F) σ) :
    read ((σ capacity.block).2 capacity.offset) =
      some (some (.u32 (UInt32.ofNat A.slots.length))) := by
  obtain ⟨x, y, separate, rfl, ⟨-, a, fields⟩, frame⟩ := holds
  exact (counted_fields_reads addr ⟨x, y, separate, rfl, fields, frame⟩).2.2

/-- The physical two-load operation for `items[i]`. A null array pointer is
not silently interpreted as an empty list or a successful load. -/
def loadItem (items : Ptr) (index : UInt32) : CProg CVal (Option Ptr) := do
  let p ← CProg.loadPtr items
  match p with
  | none => CProg.undefined
  | some p => CProg.loadPtr (p + index.toNat)

theorem load_item_refines {items count capacity : Ptr} (A : Array32 Id)
    (index : UInt32) (inside : index.toNat < A.active.length) (F : Heap L → Prop) :
    CTriple (CountedArray addr items count capacity A ∗ F) (loadItem items index)
      (fun r σ => r = some (addr A.active[index.toNat]) ∧
        (CountedArray addr items count capacity A ∗ F) σ) := by
  refine triple_pre _ (P := fun σ => ∃ a,
      (CountedFields addr items count capacity a A ∗ F) σ ∧
      A.count.toNat ≤ A.slots.length) (fun σ holds => ?_) ?_
  · obtain ⟨x, y, separate, rfl, ⟨within, a, fields⟩, frame⟩ := holds
    exact ⟨a, ⟨x, y, separate, rfl, fields, frame⟩, within⟩
  apply triple_exists
  intro a
  refine triple_pre _ (P := fun σ => A.count.toNat ≤ A.slots.length ∧
      (CountedFields addr items count capacity a A ∗ F) σ)
    (fun σ holds => ⟨holds.2, holds.1⟩) ?_
  apply triple_pure
  intro within
  unfold loadItem
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadPtr_rule (q := a) fun σ holds =>
    (counted_fields_reads addr holds).1) fun p => ?_
  apply triple_pure
  intro same
  subst p
  cases a with
  | none =>
    refine triple_pre _ (fun σ holds => ?_) (triple_false _ _ _)
    have empty := fact_of_sepConj_left holds fun τ fields =>
      fact_of_sepConj_right fields fun τ rest =>
        fact_of_sepConj_right rest fun τ rest =>
          fact_of_sepConj_right rest fun τ array => array.2.1
    have length : (A.active.map (spacePtr ∘ addr)).length = 0 := by rw [empty]; rfl
    rw [List.length_map] at length
    omega
  | some p =>
    refine triple_post _ (loadPtr_rule (q := some (addr A.active[index.toNat]))
      fun σ holds => ?_) ?_
    · rw [CountedFields] at holds
      rw [sepConj_left_comm, sepConj_left_comm, sepConj_left_comm] at holds
      have array : (DynArray (some p) A.slots.length (A.active.map (spacePtr ∘ addr)) ∗
          (PointsTo capacity (.u32 (UInt32.ofNat A.slots.length)) ∗
            (PointsTo count (.u32 A.count) ∗ (PointsTo items (.ptr (some p)) ∗ F)))) σ := by
        simpa only [sepConj_assoc, sepConj_left_comm] using holds
      have mappedInside : index.toNat < (A.active.map (spacePtr ∘ addr)).length := by
        simpa using inside
      have element : (A.active.map (spacePtr ∘ addr))[index.toNat]'mappedInside =
          spacePtr (addr A.active[index.toNat]) := by rw [List.getElem_map]; rfl
      simpa only [element, spacePtr] using
        read_dynArray (i := index.toNat) (by simpa using inside) array
    · intro r σ ⟨same, holds⟩
      refine ⟨same, ?_⟩
      obtain ⟨x, y, separate, rfl, fields, frame⟩ := holds
      exact ⟨x, y, separate, rfl, ⟨within, some p, fields⟩, frame⟩

/-- A member may be read without discarding the rest of the store. -/
theorem store_member_split [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D) :
    StoreRep (L := L) addr layout D H =
      (SpaceRep addr layout owner (H.forward owner) (H.reverse owner) ∗
        StoreRep addr layout (D.erase owner) H) := by
  rw [StoreRep, bigSep_perm ((List.perm_cons_erase member).map _),
    List.map_cons, bigSep_cons]
  rfl

def selectedArray (H : SplitHeap Id) (owner : Id) : OrderedDependencyCSource.ArrayField →
    Array32 Id
  | .forward => H.forward owner
  | .reverse => H.reverse owner

def arrayOffsets (layout : SpaceLayout) : OrderedDependencyCSource.ArrayField →
    Nat × Nat × Nat
  | .forward => (layout.deps, layout.depCount, layout.depCap)
  | .reverse => (layout.importers, layout.importerCount, layout.importerCap)

/-- Either direction exposes one counted array and frames the other direction
and every other module. No dependency view is copied for this observation. -/
theorem store_array_split [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) :
    ∃ F : Heap L → Prop, StoreRep addr layout D H =
      (CountedArray addr (addr owner + (arrayOffsets layout direction).1)
        (addr owner + (arrayOffsets layout direction).2.1)
        (addr owner + (arrayOffsets layout direction).2.2)
        (selectedArray H owner direction) ∗ F) := by
  rw [store_member_split addr layout H member, SpaceRep]
  cases direction with
  | forward => exact ⟨_, sepConj_assoc _ _ _⟩
  | reverse =>
    rw [sepConj_comm (CountedArray addr _ _ _ _) (CountedArray addr _ _ _ _)]
    exact ⟨_, sepConj_assoc _ _ _⟩

/-- Module counters are read from their block cells, not through an assumed
typed reader. The entire current store is retained unchanged. -/
theorem store_count_load [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (CProg.loadU32 (addr owner + (arrayOffsets layout direction).2.1))
      (fun r σ => r = (selectedArray H owner direction).count ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  obtain ⟨rest, split⟩ := store_array_split (L := L) addr layout H member direction
  apply loadU32_rule
  intro σ holds
  rw [split, sepConj_assoc] at holds
  exact counted_count_read addr holds

theorem store_capacity_load [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (CProg.loadU32 (addr owner + (arrayOffsets layout direction).2.2))
      (fun r σ => r = UInt32.ofNat (selectedArray H owner direction).slots.length ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  obtain ⟨rest, split⟩ := store_array_split (L := L) addr layout H member direction
  apply loadU32_rule
  intro σ holds
  rw [split, sepConj_assoc] at holds
  exact counted_capacity_read addr holds

/-- The explicit array bound prevents the represented capacity from wrapping
when stored in the actual UInt32 field. -/
theorem capacity_toNat_is_extent (A : Array32 Id) (sized : A.Sized) :
    (UInt32.ofNat A.slots.length).toNat = A.slots.length := by
  change A.slots.length % 4294967296 = A.slots.length
  apply Nat.mod_eq_of_lt
  change A.slots.length ≤ 4294967295 at sized
  omega

theorem store_capacity_load_is_exact [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField)
    (sized : (selectedArray H owner direction).Sized) (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (CProg.loadU32 (addr owner + (arrayOffsets layout direction).2.2))
      (fun r σ => r.toNat = (selectedArray H owner direction).slots.length ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  refine triple_post _ (store_capacity_load addr layout H member direction F) ?_
  rintro r σ ⟨rfl, holds⟩
  exact ⟨capacity_toNat_is_extent _ sized, holds⟩

/-- A whole field remains whole beside a separate frame, not merely readable. -/
theorem whole_framed {P F : Heap L → Prop} {p : Ptr} {c : Option CVal} {σ : Heap L}
    (holds : (P ∗ F) σ)
    (owns : ∀ τ, P τ → (τ p.block).2 p.offset = whole c) :
    (σ p.block).2 p.offset = whole c := by
  obtain ⟨x, y, separate, rfl, held, -⟩ := holds
  have owned := owns x held
  rw [heap_add_cell, owned]
  exact whole_add_of_separate (owned ▸ (separate p.block).2 p.offset)

theorem counted_pointer_field_is_whole {items count capacity : Ptr} {A : Array32 Id}
    {F : Heap L → Prop} {σ : Heap L}
    (holds : (CountedArray addr items count capacity A ∗ F) σ) :
    ∃ a, (σ items.block).2 items.offset = whole (some (CVal.ptr a)) := by
  obtain ⟨x, y, separate, rfl, ⟨-, a, fields⟩, frame⟩ := holds
  refine ⟨a, whole_framed ⟨x, y, separate, rfl, fields, frame⟩ fun τ fields => ?_⟩
  apply whole_framed fields
  rintro τ rfl
  have atCell := segment_at (L := L) items.offset [whole (some (CVal.ptr a))]
    (k := 0) (by simp)
  simpa only [Nat.add_zero, atBlock_same, List.map_cons, List.map_nil,
    List.getElem_cons_zero] using atCell

/-- The representation enforces module-address injectivity on its domain.
Preparation may therefore connect physical pointer equality to module identity
without assuming an inverse-address oracle. -/
theorem represented_module_addresses_are_distinct [DecidableEq Id] (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) {left right : Id} (leftIn : left ∈ D)
    (rightIn : right ∈ D) (different : left ≠ right) {σ : Heap L}
    (holds : StoreRep addr layout D H σ) : addr left ≠ addr right := by
  intro same
  rw [storeRep_split addr layout H leftIn rightIn different] at holds
  apply fact_of_sepConj_left holds
  rintro τ ⟨x, y, separate, -, spaceX, spaceY⟩
  obtain ⟨p, ownedX⟩ := counted_pointer_field_is_whole addr spaceX
  obtain ⟨q, ownedY⟩ := counted_pointer_field_is_whole addr spaceY
  rw [← same] at ownedY
  have incompatible := (separate (addr left + layout.deps).block).2
    (addr left + layout.deps).offset
  rw [ownedX, ownedY] at incompatible
  exact whole_ne_zero (some (CVal.ptr q)) (eq_zero_of_whole_separate incompatible)

theorem store_item_load [DecidableEq Id] (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {owner : Id} (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) (index : UInt32)
    (inside : index.toNat < (selectedArray H owner direction).active.length)
    (F : Heap L → Prop) :
    CTriple (StoreRep addr layout D H ∗ F)
      (loadItem (addr owner + (arrayOffsets layout direction).1) index)
      (fun r σ => r = some (addr (selectedArray H owner direction).active[index.toNat]) ∧
        (StoreRep addr layout D H ∗ F) σ) := by
  obtain ⟨rest, split⟩ := store_array_split (L := L) addr layout H member direction
  rw [split, sepConj_assoc]
  exact load_item_refines addr _ index inside (rest ∗ F)

end Mettapedia.Machines.CMemory.DependencyReads
