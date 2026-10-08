import Mettapedia.Machines.CMemory.DependencyReads
import Mettapedia.Machines.OrderedDependencyCReserveGrowth

/-!
# Exact capacity and counted-array reservation over block memory

The shared reserve program is related to the fallible split-array service.
Its exact requested extent, counter, initialized prefix and retired storage
are retained. Logical spare values witness the representation only: this
module does not initialize or read indeterminate physical spare cells.

The allocator remains the shared moving-or-failing block primitive. This is
not a byte-layout, native-compiler or whole-operation synchronization proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.DependencyReserve

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

/-- A stronger postcondition than capacity coverage: successful growth records
the exact computed extent and the old storage, while failure preserves all
fields. No-growth success is kept distinct from allocator success. -/
def ReserveResult (pointerBytes sizeMaximum : Nat) (items capacity : Ptr)
    (required cap : UInt32) (a : Option Ptr)
    (xs : List CVal) (ok : Bool) (σ : Heap L) : Prop :=
  (ok = true ∧ required ≤ cap ∧ ArrayFields items capacity a cap xs σ) ∨
  (ok = true ∧ cap < required ∧ nextCapacity required cap * pointerBytes ≤ sizeMaximum ∧ ∃ p,
    (ArrayFields items capacity (some p) (UInt32.ofNat (nextCapacity required cap)) xs ∗
      DeadStorage a cap.toNat) σ) ∨
  (ok = false ∧ cap < required ∧ ArrayFields items capacity a cap xs σ)

/-- Exact reserve refinement, using the existing primitive realloc rule and
frame rule. The stronger result is derived from the actual program stores,
not from an allocator-success assumption. -/
theorem reserve_exact_spec (pointerBytes sizeMaximum : Nat) (items capacity : Ptr)
    (required : UInt32) (a : Option Ptr) (cap : UInt32) (xs : List CVal) :
    CTriple (L := L) (ArrayFields items capacity a cap xs)
      (reserve pointerBytes sizeMaximum items capacity required)
      (ReserveResult pointerBytes sizeMaximum items capacity required cap a xs) := by
  unfold reserve
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := cap) fun σ holds => ?_) fun c => ?_
  · rw [ArrayFields, sepConj_left_comm] at holds
    exact read_of_pointsTo holds
  apply triple_pure
  intro same
  subst c
  by_cases fits : required ≤ cap
  · rw [if_pos fits]
    refine triple_pre _ ?_ (triple_ret _ true _)
    intro σ holds
    exact Or.inl ⟨rfl, fits, holds⟩
  rw [if_neg fits]
  have needsGrowth : cap < required := Nat.not_le.mp fits
  by_cases tooLarge : sizeMaximum < nextCapacity required cap * pointerBytes
  · rw [if_pos tooLarge]
    refine triple_pre _ ?_ (triple_ret _ false _)
    intro σ holds
    exact Or.inr (Or.inr ⟨rfl, needsGrowth, holds⟩)
  rw [if_neg tooLarge]
  refine triple_bind _ (loadPtr_rule (q := a) fun σ holds => read_of_pointsTo holds)
    fun old => ?_
  apply triple_pure
  intro same
  subst old
  have positive : 0 < nextCapacity required cap := by
    have covers := nextCapacity_covers required cap
    have smaller := UInt32.lt_iff_toNat_lt.mp needsGrowth
    omega
  let fields := PointsTo (L := L) items (.ptr a) ∗ PointsTo capacity (.u32 cap)
  have moved := frame_left (realloc_dynArray (L := L) a cap.toNat
    (nextCapacity required cap) xs positive (nextCapacity_preserves required cap)) fields
  refine triple_bind _ (triple_pre _ (fun σ holds => ?_) moved) fun g => ?_
  · rwa [ArrayFields, ← sepConj_assoc] at holds
  cases g with
  | none =>
    refine triple_pre _ (fun σ holds => ?_) (triple_ret _ false _)
    refine Or.inr (Or.inr ⟨rfl, needsGrowth, ?_⟩)
    rw [ArrayFields, ← sepConj_assoc]
    refine sepConj_mono le_rfl (fun τ unchanged => ?_) σ holds
    rcases unchanged with ⟨-, array⟩ | ⟨b, impossible, -⟩
    · exact array
    · cases impossible
  | some grown =>
    simp only
    let next := nextCapacity required cap
    let rest := DynArray (L := L) (some grown) next xs ∗ DeadStorage a cap.toNat
    have arrived : ∀ σ, (fields ∗ fun σ =>
        (some grown = none ∧ DynArray a cap.toNat xs σ) ∨
        ∃ b, some grown = some ⟨b, 0⟩ ∧
          (DynArray (some ⟨b, 0⟩) next xs ∗ DeadStorage a cap.toNat) σ) σ →
        (PointsToAny items ∗ (PointsTo capacity (.u32 cap) ∗ rest)) σ := by
      intro σ holds
      change ((PointsTo items (.ptr a) ∗ PointsTo capacity (.u32 cap)) ∗ _) σ at holds
      rw [sepConj_assoc] at holds
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
    refine Or.inr (Or.inl ⟨rfl, needsGrowth, Nat.le_of_not_lt tooLarge, grown, ?_⟩)
    rw [ArrayFields, nextCapacity_toNat, sepConj_assoc, sepConj_assoc]
    exact holds

variable {Id : Type}

/-- Padding is a witness for unobserved split-model slots, not physical stores. -/
def padded (before : Array32 Id) (extent : Nat) (filler : Id) : Array32 Id :=
  ⟨before.slots ++ List.replicate (extent - before.slots.length) filler, before.count⟩

theorem padded_extent (before : Array32 Id) (extent : Nat) (filler : Id)
    (grows : before.slots.length ≤ extent) :
    (padded before extent filler).slots.length = extent := by
  simp only [padded, List.length_append, List.length_replicate]
  omega

theorem padded_count (before : Array32 Id) (extent : Nat) (filler : Id) :
    (padded before extent filler).count = before.count := rfl

theorem padded_active (before : Array32 Id) (extent : Nat) (filler : Id)
    (within : before.count.toNat ≤ before.slots.length) :
    (padded before extent filler).active = before.active := by
  simp only [padded, Array32.active]
  exact List.take_append_of_le_length within

theorem padded_sized (before : Array32 Id) (required : UInt32) (filler : Id)
    (sized : before.Sized) :
    (padded before (OrderedDependencyCReserve.chosenCapacity before required) filler).Sized := by
  change (padded _ _ _).slots.length ≤ OrderedDependencyCapacity.maximum
  rw [padded_extent before _ filler
    (OrderedDependencyCReserve.chosen_capacity_preserves_extent before required)]
  exact OrderedDependencyCReserve.chosen_capacity_bounded before required sized

variable (addr : Id → Ptr)

theorem counted_fields_as_array_fields (items count capacity : Ptr) (a : Option Ptr)
    (before : Array32 Id) (sized : before.Sized) :
    CountedFields (L := L) addr items count capacity a before =
      (ArrayFields items capacity a (UInt32.ofNat before.slots.length)
        (before.active.map (spacePtr ∘ addr)) ∗ PointsTo count (.u32 before.count)) := by
  rw [CountedFields, sepConj_left_comm, sepConj_comm]
  rw [ArrayFields, DependencyReads.capacity_toNat_is_extent before sized]

/-- The counted representation keeps the initialized observation and count
while the reserve program changes only its pointer/capacity fields. -/
def CountedReserveResult (pointerBytes sizeMaximum : Nat) (items count capacity : Ptr)
    (a : Option Ptr)
    (before : Array32 Id) (required : UInt32) (filler : Id) (ok : Bool)
    (σ : Heap L) : Prop :=
  (ok = true ∧ required.toNat ≤ before.slots.length ∧
    CountedFields addr items count capacity a before σ) ∨
  (ok = true ∧ before.slots.length < required.toNat ∧
    OrderedDependencyCReserve.chosenCapacity before required * pointerBytes ≤ sizeMaximum ∧ ∃ p,
    (CountedFields addr items count capacity (some p)
      (padded before (OrderedDependencyCReserve.chosenCapacity before required) filler) ∗
      DeadStorage a before.slots.length) σ) ∨
  (ok = false ∧ before.slots.length < required.toNat ∧
    CountedFields addr items count capacity a before σ)

/-- A framed counter lifts an exact array result to its counted representation.
This conversion is independent of how the reserve program was produced. -/
theorem reserve_result_with_counter (pointerBytes sizeMaximum : Nat)
    (items count capacity : Ptr) (a : Option Ptr) (before : Array32 Id)
    (required : UInt32) (filler : Id) (sized : before.Sized)
    (within : before.count.toNat ≤ before.slots.length) (ok : Bool) (σ : Heap L)
    (holds : (ReserveResult pointerBytes sizeMaximum items capacity required
      (UInt32.ofNat before.slots.length) a (before.active.map (spacePtr ∘ addr)) ok ∗
        PointsTo count (.u32 before.count)) σ) :
    CountedReserveResult addr pointerBytes sizeMaximum items count capacity a before
      required filler ok σ := by
  have extent := DependencyReads.capacity_toNat_is_extent before sized
  have chosen := nextCapacity_eq_chosenCapacity required (UInt32.ofNat before.slots.length)
    before extent.symm
  obtain ⟨x, y, separate, rfl, result, counter⟩ := holds
  rcases result with ⟨same, fits, fields⟩ | ⟨same, grows, byteGuard, p, fields⟩ |
    ⟨same, grows, fields⟩
  ·
    refine Or.inl ⟨same, ?_, ?_⟩
    · have bound := UInt32.le_iff_toNat_le.mp fits
      rwa [extent] at bound
    · rw [counted_fields_as_array_fields addr items count capacity a before sized]
      exact ⟨x, y, separate, rfl, fields, counter⟩

  ·
    refine Or.inr (Or.inl ⟨same, ?_, ?_, p, ?_⟩)
    · have bound := UInt32.lt_iff_toNat_lt.mp grows
      rwa [extent] at bound
    · rwa [chosen] at byteGuard
    · have size := padded_extent before _ filler
        (OrderedDependencyCReserve.chosen_capacity_preserves_extent before required)
      have active := padded_active before
        (OrderedDependencyCReserve.chosenCapacity before required) filler within
      have fields' :
          ((ArrayFields items capacity (some p)
              (UInt32.ofNat (OrderedDependencyCReserve.chosenCapacity before required))
              (before.active.map (spacePtr ∘ addr)) ∗ DeadStorage a before.slots.length) ∗
            PointsTo count (.u32 before.count)) (x + y) := by
        simpa only [chosen, extent] using
          (show ((_ ∗ _) ∗ _) (x + y) from ⟨x, y, separate, rfl, fields, counter⟩)
      rw [CountedFields, size, active, padded_count, sepConj_left_comm]
      have nextExtent : (UInt32.ofNat
          (OrderedDependencyCReserve.chosenCapacity before required)).toNat =
          OrderedDependencyCReserve.chosenCapacity before required := by
        rw [← chosen, nextCapacity_toNat]
      rw [ArrayFields, nextExtent, sepConj_assoc] at fields'
      simpa only [sepConj_assoc, sepConj_comm, sepConj_left_comm] using fields'
  ·
    refine Or.inr (Or.inr ⟨same, ?_, ?_⟩)
    · have bound := UInt32.lt_iff_toNat_lt.mp grows
      rwa [extent] at bound
    · rw [counted_fields_as_array_fields addr items count capacity a before sized]
      exact ⟨x, y, separate, rfl, fields, counter⟩

theorem counted_reserve_exact_spec (pointerBytes sizeMaximum : Nat)
    (items count capacity : Ptr) (a : Option Ptr) (before : Array32 Id)
    (required : UInt32) (filler : Id) (sized : before.Sized)
    (within : before.count.toNat ≤ before.slots.length) :
    CTriple (L := L) (CountedFields addr items count capacity a before)
      (reserve pointerBytes sizeMaximum items capacity required)
      (CountedReserveResult addr pointerBytes sizeMaximum items count capacity a before
        required filler) := by
  refine triple_post _ (triple_pre _ (fun σ holds => ?_)
    (frame (reserve_exact_spec pointerBytes sizeMaximum items capacity required a
      (UInt32.ofNat before.slots.length) (before.active.map (spacePtr ∘ addr)))
      (PointsTo count (.u32 before.count)))) ?_
  · rwa [counted_fields_as_array_fields addr items count capacity a before sized] at holds
  exact fun ok σ holds => reserve_result_with_counter addr pointerBytes sizeMaximum
    items count capacity a before required filler sized within ok σ holds

/-- Every physical outcome has a lawful logical allocation outcome. The
availability witness chooses failure or success; spare values remain hidden.
The retired block is kept as a separate resource only after successful growth. -/
def ReservationRel (pointerBytes sizeMaximum : Nat) (items count capacity : Ptr)
    (old : Option Ptr) (before : Array32 Id) (required : UInt32) (filler : Id)
    (ok : Bool) (σ : Heap L) : Prop :=
  ∃ (after : Array32 Id) (available : Bool),
    OrderedDependencyCReserve.reserve (OrderedDependencyCReserve.paddingAllocator filler available)
      pointerBytes sizeMaximum before required = (ok, after) ∧
    after.count = before.count ∧ after.active = before.active ∧ after.Sized ∧
    (ok = true → required.toNat ≤ after.slots.length) ∧
    (CountedArray addr items count capacity after ∗
      (if before.slots.length < required.toNat ∧ ok = true then
        DeadStorage old before.slots.length else emp)) σ

theorem exact_result_refines_array (pointerBytes sizeMaximum : Nat)
    (items count capacity : Ptr) (old : Option Ptr) (before : Array32 Id)
    (required : UInt32) (filler : Id) (sized : before.Sized)
    (within : before.count.toNat ≤ before.slots.length) (ok : Bool) (σ : Heap L)
    (result : CountedReserveResult addr pointerBytes sizeMaximum items count capacity old
      before required filler ok σ) :
    ReservationRel addr pointerBytes sizeMaximum items count capacity old before required
      filler ok σ := by
  rcases result with ⟨rfl, fits, fields⟩ | ⟨rfl, grows, byteGuard, p, fields⟩ |
    ⟨rfl, grows, fields⟩
  · refine ⟨before, false, ?_, rfl, rfl, sized, fun _ => fits, ?_⟩
    · rw [OrderedDependencyCReserve.reserve, if_pos fits]
    · rw [if_neg (by omega), sepConj_emp]
      exact ⟨within, old, fields⟩
  · let after := padded before (OrderedDependencyCReserve.chosenCapacity before required) filler
    have extent := padded_extent before _ filler
      (OrderedDependencyCReserve.chosen_capacity_preserves_extent before required)
    refine ⟨after, true, ?_, rfl, padded_active before _ filler within,
      padded_sized before required filler sized, ?_, ?_⟩
    · rw [OrderedDependencyCReserve.reserve, if_neg (by omega),
        if_neg (Nat.not_lt.mpr byteGuard)]
      simp [OrderedDependencyCReserve.paddingAllocator,
        OrderedDependencyCReserve.chosen_capacity_preserves_extent, after, padded]
    · intro _
      rw [extent]
      exact OrderedDependencyCReserve.chosen_capacity_covers before required
    · rw [if_pos ⟨grows, rfl⟩]
      refine sepConj_mono (fun τ holds => ?_) le_rfl σ fields
      refine ⟨?_, some p, holds⟩
      rw [extent]
      exact within.trans
        (OrderedDependencyCReserve.chosen_capacity_preserves_extent before required)
  · refine ⟨before, false, ?_, rfl, rfl, sized, by simp, ?_⟩
    · rw [OrderedDependencyCReserve.reserve, if_neg (by omega)]
      dsimp only
      split
      · rfl
      · simp [OrderedDependencyCReserve.paddingAllocator]
    · rw [if_neg (by simp), sepConj_emp]
      exact ⟨within, old, fields⟩

/-- The block-memory reserve discharges the split-array allocation contract;
no separate `AllocationLaw` is assumed for the physical operation. -/
theorem counted_reserve_refines (pointerBytes sizeMaximum : Nat)
    (items count capacity : Ptr) (before : Array32 Id) (required : UInt32)
    (filler : Id) (sized : before.Sized) :
    CTriple (L := L) (CountedArray addr items count capacity before)
      (reserve pointerBytes sizeMaximum items capacity required)
      (fun ok σ => ∃ old,
        ReservationRel addr pointerBytes sizeMaximum items count capacity old before required
          filler ok σ) := by
  apply triple_pure
  intro within
  apply triple_exists
  intro old
  refine triple_post _ (counted_reserve_exact_spec addr pointerBytes sizeMaximum
    items count capacity old before required filler sized within) ?_
  intro ok σ result
  exact ⟨old, exact_result_refines_array addr pointerBytes sizeMaximum items count capacity
    old before required filler sized within ok σ result⟩

section Store

variable [DecidableEq Id]

def updateArray (H : SplitHeap Id) (owner : Id)
    (direction : OrderedDependencyCSource.ArrayField) (after : Array32 Id) : SplitHeap Id :=
  match direction with
  | .forward => ⟨Function.update H.forward owner after, H.reverse⟩
  | .reverse => ⟨H.forward, Function.update H.reverse owner after⟩

theorem update_array_observation (H : SplitHeap Id) (owner : Id)
    (direction : OrderedDependencyCSource.ArrayField) (after : Array32 Id)
    (active : after.active = (DependencyReads.selectedArray H owner direction).active) :
    OrderedDependencyCArray.observe (updateArray H owner direction after) =
      OrderedDependencyCArray.observe H := by
  cases direction <;> apply OrderedDependencyCArray.Links.ext <;> funext i
  all_goals by_cases same : i = owner
  all_goals simp only [updateArray, OrderedDependencyCArray.observe,
    DependencyReads.selectedArray] at active ⊢
  all_goals simp [same, active]

theorem update_array_sized (H : SplitHeap Id) (owner : Id)
    (direction : OrderedDependencyCSource.ArrayField) (after : Array32 Id)
    (sized : H.Sized) (afterSized : after.Sized) :
    (updateArray H owner direction after).Sized := by
  cases direction with
  | forward =>
    refine ⟨fun i => ?_, sized.2⟩
    by_cases same : i = owner
    · simpa [updateArray, same] using afterSized
    · simpa [updateArray, Function.update_of_ne same] using sized.1 i
  | reverse =>
    refine ⟨sized.1, fun i => ?_⟩
    by_cases same : i = owner
    · simpa [updateArray, same] using afterSized
    · simpa [updateArray, Function.update_of_ne same] using sized.2 i

/-- Extracting one array and reassembling it after growth uses the same frame.
Other modules and the other direction retain their actual representations. -/
theorem store_array_update_frame (layout : SpaceLayout) {D : List Id}
    (distinct : D.Nodup) (H : SplitHeap Id) (owner : Id) (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) :
    ∃ F : Heap L → Prop,
      StoreRep addr layout D H =
        (CountedArray addr (addr owner + (DependencyReads.arrayOffsets layout direction).1)
          (addr owner + (DependencyReads.arrayOffsets layout direction).2.1)
          (addr owner + (DependencyReads.arrayOffsets layout direction).2.2)
          (DependencyReads.selectedArray H owner direction) ∗ F) ∧
      ∀ after, StoreRep addr layout D (updateArray H owner direction after) =
        (CountedArray addr (addr owner + (DependencyReads.arrayOffsets layout direction).1)
          (addr owner + (DependencyReads.arrayOffsets layout direction).2.1)
          (addr owner + (DependencyReads.arrayOffsets layout direction).2.2) after ∗ F) := by
  have rest : ∀ after, StoreRep (L := L) addr layout (D.erase owner)
      (updateArray H owner direction after) = StoreRep addr layout (D.erase owner) H := by
    intro after
    apply storeRep_congr
    intro i inside
    have different := (distinct.mem_erase_iff.mp inside).1
    cases direction <;> simp [updateArray, Function.update_of_ne different]
  cases direction with
  | forward =>
    refine ⟨CountedArray addr (addr owner + layout.importers)
      (addr owner + layout.importerCount) (addr owner + layout.importerCap) (H.reverse owner) ∗
        StoreRep addr layout (D.erase owner) H, ?_, ?_⟩
    · rw [DependencyReads.store_member_split addr layout H member, SpaceRep]
      exact sepConj_assoc _ _ _
    · intro after
      rw [DependencyReads.store_member_split addr layout _ member, rest, SpaceRep]
      simp only [updateArray, Function.update_self, DependencyReads.arrayOffsets]
      exact sepConj_assoc _ _ _
  | reverse =>
    refine ⟨CountedArray addr (addr owner + layout.deps) (addr owner + layout.depCount)
      (addr owner + layout.depCap) (H.forward owner) ∗
        StoreRep addr layout (D.erase owner) H, ?_, ?_⟩
    · rw [DependencyReads.store_member_split addr layout H member, SpaceRep,
        sepConj_comm (CountedArray addr _ _ _ _) (CountedArray addr _ _ _ _)]
      exact sepConj_assoc _ _ _
    · intro after
      rw [DependencyReads.store_member_split addr layout _ member, rest, SpaceRep]
      simp only [updateArray, Function.update_self, DependencyReads.arrayOffsets]
      rw [sepConj_comm (CountedArray addr _ _ _ _) (CountedArray addr _ _ _ _)]
      exact sepConj_assoc _ _ _

/-- Reserve either direction within a complete module store. Observation of
both directions is preserved even on moving allocation, but retired storage
is explicitly recorded, not mistaken for the current array. -/
theorem store_reserve_refines (pointerBytes sizeMaximum : Nat) (layout : SpaceLayout)
    {D : List Id} (distinct : D.Nodup) (H : SplitHeap Id) (owner : Id) (member : owner ∈ D)
    (direction : OrderedDependencyCSource.ArrayField) (required : UInt32) (filler : Id)
    (sized : H.Sized) :
    CTriple (L := L) (StoreRep addr layout D H)
      (reserve pointerBytes sizeMaximum
        (addr owner + (DependencyReads.arrayOffsets layout direction).1)
        (addr owner + (DependencyReads.arrayOffsets layout direction).2.2) required)
      (fun ok σ => ∃ (old : Option Ptr) (after : Array32 Id) (available : Bool),
        OrderedDependencyCReserve.reserve
          (OrderedDependencyCReserve.paddingAllocator filler available) pointerBytes sizeMaximum
          (DependencyReads.selectedArray H owner direction) required = (ok, after) ∧
        after.count = (DependencyReads.selectedArray H owner direction).count ∧
        (ok = true → required.toNat ≤ after.slots.length) ∧
        OrderedDependencyCArray.observe (updateArray H owner direction after) =
          OrderedDependencyCArray.observe H ∧
        (updateArray H owner direction after).Sized ∧
        (StoreRep addr layout D (updateArray H owner direction after) ∗
          (if (DependencyReads.selectedArray H owner direction).slots.length < required.toNat ∧
              ok = true then
            DeadStorage old (DependencyReads.selectedArray H owner direction).slots.length
            else emp)) σ) := by
  obtain ⟨F, beforeFrame, afterFrame⟩ :=
    store_array_update_frame (L := L) addr layout distinct H owner member direction
  have arraySized : (DependencyReads.selectedArray H owner direction).Sized := by
    cases direction
    · exact sized.1 owner
    · exact sized.2 owner
  refine triple_post _ (triple_pre _ (fun σ holds => beforeFrame ▸ holds)
    (frame (counted_reserve_refines addr pointerBytes sizeMaximum _ _ _
      (DependencyReads.selectedArray H owner direction) required filler arraySized) F)) ?_
  rintro ok σ ⟨x, y, separate, rfl,
    ⟨old, after, available, allocated, count, active, afterSized, covers, fields⟩, frame⟩
  refine ⟨old, after, available, allocated, count, covers,
    update_array_observation H owner direction after active,
    update_array_sized H owner direction after sized afterSized, ?_⟩
  rw [afterFrame]
  simpa only [sepConj_assoc, sepConj_comm, sepConj_left_comm] using
    (show ((_ ∗ _) ∗ F) (x + y) from ⟨x, y, separate, rfl, fields, frame⟩)

end Store

namespace Controls

/-- No-growth success does not require an array-pointer field or an allocator
capability: the actual program returns immediately after the capacity load. -/
theorem sufficient_capacity_needs_only_capacity (pointerBytes sizeMaximum : Nat)
    (items capacity : Ptr) (required cap : UInt32) (fits : required ≤ cap) :
    CTriple (L := L) (PointsTo capacity (.u32 cap))
      (reserve pointerBytes sizeMaximum items capacity required)
      (fun ok σ => ok = true ∧ PointsTo capacity (.u32 cap) σ) := by
  unfold reserve
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := cap) fun _ holds =>
    read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using holds)) fun c => ?_
  apply triple_pure
  intro same
  subst c
  rw [if_pos fits]
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ true _)

/-- The byte guard fails before dereferencing `items` or calling realloc. -/
theorem byte_guard_needs_only_capacity (pointerBytes sizeMaximum : Nat)
    (items capacity : Ptr) (required cap : UInt32) (grows : cap < required)
    (tooLarge : sizeMaximum < nextCapacity required cap * pointerBytes) :
    CTriple (L := L) (PointsTo capacity (.u32 cap))
      (reserve pointerBytes sizeMaximum items capacity required)
      (fun ok σ => ok = false ∧ PointsTo capacity (.u32 cap) σ) := by
  unfold reserve
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := cap) fun _ holds =>
    read_of_pointsTo (F := emp) (by simpa only [sepConj_emp] using holds)) fun c => ?_
  apply triple_pure
  intro same
  subst c
  have notFits : ¬ required ≤ cap := by
    intro fits
    have before := UInt32.lt_iff_toNat_lt.mp grows
    have enough := UInt32.le_iff_toNat_le.mp fits
    omega
  rw [if_neg notFits, if_pos tooLarge]
  exact triple_pre _ (fun _ holds => ⟨rfl, holds⟩) (triple_ret _ false _)

def sample : Array32 Nat := ⟨[10, 20], 2⟩

theorem different_spare_witnesses_same_observation :
    (padded sample 4 0).slots ≠ (padded sample 4 99).slots ∧
    (padded sample 4 0).active = (padded sample 4 99).active := by decide +kernel

theorem padding_does_not_publish :
    (padded sample 4 99).count = 2 ∧ (padded sample 4 99).active = [10, 20] := by
  decide +kernel

theorem early_count_increment_changes_observation :
    (Array32.mk (padded sample 4 99).slots 3).active ≠ sample.active := by decide +kernel

theorem changed_old_prefix_breaks_correspondence :
    (Array32.mk [99, 20, 0, 0] 2).active ≠ sample.active := by decide +kernel

/-- A defined reallocation may fail without retiring or editing the old block.
Its positive request, base pointer and whole-block ownership are explicit. -/
theorem allocator_failure_is_unchanged (p : Ptr) (extent : Nat) (σ : Heap L)
    (positive : 0 < extent) (base : p.offset = 0)
    (owned : ∃ capacity, HoldsBlock σ p.block capacity) :
    (CProg.realloc (V := CVal) (some p) extent).Safe act σ ∧
      (CProg.realloc (V := CVal) (some p) extent).Runs act σ none σ := by
  exact ⟨⟨⟨positive, base, owned⟩, fun _ _ _ => trivial⟩,
    prim_runs (Or.inl ⟨rfl, rfl⟩)⟩

/-- Growth leaves a dead old block and a distinct current block. -/
theorem current_array_is_not_retired_array (items count capacity p old : Ptr)
    (after : Array32 Id) (previousExtent : Nat) (σ : Heap L)
    (holds : (CountedFields addr items count capacity (some p) after ∗
      DeadStorage (some old) previousExtent) σ) : p.block ≠ old.block := by
  rw [CountedFields, sepConj_assoc, sepConj_assoc, sepConj_assoc] at holds
  exact fact_of_sepConj_right holds fun _ rest =>
    fact_of_sepConj_right rest fun _ rest => fact_of_sepConj_right rest fun _ moved =>
      moved_array_is_fresh moved

end Controls

end Mettapedia.Machines.CMemory.DependencyReserve
