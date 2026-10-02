import Mettapedia.GSLT.LanguageDef.NativeWord64

/-!
# Exact scalar allocator context

These are the five counters present in the native operational context. The
declared ABI has 64-bit `size_t`; allocation header and table-cell widths are
separate layout parameters. Private allocation tables and callback effects
remain part of the independently related allocator world.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word bounded encode)

structure SourceAllocatorStats where
  liveBytes : Word
  liveAllocations : Word
  slotCapacity : Word
  slotOccupied : Word
  slotDeleted : Word
  deriving DecidableEq, Repr

structure TargetAllocatorStats where
  liveBytes : BitVec 64
  liveAllocations : BitVec 64
  slotCapacity : BitVec 64
  slotOccupied : BitVec 64
  slotDeleted : BitVec 64
  deriving DecidableEq, Repr

structure AllocatorStatsRelated (source : SourceAllocatorStats)
    (target : TargetAllocatorStats) : Prop where
  liveBytes : target.liveBytes = encode source.liveBytes
  liveAllocations : target.liveAllocations = encode source.liveAllocations
  slotCapacity : target.slotCapacity = encode source.slotCapacity
  slotOccupied : target.slotOccupied = encode source.slotOccupied
  slotDeleted : target.slotDeleted = encode source.slotDeleted

namespace AllocatorStats

def sourceEmpty : SourceAllocatorStats := ⟨0, 0, 0, 0, 0⟩
def targetEmpty : TargetAllocatorStats := ⟨0, 0, 0, 0, 0⟩

theorem empty_related : AllocatorStatsRelated sourceEmpty targetEmpty :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem encode_one : encode (1 : Word) = (1 : BitVec 64) := by decide +kernel

def sourceAdd (left right : Word) : Word := bounded 64 (left.val + right.val)
def sourceSubtract (left right : Word) : Word := bounded 64 ((2 ^ 64 - right.val) + left.val)

theorem add_correspondence (left right : Word) :
    encode (sourceAdd left right) = encode left + encode right := by
  apply BitVec.eq_of_toNat_eq
  simp only [NativeWord64.encode_toNat, sourceAdd, bounded, BitVec.toNat_add]

theorem subtract_correspondence (left right : Word) :
    encode (sourceSubtract left right) = encode left - encode right := by
  apply BitVec.eq_of_toNat_eq
  simp only [NativeWord64.encode_toNat, sourceSubtract, bounded, BitVec.toNat_sub]

def sourceRecordAllocation (stats : SourceAllocatorStats) (bytes : Word)
    (reusesDeleted : Bool) : SourceAllocatorStats := {
  stats with
  liveBytes := sourceAdd stats.liveBytes bytes
  liveAllocations := sourceAdd stats.liveAllocations 1
  slotOccupied := sourceAdd stats.slotOccupied 1
  slotDeleted := if reusesDeleted then sourceSubtract stats.slotDeleted 1 else stats.slotDeleted }

def targetRecordAllocation (stats : TargetAllocatorStats) (bytes : BitVec 64)
    (reusesDeleted : Bool) : TargetAllocatorStats := {
  stats with
  liveBytes := stats.liveBytes + bytes
  liveAllocations := stats.liveAllocations + 1
  slotOccupied := stats.slotOccupied + 1
  slotDeleted := if reusesDeleted then stats.slotDeleted - 1 else stats.slotDeleted }

theorem record_allocation_correspondence {source : SourceAllocatorStats}
    {target : TargetAllocatorStats} (related : AllocatorStatsRelated source target)
    (bytes : Word) (reusesDeleted : Bool) :
    AllocatorStatsRelated (sourceRecordAllocation source bytes reusesDeleted)
      (targetRecordAllocation target (encode bytes) reusesDeleted) := by
  constructor
  · simpa only [sourceRecordAllocation, targetRecordAllocation, related.liveBytes] using
      (add_correspondence source.liveBytes bytes).symm
  · simpa only [sourceRecordAllocation, targetRecordAllocation, related.liveAllocations,
      encode_one] using
      (add_correspondence source.liveAllocations 1).symm
  · exact related.slotCapacity
  · simpa only [sourceRecordAllocation, targetRecordAllocation, related.slotOccupied,
      encode_one] using
      (add_correspondence source.slotOccupied 1).symm
  · cases reusesDeleted
    · exact related.slotDeleted
    · simpa only [sourceRecordAllocation, targetRecordAllocation, related.slotDeleted,
        encode_one, Bool.true_eq, if_true] using
        (subtract_correspondence source.slotDeleted 1).symm

def sourceRehash (stats : SourceAllocatorStats) (capacity : Word) : SourceAllocatorStats :=
  { stats with slotCapacity := capacity, slotDeleted := 0 }

def targetRehash (stats : TargetAllocatorStats) (capacity : BitVec 64) : TargetAllocatorStats :=
  { stats with slotDeleted := 0, slotCapacity := capacity }

theorem rehash_correspondence {source : SourceAllocatorStats}
    {target : TargetAllocatorStats} (related : AllocatorStatsRelated source target)
    (capacity : Word) : AllocatorStatsRelated (sourceRehash source capacity)
      (targetRehash target (encode capacity)) :=
  ⟨related.liveBytes, related.liveAllocations, rfl, related.slotOccupied, rfl⟩

def sourceRecordRelease (stats : SourceAllocatorStats) (bytes : Word) : SourceAllocatorStats :=
  let occupied := sourceSubtract stats.slotOccupied 1
  let next := { stats with
    liveBytes := sourceSubtract stats.liveBytes bytes
    liveAllocations := sourceSubtract stats.liveAllocations 1
    slotOccupied := occupied
    slotDeleted := sourceAdd stats.slotDeleted 1 }
  if occupied.val = 0 then { next with slotCapacity := 0, slotDeleted := 0 } else next

def targetRecordRelease (stats : TargetAllocatorStats) (bytes : BitVec 64) : TargetAllocatorStats :=
  let next := { stats with
    slotOccupied := stats.slotOccupied - 1
    slotDeleted := stats.slotDeleted + 1
    liveAllocations := stats.liveAllocations - 1
    liveBytes := stats.liveBytes - bytes }
  if next.slotOccupied = 0 then { next with slotDeleted := 0, slotCapacity := 0 } else next

theorem record_release_correspondence {source : SourceAllocatorStats}
    {target : TargetAllocatorStats} (related : AllocatorStatsRelated source target)
    (bytes : Word) : AllocatorStatsRelated (sourceRecordRelease source bytes)
      (targetRecordRelease target (encode bytes)) := by
  have occupied : target.slotOccupied - 1 = encode (sourceSubtract source.slotOccupied 1) := by
    simpa only [related.slotOccupied, encode_one] using
      (subtract_correspondence source.slotOccupied 1).symm
  have guard : target.slotOccupied - 1 = 0 ↔ (sourceSubtract source.slotOccupied 1).val = 0 := by
    rw [occupied, NativeWord64.encode_eq_zero]
  unfold sourceRecordRelease targetRecordRelease
  simp only [guard]
  split_ifs
  all_goals constructor
  all_goals first
  | simpa only [related.liveBytes] using (subtract_correspondence source.liveBytes bytes).symm
  | simpa only [related.liveAllocations, encode_one] using
      (subtract_correspondence source.liveAllocations 1).symm
  | exact occupied
  | exact related.slotCapacity
  | simpa only [related.slotDeleted, encode_one] using
      (add_correspondence source.slotDeleted 1).symm
  | rfl

theorem last_release_discards_table : sourceRecordRelease ⟨8, 1, 16, 1, 3⟩ 8 = sourceEmpty :=
  by decide +kernel

theorem remaining_allocation_retains_table :
    targetRecordRelease ⟨16, 2, 16, 2, 3⟩ 8 = ⟨8, 1, 16, 1, 4⟩ := by decide +kernel

theorem rehash_preserves_live_counters (stats : SourceAllocatorStats) (capacity : Word) :
    (sourceRehash stats capacity).liveBytes = stats.liveBytes ∧
      (sourceRehash stats capacity).liveAllocations = stats.liveAllocations ∧
      (sourceRehash stats capacity).slotOccupied = stats.slotOccupied := ⟨rfl, rfl, rfl⟩

theorem deleted_slot_reuse_changes_deleted_counter :
    targetRecordAllocation ⟨8, 1, 16, 1, 3⟩ 8 true = ⟨16, 2, 16, 2, 2⟩ := by decide +kernel

end AllocatorStats

end Mettapedia.GSLT.LanguageDef.NativeOps
