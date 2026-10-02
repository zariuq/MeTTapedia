import Mettapedia.GSLT.LanguageDef.NativeWord64

/-!
# Checked compact storage guards for the native operational fragment

The source computes natural extents and offsets from bounded word operands.
The target independently follows unsigned division, comparison, subtraction
and multiplication in the 64-bit `size_t` ABI profile.  Guard order is the
order of the shared native storage primitives.  Pointer liveness and actual
storage contents belong to the memory relation, rather than to a null check.

These are operational models of the admitted primitive profile.  They do not
assert refinement by an ISO C compiler or by physical pointer arithmetic.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsMemoryGuards

open NativeWord64

def sourceExtent (count width : Word) : Except Fault Nat :=
  if width.val = 0 then .error .invalidRequest
  else if count.val * width.val < bound then .ok (count.val * width.val)
  else .error .lengthOverflow

def targetExtent (count width : BitVec 64) : Except Fault (BitVec 64) :=
  if width = 0 then .error .invalidRequest
  else if BitVec.allOnes 64 / width < count then .error .lengthOverflow
  else .ok (count * width)

def observeNat (result : Except Fault (BitVec 64)) : Except Fault Nat :=
  result.map BitVec.toNat

theorem extent_unsigned_guard (count width : Word) (nonzero : width.val ≠ 0) :
    BitVec.allOnes 64 / encode width < encode count ↔ bound ≤ count.val * width.val := by
  rw [BitVec.lt_def]
  simp only [BitVec.toNat_udiv, BitVec.toNat_allOnes, encode_toNat]
  rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero nonzero)]
  change 2 ^ 64 - 1 < count.val * width.val ↔ 2 ^ 64 ≤ count.val * width.val
  have positive : 0 < 2 ^ 64 := Nat.two_pow_pos _
  rw [← Nat.succ_le_iff]
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt positive)]

theorem extent_correspondence (count width : Word) :
    observeNat (targetExtent (encode count) (encode width)) = sourceExtent count width := by
  simp only [sourceExtent, targetExtent, encode_eq_zero]
  by_cases nonzero : width.val = 0
  · simp only [nonzero, if_true, observeNat, Except.map]
  · simp only [nonzero, if_false]
    by_cases bounded : count.val * width.val < bound
    · have guard : ¬(BitVec.allOnes 64 / encode width < encode count) :=
        fun overflow => (Nat.not_le_of_lt bounded) ((extent_unsigned_guard count width nonzero).mp overflow)
      simp only [guard, if_false, bounded, if_true, observeNat, Except.map, BitVec.toNat_mul,
        encode_toNat]
      simp only [bound] at bounded
      rw [Nat.mod_eq_of_lt bounded]
    · have guard : BitVec.allOnes 64 / encode width < encode count :=
        (extent_unsigned_guard count width nonzero).mpr (Nat.le_of_not_lt bounded)
      simp only [guard, if_true, bounded, if_false, observeNat, Except.map]

theorem sourceExtent_success {count width : Word} {bytes : Nat}
    (success : sourceExtent count width = .ok bytes) :
    width.val ≠ 0 ∧ bytes = count.val * width.val ∧ bytes < bound := by
  unfold sourceExtent at success
  split at success
  · contradiction
  · rename_i nonzero
    split at success
    · rename_i bounded
      cases success
      exact ⟨nonzero, rfl, bounded⟩
    · contradiction

theorem extent_result_iff (count width : Word) (bytes : BitVec 64) :
    targetExtent (encode count) (encode width) = .ok bytes ↔
      sourceExtent count width = .ok bytes.toNat := by
  rw [← extent_correspondence]
  cases result : targetExtent (encode count) (encode width) with
  | error fault => simp [observeNat, Except.map]
  | ok actual => simp [observeNat, Except.map, ← BitVec.toNat_inj]

theorem extent_fault_iff (count width : Word) (fault : Fault) :
    targetExtent (encode count) (encode width) = .error fault ↔
      sourceExtent count width = .error fault := by
  rw [← extent_correspondence]
  cases result : targetExtent (encode count) (encode width) <;>
    simp [observeNat, Except.map]

def sourceIndex (length width index : Word) (nonnull : Bool) : Except Fault Nat :=
  match sourceExtent length width with
  | .error fault => .error fault
  | .ok _ =>
      if length.val ≤ index.val then .error .indexOutOfBounds
      else if nonnull then .ok (index.val * width.val) else .error .nullReference

def targetIndex (length width index : BitVec 64) (nonnull : Bool) :
    Except Fault (BitVec 64) :=
  match targetExtent length width with
  | .error fault => .error fault
  | .ok _ =>
      if length ≤ index then .error .indexOutOfBounds
      else if nonnull then .ok (index * width) else .error .nullReference

def sourceSlice (length width start count : Word) (nonnull : Bool) :
    Except Fault (Option Nat) :=
  match sourceExtent length width with
  | .error fault => .error fault
  | .ok _ =>
      if length.val < start.val ∨ length.val - start.val < count.val then
        .error .indexOutOfBounds
      else if count.val = 0 then .ok none
      else if nonnull then .ok (some (start.val * width.val)) else .error .nullReference

def targetSlice (length width start count : BitVec 64) (nonnull : Bool) :
    Except Fault (Option (BitVec 64)) :=
  match targetExtent length width with
  | .error fault => .error fault
  | .ok _ =>
      if length < start then .error .indexOutOfBounds
      else if length - start < count then .error .indexOutOfBounds
      else if count = 0 then .ok none
      else if nonnull then .ok (some (start * width)) else .error .nullReference

def sourceFreeGuard (count width : Word) (nonnull : Bool) (ownedExtent : Option Word) :
    Except Fault Unit :=
  match sourceExtent count width with
  | .error fault => .error fault
  | .ok bytes =>
      if nonnull = false ∧ bytes = 0 then .ok ()
      else if nonnull = false then .error .notOwned
      else match ownedExtent with
        | none => .error .notOwned
        | some allocated => if allocated.val = bytes then .ok () else .error .notOwned

def targetFreeGuard (count width : BitVec 64) (nonnull : Bool)
    (ownedExtent : Option (BitVec 64)) : Except Fault Unit :=
  match targetExtent count width with
  | .error fault => .error fault
  | .ok bytes =>
      if nonnull = false ∧ bytes = 0 then .ok ()
      else if nonnull = false then .error .notOwned
      else match ownedExtent with
        | none => .error .notOwned
        | some allocated => if allocated = bytes then .ok () else .error .notOwned

theorem index_correspondence (length width index : Word) (nonnull : Bool) :
    observeNat (targetIndex (encode length) (encode width) (encode index) nonnull) =
      sourceIndex length width index nonnull := by
  cases extent : targetExtent (encode length) (encode width) with
  | error fault =>
      have source := extent_correspondence length width
      simp only [extent, observeNat, Except.map] at source
      simp [targetIndex, sourceIndex, extent, ← source, observeNat, Except.map]
  | ok bytes =>
      have source := extent_correspondence length width
      simp only [extent, observeNat, Except.map] at source
      obtain ⟨nonzero, size, bounded⟩ := sourceExtent_success source.symm
      simp only [targetIndex, extent, sourceIndex, ← source,
        BitVec.le_def, encode_toNat]
      by_cases outside : length.val ≤ index.val
      · simp [outside, observeNat, Except.map]
      · have offset : index.val * width.val < bound :=
          Nat.lt_trans (Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge outside)
            (Nat.pos_of_ne_zero nonzero)) (by simpa only [size] using bounded)
        cases nonnull <;> simp [outside, observeNat, Except.map, BitVec.toNat_mul]
        exact offset

theorem index_result_iff (length width index : Word) (nonnull : Bool) (offset : BitVec 64) :
    targetIndex (encode length) (encode width) (encode index) nonnull = .ok offset ↔
      sourceIndex length width index nonnull = .ok offset.toNat := by
  rw [← index_correspondence]
  cases result : targetIndex (encode length) (encode width) (encode index) nonnull <;>
    simp [observeNat, Except.map, ← BitVec.toNat_inj]

theorem index_fault_iff (length width index : Word) (nonnull : Bool) (fault : Fault) :
    targetIndex (encode length) (encode width) (encode index) nonnull = .error fault ↔
      sourceIndex length width index nonnull = .error fault := by
  rw [← index_correspondence]
  cases result : targetIndex (encode length) (encode width) (encode index) nonnull <;>
    simp [observeNat, Except.map]

def observeSlice (result : Except Fault (Option (BitVec 64))) : Except Fault (Option Nat) :=
  result.map (Option.map BitVec.toNat)

theorem subtraction_without_underflow (length start : Word) (within : start.val ≤ length.val) :
    (encode length - encode start).toNat = length.val - start.val := by
  apply BitVec.toNat_sub_of_not_usubOverflow
  simp only [BitVec.usubOverflow, encode_toNat]
  intro positive
  exact (Nat.not_lt_of_ge within) (of_decide_eq_true positive)

theorem slice_correspondence (length width start count : Word) (nonnull : Bool) :
    observeSlice (targetSlice (encode length) (encode width) (encode start) (encode count)
      nonnull) = sourceSlice length width start count nonnull := by
  cases extent : targetExtent (encode length) (encode width) with
  | error fault =>
      have source := extent_correspondence length width
      simp only [extent, observeNat, Except.map] at source
      simp [targetSlice, sourceSlice, extent, ← source, observeSlice, Except.map]
  | ok bytes =>
      have source := extent_correspondence length width
      simp only [extent, observeNat, Except.map] at source
      obtain ⟨_, size, bounded⟩ := sourceExtent_success source.symm
      simp only [targetSlice, extent, sourceSlice, ← source,
        BitVec.lt_def, encode_toNat]
      by_cases beyond : length.val < start.val
      · simp [beyond, observeSlice, Except.map]
      · have within : start.val ≤ length.val := Nat.le_of_not_lt beyond
        rw [subtraction_without_underflow length start within]
        simp only [beyond, false_or, if_false, encode_eq_zero]
        by_cases tooLong : length.val - start.val < count.val
        · simp [tooLong, observeSlice, Except.map]
        · have offset : start.val * width.val < bound :=
            Nat.lt_of_le_of_lt (Nat.mul_le_mul_right width.val within)
              (by simpa only [size] using bounded)
          by_cases empty : count.val = 0
          · simp [empty, observeSlice, Except.map]
          · cases nonnull <;> simp [tooLong, empty, observeSlice, Except.map, BitVec.toNat_mul]
            exact offset

theorem slice_result_iff (length width start count : Word) (nonnull : Bool)
    (offset : Option (BitVec 64)) :
    targetSlice (encode length) (encode width) (encode start) (encode count) nonnull =
      .ok offset ↔ sourceSlice length width start count nonnull =
        .ok (offset.map BitVec.toNat) := by
  rw [← slice_correspondence]
  cases result : targetSlice (encode length) (encode width) (encode start) (encode count)
      nonnull with
  | error fault => simp [observeSlice, Except.map]
  | ok actual =>
      cases actual <;> cases offset <;>
        simp [observeSlice, Except.map, ← BitVec.toNat_inj]

theorem slice_fault_iff (length width start count : Word) (nonnull : Bool) (fault : Fault) :
    targetSlice (encode length) (encode width) (encode start) (encode count) nonnull =
      .error fault ↔ sourceSlice length width start count nonnull = .error fault := by
  rw [← slice_correspondence]
  cases result : targetSlice (encode length) (encode width) (encode start) (encode count)
      nonnull <;> simp [observeSlice, Except.map]

theorem free_guard_correspondence (count width : Word) (nonnull : Bool)
    (ownedExtent : Option Word) :
    targetFreeGuard (encode count) (encode width) nonnull (ownedExtent.map encode) =
      sourceFreeGuard count width nonnull ownedExtent := by
  cases extent : targetExtent (encode count) (encode width) with
  | error fault =>
      have source := extent_correspondence count width
      simp only [extent, observeNat, Except.map] at source
      simp [targetFreeGuard, sourceFreeGuard, extent, ← source]
  | ok bytes =>
      have source := extent_correspondence count width
      simp only [extent, observeNat, Except.map] at source
      simp only [targetFreeGuard, extent, sourceFreeGuard, ← source,
        ← BitVec.toNat_inj]
      cases ownedExtent <;> simp [encode_toNat]
      rfl

/-- Equality of full outcomes supplies success and every refusal in both directions. -/
theorem free_guard_outcome_iff (count width : Word) (nonnull : Bool)
    (ownedExtent : Option Word) (outcome : Except Fault Unit) :
    targetFreeGuard (encode count) (encode width) nonnull (ownedExtent.map encode) = outcome ↔
      sourceFreeGuard count width nonnull ownedExtent = outcome := by
  rw [free_guard_correspondence]

/-- A failed physical operation supplies a placeholder to C, but no successful value. -/
def sourceReady (prior : Option Fault) (allocator release : Bool) : Except Fault Unit :=
  match prior with
  | some fault => .error fault
  | none => if allocator && release then .ok () else .error .invalidRequest

def targetReady (prior : Option Fault) (allocator release : Bool) : Except Fault Unit :=
  match prior with
  | some fault => .error fault
  | none =>
      if !allocator then .error .invalidRequest
      else if !release then .error .invalidRequest
      else .ok ()

theorem ready_correspondence (prior : Option Fault) (allocator release : Bool) :
    targetReady prior allocator release = sourceReady prior allocator release := by
  cases prior <;> cases allocator <;> cases release <;> rfl

def sourceChecked {α : Type} (prior : Option Fault) (allocator release : Bool)
    (operation : Unit → Except Fault α) : Except Fault α :=
  match sourceReady prior allocator release with
  | .error fault => .error fault
  | .ok _ => operation ()

def targetChecked {α : Type} (prior : Option Fault) (allocator release : Bool)
    (operation : Unit → Except Fault α) : Except Fault α :=
  match targetReady prior allocator release with
  | .error fault => .error fault
  | .ok _ => operation ()

theorem checked_correspondence {α β : Type} (observe : β → α) (prior : Option Fault)
    (allocator release : Bool) (source : Unit → Except Fault α)
    (target : Unit → Except Fault β)
    (operations : (target ()).map observe = source ()) :
    (targetChecked prior allocator release target).map observe =
      sourceChecked prior allocator release source := by
  simp only [targetChecked, ready_correspondence, sourceChecked]
  cases sourceReady prior allocator release with
  | error fault => rfl
  | ok _ => exact operations

theorem checked_prior_fault {α : Type} (fault : Fault) (allocator release : Bool)
    (operation : Unit → Except Fault α) :
    targetChecked (some fault) allocator release operation = .error fault := rfl

theorem checked_success_ready {α : Type} {prior : Option Fault} {allocator release : Bool}
    {operation : Unit → Except Fault α} {value : α}
    (success : targetChecked prior allocator release operation = .ok value) :
    prior = none ∧ allocator = true ∧ release = true ∧ operation () = .ok value := by
  cases prior with
  | some fault => contradiction
  | none =>
      cases allocator <;> cases release <;> simp_all [targetChecked, targetReady]

/-- Ref guards check nullness.  They do not assert ownership or lifetime. -/
def sourceReference (nonnull : Bool) : Except Fault Unit :=
  if nonnull then .ok () else .error .nullReference

def targetReference (nonnull : Bool) : Except Fault Unit :=
  match nonnull with
  | false => .error .nullReference
  | true => .ok ()

theorem reference_correspondence (nonnull : Bool) :
    targetReference nonnull = sourceReference nonnull := by
  cases nonnull <;> rfl

theorem reference_success_iff (nonnull : Bool) :
    targetReference nonnull = .ok () ↔ nonnull = true := by
  cases nonnull <;> simp [targetReference]

def sourceAllocationExtent (count width metadata liveBytes : Word) : Except Fault (Option Nat) :=
  match sourceExtent count width with
  | .error fault => .error fault
  | .ok bytes =>
      if bytes = 0 then .ok none
      else if bound ≤ bytes + metadata.val ∨ bound ≤ bytes + liveBytes.val then
        .error .lengthOverflow
      else .ok (some bytes)

def targetAllocationExtent (count width metadata liveBytes : BitVec 64) :
    Except Fault (Option (BitVec 64)) :=
  match targetExtent count width with
  | .error fault => .error fault
  | .ok bytes =>
      if bytes = 0 then .ok none
      else if BitVec.allOnes 64 - metadata < bytes ||
          BitVec.allOnes 64 - liveBytes < bytes then .error .lengthOverflow
      else .ok (some bytes)

theorem remaining_extent_guard (bytes : BitVec 64) (occupied : Word) :
    BitVec.allOnes 64 - encode occupied < bytes ↔ bound ≤ bytes.toNat + occupied.val := by
  rw [BitVec.lt_def]
  have within : occupied.val ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt occupied.isLt
  have noUnderflow : ¬BitVec.usubOverflow (BitVec.allOnes 64) (encode occupied) := by
    simp only [BitVec.usubOverflow, BitVec.toNat_allOnes, encode_toNat]
    intro positive
    exact (Nat.not_lt_of_ge within) (of_decide_eq_true positive)
  rw [BitVec.toNat_sub_of_not_usubOverflow noUnderflow]
  simp only [BitVec.toNat_allOnes, encode_toNat]
  rw [Nat.sub_lt_iff_lt_add within]
  change 2 ^ 64 - 1 < bytes.toNat + occupied.val ↔ 2 ^ 64 ≤ bytes.toNat + occupied.val
  rw [← Nat.succ_le_iff, Nat.succ_eq_add_one,
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.two_pow_pos 64))]

theorem allocation_extent_correspondence (count width metadata liveBytes : Word) :
    observeSlice (targetAllocationExtent (encode count) (encode width) (encode metadata)
      (encode liveBytes)) = sourceAllocationExtent count width metadata liveBytes := by
  cases extent : targetExtent (encode count) (encode width) with
  | error fault =>
      have source := extent_correspondence count width
      simp only [extent, observeNat, Except.map] at source
      simp [targetAllocationExtent, sourceAllocationExtent, extent, ← source,
        observeSlice, Except.map]
  | ok bytes =>
      have source := extent_correspondence count width
      simp only [extent, observeNat, Except.map] at source
      simp only [targetAllocationExtent, sourceAllocationExtent, extent, ← source]
      by_cases empty : bytes = 0
      · simp [empty, observeSlice, Except.map]
      · have nonempty : bytes.toNat ≠ 0 := by simpa [← BitVec.toNat_inj] using empty
        simp only [empty, nonempty, if_false, Bool.or_eq_true, remaining_extent_guard, decide_eq_true_eq]
        split <;> simp_all [observeSlice, Except.map]

theorem allocation_extent_result_iff (count width metadata liveBytes : Word)
    (extent : Option (BitVec 64)) :
    targetAllocationExtent (encode count) (encode width) (encode metadata) (encode liveBytes) =
      .ok extent ↔ sourceAllocationExtent count width metadata liveBytes =
        .ok (extent.map BitVec.toNat) := by
  rw [← allocation_extent_correspondence]
  cases result : targetAllocationExtent (encode count) (encode width) (encode metadata)
      (encode liveBytes) with
  | error fault => simp [observeSlice, Except.map]
  | ok actual => cases actual <;> cases extent <;>
      simp [observeSlice, Except.map, ← BitVec.toNat_inj]

theorem allocation_extent_fault_iff (count width metadata liveBytes : Word) (fault : Fault) :
    targetAllocationExtent (encode count) (encode width) (encode metadata) (encode liveBytes) =
      .error fault ↔ sourceAllocationExtent count width metadata liveBytes = .error fault := by
  rw [← allocation_extent_correspondence]
  cases result : targetAllocationExtent (encode count) (encode width) (encode metadata)
      (encode liveBytes) <;> simp [observeSlice, Except.map]

end Mettapedia.GSLT.LanguageDef.NativeOpsMemoryGuards
