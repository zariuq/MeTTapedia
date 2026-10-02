import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryGuards

/-!
The compact allocator's ordered extent, header-size and aggregate live-byte
guards in the 64-bit size_t ABI profile. Zero-sized allocation returns null
without fault before the header and live-byte checks. Allocation-table
reservation and physical allocation follow these guards and have separate
stateful resource effects.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsAllocationGuards

open NativeWord64
open NativeOpsMemoryGuards

theorem remaining_capacity (used : Word) :
    (BitVec.allOnes 64 - encode used).toNat = bound - 1 - used.val := by
  have noUnderflow : ¬ (BitVec.allOnes 64).usubOverflow (encode used) := by
    simp only [BitVec.usubOverflow, BitVec.toNat_allOnes, encode_toNat]
    have bounded := used.isLt
    change used.val < 2 ^ 64 at bounded
    intro underflow
    have tooLarge := of_decide_eq_true underflow
    omega
  rw [BitVec.toNat_sub_of_not_usubOverflow noUnderflow, BitVec.toNat_allOnes, encode_toNat]
  rfl

theorem additive_capacity_guard (used amount : Word) :
    BitVec.allOnes 64 - encode used < encode amount ↔ bound ≤ used.val + amount.val := by
  rw [BitVec.lt_def, remaining_capacity, encode_toNat]
  have bounded := used.isLt
  change used.val < bound at bounded
  have positive : 0 < bound := Nat.two_pow_pos 64
  constructor <;> intro guard <;> omega

def sourceAllocationBytes (count width header live : Word) : Except Fault (Option Nat) :=
  match sourceExtent count width with
  | .error fault => .error fault
  | .ok bytes =>
      if bytes = 0 then .ok none
      else if bound ≤ bytes + header.val ∨ bound ≤ live.val + bytes then .error .lengthOverflow
      else .ok (some bytes)

def targetAllocationBytes (count width header live : BitVec 64) :
    Except Fault (Option (BitVec 64)) :=
  match targetExtent count width with
  | .error fault => .error fault
  | .ok bytes =>
      if bytes = 0 then .ok none
      else if BitVec.allOnes 64 - header < bytes ∨ BitVec.allOnes 64 - live < bytes then
        .error .lengthOverflow
      else .ok (some bytes)

def observeAllocation (result : Except Fault (Option (BitVec 64))) : Except Fault (Option Nat) :=
  result.map (Option.map BitVec.toNat)

theorem allocation_bytes_correspondence (count width header live : Word) :
    observeAllocation (targetAllocationBytes (encode count) (encode width) (encode header)
      (encode live)) = sourceAllocationBytes count width header live := by
  cases extent : targetExtent (encode count) (encode width) with
  | error fault =>
      have source := extent_correspondence count width
      simp only [extent, observeNat, Except.map] at source
      simp only [targetAllocationBytes, extent, sourceAllocationBytes, ← source,
        observeAllocation, Except.map]
  | ok bytes =>
      have source := extent_correspondence count width
      simp only [extent, observeNat, Except.map] at source
      simp only [targetAllocationBytes, extent, sourceAllocationBytes, ← source]
      have encoded : encode bytes.toFin = bytes := BitVec.ofFin_toFin bytes
      have headerGuard := additive_capacity_guard header bytes.toFin
      have liveGuard := additive_capacity_guard live bytes.toFin
      rw [encoded] at headerGuard liveGuard
      change BitVec.allOnes 64 - encode header < bytes ↔
        bound ≤ header.val + bytes.toNat at headerGuard
      change BitVec.allOnes 64 - encode live < bytes ↔
        bound ≤ live.val + bytes.toNat at liveGuard
      have zero : bytes = 0 ↔ bytes.toNat = 0 := by
        rw [← BitVec.toNat_inj]
        rfl
      simp only [zero, headerGuard, liveGuard]
      by_cases empty : bytes.toNat = 0
      · simp only [empty, if_true, observeAllocation, Except.map, Option.map_none]
      · simp only [empty, if_false]
        have reordered : bound ≤ bytes.toNat + header.val ↔ bound ≤ header.val + bytes.toNat := by
          rw [Nat.add_comm]
        simp only [reordered]
        split <;> rfl

theorem allocation_refusal_iff (count width header live : Word) (fault : Fault) :
    targetAllocationBytes (encode count) (encode width) (encode header) (encode live) =
      .error fault ↔ sourceAllocationBytes count width header live = .error fault := by
  rw [← allocation_bytes_correspondence]
  cases targetAllocationBytes (encode count) (encode width) (encode header) (encode live) <;>
    simp [observeAllocation, Except.map]

theorem accepted_allocation_bounds {count width header live : Word} {bytes : Nat}
    (accepted : sourceAllocationBytes count width header live = .ok (some bytes)) :
    bytes = count.val * width.val ∧ 0 < bytes ∧ bytes + header.val < bound ∧
      live.val + bytes < bound := by
  unfold sourceAllocationBytes at accepted
  cases extent : sourceExtent count width with
  | error fault => simp [extent] at accepted
  | ok size =>
      simp only [extent] at accepted
      by_cases zero : size = 0
      · rw [if_pos zero] at accepted
        cases accepted
      · rw [if_neg zero] at accepted
        by_cases bad : bound ≤ size + header.val ∨ bound ≤ live.val + size
        · rw [if_pos bad] at accepted
          cases accepted
        · rw [if_neg bad] at accepted
          have same : size = bytes := Option.some.inj (Except.ok.inj accepted)
          subst size
          obtain ⟨_, size, _⟩ := sourceExtent_success extent
          exact ⟨size, Nat.pos_of_ne_zero zero,
            Nat.lt_of_not_ge (fun overflow => bad (Or.inl overflow)),
            Nat.lt_of_not_ge (fun overflow => bad (Or.inr overflow))⟩

private def word (value : Nat) : Word := ⟨value % bound, Nat.mod_lt _ (Nat.two_pow_pos 64)⟩

theorem zero_allocation_precedes_live_capacity :
    sourceAllocationBytes (word 0) (word 8) (word 32) (word (bound - 1)) = .ok none := by
  decide +kernel

theorem zero_width_precedes_empty_allocation :
    sourceAllocationBytes (word 0) (word 0) (word 32) (word 0) = .error .invalidRequest := by
  decide +kernel

theorem maximal_extent_refused_by_header :
    sourceAllocationBytes (word (bound - 1)) (word 1) (word 32) (word 0) =
      .error .lengthOverflow := by decide +kernel

theorem cumulative_live_overflow_refuses :
    sourceAllocationBytes (word 1) (word 1) (word 32) (word (bound - 1)) =
      .error .lengthOverflow := by decide +kernel

theorem last_representable_header_extent_accepts :
    sourceAllocationBytes (word (bound - 33)) (word 1) (word 32) (word 0) =
      .ok (some (bound - 33)) := by decide +kernel

theorem first_unrepresentable_header_extent_refuses :
    sourceAllocationBytes (word (bound - 32)) (word 1) (word 32) (word 0) =
      .error .lengthOverflow := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOpsAllocationGuards
