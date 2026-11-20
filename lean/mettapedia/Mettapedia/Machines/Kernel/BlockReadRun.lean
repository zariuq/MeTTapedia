import Mathlib.Data.Nat.Basic

/-!
# Bounded command runs

A request owns one contiguous interval. Drive moves its prefix in commands
limited by the controller, and Files publishes the interval after settlement.
This model covers the interval arithmetic used by the command loop.
-/

namespace Mettapedia.Machines.Kernel.BlockReadRun

def chunks (limit remaining : Nat) : List Nat :=
  if _h : 0 < min limit remaining then
    min limit remaining :: chunks limit (remaining - min limit remaining)
  else []
termination_by remaining
decreasing_by omega

theorem chunks_total (limit remaining : Nat) (positive : 0 < limit) :
    (chunks limit remaining).sum = remaining := by
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    rw [chunks]
    split
    · rename_i progress
      rw [List.sum_cons, ih _ (by omega)]
      have bounded := Nat.min_le_right limit remaining
      omega
    · rename_i stopped
      have zero : remaining = 0 := by omega
      simp [zero]

theorem chunks_bounded (limit remaining : Nat) :
    ∀ count ∈ chunks limit remaining, 0 < count ∧ count ≤ limit := by
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    rw [chunks]
    split
    · rename_i progress
      intro count present
      rcases List.mem_cons.mp present with same | later
      · subst count
        exact ⟨progress, Nat.min_le_left _ _⟩
      · exact ih _ (by omega) count later
    · simp

theorem next_within_request (base bytes done limit : Nat)
    (pending : done < bytes) (positive : 0 < limit) :
    let count := min (bytes - done) limit
    0 < count ∧ count ≤ limit ∧ base + done + count ≤ base + bytes := by
  have lower : 0 < min (bytes - done) limit := by omega
  have upper := Nat.min_le_left (bytes - done) limit
  exact ⟨lower, Nat.min_le_right _ _, by omega⟩

theorem command_sector_aligned (remaining limit : Nat)
    (requestAligned : 512 ∣ remaining) (limitAligned : 512 ∣ limit) :
    512 ∣ min remaining limit ∧ 512 ∣ remaining - min remaining limit := by
  by_cases shorter : remaining ≤ limit
  · simp [Nat.min_eq_left shorter, requestAligned]
  · have ordered : limit ≤ remaining := by omega
    rw [Nat.min_eq_right ordered]
    exact ⟨limitAligned, Nat.dvd_sub requestAligned limitAligned⟩

example : chunks 131072 262656 = [131072, 131072, 512] := by
  simp [chunks]

example : chunks 131072 0 = [] := by
  simp [chunks]

#print axioms chunks_total
#print axioms chunks_bounded
#print axioms command_sector_aligned

end Mettapedia.Machines.Kernel.BlockReadRun
