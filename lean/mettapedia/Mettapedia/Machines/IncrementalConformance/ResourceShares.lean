import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! Collection thresholds shared by concurrent workers and their coordinator.

The threshold is not an allocation limit: a live object graph can exceed it.
The floor permits progress with a small configured budget, so the unconditional
bound includes that floor. These arithmetic laws do not bound process RSS.
-/

namespace Mettapedia.Machines.IncrementalConformance.ResourceShares

def owners (workers : Nat) : Nat :=
  if 1 < workers then workers + 1 else 1

def quota (budget workers floor cap : Nat) : Nat :=
  min cap (max floor (budget / owners workers))

theorem owners_pos (workers : Nat) : 0 < owners workers := by
  unfold owners
  split <;> omega

theorem workers_le_owners (workers : Nat) : workers ≤ owners workers := by
  unfold owners
  split <;> omega

theorem sequential_quota (budget floor cap : Nat) :
    quota budget 1 floor cap = min cap (max floor budget) := by
  simp [quota, owners]

theorem floor_le_quota (budget workers floor cap : Nat) (hcap : floor ≤ cap) :
    floor ≤ quota budget workers floor cap := by
  exact le_min hcap (le_max_left _ _)

theorem quota_le_division (budget workers floor cap : Nat)
    (hfloor : floor ≤ budget / owners workers) :
    quota budget workers floor cap ≤ budget / owners workers := by
  simp only [quota, max_eq_right hfloor]
  exact min_le_right _ _

theorem funded_owners (budget workers floor cap : Nat)
    (hfloor : floor ≤ budget / owners workers) :
    owners workers * quota budget workers floor cap ≤ budget := by
  exact Nat.le_trans (Nat.mul_le_mul_left _
    (quota_le_division budget workers floor cap hfloor))
      (Nat.mul_div_le budget (owners workers))

theorem workers_and_reserve (budget workers floor cap : Nat)
    (hworkers : 1 < workers)
    (hfloor : floor ≤ budget / owners workers) :
    workers * quota budget workers floor cap +
      quota budget workers floor cap ≤ budget := by
  have h := funded_owners budget workers floor cap hfloor
  simpa [owners, hworkers, Nat.add_mul] using h

theorem quota_le_floor_add_division (budget workers floor cap : Nat) :
    quota budget workers floor cap ≤ floor + budget / owners workers := by
  have h : quota budget workers floor cap ≤
      max floor (budget / owners workers) := min_le_right _ _
  exact Nat.le_trans h (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

theorem floor_overshoot_bound (budget workers floor cap : Nat) :
    owners workers * quota budget workers floor cap ≤
      budget + owners workers * floor := by
  have h := Nat.mul_le_mul_left (owners workers)
    (quota_le_floor_add_division budget workers floor cap)
  have hd := Nat.mul_div_le budget (owners workers)
  rw [Nat.mul_add] at h
  omega

theorem four_worker_example :
    quota 67108864 4 65536 16777216 = 13421772 := by decide

theorem floor_can_exceed_budget :
    owners 4 * quota 1 4 65536 16777216 > 1 := by decide

end Mettapedia.Machines.IncrementalConformance.ResourceShares
