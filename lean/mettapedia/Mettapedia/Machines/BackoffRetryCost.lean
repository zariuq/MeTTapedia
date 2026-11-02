import Mathlib.Tactic

/-!
# Retrying a refused compilation: every call, or at doubling gaps

A call that a prepared machine may run is compiled first; a compilation can be
refused for a reason that certifies nothing about later calls, and the call then
runs on the ordinary path.  Retrying at every call costs one compilation per
call: a function called a million times whose program is refused is compiled a
million times.

Retrying at doubling gaps, capped at `2 ^ m` calls, compiles at calls
`pos m 0, pos m 1, …` with `pos m (k + 1) = pos m k + 2 ^ min k m`: the call
right after the first refusal, then gaps of two, four, and so on up to `2 ^ m`.
A skipped call runs on the ordinary path, as a refused one does, so no answer
changes.  Below the cap the attempts are the calls `2 ^ k - 1`; over `C` calls
they number at most `m + 1 + C / 2 ^ m`, where retrying at every call makes `C`,
and a compilation that would succeed from call `t` on is tried no later than
call `2 * t` and no later than call `t + 2 ^ m`.

This file proves:
* `pos_one`: the first retry is the next call;
* `pos_eq`: below the cap, `pos m k = 2 ^ k - 1`;
* `attempts_le`: the attempts among the first `C` calls number at most
  `m + 1 + C / 2 ^ m`;
* `attempt_by`: some attempt falls in `[t, 2 * t]` and in `[t, t + 2 ^ m]`, for
  every `t`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BackoffRetryCost

/-- The call at which the `k`-th compilation is attempted (from `0`), with gaps
capped at `2 ^ m` calls. -/
def pos (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => pos m k + 2 ^ min k m

/-- The first retry is the call right after the first refusal. -/
theorem pos_one (m : Nat) : pos m 1 = 1 := by simp [pos]

theorem pos_strictMono (m : Nat) : StrictMono (pos m) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [pos]
  have := Nat.one_le_two_pow (n := min k m)
  omega

theorem le_pos (m k : Nat) : k ≤ pos m k := (pos_strictMono m).id_le k

/-- Below the cap the attempts are the calls `2 ^ k - 1`. -/
theorem pos_eq (m k : Nat) (hk : k ≤ m) : pos m k + 1 = 2 ^ k := by
  induction k with
  | zero => simp [pos]
  | succ k ih =>
    simp only [pos, Nat.min_eq_left (Nat.le_of_succ_le hk), pow_succ]
    have := ih (Nat.le_of_succ_le hk)
    omega

/-- A gap is at most one more than the attempt it starts from. -/
theorem gap_le_pos_succ (m k : Nat) : 2 ^ min k m ≤ pos m k + 1 := by
  rcases le_total k m with h | h
  · rw [Nat.min_eq_left h, pos_eq m k h]
  · rw [Nat.min_eq_right h]
    have hmono : pos m m ≤ pos m k := (pos_strictMono m).monotone h
    have := pos_eq m m le_rfl
    omega

/-- Past the cap the attempts are `2 ^ m` calls apart. -/
theorem pos_cap (m j : Nat) : pos m (m + j) + 1 = 2 ^ m * (j + 1) := by
  induction j with
  | zero => simpa using pos_eq m m le_rfl
  | succ j ih =>
    have h : pos m (m + (j + 1)) = pos m (m + j) + 2 ^ m := by
      rw [← Nat.add_assoc, pos, Nat.min_eq_right (Nat.le_add_right m j)]
    rw [h, Nat.add_right_comm, ih]
    ring

/-- The attempts among the first `C` calls. -/
def attempts (m C : Nat) : Finset Nat := ((Finset.range C).image (pos m)).filter (· < C)

/-- Retrying at every call attempts at each of the first `C` calls. -/
theorem retry_always (C : Nat) : (Finset.range C).card = C := Finset.card_range C

/-- The attempts among the first `C` calls number at most `m + 1 + C / 2 ^ m`:
at most `m` below the cap, and past it one per `2 ^ m` calls. -/
theorem attempts_le (m C : Nat) : (attempts m C).card ≤ m + 1 + C / 2 ^ m := by
  -- Every attempt below `C` has an index below `m + C / 2 ^ m + 1`.
  have hsub : attempts m C ⊆ (Finset.range (m + C / 2 ^ m + 1)).image (pos m) := by
    intro n hn
    simp only [attempts, Finset.mem_filter, Finset.mem_image] at hn
    obtain ⟨⟨k, _, rfl⟩, hlt⟩ := hn
    refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
    rw [Finset.mem_range]
    rcases le_or_gt k m with h | h
    · exact Nat.lt_succ_of_le (le_trans h (Nat.le_add_right _ _))
    · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      have hcap := pos_cap m j
      have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
      -- `2 ^ m * (j + 1) ≤ C`, so `j + 1 ≤ C / 2 ^ m`.
      have hle : 2 ^ m * (j + 1) ≤ C := by omega
      have hj : j + 1 ≤ C / 2 ^ m := (Nat.le_div_iff_mul_le hpos).mpr (by linarith)
      generalize C / 2 ^ m = q at hj ⊢
      omega
  calc (attempts m C).card
      ≤ ((Finset.range (m + C / 2 ^ m + 1)).image (pos m)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (m + C / 2 ^ m + 1)).card := Finset.card_image_le
    _ = m + 1 + C / 2 ^ m := by rw [Finset.card_range]; ring

/-- For every call `t`, some attempt falls at or after `t`, no later than
`2 * t` and no later than `t + 2 ^ m`. -/
theorem attempt_by (m t : Nat) :
    ∃ k, t ≤ pos m k ∧ pos m k ≤ 2 * t ∧ pos m k ≤ t + 2 ^ m := by
  have hex : ∃ k, t ≤ pos m k := ⟨t, le_pos m t⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, t ≤ pos m k ∧ ∀ j < k, ¬ t ≤ pos m j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  refine ⟨k, hk, ?_⟩
  cases k with
  | zero => simp [pos]
  | succ j =>
    have hj : ¬ t ≤ pos m j := hmin j (Nat.lt_succ_self j)
    have hgap := gap_le_pos_succ m j
    have hcap : 2 ^ min j m ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right j m)
    simp only [pos]
    omega

end Mettapedia.Machines.BackoffRetryCost
