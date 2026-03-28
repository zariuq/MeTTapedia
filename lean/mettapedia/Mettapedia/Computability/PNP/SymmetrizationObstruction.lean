import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# P vs NP crux: majority symmetrization fails at zero margin

The Goertzel switching paper claims that a majority over only polylogarithmically many
symmetrized surrogate labels concentrates to the Bayes rule on the local sigma-field.

This file isolates a sharp obstruction to that step: if the surrogate labels are unbiased
(`p = 1/2`) for some local input `u`, then on an odd number of samples the majority vote is
exactly balanced between `true` and `false`. Therefore it matches any fixed tie-breaking Bayes
rule on only half of the seed choices.

So the concentration-to-Bayes step cannot be correct without an additional margin assumption
separating the conditional mean away from `1/2`.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

/-- Length-`n` bit-vectors. -/
abbrev BitVec (n : ℕ) := Fin n → Bool

/-- Number of `true` entries in a bit-vector. -/
def ones {n : ℕ} (x : BitVec n) : ℕ :=
  ∑ i, if x i then 1 else 0

/-- Strict majority predicate. For odd `n`, ties are impossible. -/
def majority {n : ℕ} (x : BitVec n) : Bool :=
  n / 2 < ones x

/-- Bitwise complement. -/
def compl {n : ℕ} (x : BitVec n) : BitVec n :=
  fun i => !(x i)

lemma ones_add_ones_compl {n : ℕ} (x : BitVec n) :
    ones x + ones (compl x) = n := by
  unfold ones compl
  calc
    (∑ i, if x i then 1 else 0) + (∑ i, if !x i then 1 else 0)
        = ∑ i, ((if x i then 1 else 0) + (if !x i then 1 else 0)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ i, 1 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases h : x i <;> simp [h]
    _ = n := by simp

lemma majority_compl {n : ℕ} (hodd : Odd n) (x : BitVec n) :
    majority (compl x) = !(majority x) := by
  rcases hodd with ⟨k, rfl⟩
  unfold majority
  have hsum := ones_add_ones_compl x
  by_cases hx : (2 * k + 1) / 2 < ones x
  · have hnot : ¬ (2 * k + 1) / 2 < ones (compl x) := by
      omega
    simp [hx, hnot]
  · have hyes : (2 * k + 1) / 2 < ones (compl x) := by
      omega
    simp [hx, hyes]

/-- On odd sample size, complement gives a bijection between majority-true and majority-false
bit-vectors. -/
def majorityTrueEquivMajorityFalse {n : ℕ} (hodd : Odd n) :
    {x : BitVec n // majority x = true} ≃ {x : BitVec n // majority x = false} where
  toFun x := ⟨compl x.1, by
    have hcomp := majority_compl hodd x.1
    simpa [x.2] using hcomp⟩
  invFun x := ⟨compl x.1, by
    have hcomp := majority_compl hodd x.1
    simpa [x.2] using hcomp⟩
  left_inv x := by
    ext i
    simp [compl]
  right_inv x := by
    ext i
    simp [compl]

theorem card_majority_true_eq_card_majority_false {n : ℕ} (hodd : Odd n) :
    Fintype.card {x : BitVec n // majority x = true} =
      Fintype.card {x : BitVec n // majority x = false} :=
  Fintype.card_congr (majorityTrueEquivMajorityFalse hodd)

theorem card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  simp [BitVec]

/-- For odd sample size, strict majority succeeds on exactly half of all unbiased bit-vectors. -/
theorem two_mul_card_majority_true {n : ℕ} (hodd : Odd n) :
    2 * Fintype.card {x : BitVec n // majority x = true} = 2 ^ n := by
  set a : ℕ := Fintype.card {x : BitVec n // majority x = true}
  have hcomp :
      Fintype.card {x : BitVec n // majority x = false} =
        Fintype.card (BitVec n) - a := by
    simpa using (Fintype.card_subtype_compl fun x : BitVec n => majority x = true)
  have heq : a = Fintype.card {x : BitVec n // majority x = false} := by
    simpa [a] using card_majority_true_eq_card_majority_false hodd
  rw [card_bitVec] at hcomp
  have hsub : 2 ^ n - a = a := by
    simpa [heq] using hcomp.symm
  have hle : a ≤ 2 ^ n := by
    rw [← card_bitVec]
    simpa [a] using Fintype.card_subtype_le (fun x : BitVec n => majority x = true)
  have hsum : 2 ^ n = a + a := Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum.symm

/-- If the Bayes classifier ties at `p = 1/2` and breaks toward `true`, then majority on an odd
number of unbiased labels can match that Bayes rule on at most half the samples. -/
theorem majority_tie_break_not_high_probability {n : ℕ} (hodd : Odd n) :
    Fintype.card {x : BitVec n // majority x = true} * 2 = Fintype.card (BitVec n) := by
  simpa [Nat.mul_comm] using two_mul_card_majority_true hodd

end Mettapedia.Computability.PNP
