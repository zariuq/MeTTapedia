import Mathlib.Tactic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic

#check mul_dvd_mul_iff_left
#check mul_dvd_mul_iff_right
#check Nat.pow_dvd_pow_iff_le_right
#check Finset.sum_bij
#check Nat.factorization_pow_self
#check Finset.sum_range_succ
#check Nat.add_left_cancel
#check Nat.add_left_cancel_iff
#check Nat.pow_le_pow_right
#check Nat.pow_le_pow_left
#check Nat.le_pow
#check one_le_pow₀
#check Nat.totient_pos

example (n : Nat) (h : 3 ≤ n) : n + 1 < 2 ^ n := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ n _ inductionHypothesis =>
      rw [pow_succ]
      have powerPositive : 0 < 2 ^ n := pow_pos (by omega) n
      omega

example (n : Nat) (h : 5 ≤ n) : 3 * n < 2 ^ n - 1 := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ n nBound inductionHypothesis =>
      rw [pow_succ]
      have powerLarge : 4 ≤ 2 ^ n := by
        exact (Nat.pow_le_pow_right (n := 2) (by omega) (by omega : 2 ≤ n))
      omega

example (prime exponent : Nat) (primeBound : 5 ≤ prime)
    (exponentPositive : 0 < exponent) :
    prime * 3 ^ exponent < (2 ^ prime - 1) ^ exponent := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero exponentPositive.ne'
  have baseBound : 3 * prime < 2 ^ prime - 1 := by
    induction prime, primeBound using Nat.le_induction with
    | base => norm_num
    | succ n nBound inductionHypothesis =>
        rw [pow_succ]
        have powerLarge : 4 ≤ 2 ^ n := by
          exact Nat.pow_le_pow_right (n := 2) (by omega) (by omega : 2 ≤ n)
        omega
  have threeLeBase : 3 ≤ 2 ^ prime - 1 := by omega
  have powersLe : 3 ^ previous ≤ (2 ^ prime - 1) ^ previous :=
    Nat.pow_le_pow_left threeLeBase previous
  simp only [pow_succ]
  calc
    prime * (3 ^ previous * 3) = (3 * prime) * 3 ^ previous := by ring
    _ < (2 ^ prime - 1) * 3 ^ previous :=
      Nat.mul_lt_mul_of_pos_right baseBound (pow_pos (by omega) previous)
    _ ≤ (2 ^ prime - 1) * (2 ^ prime - 1) ^ previous :=
      Nat.mul_le_mul_left _ powersLe
    _ = (2 ^ prime - 1) ^ previous * (2 ^ prime - 1) := by ring

example (k previous : Nat) (h : previous ≤ k) :
    k - (k - previous + 1) = previous - 1 := by
  have restored : k - previous + previous = k := Nat.sub_add_cancel h
  omega

example (p : Nat) (h : 2 ≤ p) : p - 1 + 1 = p := by omega
example (p : Nat) (h : 2 ≤ p) : p - 1 - 1 = p - 2 := by omega

example {p exponent multiplier : Nat}
    (hp : p.Prime) (hpOdd : Odd p)
    (exponentPositive : 0 < exponent) (multiplierPositive : 0 < multiplier)
    (pDivides : p ∣ 2 ^ exponent - 1) :
    (2 ^ (exponent * multiplier) - 1).factorization p =
      (2 ^ exponent - 1).factorization p + multiplier.factorization p := by
  have pNotDvdPower : ¬p ∣ 2 ^ exponent := by
    intro divides
    have pDividesTwo := hp.dvd_of_dvd_pow divides
    rcases (Nat.dvd_prime Nat.prime_two).mp pDividesTwo with pIsOne | pIsTwo
    · exact hp.ne_one pIsOne
    · subst p
      norm_num at hpOdd
  have lte := Nat.emultiplicity_pow_sub_pow hp hpOdd pDivides pNotDvdPower multiplier
  rw [one_pow, ← pow_mul] at lte
  have leftNonzero : 2 ^ (exponent * multiplier) - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt
      (one_lt_pow₀ (by omega) (mul_pos exponentPositive multiplierPositive).ne')).ne'
  have middleNonzero : 2 ^ exponent - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) exponentPositive.ne')).ne'
  have multiplierNonzero : multiplier ≠ 0 := multiplierPositive.ne'
  have leftFinite : FiniteMultiplicity p (2 ^ (exponent * multiplier) - 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.pos_of_ne_zero leftNonzero⟩
  have middleFinite : FiniteMultiplicity p (2 ^ exponent - 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.pos_of_ne_zero middleNonzero⟩
  have multiplierFinite : FiniteMultiplicity p multiplier :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, multiplierPositive⟩
  rw [leftFinite.emultiplicity_eq_multiplicity,
    middleFinite.emultiplicity_eq_multiplicity,
    multiplierFinite.emultiplicity_eq_multiplicity] at lte
  norm_cast at lte
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    Nat.factorization_def _ hp,
    padicValNat_def' hp.ne_one leftNonzero,
    padicValNat_def' hp.ne_one middleNonzero,
    padicValNat_def' hp.ne_one multiplierNonzero]
  exact lte
