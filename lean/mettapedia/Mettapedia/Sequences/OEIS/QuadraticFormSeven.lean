import Mathlib.Tactic

/-!
# The quadratic form `a^2 + 7*b^2`

This module packages the two identities needed to generate certified
representations of a family of Mersenne numbers.  The construction is not
specific to a finite OEIS prefix: representations compose multiplicatively,
and the cyclotomic cofactor from exponent `n` to exponent `7*n` has an explicit
representation whenever `n` is positive.
-/

namespace Mettapedia.Sequences.OEIS.QuadraticFormSeven

/-- A natural number represented by the binary quadratic form
`a^2 + 7*b^2`. -/
def Represents (number : Nat) : Prop :=
  ∃ a b : Nat, number = a ^ 2 + 7 * b ^ 2

/-- The norm-composition identity, with `natAbs` handling the sign of the
first composed coordinate. -/
theorem Represents.mul {first second : Nat}
    (firstRep : Represents first) (secondRep : Represents second) :
    Represents (first * second) := by
  rcases firstRep with ⟨a, b, firstEq⟩
  rcases secondRep with ⟨c, d, secondEq⟩
  let firstCoord : Int := (a : Int) * c - 7 * (b : Int) * d
  refine ⟨firstCoord.natAbs,
    a * d + b * c, ?_⟩
  apply Nat.cast_injective (R := Int)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Int.natCast_natAbs, sq_abs]
  have firstEqInt : (first : Int) = (a : Int) ^ 2 + 7 * (b : Int) ^ 2 := by
    exact_mod_cast firstEq
  have secondEqInt : (second : Int) = (c : Int) ^ 2 + 7 * (d : Int) ^ 2 := by
    exact_mod_cast secondEq
  rw [firstEqInt, secondEqInt]
  simp only [firstCoord]
  push_cast
  ring

/-- The seventh geometric cofactor `1 + x + ... + x^6`. -/
def sevenCofactor (x : Nat) : Nat :=
  1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6

/-- For `x = 2*y`, the seventh cofactor has the representation

`4 * (1+x+...+x^6) = (2*x^3+x^2-x-2)^2 + 7*(x^2+x)^2`.

Writing `x=2*y` removes both factors of two and gives integral coordinates. -/
theorem sevenCofactor_two_mul_represents (y : Nat) :
    Represents (sevenCofactor (2 * y)) := by
  let first : Int := 8 * (y : Int) ^ 3 + 2 * (y : Int) ^ 2 - y - 1
  let second : Nat := 2 * y ^ 2 + y
  refine ⟨first.natAbs, second, ?_⟩
  apply Nat.cast_injective (R := Int)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Int.natCast_natAbs, sq_abs]
  simp only [sevenCofactor, first, second]
  push_cast
  ring

/-- The Mersenne number at exponent `n`. -/
def mersenne (n : Nat) : Nat := 2 ^ n - 1

/-- The standard seventh-power factorization of a Mersenne number. -/
theorem mersenne_seven_mul (n : Nat) :
    mersenne (7 * n) = mersenne n * sevenCofactor (2 ^ n) := by
  unfold mersenne
  apply Nat.cast_injective (R := Int)
  simp only [Nat.cast_mul]
  rw [Nat.cast_sub (Nat.one_le_pow n 2 (by omega)),
    Nat.cast_sub (Nat.one_le_pow (7 * n) 2 (by omega))]
  simp only [sevenCofactor, Nat.cast_add,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [show 7 * n = n * 7 by omega, pow_mul]
  ring

/-- At every positive exponent, the seventh cofactor of `2^n` is represented
by `a^2 + 7*b^2`. -/
theorem sevenCofactor_two_pow_represents {n : Nat} (positive : 0 < n) :
    Represents (sevenCofactor (2 ^ n)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  simpa [pow_succ, Nat.mul_comm] using
    sevenCofactor_two_mul_represents (2 ^ k)

/-- A represented Mersenne number remains represented when its exponent is
multiplied by seven. -/
theorem mersenne_seven_mul_represents {n : Nat} (positive : 0 < n)
    (represented : Represents (mersenne n)) :
    Represents (mersenne (7 * n)) := by
  rw [mersenne_seven_mul]
  exact represented.mul (sevenCofactor_two_pow_represents positive)

/-- The base certificate `2^6 - 1 = 0^2 + 7*3^2`. -/
theorem mersenne_six_represents : Represents (mersenne 6) := by
  exact ⟨0, 3, by norm_num [mersenne]⟩

/-- An infinite certified family containing the four published exponents
`6, 42, 294, 2058`: every `2^(6*7^r)-1` is represented by
`a^2 + 7*b^2`. -/
theorem mersenne_six_mul_seven_pow_represents (r : Nat) :
    Represents (mersenne (6 * 7 ^ r)) := by
  induction r with
  | zero => simpa using mersenne_six_represents
  | succ r inductionHypothesis =>
      have lifted := mersenne_seven_mul_represents
        (n := 6 * 7 ^ r) (by positivity) inductionHypothesis
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using lifted

#print axioms Represents.mul
#print axioms sevenCofactor_two_mul_represents
#print axioms mersenne_six_mul_seven_pow_represents

end Mettapedia.Sequences.OEIS.QuadraticFormSeven
