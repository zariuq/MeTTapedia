import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Exact rational complex amplitudes

Executable amplitudes are Mathlib's quadratic algebra over the rationals
with the relation `i² = -1`. Pair arithmetic is proved to agree with that
algebra, and its interpretation into the complex numbers is injective.

Squared norm is a nonnegative, multiplicative readout. It is not additive:
alternative amplitudes may interfere. Consequently normalization and support
must be declared observations, rather than silent changes of coefficient
algebra.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RationalComplexAmplitude

open scoped QuadraticAlgebra

abbrev Amplitude := QuadraticAlgebra ℚ (-1) 0

def pairAdd (left right : ℚ × ℚ) : ℚ × ℚ :=
  (left.1 + right.1, left.2 + right.2)

def pairMultiply (left right : ℚ × ℚ) : ℚ × ℚ :=
  (left.1 * right.1 - left.2 * right.2,
    left.1 * right.2 + left.2 * right.1)

def fromPair (pair : ℚ × ℚ) : Amplitude := ⟨pair.1, pair.2⟩
def toPair (value : Amplitude) : ℚ × ℚ := (value.re, value.im)

theorem pair_add_agrees (left right : ℚ × ℚ) :
    fromPair (pairAdd left right) = fromPair left + fromPair right := rfl

theorem pair_multiply_agrees (left right : ℚ × ℚ) :
    fromPair (pairMultiply left right) = fromPair left * fromPair right := by
  ext <;> simp [fromPair, pairMultiply, sub_eq_add_neg]

@[simp] theorem fromPair_toPair (value : Amplitude) : fromPair (toPair value) = value := rfl
@[simp] theorem toPair_fromPair (pair : ℚ × ℚ) : toPair (fromPair pair) = pair := rfl

noncomputable def intoComplex : Amplitude →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp [Algebra.smul_def]⟩

theorem intoComplex_re (value : Amplitude) : (intoComplex value).re = (value.re : ℝ) := by
  simp [intoComplex, QuadraticAlgebra.lift, Algebra.smul_def]

theorem intoComplex_im (value : Amplitude) : (intoComplex value).im = (value.im : ℝ) := by
  simp [intoComplex, QuadraticAlgebra.lift, Algebra.smul_def]

theorem intoComplex_injective : Function.Injective intoComplex := by
  intro left right equality
  ext
  · have reals := congrArg Complex.re equality
    rw [intoComplex_re, intoComplex_re] at reals
    exact_mod_cast reals
  · have imaginaries := congrArg Complex.im equality
    rw [intoComplex_im, intoComplex_im] at imaginaries
    exact_mod_cast imaginaries

/-- The exact Born readout, supplied by the standard quadratic norm. -/
def born : Amplitude →* ℚ := QuadraticAlgebra.norm

theorem born_formula (value : Amplitude) :
    born value = value.re * value.re + value.im * value.im := by
  simp [born, QuadraticAlgebra.norm_def]

theorem born_nonnegative (value : Amplitude) : 0 ≤ born value := by
  rw [born_formula]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem born_zero_iff (value : Amplitude) : born value = 0 ↔ value = 0 := by
  constructor
  · intro zero
    rw [born_formula] at zero
    have realZero : value.re = 0 := by nlinarith [sq_nonneg value.im]
    have imaginaryZero : value.im = 0 := by nlinarith [sq_nonneg value.re]
    ext
    · exact realZero
    · exact imaginaryZero
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

theorem born_agrees_complex (value : Amplitude) :
    (born value : ℝ) = Complex.normSq (intoComplex value) := by
  rw [born_formula, Complex.normSq_apply, intoComplex_re, intoComplex_im]
  norm_cast

theorem conjugation_agrees (value : Amplitude) :
    toPair (star value) = (value.re, -value.im) := by
  simp [toPair]

theorem imaginary_square : fromPair (0, 1) * fromPair (0, 1) = (-1 : Amplitude) := by
  ext <;> norm_num [fromPair, Amplitude]

theorem interference_cancels : (1 : Amplitude) + (-1) = 0 := add_neg_cancel _

theorem born_not_additive :
    born ((1 : Amplitude) + (-1)) ≠ born 1 + born (-1) := by
  norm_num [born, QuadraticAlgebra.norm_def, Amplitude]

theorem exact_mixed_product :
    pairMultiply (2, 3) (5, 7) = (-11, 29) := by norm_num [pairMultiply]

end Mettapedia.Algebra.RationalComplexAmplitude
