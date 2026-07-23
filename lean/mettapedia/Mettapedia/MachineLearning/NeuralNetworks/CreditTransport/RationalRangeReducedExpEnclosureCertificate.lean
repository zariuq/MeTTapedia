import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalExpEnclosureCertificate

/-!
# Power-of-two range reduction for rational exponential certificates

The direct rational Taylor checker is intentionally restricted to arguments
of absolute value at most one.  This file enlarges its domain without enlarging
the trusted Taylor theorem: an untrusted producer supplies a checked direct
certificate at `x / 2^k`, and the kernel raises its endpoints to `2^k` using
`exp (2^k * y) = exp y ^ (2^k)`.

The lower endpoint of the reduced certificate must be nonnegative.  This is a
real mathematical premise needed for order-preserving exponentiation, not a
formatting convention.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalRangeReducedExpEnclosureCertificate

open RationalExpEnclosureCertificate

/-- Natural power-of-two scale used by repeated-squaring range reduction. -/
def expScale (halvings : ℕ) : ℕ := 2 ^ halvings

/-- A direct small-region certificate lifted to an arbitrary rational
argument by a power-of-two scale. -/
structure RangeReducedExpEnclosure where
  argument : ℚ
  halvings : ℕ
  reduced : ExpEnclosure
  lower : ℚ
  upper : ℚ
  deriving Repr

/-- Propositional meaning mirrored by `RangeReducedExpEnclosure.check`. -/
def RangeReducedExpEnclosure.Valid
    (certificate : RangeReducedExpEnclosure) : Prop :=
  certificate.reduced.Valid ∧
  certificate.reduced.argument * expScale certificate.halvings =
    certificate.argument ∧
  0 ≤ certificate.reduced.lower ∧
  certificate.lower ≤
    certificate.reduced.lower ^ expScale certificate.halvings ∧
  certificate.reduced.upper ^ expScale certificate.halvings ≤
    certificate.upper

/-- Executable rational checker for power-of-two range reduction. -/
def RangeReducedExpEnclosure.check
    (certificate : RangeReducedExpEnclosure) : Bool :=
  certificate.reduced.check &&
    decide (
      certificate.reduced.argument * expScale certificate.halvings =
        certificate.argument ∧
      0 ≤ certificate.reduced.lower ∧
      certificate.lower ≤
        certificate.reduced.lower ^ expScale certificate.halvings ∧
      certificate.reduced.upper ^ expScale certificate.halvings ≤
        certificate.upper)

theorem RangeReducedExpEnclosure.check_eq_true_iff
    (certificate : RangeReducedExpEnclosure) :
    certificate.check = true ↔ certificate.Valid := by
  simp [RangeReducedExpEnclosure.check, RangeReducedExpEnclosure.Valid,
    ExpEnclosure.check_eq_true_iff]

/-- An accepted range-reduced record encloses the exact exponential at its
declared full argument. -/
theorem RangeReducedExpEnclosure.sound
    (certificate : RangeReducedExpEnclosure)
    (hcheck : certificate.check = true) :
    (certificate.lower : ℝ) ≤ Real.exp (certificate.argument : ℝ) ∧
      Real.exp (certificate.argument : ℝ) ≤ (certificate.upper : ℝ) := by
  rcases certificate.check_eq_true_iff.mp hcheck with
    ⟨hreduced, hargument, hlowerNonneg, hlower, hupper⟩
  have hreducedCheck : certificate.reduced.check = true :=
    certificate.reduced.check_eq_true_iff.mpr hreduced
  have hreducedSound := certificate.reduced.sound hreducedCheck
  have hargumentReal :
      (certificate.reduced.argument : ℝ) *
          (expScale certificate.halvings : ℕ) =
        (certificate.argument : ℝ) := by
    exact_mod_cast hargument
  have hlowerNonnegReal : 0 ≤ (certificate.reduced.lower : ℝ) := by
    exact_mod_cast hlowerNonneg
  have hlowerReal :
      (certificate.lower : ℝ) ≤
        (certificate.reduced.lower : ℝ) ^
          expScale certificate.halvings := by
    exact_mod_cast hlower
  have hupperReal :
      (certificate.reduced.upper : ℝ) ^
          expScale certificate.halvings ≤
        (certificate.upper : ℝ) := by
    exact_mod_cast hupper
  have hlowerPow :
      (certificate.reduced.lower : ℝ) ^ expScale certificate.halvings ≤
        Real.exp (certificate.reduced.argument : ℝ) ^
          expScale certificate.halvings :=
    pow_le_pow_left₀ hlowerNonnegReal hreducedSound.1 _
  have hupperPow :
      Real.exp (certificate.reduced.argument : ℝ) ^
          expScale certificate.halvings ≤
        (certificate.reduced.upper : ℝ) ^ expScale certificate.halvings :=
    pow_le_pow_left₀ (Real.exp_pos _).le hreducedSound.2 _
  have hexpIdentity :
      Real.exp (certificate.argument : ℝ) =
        Real.exp (certificate.reduced.argument : ℝ) ^
          expScale certificate.halvings := by
    rw [← hargumentReal, mul_comm]
    exact Real.exp_nat_mul _ _
  constructor
  · rw [hexpIdentity]
    exact hlowerReal.trans hlowerPow
  · rw [hexpIdentity]
    exact hupperPow.trans hupperReal

/-! ## Positive and corrupt fixtures -/

/-- Repeated squaring lifts the checked enclosure of `exp (-1/2)` to
`exp (-2)`. -/
def expNegTwo : RangeReducedExpEnclosure where
  argument := -2
  halvings := 2
  reduced := expNegHalf
  lower := (29 / 48) ^ 4
  upper := (39 / 64) ^ 4

theorem expNegTwo_is_accepted : expNegTwo.check = true := by
  simp only [RangeReducedExpEnclosure.check, expNegTwo]
  rw [expNegHalf_is_accepted]
  norm_num [expScale, expNegHalf]

theorem expNegTwo_sound :
    (((29 / 48 : ℚ) ^ 4 : ℚ) : ℝ) ≤ Real.exp (-2) ∧
      Real.exp (-2) ≤ (((39 / 64 : ℚ) ^ 4 : ℚ) : ℝ) := by
  simpa [expNegTwo] using expNegTwo.sound expNegTwo_is_accepted

/-- A full argument inconsistent with its reduced argument and scale is
rejected. -/
def mismatchedExpNegTwo : RangeReducedExpEnclosure :=
  { expNegTwo with argument := -3 }

theorem mismatchedExpNegTwo_is_rejected :
    mismatchedExpNegTwo.check = false := by
  simp only [mismatchedExpNegTwo, expNegTwo,
    RangeReducedExpEnclosure.check]
  rw [expNegHalf_is_accepted]
  norm_num [expScale, expNegHalf]

/-- A negative reduced lower endpoint is rejected because exponentiation
would not preserve the required lower inequality uniformly. -/
def negativeReducedLower : RangeReducedExpEnclosure :=
  { expNegTwo with
    reduced := { expNegHalf with lower := -1 }
    lower := 0 }

theorem negativeReducedLower_is_rejected :
    negativeReducedLower.check = false := by
  norm_num [negativeReducedLower, expNegTwo, RangeReducedExpEnclosure.check,
    ExpEnclosure.check, expScale, expNegHalf, expTaylorRat,
    expTaylorErrorRat, Finset.sum_range_succ, Nat.factorial]

#print axioms RangeReducedExpEnclosure.check_eq_true_iff
#print axioms RangeReducedExpEnclosure.sound
#print axioms expNegTwo_sound
#print axioms mismatchedExpNegTwo_is_rejected
#print axioms negativeReducedLower_is_rejected

end RationalRangeReducedExpEnclosureCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
