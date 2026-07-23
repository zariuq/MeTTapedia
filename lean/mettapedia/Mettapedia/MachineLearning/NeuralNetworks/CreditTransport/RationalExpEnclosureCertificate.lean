import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegisteredUnaryExpressionCertificate
import Mathlib.Analysis.Complex.Exponential

/-!
# Rational Taylor enclosures for the real exponential

This file is the first transcendental leaf accepted by the finite numerical
certificate stack.  An untrusted producer supplies a rational argument, a
positive Taylor depth, and rational lower and upper endpoints.  The Boolean
checker recomputes the Taylor polynomial and the explicit remainder from
`Real.exp_bound`; its soundness theorem places the exact real exponential
inside the claimed interval.

The direct certificate is deliberately restricted to arguments of absolute
value at most one.  Range reduction and correspondence with a particular
floating-point library implementation are separate later layers.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalExpEnclosureCertificate

open Finset

/-- Rational Taylor polynomial `sum_{m < terms} x^m / m!`. -/
def expTaylorRat (terms : ℕ) (argument : ℚ) : ℚ :=
  ∑ m ∈ range terms, argument ^ m / (m.factorial : ℚ)

/-- Rational remainder used by `Real.exp_bound` on `|argument| <= 1`. -/
def expTaylorErrorRat (terms : ℕ) (argument : ℚ) : ℚ :=
  |argument| ^ terms *
    ((terms.succ : ℚ) / ((terms.factorial : ℚ) * (terms : ℚ)))

@[simp] theorem cast_expTaylorRat (terms : ℕ) (argument : ℚ) :
    ((expTaylorRat terms argument : ℚ) : ℝ) =
      ∑ m ∈ range terms, (argument : ℝ) ^ m / m.factorial := by
  simp [expTaylorRat, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast]

@[simp] theorem cast_expTaylorErrorRat (terms : ℕ) (argument : ℚ) :
    ((expTaylorErrorRat terms argument : ℚ) : ℝ) =
      |(argument : ℝ)| ^ terms *
        (terms.succ / (terms.factorial * terms)) := by
  simp [expTaylorErrorRat, Rat.cast_abs, Rat.cast_pow, Rat.cast_div,
    Rat.cast_mul, Rat.cast_natCast]

/-- Finite source-facing record for one real-exponential enclosure. -/
structure ExpEnclosure where
  argument : ℚ
  terms : ℕ
  lower : ℚ
  upper : ℚ
  deriving Repr

/-- Propositional meaning mirrored by `ExpEnclosure.check`. -/
def ExpEnclosure.Valid (certificate : ExpEnclosure) : Prop :=
  0 < certificate.terms ∧
  |certificate.argument| ≤ 1 ∧
  certificate.lower ≤
    expTaylorRat certificate.terms certificate.argument -
      expTaylorErrorRat certificate.terms certificate.argument ∧
  expTaylorRat certificate.terms certificate.argument +
      expTaylorErrorRat certificate.terms certificate.argument ≤
    certificate.upper

/-- Decidable checker for a rational real-exponential enclosure. -/
def ExpEnclosure.check (certificate : ExpEnclosure) : Bool :=
  decide (0 < certificate.terms) &&
    (decide (|certificate.argument| ≤ 1) &&
      (decide (certificate.lower ≤
        expTaylorRat certificate.terms certificate.argument -
          expTaylorErrorRat certificate.terms certificate.argument) &&
       decide (expTaylorRat certificate.terms certificate.argument +
          expTaylorErrorRat certificate.terms certificate.argument ≤
        certificate.upper)))

theorem ExpEnclosure.check_eq_true_iff (certificate : ExpEnclosure) :
    certificate.check = true ↔ certificate.Valid := by
  simp [ExpEnclosure.check, ExpEnclosure.Valid]

/-- Every accepted record encloses the exact real exponential. -/
theorem ExpEnclosure.sound (certificate : ExpEnclosure)
    (hcheck : certificate.check = true) :
    (certificate.lower : ℝ) ≤ Real.exp (certificate.argument : ℝ) ∧
      Real.exp (certificate.argument : ℝ) ≤ (certificate.upper : ℝ) := by
  rcases (certificate.check_eq_true_iff.mp hcheck) with
    ⟨hterms, hargument, hlower, hupper⟩
  have hargumentReal : |(certificate.argument : ℝ)| ≤ 1 := by
    exact_mod_cast hargument
  have hbound := Real.exp_bound hargumentReal hterms
  rw [← cast_expTaylorRat, ← cast_expTaylorErrorRat] at hbound
  have habs := abs_le.mp hbound
  have hlowerReal :
      (certificate.lower : ℝ) ≤
        (expTaylorRat certificate.terms certificate.argument : ℝ) -
          (expTaylorErrorRat certificate.terms certificate.argument : ℝ) := by
    exact_mod_cast hlower
  have hupperReal :
      (expTaylorRat certificate.terms certificate.argument : ℝ) +
          (expTaylorErrorRat certificate.terms certificate.argument : ℝ) ≤
        (certificate.upper : ℝ) := by
    exact_mod_cast hupper
  constructor <;> linarith

/-! ## Positive and negative fixtures -/

/-- Five Taylor terms certify a nontrivial rational enclosure of `exp (-1/2)`. -/
def expNegHalf : ExpEnclosure where
  argument := -1 / 2
  terms := 5
  lower := 29 / 48
  upper := 39 / 64

theorem expNegHalf_is_accepted : expNegHalf.check = true := by
  norm_num [expNegHalf, ExpEnclosure.check, ExpEnclosure.Valid,
    expTaylorRat, expTaylorErrorRat, Finset.sum_range_succ, Nat.factorial]

theorem expNegHalf_sound :
    (29 / 48 : ℝ) ≤ Real.exp (-1 / 2) ∧
      Real.exp (-1 / 2) ≤ (39 / 64 : ℝ) := by
  simpa [expNegHalf] using expNegHalf.sound expNegHalf_is_accepted

/-- A lower endpoint above the checked Taylor remainder is rejected. -/
def corruptExpNegHalf : ExpEnclosure where
  argument := -1 / 2
  terms := 5
  lower := 61 / 100
  upper := 39 / 64

theorem corruptExpNegHalf_is_rejected : corruptExpNegHalf.check = false := by
  norm_num [corruptExpNegHalf, ExpEnclosure.check, ExpEnclosure.Valid,
    expTaylorRat, expTaylorErrorRat, Finset.sum_range_succ, Nat.factorial]

/-- The direct Taylor checker refuses an argument outside its proved region. -/
def outOfRegion : ExpEnclosure where
  argument := 2
  terms := 8
  lower := 0
  upper := 10

theorem outOfRegion_is_rejected : outOfRegion.check = false := by
  norm_num [outOfRegion, ExpEnclosure.check, ExpEnclosure.Valid]

#print axioms ExpEnclosure.sound
#print axioms expNegHalf_sound
#print axioms corruptExpNegHalf_is_rejected
#print axioms outOfRegion_is_rejected

end RationalExpEnclosureCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
