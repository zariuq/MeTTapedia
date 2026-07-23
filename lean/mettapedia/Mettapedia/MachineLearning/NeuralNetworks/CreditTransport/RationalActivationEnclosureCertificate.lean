import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RationalExpEnclosureCertificate

/-!
# Rational sigmoid and SiLU enclosure certificates

An accepted record contains a checked rational enclosure of `exp (-x)`, a
rational output interval obtained from it, and a local runtime-error radius.
The checker validates all relations over rationals.  Its theorem then proves
the corresponding runtime-to-real error for the registered sigmoid or SiLU
semantics.

Square is intentionally rejected by this transcendental certificate type; it
has an exact algebraic checker.  This layer still does not identify the
rational runtime value with the output of any particular hardware kernel.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace RationalActivationEnclosureCertificate

open RegisteredUnaryExpressionCertificate
open RationalExpEnclosureCertificate
open SiLUTransitionBounds

noncomputable section

/-- Lower endpoint for sigmoid obtained from an upper bound on `exp (-x)`. -/
def sigmoidLowerRat (expUpper : ℚ) : ℚ := (1 + expUpper)⁻¹

/-- Upper endpoint for sigmoid obtained from a lower bound on `exp (-x)`. -/
def sigmoidUpperRat (expLower : ℚ) : ℚ := (1 + expLower)⁻¹

/-- Candidate lower endpoint for the registered activation. -/
def activationLowerRat (operation : RegisteredUnaryOp) (argument : ℚ)
    (expLower expUpper : ℚ) : ℚ :=
  match operation with
  | .square => argument ^ 2
  | .sigmoid => sigmoidLowerRat expUpper
  | .silu => min (argument * sigmoidLowerRat expUpper)
      (argument * sigmoidUpperRat expLower)

/-- Candidate upper endpoint for the registered activation. -/
def activationUpperRat (operation : RegisteredUnaryOp) (argument : ℚ)
    (expLower expUpper : ℚ) : ℚ :=
  match operation with
  | .square => argument ^ 2
  | .sigmoid => sigmoidUpperRat expLower
  | .silu => max (argument * sigmoidLowerRat expUpper)
      (argument * sigmoidUpperRat expLower)

/-- Source-facing rational record for a sigmoid or SiLU local evaluation. -/
structure ActivationEnclosure where
  operation : RegisteredUnaryOp
  argument : ℚ
  runtimeValue : ℚ
  localError : ℚ
  outputLower : ℚ
  outputUpper : ℚ
  expCertificate : ExpEnclosure
  deriving Repr

/-- Propositional meaning mirrored by `ActivationEnclosure.check`. -/
def ActivationEnclosure.Valid (certificate : ActivationEnclosure) : Prop :=
  match certificate.operation with
  | .square => False
  | .sigmoid | .silu =>
      certificate.expCertificate.argument = -certificate.argument ∧
      certificate.expCertificate.Valid ∧
      0 < certificate.expCertificate.lower ∧
      0 ≤ certificate.localError ∧
      certificate.outputLower ≤ activationLowerRat certificate.operation
        certificate.argument certificate.expCertificate.lower
        certificate.expCertificate.upper ∧
      activationUpperRat certificate.operation certificate.argument
        certificate.expCertificate.lower certificate.expCertificate.upper ≤
        certificate.outputUpper ∧
      certificate.runtimeValue - certificate.localError ≤
        certificate.outputLower ∧
      certificate.outputUpper ≤
        certificate.runtimeValue + certificate.localError

/-- Executable rational checker for a sigmoid or SiLU local enclosure. -/
def ActivationEnclosure.check (certificate : ActivationEnclosure) : Bool :=
  match certificate.operation with
  | .square => false
  | .sigmoid | .silu =>
      decide (certificate.expCertificate.argument = -certificate.argument) &&
      (certificate.expCertificate.check &&
        (decide (0 < certificate.expCertificate.lower) &&
         (decide (0 ≤ certificate.localError) &&
          (decide (certificate.outputLower ≤
            activationLowerRat certificate.operation certificate.argument
              certificate.expCertificate.lower certificate.expCertificate.upper) &&
           (decide (activationUpperRat certificate.operation certificate.argument
              certificate.expCertificate.lower certificate.expCertificate.upper ≤
                certificate.outputUpper) &&
            (decide (certificate.runtimeValue - certificate.localError ≤
                certificate.outputLower) &&
             decide (certificate.outputUpper ≤
                certificate.runtimeValue + certificate.localError)))))))

theorem ActivationEnclosure.check_eq_true_iff
    (certificate : ActivationEnclosure) :
    certificate.check = true ↔ certificate.Valid := by
  cases hop : certificate.operation <;>
    simp [ActivationEnclosure.check, ActivationEnclosure.Valid, hop,
      ExpEnclosure.check_eq_true_iff]

theorem ActivationEnclosure.Valid.localError_nonneg
    {certificate : ActivationEnclosure} (hvalid : certificate.Valid) :
    0 ≤ certificate.localError := by
  cases hoperation : certificate.operation with
  | square => simp only [ActivationEnclosure.Valid, hoperation] at hvalid
  | sigmoid | silu =>
      simp only [ActivationEnclosure.Valid, hoperation] at hvalid
      exact hvalid.2.2.2.1

private theorem sigmoid_bounds_of_exp_bounds
    {argument expLower expUpper : ℚ}
    (hlowerPositive : 0 < expLower)
    (hexpLower : (expLower : ℝ) ≤ Real.exp (-(argument : ℝ)))
    (hexpUpper : Real.exp (-(argument : ℝ)) ≤ (expUpper : ℝ)) :
    (sigmoidLowerRat expUpper : ℝ) ≤ Real.sigmoid (argument : ℝ) ∧
      Real.sigmoid (argument : ℝ) ≤ (sigmoidUpperRat expLower : ℝ) := by
  have hlowerPositiveReal : 0 < (expLower : ℝ) := by exact_mod_cast hlowerPositive
  have hupperPositiveReal : 0 < (expUpper : ℝ) :=
    (Real.exp_pos _).trans_le hexpUpper
  have hdenLower : 0 < (1 : ℝ) + expLower := by positivity
  have hdenExact : 0 < (1 : ℝ) + Real.exp (-(argument : ℝ)) := by positivity
  have hdenUpper : 0 < (1 : ℝ) + expUpper := by positivity
  constructor
  · rw [Real.sigmoid_def, sigmoidLowerRat, Rat.cast_inv, Rat.cast_add,
      Rat.cast_one]
    exact (inv_le_inv₀ hdenUpper hdenExact).2 <| by
      simpa [add_comm] using add_le_add_left hexpUpper 1
  · rw [Real.sigmoid_def, sigmoidUpperRat, Rat.cast_inv, Rat.cast_add,
      Rat.cast_one]
    exact (inv_le_inv₀ hdenExact hdenLower).2 <| by
      simpa [add_comm] using add_le_add_left hexpLower 1

private theorem mul_mem_min_max
    {argument lower value upper : ℝ}
    (hlower : lower ≤ value) (hupper : value ≤ upper) :
    min (argument * lower) (argument * upper) ≤ argument * value ∧
      argument * value ≤ max (argument * lower) (argument * upper) := by
  rcases le_total 0 argument with hargument | hargument
  · have hleft := mul_le_mul_of_nonneg_left hlower hargument
    have hright := mul_le_mul_of_nonneg_left hupper hargument
    exact ⟨(min_le_left _ _).trans hleft, hright.trans (le_max_right _ _)⟩
  · have hleft := mul_le_mul_of_nonpos_left hupper hargument
    have hright := mul_le_mul_of_nonpos_left hlower hargument
    exact ⟨(min_le_right _ _).trans hleft, hright.trans (le_max_left _ _)⟩

theorem exact_output_mem_candidates
    (operation : RegisteredUnaryOp) {argument expLower expUpper : ℚ}
    (hlowerPositive : 0 < expLower)
    (hexpLower : (expLower : ℝ) ≤ Real.exp (-(argument : ℝ)))
    (hexpUpper : Real.exp (-(argument : ℝ)) ≤ (expUpper : ℝ))
    (hnotSquare : operation ≠ .square) :
    (activationLowerRat operation argument expLower expUpper : ℝ) ≤
        operation.realMap (argument : ℝ) ∧
      operation.realMap (argument : ℝ) ≤
        (activationUpperRat operation argument expLower expUpper : ℝ) := by
  have hsigmoid := sigmoid_bounds_of_exp_bounds hlowerPositive hexpLower hexpUpper
  cases operation with
  | square => exact False.elim (hnotSquare rfl)
  | sigmoid =>
      simpa [activationLowerRat, activationUpperRat,
        RegisteredUnaryOp.realMap] using hsigmoid
  | silu =>
      have hmul := mul_mem_min_max (argument := (argument : ℝ))
        hsigmoid.1 hsigmoid.2
      simpa [activationLowerRat, activationUpperRat,
        RegisteredUnaryOp.realMap, sourceSiLU, Rat.cast_min, Rat.cast_max,
        Rat.cast_mul] using hmul

/-- Every accepted local record bounds its rational runtime output against
the registered exact real sigmoid or SiLU value. -/
theorem ActivationEnclosure.sound (certificate : ActivationEnclosure)
    (hcheck : certificate.check = true) :
    |(certificate.runtimeValue : ℝ) -
        certificate.operation.realMap (certificate.argument : ℝ)| ≤
      (certificate.localError : ℝ) := by
  have hvalid := certificate.check_eq_true_iff.mp hcheck
  cases hop : certificate.operation with
  | square =>
      simp only [ActivationEnclosure.Valid, hop] at hvalid
  | sigmoid | silu =>
      simp only [ActivationEnclosure.Valid, hop] at hvalid
      rcases hvalid with
        ⟨hexpArgument, hexpValid, hexpLowerPositive, hlocalNonneg,
          houtLower, houtUpper, hruntimeLower, hruntimeUpper⟩
      have hexpCheck : certificate.expCertificate.check = true :=
        certificate.expCertificate.check_eq_true_iff.mpr hexpValid
      have hexpSound := certificate.expCertificate.sound hexpCheck
      have hexpArgumentReal :
          (certificate.expCertificate.argument : ℝ) =
            -(certificate.argument : ℝ) := by
        exact_mod_cast hexpArgument
      rw [hexpArgumentReal] at hexpSound
      have hcandidates := exact_output_mem_candidates certificate.operation
        hexpLowerPositive hexpSound.1 hexpSound.2 (by simp [hop])
      have houtLowerReal :
          (certificate.outputLower : ℝ) ≤
            (activationLowerRat certificate.operation certificate.argument
              certificate.expCertificate.lower
              certificate.expCertificate.upper : ℝ) := by
        rw [hop]
        exact_mod_cast houtLower
      have houtUpperReal :
          (activationUpperRat certificate.operation certificate.argument
              certificate.expCertificate.lower
              certificate.expCertificate.upper : ℝ) ≤
            (certificate.outputUpper : ℝ) := by
        rw [hop]
        exact_mod_cast houtUpper
      have hruntimeLowerReal :
          (certificate.runtimeValue : ℝ) - certificate.localError ≤
            certificate.outputLower := by
        exact_mod_cast hruntimeLower
      have hruntimeUpperReal :
          (certificate.outputUpper : ℝ) ≤
            certificate.runtimeValue + certificate.localError := by
        exact_mod_cast hruntimeUpper
      have hlow :
          (certificate.runtimeValue : ℝ) - certificate.localError ≤
            certificate.operation.realMap (certificate.argument : ℝ) :=
        hruntimeLowerReal.trans <| houtLowerReal.trans hcandidates.1
      have hhigh :
          certificate.operation.realMap (certificate.argument : ℝ) ≤
            (certificate.runtimeValue : ℝ) + certificate.localError :=
        hcandidates.2.trans <| houtUpperReal.trans hruntimeUpperReal
      have hresult :
          |(certificate.runtimeValue : ℝ) -
              certificate.operation.realMap (certificate.argument : ℝ)| ≤
            (certificate.localError : ℝ) := by
        rw [abs_sub_le_iff]
        constructor <;> linarith
      simpa only [hop] using hresult

/-! ## Positive and negative fixtures -/

def sigmoidHalf : ActivationEnclosure where
  operation := .sigmoid
  argument := 1 / 2
  runtimeValue := 5 / 8
  localError := 1 / 100
  outputLower := 64 / 103
  outputUpper := 48 / 77
  expCertificate := expNegHalf

theorem sigmoidHalf_is_accepted : sigmoidHalf.check = true := by
  norm_num [sigmoidHalf, ActivationEnclosure.check, expNegHalf,
    ExpEnclosure.check, ExpEnclosure.Valid, expTaylorRat, expTaylorErrorRat,
    activationLowerRat, activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial]

theorem sigmoidHalf_sound :
    |(5 / 8 : ℝ) - Real.sigmoid (1 / 2)| ≤ (1 / 100 : ℝ) := by
  simpa [sigmoidHalf, RegisteredUnaryOp.realMap] using
    sigmoidHalf.sound sigmoidHalf_is_accepted

def siluHalf : ActivationEnclosure where
  operation := .silu
  argument := 1 / 2
  runtimeValue := 5 / 16
  localError := 1 / 100
  outputLower := 32 / 103
  outputUpper := 24 / 77
  expCertificate := expNegHalf

theorem siluHalf_is_accepted : siluHalf.check = true := by
  norm_num [siluHalf, ActivationEnclosure.check, expNegHalf,
    ExpEnclosure.check, ExpEnclosure.Valid, expTaylorRat, expTaylorErrorRat,
    activationLowerRat, activationUpperRat, sigmoidLowerRat, sigmoidUpperRat,
    Finset.sum_range_succ, Nat.factorial]

theorem siluHalf_sound :
    |(5 / 16 : ℝ) - sourceSiLU (1 / 2)| ≤ (1 / 100 : ℝ) := by
  simpa [siluHalf, RegisteredUnaryOp.realMap] using
    siluHalf.sound siluHalf_is_accepted

def tooTightSigmoidHalf : ActivationEnclosure :=
  { sigmoidHalf with localError := 1 / 1000 }

theorem tooTightSigmoidHalf_is_rejected :
    tooTightSigmoidHalf.check = false := by
  norm_num [tooTightSigmoidHalf, sigmoidHalf, ActivationEnclosure.check,
    expNegHalf, ExpEnclosure.check, ExpEnclosure.Valid, expTaylorRat,
    expTaylorErrorRat, activationLowerRat, activationUpperRat,
    sigmoidLowerRat, sigmoidUpperRat, Finset.sum_range_succ, Nat.factorial]

def mismatchedExpArgument : ActivationEnclosure :=
  { sigmoidHalf with
    expCertificate := { expNegHalf with argument := 0, lower := 1, upper := 1 } }

theorem mismatchedExpArgument_is_rejected :
    mismatchedExpArgument.check = false := by
  norm_num [mismatchedExpArgument, sigmoidHalf, ActivationEnclosure.check]

#print axioms ActivationEnclosure.sound
#print axioms sigmoidHalf_sound
#print axioms siluHalf_sound
#print axioms tooTightSigmoidHalf_is_rejected
#print axioms mismatchedExpArgument_is_rejected

end

end RationalActivationEnclosureCertificate

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
