import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedCorrectRounding

/-!
# Certified elementary-function approximation

This file reconstructs two reusable correctness layers from Becker et al.,
*Dandelion: Certified Approximations of Elementary Functions* (2022).

Theorem 9 composes a certified elementary-to-Taylor approximation error with
the residual polynomial error.  `ApproximationBudgetCertificate` makes that
budget split finite and executable.  Its soundness theorem is uniform over an
arbitrary domain and arbitrary real functions.

Theorem 8 bounds a differentiable error function on a compact interval from
its endpoint values and validated confidence intervals covering every
critical point.  `critical_interval_envelope` formalizes a strengthened,
function-generic version: a derivative bound transports the sampled value at
the lower endpoint of each confidence interval to its enclosed critical
point.  Compact extrema then control every point in the domain.

Negative fixtures reject an under-sized composed budget and show that
endpoint values alone cannot bound an interior extremum.  This module does not
certify a Taylor-series generator, Sturm sequence, root oracle, or runtime
elementary-function implementation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CertifiedElementaryApproximation

noncomputable section

open Set

/-! ## Executable composition of Dandelion's two phases -/

/-- Rational split between elementary/Taylor error, residual polynomial error,
and the requested total error. -/
structure ApproximationBudgetCertificate where
  elementaryError : ℚ
  residualError : ℚ
  totalError : ℚ
  deriving Repr

namespace ApproximationBudgetCertificate

/-- Propositional meaning of a valid two-phase error budget. -/
def Valid (certificate : ApproximationBudgetCertificate) : Prop :=
  0 ≤ certificate.elementaryError ∧
    0 ≤ certificate.residualError ∧
    certificate.elementaryError + certificate.residualError ≤
      certificate.totalError

instance instDecidableValid
    (certificate : ApproximationBudgetCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

/-- Executable checker for the rational error split. -/
def check (certificate : ApproximationBudgetCertificate) : Bool :=
  decide certificate.Valid

theorem check_eq_true_iff_valid
    (certificate : ApproximationBudgetCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- Dandelion's two sound phases compose to the checked total error by the
triangle inequality. -/
theorem uniform_error_of_check
    (certificate : ApproximationBudgetCertificate)
    {Input : Type*}
    (domain : Set Input)
    (elementary taylor candidate : Input → Real)
    (checked : certificate.check = true)
    (elementaryBound :
      ∀ input ∈ domain,
        |elementary input - taylor input| ≤
          (certificate.elementaryError : Real))
    (residualBound :
      ∀ input ∈ domain,
        |taylor input - candidate input| ≤
          (certificate.residualError : Real)) :
    ∀ input ∈ domain,
      |elementary input - candidate input| ≤
        (certificate.totalError : Real) := by
  have valid := (certificate.check_eq_true_iff_valid).mp checked
  have totalBudget :
      (certificate.elementaryError : Real) +
          (certificate.residualError : Real) ≤
        (certificate.totalError : Real) := by
    exact_mod_cast valid.2.2
  intro input inputInDomain
  calc
    |elementary input - candidate input| =
        |(elementary input - taylor input) +
          (taylor input - candidate input)| := by ring_nf
    _ ≤ |elementary input - taylor input| +
          |taylor input - candidate input| := abs_add_le _ _
    _ ≤ (certificate.elementaryError : Real) +
          (certificate.residualError : Real) :=
      add_le_add
        (elementaryBound input inputInDomain)
        (residualBound input inputInDomain)
    _ ≤ (certificate.totalError : Real) := totalBudget

end ApproximationBudgetCertificate

private def exactBudget : ApproximationBudgetCertificate :=
  ⟨1 / 100, 2 / 100, 3 / 100⟩

/-- A budget whose two phase errors exactly attain the requested total is
accepted. -/
theorem exact_budget_accepted : exactBudget.check = true := by
  norm_num [ApproximationBudgetCertificate.check,
    ApproximationBudgetCertificate.Valid, exactBudget]

/-- The executable budget produces a concrete uniform theorem. -/
theorem exact_budget_concrete_sound :
    ∀ x ∈ Set.Icc (0 : Real) 1,
      |(x + 3 / 100) - x| ≤ (3 / 100 : Real) := by
  have composed :=
    exactBudget.uniform_error_of_check
      (Set.Icc (0 : Real) 1)
      (fun x => x + 3 / 100)
      (fun x => x + 2 / 100)
      (fun x => x)
      exact_budget_accepted
      (by
        intro
        norm_num [exactBudget])
      (by
        intro
        norm_num [exactBudget])
  simpa [exactBudget] using composed

private def undersizedBudget : ApproximationBudgetCertificate :=
  ⟨1, 1, 1⟩

/-- A requested total smaller than the sum of the two certified phases is
rejected. -/
theorem undersized_budget_rejected :
    undersizedBudget.check = false := by
  norm_num [ApproximationBudgetCertificate.check,
    ApproximationBudgetCertificate.Valid, undersizedBudget]

/-- The rejected budget is not conservative: both local errors can be one
while the total error is two. -/
theorem undersized_budget_has_concrete_failure :
    let elementary : Real := 2
    let taylor : Real := 1
    let candidate : Real := 0
    |elementary - taylor| ≤ 1 ∧
      |taylor - candidate| ≤ 1 ∧
      ¬ |elementary - candidate| ≤ 1 := by
  norm_num

/-! ## Critical-point confidence intervals -/

/-- A validated interval intended to contain a critical point. -/
structure CriticalInterval where
  lower : Real
  upper : Real

/-- The interval-local obligations used to turn a critical-point confidence
interval into a value bound. -/
def CriticalInterval.Valid
    (f : Real → Real)
    (a b derivativeBound sampleBound widthBound : Real)
    (interval : CriticalInterval) : Prop :=
  a ≤ interval.lower ∧
    interval.lower ≤ interval.upper ∧
    interval.upper ≤ b ∧
    interval.upper - interval.lower ≤ widthBound ∧
    |f interval.lower| ≤ sampleBound ∧
    0 ≤ derivativeBound ∧
    0 ≤ widthBound

/-- A derivative bound on the compact domain gives the point-pair error
transport used inside every validated critical interval. -/
theorem value_transport_of_derivative_bound
    (f : Real → Real)
    {a b derivativeBound : Real}
    (differentiable :
      ∀ x ∈ Set.Icc a b, DifferentiableAt Real f x)
    (derivativeBounded :
      ∀ x ∈ Set.Icc a b, ‖deriv f x‖ ≤ derivativeBound)
    {x y : Real}
    (xIn : x ∈ Set.Icc a b)
    (yIn : y ∈ Set.Icc a b) :
    ‖f y - f x‖ ≤ derivativeBound * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le
    differentiable derivativeBounded (convex_Icc a b) xIn yIn

/-- A point enclosed by a valid confidence interval is bounded by the sampled
value plus derivative-bound times interval width. -/
theorem critical_value_le_sample_add_width
    (f : Real → Real)
    {a b derivativeBound sampleBound widthBound : Real}
    (differentiable :
      ∀ x ∈ Set.Icc a b, DifferentiableAt Real f x)
    (derivativeBounded :
      ∀ x ∈ Set.Icc a b, ‖deriv f x‖ ≤ derivativeBound)
    (interval : CriticalInterval)
    (valid :
      interval.Valid f a b derivativeBound sampleBound widthBound)
    {critical : Real}
    (criticalIn : critical ∈ Set.Icc a b)
    (enclosed :
      interval.lower ≤ critical ∧ critical ≤ interval.upper) :
    |f critical| ≤ sampleBound + derivativeBound * widthBound := by
  have lowerIn : interval.lower ∈ Set.Icc a b :=
    ⟨valid.1, valid.2.1.trans valid.2.2.1⟩
  have pairBound :=
    value_transport_of_derivative_bound f differentiable
      derivativeBounded lowerIn criticalIn
  have distanceNonnegative : 0 ≤ critical - interval.lower := sub_nonneg.mpr enclosed.1
  have distanceLeWidth :
      critical - interval.lower ≤ widthBound := by
    calc
      critical - interval.lower ≤
          interval.upper - interval.lower := sub_le_sub_right enclosed.2 _
      _ ≤ widthBound := valid.2.2.2.1
  have normDistance :
      ‖critical - interval.lower‖ ≤ widthBound := by
    simpa [Real.norm_eq_abs, abs_of_nonneg distanceNonnegative] using
      distanceLeWidth
  have transported :
      ‖f critical - f interval.lower‖ ≤
        derivativeBound * widthBound := by
    exact pairBound.trans
      (mul_le_mul_of_nonneg_left normDistance valid.2.2.2.2.2.1)
  calc
    |f critical| =
        |f interval.lower +
          (f critical - f interval.lower)| := by ring_nf
    _ ≤ |f interval.lower| +
          |f critical - f interval.lower| := abs_add_le _ _
    _ ≤ sampleBound + derivativeBound * widthBound := by
      simpa [Real.norm_eq_abs] using
        add_le_add valid.2.2.2.2.1 transported

/-- A point attaining a maximum or minimum on `[a,b]` is either an endpoint
or a critical point. -/
theorem extremizer_endpoint_or_critical
    (f : Real → Real)
    {a b point : Real}
    (pointIn : point ∈ Set.Icc a b)
    (extremum :
      IsMaxOn f (Set.Icc a b) point ∨
        IsMinOn f (Set.Icc a b) point) :
    point = a ∨ point = b ∨ deriv f point = 0 := by
  by_cases pointEqA : point = a
  · exact Or.inl pointEqA
  by_cases pointEqB : point = b
  · exact Or.inr (Or.inl pointEqB)
  have aLtPoint : a < point := lt_of_le_of_ne pointIn.1 (Ne.symm pointEqA)
  have pointLtB : point < b := lt_of_le_of_ne pointIn.2 pointEqB
  apply Or.inr
  apply Or.inr
  rcases extremum with maximum | minimum
  · exact (maximum.isLocalMax (Icc_mem_nhds aLtPoint pointLtB)).deriv_eq_zero
  · exact (minimum.isLocalMin (Icc_mem_nhds aLtPoint pointLtB)).deriv_eq_zero

/-- Dandelion-style compact error envelope from endpoints and confidence
intervals that cover every critical point. -/
theorem critical_interval_envelope
    (f : Real → Real)
    {a b derivativeBound sampleBound widthBound : Real}
    (aLeB : a ≤ b)
    (differentiable :
      ∀ x ∈ Set.Icc a b, DifferentiableAt Real f x)
    (derivativeBounded :
      ∀ x ∈ Set.Icc a b, ‖deriv f x‖ ≤ derivativeBound)
    (intervals : List CriticalInterval)
    (intervalsValid :
      ∀ interval ∈ intervals,
        interval.Valid f a b derivativeBound sampleBound widthBound)
    (criticalCoverage :
      ∀ critical ∈ Set.Icc a b,
        deriv f critical = 0 →
          ∃ interval ∈ intervals,
            interval.lower ≤ critical ∧ critical ≤ interval.upper) :
    ∀ x ∈ Set.Icc a b,
      |f x| ≤
        max (max |f a| |f b|)
          (sampleBound + derivativeBound * widthBound) := by
  have domainNonempty : (Set.Icc a b).Nonempty := ⟨a, le_rfl, aLeB⟩
  have continuous : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (differentiable x hx).continuousAt.continuousWithinAt
  obtain ⟨minimum, minimumIn, minimumIs⟩ :=
    isCompact_Icc.exists_isMinOn domainNonempty continuous
  obtain ⟨maximum, maximumIn, maximumIs⟩ :=
    isCompact_Icc.exists_isMaxOn domainNonempty continuous
  have extremumBound :
      ∀ point ∈ Set.Icc a b,
        (IsMaxOn f (Set.Icc a b) point ∨
          IsMinOn f (Set.Icc a b) point) →
        |f point| ≤
          max (max |f a| |f b|)
            (sampleBound + derivativeBound * widthBound) := by
    intro point pointIn extremum
    rcases extremizer_endpoint_or_critical f pointIn extremum with
      pointEqA | pointEqB | critical
    · subst point
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    · subst point
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    · obtain ⟨interval, intervalIn, enclosed⟩ :=
        criticalCoverage point pointIn critical
      exact le_trans
        (critical_value_le_sample_add_width f differentiable
          derivativeBounded interval (intervalsValid interval intervalIn)
          pointIn enclosed)
        (le_max_right _ _)
  intro x xIn
  have minimumLe : f minimum ≤ f x := minimumIs xIn
  have leMaximum : f x ≤ f maximum := maximumIs xIn
  calc
    |f x| ≤ max |f minimum| |f maximum| :=
      abs_le_max_abs_abs minimumLe leMaximum
    _ ≤ max (max |f a| |f b|)
        (sampleBound + derivativeBound * widthBound) :=
      max_le
        (extremumBound minimum minimumIn (Or.inr minimumIs))
        (extremumBound maximum maximumIn (Or.inl maximumIs))

/-! ## Endpoint-only boundary -/

/-- Zero endpoint values do not control an interior extremum. -/
theorem endpoint_values_alone_do_not_bound_interior :
    let f : Real → Real := fun x => 1 - x ^ 2
    f (-1) = 0 ∧ f 1 = 0 ∧ |f 0| = 1 := by
  norm_num

#print axioms ApproximationBudgetCertificate.uniform_error_of_check
#print axioms undersized_budget_has_concrete_failure
#print axioms value_transport_of_derivative_bound
#print axioms critical_value_le_sample_add_width
#print axioms critical_interval_envelope
#print axioms endpoint_values_alone_do_not_bound_interior

end

end CertifiedElementaryApproximation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
