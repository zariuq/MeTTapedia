import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CertifiedElementaryApproximation

/-!
# Symbolic Taylor round-off certificates

This file reconstructs the load-bearing error reduction in Solovyev et al.,
*Rigorous Estimation of Floating-Point Round-off Errors with Symbolic Taylor
Expansions* (2018).

Equations (8)--(10) replace a discontinuous floating-point optimization by a
first-order symbolic sensitivity expression plus a rigorously bounded
remainder.  `symbolicTaylor_pointwise_roundoff_le` proves the reduction for an
arbitrary finite family of error coordinates.  An executable rational
certificate then checks the global sensitivity, remainder, and total budgets.

Equation (11) permits separately maximizing each absolute sensitivity.  The
general theorem below proves that decomposition sound, while a two-point
fixture shows it can be strictly twice the correlation-preserving bound.
Another negative fixture proves that the Taylor remainder may not be dropped.

This module does not authenticate an IEEE-754 operation, derive a symbolic
Taylor form from a source expression, certify a global optimizer, or replay a
runtime floating-point trace.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SymbolicTaylorRoundoff

noncomputable section

open scoped BigOperators
open Finset

/-! ## The symbolic first-order error reduction -/

/-- A finite linear error form is bounded by the common error radius times
the `L1` norm of its symbolic sensitivities. -/
theorem abs_linear_error_le
    {ι : Type*} [Fintype ι]
    (epsilon : ℝ)
    (sensitivity noise : ι → ℝ)
    (noise_bounded : ∀ i, |noise i| ≤ epsilon) :
    |∑ i, sensitivity i * noise i| ≤
      epsilon * ∑ i, |sensitivity i| := by
  calc
    |∑ i, sensitivity i * noise i| ≤
        ∑ i, |sensitivity i * noise i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |sensitivity i| * |noise i| := by
      congr 1
      funext i
      exact abs_mul (sensitivity i) (noise i)
    _ ≤ ∑ i, |sensitivity i| * epsilon := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (noise_bounded i) (abs_nonneg _)
    _ = epsilon * ∑ i, |sensitivity i| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- FPTaylor Equations (8)--(10), pointwise and with the second-order
remainder retained explicitly. -/
theorem symbolicTaylor_pointwise_roundoff_le
    {ι : Type*} [Fintype ι]
    (epsilon sensitivityBudget remainderBudget : ℝ)
    (exact approximate remainder : ℝ)
    (sensitivity noise : ι → ℝ)
    (epsilon_nonnegative : 0 ≤ epsilon)
    (noise_bounded : ∀ i, |noise i| ≤ epsilon)
    (sensitivity_bounded :
      ∑ i, |sensitivity i| ≤ sensitivityBudget)
    (remainder_bounded : |remainder| ≤ remainderBudget)
    (expansion :
      approximate =
        exact + (∑ i, sensitivity i * noise i) + remainder) :
    |approximate - exact| ≤
      remainderBudget + epsilon * sensitivityBudget := by
  have linearBound :
      |∑ i, sensitivity i * noise i| ≤
        epsilon * sensitivityBudget := by
    calc
      |∑ i, sensitivity i * noise i| ≤
          epsilon * ∑ i, |sensitivity i| :=
        abs_linear_error_le
          epsilon sensitivity noise noise_bounded
      _ ≤ epsilon * sensitivityBudget :=
        mul_le_mul_of_nonneg_left sensitivity_bounded epsilon_nonnegative
  calc
    |approximate - exact| =
        |(∑ i, sensitivity i * noise i) + remainder| := by
      rw [expansion]
      ring_nf
    _ ≤ |∑ i, sensitivity i * noise i| + |remainder| :=
      abs_add_le _ _
    _ ≤ epsilon * sensitivityBudget + remainderBudget :=
      add_le_add linearBound remainder_bounded
    _ = remainderBudget + epsilon * sensitivityBudget := by ring

/-- Uniform form of the symbolic Taylor reduction over an arbitrary domain. -/
theorem symbolicTaylor_uniform_roundoff_le
    {Input ι : Type*} [Fintype ι]
    (domain : Set Input)
    (epsilon sensitivityBudget remainderBudget : ℝ)
    (exact approximate remainder : Input → ℝ)
    (sensitivity noise : Input → ι → ℝ)
    (epsilon_nonnegative : 0 ≤ epsilon)
    (noise_bounded :
      ∀ input ∈ domain, ∀ i, |noise input i| ≤ epsilon)
    (sensitivity_bounded :
      ∀ input ∈ domain,
        ∑ i, |sensitivity input i| ≤ sensitivityBudget)
    (remainder_bounded :
      ∀ input ∈ domain, |remainder input| ≤ remainderBudget)
    (expansion :
      ∀ input ∈ domain,
        approximate input =
          exact input +
            (∑ i, sensitivity input i * noise input i) +
            remainder input) :
    ∀ input ∈ domain,
      |approximate input - exact input| ≤
        remainderBudget + epsilon * sensitivityBudget := by
  intro input inputInDomain
  exact symbolicTaylor_pointwise_roundoff_le
    epsilon sensitivityBudget remainderBudget
    (exact input) (approximate input) (remainder input)
    (sensitivity input) (noise input)
    epsilon_nonnegative
    (noise_bounded input inputInDomain)
    (sensitivity_bounded input inputInDomain)
    (remainder_bounded input inputInDomain)
    (expansion input inputInDomain)

/-! ## Executable global budget -/

/-- Rational certificate for the three quantities in FPTaylor Equation (10). -/
structure RoundoffBudgetCertificate where
  epsilon : ℚ
  sensitivityBudget : ℚ
  remainderBudget : ℚ
  totalBudget : ℚ
  deriving Repr

namespace RoundoffBudgetCertificate

/-- Propositional meaning of the executable global budget. -/
def Valid (certificate : RoundoffBudgetCertificate) : Prop :=
  0 ≤ certificate.epsilon ∧
    0 ≤ certificate.sensitivityBudget ∧
    0 ≤ certificate.remainderBudget ∧
    certificate.remainderBudget +
        certificate.epsilon * certificate.sensitivityBudget ≤
      certificate.totalBudget

instance instDecidableValid
    (certificate : RoundoffBudgetCertificate) :
    Decidable certificate.Valid := by
  unfold Valid
  infer_instance

/-- Kernel-reducible arithmetic checker for a proposed global budget. -/
def check (certificate : RoundoffBudgetCertificate) : Bool :=
  decide certificate.Valid

theorem check_eq_true_iff_valid
    (certificate : RoundoffBudgetCertificate) :
    certificate.check = true ↔ certificate.Valid := by
  simp [check]

/-- An accepted rational certificate transports authenticated Taylor-form
premises to a uniform real round-off bound. -/
theorem uniform_roundoff_of_check
    (certificate : RoundoffBudgetCertificate)
    {Input ι : Type*} [Fintype ι]
    (domain : Set Input)
    (exact approximate remainder : Input → ℝ)
    (sensitivity noise : Input → ι → ℝ)
    (checked : certificate.check = true)
    (noise_bounded :
      ∀ input ∈ domain, ∀ i,
        |noise input i| ≤ (certificate.epsilon : ℝ))
    (sensitivity_bounded :
      ∀ input ∈ domain,
        ∑ i, |sensitivity input i| ≤
          (certificate.sensitivityBudget : ℝ))
    (remainder_bounded :
      ∀ input ∈ domain,
        |remainder input| ≤ (certificate.remainderBudget : ℝ))
    (expansion :
      ∀ input ∈ domain,
        approximate input =
          exact input +
            (∑ i, sensitivity input i * noise input i) +
            remainder input) :
    ∀ input ∈ domain,
      |approximate input - exact input| ≤
        (certificate.totalBudget : ℝ) := by
  have valid := (certificate.check_eq_true_iff_valid).mp checked
  have epsilonNonnegative :
      0 ≤ (certificate.epsilon : ℝ) := by
    exact_mod_cast valid.1
  have totalBound :
      (certificate.remainderBudget : ℝ) +
          (certificate.epsilon : ℝ) *
            (certificate.sensitivityBudget : ℝ) ≤
        (certificate.totalBudget : ℝ) := by
    exact_mod_cast valid.2.2.2
  intro input inputInDomain
  calc
    |approximate input - exact input| ≤
        (certificate.remainderBudget : ℝ) +
          (certificate.epsilon : ℝ) *
            (certificate.sensitivityBudget : ℝ) :=
      symbolicTaylor_uniform_roundoff_le
        domain
        (certificate.epsilon : ℝ)
        (certificate.sensitivityBudget : ℝ)
        (certificate.remainderBudget : ℝ)
        exact approximate remainder sensitivity noise
        epsilonNonnegative
        noise_bounded sensitivity_bounded remainder_bounded expansion
        input inputInDomain
    _ ≤ (certificate.totalBudget : ℝ) := totalBound

end RoundoffBudgetCertificate

private def exactRoundoffBudget : RoundoffBudgetCertificate :=
  ⟨1 / 10, 2, 1 / 10, 3 / 10⟩

theorem exact_roundoff_budget_accepted :
    exactRoundoffBudget.check = true := by
  norm_num [RoundoffBudgetCertificate.check,
    RoundoffBudgetCertificate.Valid, exactRoundoffBudget]

/-- The checked budget can be consumed by a concrete nonzero linear error and
nonzero remainder that exactly attain the requested total. -/
theorem exact_roundoff_budget_concrete_sound :
    ∀ input ∈ Set.Icc (0 : ℝ) 1,
      |((input + 3 / 10) - input)| ≤ (3 / 10 : ℝ) := by
  have certified :=
    exactRoundoffBudget.uniform_roundoff_of_check
      (Set.Icc (0 : ℝ) 1)
      (fun input => input)
      (fun input => input + 3 / 10)
      (fun _ => 1 / 10)
      (fun _ (_ : Fin 1) => 2)
      (fun _ (_ : Fin 1) => 1 / 10)
      exact_roundoff_budget_accepted
      (by
        intro _ _ _
        norm_num [exactRoundoffBudget])
      (by
        intro _ _
        simp [exactRoundoffBudget])
      (by
        intro _ _
        norm_num [exactRoundoffBudget])
      (by
        intro _ _
        simp
        ring)
  simpa [exactRoundoffBudget] using certified

/-! ## Correlation-preserving and decomposed sensitivity bounds -/

/-- Separately bounding every sensitivity is sound, but may lose correlations
between sensitivities that cannot be simultaneously maximal. -/
theorem monolithic_sensitivity_le_decomposed
    {Input ι : Type*} [Fintype ι]
    (domain : Set Input)
    (sensitivity : Input → ι → ℝ)
    (coordinateBudget : ι → ℝ)
    (coordinate_bounded :
      ∀ input ∈ domain, ∀ i,
        |sensitivity input i| ≤ coordinateBudget i) :
    ∀ input ∈ domain,
      ∑ i, |sensitivity input i| ≤ ∑ i, coordinateBudget i := by
  intro input inputInDomain
  exact Finset.sum_le_sum fun i _ =>
    coordinate_bounded input inputInDomain i

private def alternatingSensitivity (input : Bool) (i : Fin 2) : ℝ :=
  if i = 0 then
    if input then 1 else 0
  else
    if input then 0 else 1

/-- FPTaylor Equation (11) can be strict: each coordinate separately attains
one, while the correlation-preserving sum is always one. -/
theorem decomposed_sensitivity_bound_is_strict :
    (∀ input : Bool,
      ∑ i : Fin 2, |alternatingSensitivity input i| = (1 : ℝ)) ∧
    (∀ input : Bool, ∀ i : Fin 2,
      |alternatingSensitivity input i| ≤ (1 : ℝ)) ∧
    (∑ _i : Fin 2, (1 : ℝ)) = 2 ∧
    (1 : ℝ) < 2 := by
  constructor
  · intro input
    cases input <;> norm_num [alternatingSensitivity, Fin.sum_univ_two]
  constructor
  · intro input i
    fin_cases i <;> cases input <;>
      norm_num [alternatingSensitivity]
  constructor
  · norm_num [Fin.sum_univ_two]
  · norm_num

/-- The second-order remainder in Equation (10) is load-bearing even when all
first-order sensitivities vanish. -/
theorem dropping_remainder_is_unsound :
    let exact : ℝ := 0
    let approximate : ℝ := 1
    let sensitivity : Fin 1 → ℝ := fun _ => 0
    let noise : Fin 1 → ℝ := fun _ => 0
    let remainder : ℝ := 1
    approximate =
        exact + (∑ i, sensitivity i * noise i) + remainder ∧
      ¬ |approximate - exact| ≤
        (0 : ℝ) * ∑ i, |sensitivity i| := by
  norm_num

#print axioms abs_linear_error_le
#print axioms symbolicTaylor_pointwise_roundoff_le
#print axioms symbolicTaylor_uniform_roundoff_le
#print axioms RoundoffBudgetCertificate.uniform_roundoff_of_check
#print axioms exact_roundoff_budget_concrete_sound
#print axioms monolithic_sensitivity_le_decomposed
#print axioms decomposed_sensitivity_bound_is_strict
#print axioms dropping_remainder_is_unsound

end

end SymbolicTaylorRoundoff

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
