import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.AmortizedInitialization

/-!
# Finite-horizon integral quadratic certificates

Lessard, Recht, and Packard, *Analysis and Design of Optimization Algorithms
via Integral Quadratic Constraints* (2016), use a weighted hard integral
quadratic constraint (IQC) to turn a one-step storage inequality into an
exponential convergence certificate.  The primary PDF has SHA-256
`ef4cb55f27a707fc67f1bd19e340ed2a6899da48877c5e8df8bc36f5986860bc`.

This file isolates and generalizes the telescoping core of source Theorem 4.
`discountedSupply rate supply horizon` is the chronological finite-horizon
accumulation with one factor of `rate = ρ²` per older sample.  A `RhoHardIQC`
requires every such prefix to be nonnegative.  Combining this with a one-step
storage-plus-supply inequality yields the exact geometric storage bound.

The result is deliberately trace-level.  It does not trust an external
semidefinite solver, infer a quadratic storage matrix, or infer that a neural
nonlinearity satisfies a sector constraint.  Those remain executable
obligations.  An explicit fixture also preserves a subtle source boundary:
the aggregate certificate can hold even though storage increases on an
intermediate step, so the storage need not be a pointwise Lyapunov function.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace IntegralQuadraticConstraint

noncomputable section

/-! ## Discounted hard supplies -/

/-- Chronological finite-horizon IQC supply. Older samples receive one
additional factor of `rate` at every subsequent step. -/
def discountedSupply (rate : ℝ) (supply : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | horizon + 1 =>
      rate * discountedSupply rate supply horizon + supply horizon

@[simp] theorem discountedSupply_zero
    (rate : ℝ) (supply : ℕ → ℝ) :
    discountedSupply rate supply 0 = 0 := rfl

@[simp] theorem discountedSupply_succ
    (rate : ℝ) (supply : ℕ → ℝ) (horizon : ℕ) :
    discountedSupply rate supply (horizon + 1) =
      rate * discountedSupply rate supply horizon + supply horizon := rfl

/-- Source ρ-hardness, expressed with `rate = ρ²`. -/
def RhoHardIQC (rate : ℝ) (supply : ℕ → ℝ) : Prop :=
  ∀ horizon, 0 ≤ discountedSupply rate supply horizon

/-- A pointwise IQC is stronger than a hard IQC whenever the discount is
nonnegative. -/
theorem rhoHard_of_pointwise
    {rate : ℝ} (rateNonnegative : 0 ≤ rate)
    {supply : ℕ → ℝ}
    (pointwise : ∀ step, 0 ≤ supply step) :
    RhoHardIQC rate supply := by
  intro horizon
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ]
      exact add_nonneg
        (mul_nonneg rateNonnegative inductionHypothesis)
        (pointwise horizon)

theorem discountedSupply_add
    (rate : ℝ) (left right : ℕ → ℝ) (horizon : ℕ) :
    discountedSupply rate (fun step => left step + right step) horizon =
      discountedSupply rate left horizon +
        discountedSupply rate right horizon := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, discountedSupply_succ,
        discountedSupply_succ, inductionHypothesis]
      ring

theorem discountedSupply_smul
    (rate weight : ℝ) (supply : ℕ → ℝ) (horizon : ℕ) :
    discountedSupply rate (fun step => weight * supply step) horizon =
      weight * discountedSupply rate supply horizon := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, discountedSupply_succ,
        inductionHypothesis]
      ring

theorem RhoHardIQC.add
    {rate : ℝ} {left right : ℕ → ℝ}
    (leftHard : RhoHardIQC rate left)
    (rightHard : RhoHardIQC rate right) :
    RhoHardIQC rate (fun step => left step + right step) := by
  intro horizon
  rw [discountedSupply_add]
  exact add_nonneg (leftHard horizon) (rightHard horizon)

theorem RhoHardIQC.nonnegative_smul
    {rate weight : ℝ} {supply : ℕ → ℝ}
    (weightNonnegative : 0 ≤ weight)
    (hard : RhoHardIQC rate supply) :
    RhoHardIQC rate (fun step => weight * supply step) := by
  intro horizon
  rw [discountedSupply_smul]
  exact mul_nonneg weightNonnegative (hard horizon)

theorem discountedSupply_finset_sum
    {Index : Type*} (indices : Finset Index)
    (rate : ℝ) (weight : Index → ℝ)
    (supply : Index → ℕ → ℝ) (horizon : ℕ) :
    discountedSupply rate
        (fun step =>
          ∑ index ∈ indices, weight index * supply index step)
        horizon =
      ∑ index ∈ indices,
        weight index * discountedSupply rate (supply index) horizon := by
  classical
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, inductionHypothesis]
      simp_rw [discountedSupply_succ]
      rw [Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      ring

/-- Source Equation (3.11), at the supply-trace level: any finite
nonnegative combination of ρ-hard IQCs is again ρ-hard. -/
theorem rhoHard_finset_sum
    {Index : Type*} {rate : ℝ}
    (indices : Finset Index)
    (weight : Index → ℝ)
    (supply : Index → ℕ → ℝ)
    (weightNonnegative : ∀ index ∈ indices, 0 ≤ weight index)
    (hard : ∀ index ∈ indices, RhoHardIQC rate (supply index)) :
    RhoHardIQC rate
      (fun step => ∑ index ∈ indices, weight index * supply index step) := by
  classical
  intro horizon
  rw [discountedSupply_finset_sum]
  exact Finset.sum_nonneg fun index indexMem =>
    mul_nonneg
      (weightNonnegative index indexMem)
      (hard index indexMem horizon)

/-! ## The source telescoping theorem -/

/-- One-step form obtained by evaluating the source LMI on the runtime trace. -/
def DissipatesWithSupply
    (rate multiplier : ℝ)
    (storage supply : ℕ → ℝ) : Prop :=
  ∀ step,
    storage (step + 1) - rate * storage step +
        multiplier * supply step ≤
      0

/-- Exact accumulated storage-plus-supply inequality underlying source
Theorem 4. -/
theorem accumulated_storage_supply_le
    {rate multiplier : ℝ}
    (rateNonnegative : 0 ≤ rate)
    {storage supply : ℕ → ℝ}
    (dissipates :
      DissipatesWithSupply rate multiplier storage supply)
    (horizon : ℕ) :
    storage horizon - rate ^ horizon * storage 0 +
        multiplier * discountedSupply rate supply horizon ≤
      0 := by
  induction horizon with
  | zero =>
      simp
  | succ horizon inductionHypothesis =>
      rw [discountedSupply_succ, pow_succ]
      calc
        storage (horizon + 1) -
              rate ^ horizon * rate * storage 0 +
              multiplier *
                (rate * discountedSupply rate supply horizon +
                  supply horizon) =
            (storage (horizon + 1) - rate * storage horizon +
                multiplier * supply horizon) +
              rate *
                (storage horizon - rate ^ horizon * storage 0 +
                  multiplier *
                    discountedSupply rate supply horizon) := by
              ring
        _ ≤ 0 :=
          add_nonpos (dissipates horizon)
            (mul_nonpos_of_nonneg_of_nonpos
              rateNonnegative inductionHypothesis)

/-- Source Theorem 4 at the trace level: a nonnegative multiplier times a
ρ-hard supply can be discarded from the accumulated inequality, leaving the
geometric storage rate. -/
theorem storage_le_geometric
    {rate multiplier : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (multiplierNonnegative : 0 ≤ multiplier)
    {storage supply : ℕ → ℝ}
    (hard : RhoHardIQC rate supply)
    (dissipates :
      DissipatesWithSupply rate multiplier storage supply)
    (horizon : ℕ) :
    storage horizon ≤ rate ^ horizon * storage 0 := by
  have accumulated :=
    accumulated_storage_supply_le rateNonnegative dissipates horizon
  have weightedSupplyNonnegative :
      0 ≤ multiplier * discountedSupply rate supply horizon :=
    mul_nonneg multiplierNonnegative (hard horizon)
  linarith

/-- Transport the storage rate through supplied quadratic lower and upper
bounds. This is the squared-norm form of the source condition-number bound. -/
theorem state_squaredNorm_rate
    {State : Type*} [NormedAddCommGroup State]
    {rate multiplier lower upper : ℝ}
    (rateNonnegative : 0 ≤ rate)
    (multiplierNonnegative : 0 ≤ multiplier)
    (lowerPositive : 0 < lower)
    {state : ℕ → State}
    {storage supply : ℕ → ℝ}
    (hard : RhoHardIQC rate supply)
    (dissipates :
      DissipatesWithSupply rate multiplier storage supply)
    (storageLower :
      ∀ horizon, lower * ‖state horizon‖ ^ 2 ≤ storage horizon)
    (storageInitialUpper :
      storage 0 ≤ upper * ‖state 0‖ ^ 2)
    (horizon : ℕ) :
    ‖state horizon‖ ^ 2 ≤
      (rate ^ horizon * (upper * ‖state 0‖ ^ 2)) / lower := by
  rw [le_div_iff₀ lowerPositive]
  rw [mul_comm (‖state horizon‖ ^ 2) lower]
  calc
    lower * ‖state horizon‖ ^ 2 ≤ storage horizon :=
      storageLower horizon
    _ ≤ rate ^ horizon * storage 0 :=
      storage_le_geometric rateNonnegative multiplierNonnegative
        hard dissipates horizon
    _ ≤ rate ^ horizon * (upper * ‖state 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left storageInitialUpper
        (pow_nonneg rateNonnegative horizon)

/-! ## Boundaries: hard is not pointwise, and storage need not decrease -/

def delayedCreditSupply : ℕ → ℝ
  | 0 => 2
  | 1 => -1
  | _ + 2 => 0

theorem delayedCreditSupply_discounted_after_two (tail : ℕ) :
    discountedSupply (1 / 2) delayedCreditSupply (tail + 2) = 0 := by
  induction tail with
  | zero =>
      norm_num [discountedSupply, delayedCreditSupply]
  | succ tail inductionHypothesis =>
      rw [show tail + 1 + 2 = (tail + 2) + 1 by omega,
        discountedSupply_succ, inductionHypothesis]
      simp [delayedCreditSupply]

/-- A hard IQC may contain a negative individual supply after earlier
positive credit has accumulated. -/
theorem delayedCreditSupply_is_hard_not_pointwise :
    RhoHardIQC (1 / 2) delayedCreditSupply ∧
      delayedCreditSupply 1 < 0 := by
  constructor
  · intro horizon
    cases horizon with
    | zero =>
        simp
    | succ horizon =>
        cases horizon with
        | zero =>
            norm_num [discountedSupply, delayedCreditSupply]
        | succ tail =>
            rw [show tail + 1 + 1 = tail + 2 by omega,
              delayedCreditSupply_discounted_after_two]
  · norm_num [delayedCreditSupply]

def nonLyapunovStorage : ℕ → ℝ
  | 0 => 8
  | 1 => 1
  | tail + 2 => (3 / 2) * (1 / 2) ^ tail

theorem nonLyapunovStorage_dissipates :
    DissipatesWithSupply (1 / 2) 1
      nonLyapunovStorage delayedCreditSupply := by
  intro step
  cases step with
  | zero =>
      norm_num [nonLyapunovStorage, delayedCreditSupply]
  | succ step =>
      cases step with
      | zero =>
          norm_num [nonLyapunovStorage, delayedCreditSupply]
      | succ tail =>
          simp only [nonLyapunovStorage, delayedCreditSupply]
          rw [pow_succ]
          ring_nf
          norm_num

/-- The source warning is genuine: an aggregate IQC certificate can permit
an intermediate storage increase even though the exact global geometric rate
holds at every horizon. -/
theorem hard_iqc_rate_without_pointwise_lyapunov :
    nonLyapunovStorage 1 < nonLyapunovStorage 2 ∧
      ∀ horizon,
        nonLyapunovStorage horizon ≤
          (1 / 2) ^ horizon * nonLyapunovStorage 0 := by
  constructor
  · norm_num [nonLyapunovStorage]
  · exact
      storage_le_geometric (by norm_num) (by norm_num)
        delayedCreditSupply_is_hard_not_pointwise.1
        nonLyapunovStorage_dissipates

end

end IntegralQuadraticConstraint

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint.rhoHard_finset_sum
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint.accumulated_storage_supply_le
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint.storage_le_geometric
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint.state_squaredNorm_rate
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint.delayedCreditSupply_is_hard_not_pointwise
#print axioms Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.IntegralQuadraticConstraint.hard_iqc_rate_without_pointwise_lyapunov
