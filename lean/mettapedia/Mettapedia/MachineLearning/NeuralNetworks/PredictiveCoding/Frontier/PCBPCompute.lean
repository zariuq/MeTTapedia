import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.DepthScalingVector

/-!
# Equal-compute predictive-coding versus backpropagation comparisons

This file makes the phrase "PC beats BP at equal compute" a precise
proposition.  The cost model separates work shared by both methods, work per
settling sweep, the PC weight update, one BP backward pass, and the BP weight
update.  Cost equalities and finite-speed lower bounds are exact.  Which
method attains lower nonlinear test risk at that budget remains an empirical
measurement and is represented as such rather than assumed.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-- Explicit work accounting for one PC or BP training batch.  All fields use
one declared, common work unit. -/
structure PCBPComputeModel where
  sharedForwardWork : ℕ
  pcSweepWork : ℕ
  pcWeightUpdateWork : ℕ
  backwardPassWork : ℕ
  bpWeightUpdateWork : ℕ
  deriving DecidableEq, Repr

/-- Total PC work for a declared number of settling sweeps. -/
def pcTrainingWork (model : PCBPComputeModel) (sweeps : ℕ) : ℕ :=
  model.sharedForwardWork + sweeps * model.pcSweepWork +
    model.pcWeightUpdateWork

/-- Total BP work for one forward pass, one backward pass, and one update. -/
def bpTrainingWork (model : PCBPComputeModel) : ℕ :=
  model.sharedForwardWork + model.backwardPassWork + model.bpWeightUpdateWork

/-- Exact equality of the declared work budgets. -/
def PCBPAtEqualCompute (model : PCBPComputeModel) (sweeps : ℕ) : Prop :=
  pcTrainingWork model sweeps = bpTrainingWork model

/-- Lower risk is better.  This proposition states both the cost equality and
the measured strict performance comparison; it does not infer performance
from compute alone. -/
def PCBeatsBPAtEqualCompute (model : PCBPComputeModel) (sweeps : ℕ)
    (pcRisk bpRisk : ℝ) : Prop :=
  PCBPAtEqualCompute model sweeps ∧ pcRisk < bpRisk

/-- Shared forward work cancels exactly from an equal-compute comparison. -/
theorem pcBPAtEqualCompute_iff_privateWork_eq
    (model : PCBPComputeModel) (sweeps : ℕ) :
    PCBPAtEqualCompute model sweeps ↔
      sweeps * model.pcSweepWork + model.pcWeightUpdateWork =
        model.backwardPassWork + model.bpWeightUpdateWork := by
  unfold PCBPAtEqualCompute pcTrainingWork bpTrainingWork
  constructor <;> intro h <;> omega

/-- With matched update costs, exact compute equality is precisely equality
between all settling-sweep work and one backward pass. -/
theorem pcBPAtEqualCompute_iff_sweepWork_eq_backward
    (model : PCBPComputeModel)
    (hupdate : model.pcWeightUpdateWork = model.bpWeightUpdateWork)
    (sweeps : ℕ) :
    PCBPAtEqualCompute model sweeps ↔
      sweeps * model.pcSweepWork = model.backwardPassWork := by
  rw [pcBPAtEqualCompute_iff_privateWork_eq]
  omega

/-- If PC's update alone costs more than BP's entire method-specific work,
no number of settling sweeps can achieve exact compute equality. -/
theorem no_equalCompute_of_pcUpdate_gt_bpPrivateWork
    (model : PCBPComputeModel)
    (hexpensive : model.backwardPassWork + model.bpWeightUpdateWork <
      model.pcWeightUpdateWork) :
    ¬ ∃ sweeps, PCBPAtEqualCompute model sweeps := by
  rintro ⟨sweeps, hequal⟩
  rw [pcBPAtEqualCompute_iff_privateWork_eq] at hequal
  omega

/-- Positive exact-cost fixture: three sweeps of work two equal one backward
pass of work six when update costs match. -/
def equalComputeFixture : PCBPComputeModel where
  sharedForwardWork := 5
  pcSweepWork := 2
  pcWeightUpdateWork := 1
  backwardPassWork := 6
  bpWeightUpdateWork := 1

theorem equalComputeFixture_exact :
    PCBPAtEqualCompute equalComputeFixture 3 := by
  norm_num [PCBPAtEqualCompute, pcTrainingWork, bpTrainingWork,
    equalComputeFixture]

/-- Positive outcome fixture: a declared lower PC risk makes the full
equal-compute proposition true. -/
theorem pcBeatsBPAtEqualCompute_positiveFixture :
    PCBeatsBPAtEqualCompute equalComputeFixture 3 1 2 := by
  norm_num [PCBeatsBPAtEqualCompute, equalComputeFixture,
    PCBPAtEqualCompute, pcTrainingWork, bpTrainingWork]

/-- Negative outcome fixture: exact cost equality alone does not imply a PC
advantage. -/
theorem equalCompute_does_not_imply_pcBeats :
    PCBPAtEqualCompute equalComputeFixture 3 ∧
      ¬ PCBeatsBPAtEqualCompute equalComputeFixture 3 2 1 := by
  norm_num [PCBeatsBPAtEqualCompute, equalComputeFixture,
    PCBPAtEqualCompute, pcTrainingWork, bpTrainingWork]

/-- A zero-cost sweep is a substantive degeneracy: if method-specific fixed
costs match, every sweep count is equal-compute.  Thus meaningful calibration
must record positive per-sweep work. -/
theorem zeroSweepWork_equalCompute_all_sweeps
    (shared update : ℕ) :
    let model : PCBPComputeModel :=
      { sharedForwardWork := shared
        pcSweepWork := 0
        pcWeightUpdateWork := update
        backwardPassWork := 0
        bpWeightUpdateWork := update }
    ∀ sweeps, PCBPAtEqualCompute model sweeps := by
  intro model sweeps
  simp [PCBPAtEqualCompute, pcTrainingWork, bpTrainingWork, model]

/-! ## Finite-speed work lower bounds -/

/-- Any PC run using at least `requiredSweeps` incurs at least the
corresponding sweep work. -/
theorem pcTrainingWork_mono_of_requiredSweeps
    (model : PCBPComputeModel) (requiredSweeps sweeps : ℕ)
    (hrequired : requiredSweeps ≤ sweeps) :
    pcTrainingWork model requiredSweeps ≤ pcTrainingWork model sweeps := by
  unfold pcTrainingWork
  exact Nat.add_le_add_right
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right model.pcSweepWork hrequired)
      model.sharedForwardWork)
    model.pcWeightUpdateWork

/-- Vector finite-speed plus the cost model: exact transmission through a
residual main path forces at least the work of `skipped + 1` sweeps.  The
update map remains arbitrary and may be nonlinear. -/
theorem exactVectorPC_trainingWork_lowerBound
    (model : PCBPComputeModel) (width skipped sweeps : ℕ)
    (step : ChainState (Fin width → ℝ) (skipped + 1) →
      ChainState (Fin width → ℝ) (skipped + 1))
    (hbandwidth : HasChainBandwidth step 1)
    (initial₀ initial₁ target₀ target₁ :
      ChainState (Fin width → ℝ) (skipped + 1))
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node)
    (htarget : target₀ (chainTerminalNode (skipped + 1)) ≠
      target₁ (chainTerminalNode (skipped + 1)))
    (hsettle₀ : Nat.iterate step sweeps initial₀ = target₀)
    (hsettle₁ : Nat.iterate step sweeps initial₁ = target₁) :
    pcTrainingWork model (skipped + 1) ≤ pcTrainingWork model sweeps := by
  apply pcTrainingWork_mono_of_requiredSweeps
  exact vectorResidualMainPath_exactSignal_requires_sweeps width skipped sweeps
    step hbandwidth initial₀ initial₁ target₀ target₁ haway htarget
      hsettle₀ hsettle₁

/-- If one BP pass is cheaper than the finite-speed minimum PC work, an exact
settled vector PC run cannot simultaneously match BP's compute budget. -/
theorem exactVectorPC_no_equalCompute_below_finiteSpeedBudget
    (model : PCBPComputeModel) (width skipped sweeps : ℕ)
    (hbudget : bpTrainingWork model < pcTrainingWork model (skipped + 1))
    (step : ChainState (Fin width → ℝ) (skipped + 1) →
      ChainState (Fin width → ℝ) (skipped + 1))
    (hbandwidth : HasChainBandwidth step 1)
    (initial₀ initial₁ target₀ target₁ :
      ChainState (Fin width → ℝ) (skipped + 1))
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node)
    (htarget : target₀ (chainTerminalNode (skipped + 1)) ≠
      target₁ (chainTerminalNode (skipped + 1)))
    (hsettle₀ : Nat.iterate step sweeps initial₀ = target₀)
    (hsettle₁ : Nat.iterate step sweeps initial₁ = target₁) :
    ¬ PCBPAtEqualCompute model sweeps := by
  intro hequal
  have hlower := exactVectorPC_trainingWork_lowerBound model width skipped sweeps
    step hbandwidth initial₀ initial₁ target₀ target₁ haway htarget
      hsettle₀ hsettle₁
  unfold PCBPAtEqualCompute at hequal
  omega

/-! ## Empirical verdict boundary -/

inductive PCBPComparisonStatus
  | exactCostTheorem
  | empiricalRiskMeasurement
  deriving DecidableEq, Repr

structure PCBPComparisonClaim where
  description : String
  status : PCBPComparisonStatus
  deriving DecidableEq, Repr

/-- Nonlinear accuracy or risk dominance at an equal budget is a measurement
target, not a consequence of the cost algebra. -/
def nonlinearPCBeatsBPAtEqualComputeBoundary : PCBPComparisonClaim where
  description :=
    "strict nonlinear PC risk improvement over BP at exactly matched measured work"
  status := .empiricalRiskMeasurement

theorem nonlinearPCBeatsBPAtEqualComputeBoundary_not_exact :
    nonlinearPCBeatsBPAtEqualComputeBoundary.status ≠ .exactCostTheorem := by
  decide

structure PCBPComputeCertificate : Prop where
  sharedCancellation :
    ∀ (model : PCBPComputeModel) (sweeps : ℕ),
      PCBPAtEqualCompute model sweeps ↔
        sweeps * model.pcSweepWork + model.pcWeightUpdateWork =
          model.backwardPassWork + model.bpWeightUpdateWork
  performanceSeparated :
    PCBPAtEqualCompute equalComputeFixture 3 ∧
      ¬ PCBeatsBPAtEqualCompute equalComputeFixture 3 2 1
  empiricalBoundary :
    nonlinearPCBeatsBPAtEqualComputeBoundary.status ≠ .exactCostTheorem

theorem pcBPCompute : PCBPComputeCertificate where
  sharedCancellation := pcBPAtEqualCompute_iff_privateWork_eq
  performanceSeparated := equalCompute_does_not_imply_pcBeats
  empiricalBoundary := nonlinearPCBeatsBPAtEqualComputeBoundary_not_exact

#print axioms pcBPAtEqualCompute_iff_privateWork_eq
#print axioms exactVectorPC_no_equalCompute_below_finiteSpeedBudget
#print axioms pcBPCompute

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
