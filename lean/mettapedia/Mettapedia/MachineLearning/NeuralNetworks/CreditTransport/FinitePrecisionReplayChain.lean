import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FinitePrecisionEvaluationError

/-!
# Proof-carrying finite-precision replay chains

This module folds the pointwise recurrence

`nextError = localError + rate * currentError`

through any finite homogeneous chain.  The next stage receives the preceding
runtime output definitionally, so an interior runtime value cannot be replaced
without constructing a different chain.  Each step still requires a local
evaluation certificate and a pointwise pair bound at the exact two states used
by that replay.

The certificate does not assert a global Lipschitz bound, contraction, runtime
schedule, or endpoint provenance.  Heterogeneous two- and three-stage chains
remain available in `FinitePrecisionEvaluationError`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FinitePrecisionReplayChain

noncomputable section

open FinitePrecisionEvaluationError

variable {X : Type*} [NormedAddCommGroup X]

/-- A proof-carrying homogeneous replay chain.  Its indices expose the exact
state, runtime state, certified error, and number of evaluated stages. -/
inductive HomogeneousReplayChainCertificate (X : Type*)
    [NormedAddCommGroup X] : X → X → ℝ → ℕ → Prop
  | initial (exactState runtimeState : X) (error : ℝ)
      (error_nonneg : 0 ≤ error)
      (state_error_le : ‖runtimeState - exactState‖ ≤ error) :
      HomogeneousReplayChainCertificate X exactState runtimeState error 0
  | step {exactState runtimeState : X} {error : ℝ} {stageCount : ℕ}
      (prior : HomogeneousReplayChainCertificate X
        exactState runtimeState error stageCount)
      (ideal : X → X) (runtimeOutput : X) (rate localError : ℝ)
      (rate_nonneg : 0 ≤ rate)
      (localCertificate : LocalEvaluationErrorCertificate
        ideal runtimeState runtimeOutput localError)
      (pair : ‖ideal runtimeState - ideal exactState‖ ≤
        rate * ‖runtimeState - exactState‖) :
      HomogeneousReplayChainCertificate X (ideal exactState) runtimeOutput
        (propagatedEvaluationError rate localError error) (stageCount + 1)

/-- Every replay chain establishes the error budget exposed by its index. -/
theorem HomogeneousReplayChainCertificate.sound
    {exactState runtimeState : X} {error : ℝ} {stageCount : ℕ}
    (chain : HomogeneousReplayChainCertificate X
      exactState runtimeState error stageCount) :
    ‖runtimeState - exactState‖ ≤ error := by
  induction chain with
  | initial _ _ _ _ state_error_le => exact state_error_le
  | @step exactState runtimeState error stageCount prior ideal runtimeOutput
      rate localError rate_nonneg localCertificate pair ih =>
      exact outputMismatch_le_propagatedEvaluationError
        ideal exactState runtimeState runtimeOutput rate localError error
        rate_nonneg localCertificate pair ih

/-- A chain's certified error is necessarily nonnegative. -/
theorem HomogeneousReplayChainCertificate.error_nonneg
    {exactState runtimeState : X} {error : ℝ} {stageCount : ℕ}
    (chain : HomogeneousReplayChainCertificate X
      exactState runtimeState error stageCount) :
    0 ≤ error := by
  exact le_trans (norm_nonneg (runtimeState - exactState)) chain.sound

/-! ## Positive and negative fixtures -/

private def doubleMap (value : ℝ) : ℝ := 2 * value

private def initialUnitMismatch :
    HomogeneousReplayChainCertificate ℝ 0 1 1 0 :=
  .initial 0 1 1 (by norm_num) (by norm_num)

private def firstNoisyDouble :
    HomogeneousReplayChainCertificate ℝ 0 3 3 1 := by
  convert HomogeneousReplayChainCertificate.step initialUnitMismatch
    doubleMap 3 2 1 (by norm_num)
    { localError_nonneg := by norm_num
      output_error_le := by norm_num [doubleMap] }
    (by norm_num [doubleMap]) using 1 <;>
    norm_num [doubleMap, propagatedEvaluationError]

/-- Two noisy doubling stages accumulate the exact conservative recurrence
`1 + 2 * (1 + 2 * 1) = 7`. -/
def twoNoisyDoubles :
    HomogeneousReplayChainCertificate ℝ 0 7 7 2 := by
  convert HomogeneousReplayChainCertificate.step firstNoisyDouble
    doubleMap 7 2 1 (by norm_num)
    { localError_nonneg := by norm_num
      output_error_le := by norm_num [doubleMap] }
    (by norm_num [doubleMap]) using 1 <;>
    norm_num [doubleMap, propagatedEvaluationError]

theorem twoNoisyDoubles_sound : ‖(7 : ℝ) - 0‖ ≤ 7 :=
  twoNoisyDoubles.sound

/-- No two-stage certificate can claim a budget smaller than the discrepancy
of its exposed endpoint states. -/
theorem twoNoisyDoubles_budget_six_is_impossible :
    ¬ HomogeneousReplayChainCertificate ℝ 0 7 6 2 := by
  intro chain
  have hsound := chain.sound
  norm_num at hsound

#print axioms HomogeneousReplayChainCertificate.sound
#print axioms twoNoisyDoubles_sound
#print axioms twoNoisyDoubles_budget_six_is_impossible

end

end FinitePrecisionReplayChain

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
