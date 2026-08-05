import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Model
import Mettapedia.PLN.Bridges.PredictiveCoding.EvidenceRegisterBridge
import Mettapedia.PLN.Evidence.BinEvNat

/-!
# Exact belief-register instance

The controlled belief architecture stores evidence in additive natural
coordinates.  This file first proves the concrete register equations for
natural parameters and for primal `(n⁺, n⁻)` counts.  It then packages the
real-valued natural-coordinate state as an exact `LinearEffectModel` instance.

The identity readout below is intentional: the claimed output is the complete
register state itself, not an unrestricted neural prediction.  The existing
evidence-register bridge supplies the nontrivial decoded Gaussian/PLN readout.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.PLN.Evidence
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Counts-primal register -/

/-- A sequence of binary observations accumulates in the primal count monoid. -/
def accumulatedCountRegister (evidence : List BinEvNat) : BinEvNat :=
  evidence.sum

/-- Independent count sequences fuse by list concatenation and count addition. -/
theorem accumulatedCountRegister_append (left right : List BinEvNat) :
    accumulatedCountRegister (left ++ right) =
      accumulatedCountRegister left + accumulatedCountRegister right := by
  simp [accumulatedCountRegister, List.sum_append]

/-- Positive count fixture: two positive and one negative observation remain
visible in the primal coordinates. -/
theorem accumulatedCountRegister_example :
    accumulatedCountRegister [⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩] = ⟨2, 1⟩ := by
  decide

/-- Negative/idempotence boundary: reusing one observation really adds a
second copy; count fusion does not silently deduplicate evidence. -/
theorem countRegister_reuse_not_idempotent :
    accumulatedCountRegister [⟨1, 0⟩, ⟨1, 0⟩] ≠
      accumulatedCountRegister [⟨1, 0⟩] := by
  decide

/-! ## Gaussian natural-coordinate register -/

/-- The complete real-valued belief-register state `(Λ, η)`. -/
abbrev GaussianNaturalState (Index : Type*) :=
  Matrix Index Index ℝ × (Index → ℝ)

/-- Expose an existing Gaussian ledger entry as its stored coordinates. -/
def gaussianEvidenceCoordinates {Index : Type*}
    (evidence : GaussianEvidence Index) : GaussianNaturalState Index :=
  (evidence.precision, evidence.naturalParameter)

/-- Existing evidence fusion is exactly addition of complete register states. -/
theorem gaussianEvidenceCoordinates_add {Index : Type*}
    (left right : GaussianEvidence Index) :
    gaussianEvidenceCoordinates (left.add right) =
      gaussianEvidenceCoordinates left + gaussianEvidenceCoordinates right := by
  apply Prod.ext
  · rfl
  · rfl

/-- Accumulate a sequence of already-formed natural-coordinate contributions. -/
def accumulatedGaussianNaturalState {Index : Type*}
    (evidence : List (GaussianEvidence Index)) : GaussianNaturalState Index :=
  (evidence.map gaussianEvidenceCoordinates).sum

theorem accumulatedGaussianNaturalState_append {Index : Type*}
    (left right : List (GaussianEvidence Index)) :
    accumulatedGaussianNaturalState (left ++ right) =
      accumulatedGaussianNaturalState left +
        accumulatedGaussianNaturalState right := by
  simp [accumulatedGaussianNaturalState, List.sum_append]

/-- The belief-register effect model exposes all and only the controlled
natural-coordinate state. -/
noncomputable def beliefRegisterLinearEffectModel (Index : Type*) :
    LinearEffectModel (GaussianNaturalState Index) (GaussianNaturalState Index)
      (GaussianNaturalState Index) where
  slowEffect := LinearMap.id
  fastEffect := LinearMap.id

/-- The model's fast effect of fused evidence is exactly the sum of the two
concrete register contributions. -/
theorem beliefRegister_fastEffect_add_exact {Index : Type*}
    (left right : GaussianEvidence Index) :
    (beliefRegisterLinearEffectModel Index).fastEffect
        (gaussianEvidenceCoordinates (left.add right)) =
      gaussianEvidenceCoordinates left + gaussianEvidenceCoordinates right := by
  exact gaussianEvidenceCoordinates_add left right

/-- Exact scalar crown: the same additive fast state decodes to the existing
Gaussian fusion theorem rather than merely resembling it. -/
theorem beliefRegister_linearEffectModel_gaussianFusion_exact
    (source₁ source₂ : GaussianSource) :
    (beliefRegisterLinearEffectModel (Fin 1)).fastEffect
        (gaussianEvidenceCoordinates
          ((gaussianSourceEvidence source₁).add
            (gaussianSourceEvidence source₂))) =
        gaussianEvidenceCoordinates (gaussianSourceEvidence source₁) +
          gaussianEvidenceCoordinates (gaussianSourceEvidence source₂) ∧
      scalarGaussianEvidenceMean
          ((gaussianSourceEvidence source₁).add
            (gaussianSourceEvidence source₂)) =
        gaussianFusion source₁.mean source₂.mean
          source₁.precision source₂.precision := by
  exact ⟨beliefRegister_fastEffect_add_exact _ _,
    scalarGaussianEvidenceMean_add_eq_gaussianFusion source₁ source₂⟩

#print axioms accumulatedCountRegister_append
#print axioms gaussianEvidenceCoordinates_add
#print axioms beliefRegister_fastEffect_add_exact
#print axioms beliefRegister_linearEffectModel_gaussianFusion_exact

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
