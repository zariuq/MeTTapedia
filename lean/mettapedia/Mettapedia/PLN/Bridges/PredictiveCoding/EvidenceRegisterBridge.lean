import Mettapedia.MachineLearning.ContinualLearning.EvidenceLedger
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianChain
import Mettapedia.PLN.Bridges.PredictiveCoding.GaussianRevisionBridge

/-!
# Additive evidence-register bridge

The continual-learning ledger stores Gaussian evidence in natural coordinates
`(precision, naturalParameter)`.  The scalar predictive-coding bridge instead
starts from moment coordinates `(mean, precision)`.  This file proves that the
existing Gaussian fusion, PLN revision, and depth-two settling equilibrium are
readouts of the same additive ledger.  Reusing a contribution is therefore the
same extra copy in every chart.
-/

namespace Mettapedia.PLN.Bridges.PredictiveCoding

open Mettapedia.MachineLearning.ContinualLearning
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNWeightTV

/-- A scalar Gaussian source represented in the existing natural-coordinate
continual-learning ledger.  This is a chart map, not a new fusion operation. -/
noncomputable def gaussianSourceEvidence
    (source : GaussianSource) : GaussianEvidence (Fin 1) where
  precision := Matrix.diagonal fun _ => source.precision
  naturalParameter := fun _ => source.precision * source.mean

/-- Decode the moment-coordinate mean from a scalar natural-coordinate
ledger.  Positivity is supplied by the source theorems at every use site. -/
noncomputable def scalarGaussianEvidenceMean
    (evidence : GaussianEvidence (Fin 1)) : ℝ :=
  evidence.naturalParameter 0 / evidence.precision 0 0

@[simp] theorem gaussianSourceEvidence_precision
    (source : GaussianSource) :
    (gaussianSourceEvidence source).precision 0 0 = source.precision := by
  simp [gaussianSourceEvidence]

@[simp] theorem gaussianSourceEvidence_naturalParameter
    (source : GaussianSource) :
    (gaussianSourceEvidence source).naturalParameter 0 =
      source.precision * source.mean := by
  rfl

@[simp] theorem scalarGaussianEvidenceMean_source
    (source : GaussianSource) :
    scalarGaussianEvidenceMean (gaussianSourceEvidence source) = source.mean := by
  simp [scalarGaussianEvidenceMean, source.precision_pos.ne']

/-- Load-bearing natural-coordinate identity: adding the two existing ledger
contributions and decoding the mean is exactly the existing Gaussian fusion. -/
theorem scalarGaussianEvidenceMean_add_eq_gaussianFusion
    (source₁ source₂ : GaussianSource) :
    scalarGaussianEvidenceMean
        ((gaussianSourceEvidence source₁).add
          (gaussianSourceEvidence source₂)) =
      gaussianFusion source₁.mean source₂.mean
        source₁.precision source₂.precision := by
  simp [scalarGaussianEvidenceMean, GaussianEvidence.add, gaussianSourceEvidence,
    gaussianFusion]

/-- The same additive-register readout is the existing WTV revision strength. -/
theorem scalarGaussianEvidenceMean_add_eq_plnRevisionWTV
    (source₁ source₂ : GaussianSource) :
    scalarGaussianEvidenceMean
        ((gaussianSourceEvidence source₁).add
          (gaussianSourceEvidence source₂)) =
      (revisionWTV
        (wtvOfPrecision source₁.mean source₁.precision
          source₁.mean_nonneg source₁.mean_le_one
          (le_of_lt source₁.precision_pos))
        (wtvOfPrecision source₂.mean source₂.precision
          source₂.mean_nonneg source₂.mean_le_one
          (le_of_lt source₂.precision_pos))).strength := by
  rw [scalarGaussianEvidenceMean_add_eq_gaussianFusion,
    gaussianFusion_eq_plnRevisionWTV]

/-- The same additive-register readout is the existing counts-addition
revision strength. -/
theorem scalarGaussianEvidenceMean_add_eq_binaryCountsRevision
    (source₁ source₂ : GaussianSource) :
    scalarGaussianEvidenceMean
        ((gaussianSourceEvidence source₁).add
          (gaussianSourceEvidence source₂)) =
      ((binaryCountsOfStrengthWeight source₁.mean source₁.precision
          source₁.mean_nonneg source₁.mean_le_one
          (le_of_lt source₁.precision_pos)).add
        (binaryCountsOfStrengthWeight source₂.mean source₂.precision
          source₂.mean_nonneg source₂.mean_le_one
          (le_of_lt source₂.precision_pos))).strength := by
  rw [scalarGaussianEvidenceMean_add_eq_gaussianFusion,
    gaussianFusion_eq_binaryCounts_revision_strength]

/-- The existing depth-two settling posterior reads out the same additive
natural-coordinate register. -/
theorem pcDepthTwo_posteriorMean_eq_additiveRegister
    (source₁ source₂ : GaussianSource) :
    pcConditionalPosteriorMean
        (pcDepthTwoLinks 1 1 source₁.precision source₂.precision
          source₁.precision_pos source₂.precision_pos)
        source₁.mean source₂.mean 0 =
      scalarGaussianEvidenceMean
        ((gaussianSourceEvidence source₁).add
          (gaussianSourceEvidence source₂)) := by
  rw [pcConditionalPosteriorMean_depthTwo_eq_gaussianFusion]
  simp [scalarGaussianEvidenceMean_add_eq_gaussianFusion]

/-- Settling is not merely numerically analogous to revision: the existing PC
equilibrium predicate is equality with the state decoded from the shared
additive register. -/
theorem pcDepthTwo_equilibrium_iff_eq_additiveRegister
    (source₁ source₂ : GaussianSource) (z : PCState 2) :
    pcEquilibrium
        (pcDepthTwoLinks 1 1 source₁.precision source₂.precision
          source₁.precision_pos source₂.precision_pos)
        source₁.mean source₂.mean z ↔
      z = pcStateOfInterior 1 source₁.mean source₂.mean
        (WithLp.toLp 2 fun _ : Fin 1 =>
          scalarGaussianEvidenceMean
            ((gaussianSourceEvidence source₁).add
              (gaussianSourceEvidence source₂))) := by
  let links := pcDepthTwoLinks 1 1 source₁.precision source₂.precision
    source₁.precision_pos source₂.precision_pos
  have hmean :
      pcConditionalPosteriorMean links source₁.mean source₂.mean =
        WithLp.toLp 2 (fun _ : Fin 1 =>
          scalarGaussianEvidenceMean
            ((gaussianSourceEvidence source₁).add
              (gaussianSourceEvidence source₂))) := by
    apply PiLp.ext
    intro i
    fin_cases i
    exact pcDepthTwo_posteriorMean_eq_additiveRegister source₁ source₂
  rw [pcEquilibrium_iff_eq_conditionalPosteriorMean,
    pcConditionalPosterior_integral_id, hmean]

/-- Transport of the existing double-counting theorem: reusing the first
source leaves the once-each ledger plus exactly one extra copy of that same
natural-coordinate contribution. -/
theorem gaussianSourceEvidence_reuse_exact_extra_copy
    (prior : GaussianEvidence (Fin 1)) (source₁ source₂ : GaussianSource) :
    (((prior.update (gaussianSourceEvidence source₁)).update
          (gaussianSourceEvidence source₁)).update
        (gaussianSourceEvidence source₂)) =
      ((prior.update (gaussianSourceEvidence source₁)).update
          (gaussianSourceEvidence source₂)).add
        (gaussianSourceEvidence source₁) := by
  calc
    (((prior.update (gaussianSourceEvidence source₁)).update
          (gaussianSourceEvidence source₁)).update
        (gaussianSourceEvidence source₂)) =
        (prior.update (gaussianSourceEvidence source₁)).update
          ((gaussianSourceEvidence source₂).add
            (gaussianSourceEvidence source₁)) :=
      GaussianEvidence.reused_contribution_exact_excess
        prior (gaussianSourceEvidence source₁) (gaussianSourceEvidence source₂)
    _ = ((prior.update (gaussianSourceEvidence source₁)).update
          (gaussianSourceEvidence source₂)).add
        (gaussianSourceEvidence source₁) := by
      exact (GaussianEvidence.add_assoc
        (prior.update (gaussianSourceEvidence source₁))
        (gaussianSourceEvidence source₂)
        (gaussianSourceEvidence source₁)).symm

/-- T1 crown: one addition in the existing continual-learning ledger is PLN
revision in both WTV and counts charts and is the unique depth-two PC settling
state; reusing evidence is exactly one extra copy in that same register. -/
theorem additiveEvidenceRegister_revision_settling
    (prior : GaussianEvidence (Fin 1)) (source₁ source₂ : GaussianSource) :
    scalarGaussianEvidenceMean
        ((gaussianSourceEvidence source₁).add
          (gaussianSourceEvidence source₂)) =
        (revisionWTV
          (wtvOfPrecision source₁.mean source₁.precision
            source₁.mean_nonneg source₁.mean_le_one
            (le_of_lt source₁.precision_pos))
          (wtvOfPrecision source₂.mean source₂.precision
            source₂.mean_nonneg source₂.mean_le_one
            (le_of_lt source₂.precision_pos))).strength ∧
      scalarGaussianEvidenceMean
        ((gaussianSourceEvidence source₁).add
          (gaussianSourceEvidence source₂)) =
        ((binaryCountsOfStrengthWeight source₁.mean source₁.precision
            source₁.mean_nonneg source₁.mean_le_one
            (le_of_lt source₁.precision_pos)).add
          (binaryCountsOfStrengthWeight source₂.mean source₂.precision
            source₂.mean_nonneg source₂.mean_le_one
            (le_of_lt source₂.precision_pos))).strength ∧
      (∀ z : PCState 2,
        pcEquilibrium
            (pcDepthTwoLinks 1 1 source₁.precision source₂.precision
              source₁.precision_pos source₂.precision_pos)
            source₁.mean source₂.mean z ↔
          z = pcStateOfInterior 1 source₁.mean source₂.mean
            (WithLp.toLp 2 fun _ : Fin 1 =>
              scalarGaussianEvidenceMean
                ((gaussianSourceEvidence source₁).add
                  (gaussianSourceEvidence source₂)))) ∧
      (((prior.update (gaussianSourceEvidence source₁)).update
            (gaussianSourceEvidence source₁)).update
          (gaussianSourceEvidence source₂)) =
        ((prior.update (gaussianSourceEvidence source₁)).update
            (gaussianSourceEvidence source₂)).add
          (gaussianSourceEvidence source₁) := by
  exact ⟨scalarGaussianEvidenceMean_add_eq_plnRevisionWTV source₁ source₂,
    scalarGaussianEvidenceMean_add_eq_binaryCountsRevision source₁ source₂,
    pcDepthTwo_equilibrium_iff_eq_additiveRegister source₁ source₂,
    gaussianSourceEvidence_reuse_exact_extra_copy prior source₁ source₂⟩

#print axioms additiveEvidenceRegister_revision_settling

end Mettapedia.PLN.Bridges.PredictiveCoding
