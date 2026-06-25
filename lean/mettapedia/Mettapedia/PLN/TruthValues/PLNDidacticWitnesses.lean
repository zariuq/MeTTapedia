import Mettapedia.PLN.TruthValues.PLNConfidenceWeightRevision
import Mettapedia.PLN.TruthValues.PLNAmplitudePhase

/-!
# Didactic Witnesses for PLN Truth-Value Degrees of Freedom

This module packages the small numerical witnesses used in the paper-facing
discussion of strength, confidence charts, information geometry, and
amplitude/phase.  The core theory lives in the imported modules; this file
proves the exact numbers used by the examples.
-/

namespace Mettapedia.PLN.TruthValues.PLNDidacticWitnesses

open Mettapedia.PLN.TruthValues.PLNTruthTower
open Mettapedia.PLN.TruthValues.PLNInformationGeometry
open Mettapedia.PLN.TruthValues.PLNAmplitudePhase
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight
open Mettapedia.PLN.TruthValues.PLNConfidenceWeight.EvidenceWeightCoordinate
open Mettapedia.Algebra.TwoDimClassification

/-! ## Marble bag: strength is not confidence -/

/-- One red observation has empirical strength `1`, but low PLN confidence
when the horizon is `k = 2`. -/
theorem marbleBag_one_red_strength_confidence :
    let e := BinaryCounts.ofNatCounts 1 0
    e.mleStrength = 1 ∧
      (plnOddsCoordinate 2 (by norm_num)).encode e.total = (1 / 3 : ℝ) := by
  norm_num [BinaryCounts.ofNatCounts, BinaryCounts.mleStrength,
    BinaryCounts.strength, BinaryCounts.total, plnOddsCoordinate]

/-- A large balanced sample has strength `1/2` but high PLN confidence at the
same horizon. -/
theorem marbleBag_balanced_large_strength_confidence :
    let e := BinaryCounts.ofNatCounts 100 100
    e.mleStrength = (1 / 2 : ℝ) ∧
      (plnOddsCoordinate 2 (by norm_num)).encode e.total =
        (100 / 101 : ℝ) ∧
      (1 / 3 : ℝ) < 100 / 101 := by
  norm_num [BinaryCounts.ofNatCounts, BinaryCounts.mleStrength,
    BinaryCounts.strength, BinaryCounts.total, plnOddsCoordinate]

/-! ## Loudspeakers: phase controls interference -/

/-- Two unit coherent paths can produce constructive or destructive
interference, while the incoherent view always predicts weight `2`. -/
theorem loudspeaker_interference_values :
    incoherentTwoPathWeight 1 1 = 2 ∧
      complexTwoPathBornWeight 1 1 0 0 = 4 ∧
      complexTwoPathBornWeight 1 1 0 Real.pi = 0 := by
  constructor
  · norm_num [incoherentTwoPathWeight]
  · exact ⟨complexTwoPath_constructive_at_equal_phase,
      complexTwoPath_destructive_at_pi⟩

/-! ## Same display, different chart laws -/

/-- The displayed confidence `1/2` revises to three different values in the
PLN, exponential/noisy-OR, and tanh/Einstein charts. -/
theorem halfConfidence_three_revision_values :
    plnConfidenceRevision (1 / 2) (1 / 2) = (2 / 3 : ℝ) ∧
      expConfidenceRevision (1 / 2) (1 / 2) = (3 / 4 : ℝ) ∧
      tanhConfidenceRevision (1 / 2) (1 / 2) = (4 / 5 : ℝ) := by
  norm_num [plnConfidenceRevision, expConfidenceRevision,
    tanhConfidenceRevision]

/-- The three `1/2` revision laws are pairwise distinct at the witness point. -/
theorem halfConfidence_revision_values_distinct :
    plnConfidenceRevision (1 / 2) (1 / 2) ≠
        expConfidenceRevision (1 / 2) (1 / 2) ∧
      expConfidenceRevision (1 / 2) (1 / 2) ≠
        tanhConfidenceRevision (1 / 2) (1 / 2) ∧
      plnConfidenceRevision (1 / 2) (1 / 2) ≠
        tanhConfidenceRevision (1 / 2) (1 / 2) := by
  norm_num [plnConfidenceRevision, expConfidenceRevision,
    tanhConfidenceRevision]

/-! ## Goldilocks: the positive-definite phase carrier is complex -/

/-- Complex numbers pass the positive-definite Born-weight gate, while dual
and split-complex carriers fail it. -/
theorem goldilocks_phase_carrier_ablation :
    (∀ z : KSComplexPhaseCarrier,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ∧
      (¬ ∀ z : MuAlgebra 0,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ∧
      (¬ ∀ z : MuAlgebra 1,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) := by
  exact ⟨ksComplexPhaseCarrier_positiveDefinite,
    dualCarrier_not_positiveDefinite, splitCarrier_not_positiveDefinite⟩

/-! ## Pool versus chain: m-flat averaging is not e-flat chaining -/

/-- Two likelihood-ratio-`3` tests chain to probability `9/10`, while pooling
the identical single-test posterior rates remains `3/4`. -/
theorem pool_vs_chain_lr3 :
    bernoulliNaturalToMean (Real.log 3) = (3 / 4 : ℝ) ∧
      bernoulliMixtureGeodesic (3 / 4) (3 / 4) (1 / 2) = (3 / 4 : ℝ) ∧
      bernoulliNaturalToMean (Real.log 9) = (9 / 10 : ℝ) ∧
      bernoulliMixtureGeodesic (3 / 4) (3 / 4) (1 / 2) ≠
        bernoulliNaturalToMean (Real.log 9) := by
  have hsingle :
      bernoulliNaturalToMean (Real.log 3) = (3 / 4 : ℝ) := by
    unfold bernoulliNaturalToMean
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hpool :
      bernoulliMixtureGeodesic (3 / 4) (3 / 4) (1 / 2) =
        (3 / 4 : ℝ) := by
    norm_num [bernoulliMixtureGeodesic]
  have hchain :
      bernoulliNaturalToMean (Real.log 9) = (9 / 10 : ℝ) := by
    unfold bernoulliNaturalToMean
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 9)]
    norm_num
  exact ⟨hsingle, hpool, hchain, by
    rw [hpool, hchain]
    norm_num⟩

/-! ## Bundle and runtime parity metadata -/

/-- Proof-carrying bundle for the paper-facing didactic witnesses, together
with the paired PeTTa/CeTTa runtime canary locations. -/
structure DidacticWitnessProfile where
  marbleBagOneRed :
    let e := BinaryCounts.ofNatCounts 1 0
    e.mleStrength = 1 ∧
      (plnOddsCoordinate 2 (by norm_num)).encode e.total = (1 / 3 : ℝ)
  marbleBagBalancedLarge :
    let e := BinaryCounts.ofNatCounts 100 100
    e.mleStrength = (1 / 2 : ℝ) ∧
      (plnOddsCoordinate 2 (by norm_num)).encode e.total =
        (100 / 101 : ℝ) ∧
      (1 / 3 : ℝ) < 100 / 101
  loudspeakerInterference :
    incoherentTwoPathWeight 1 1 = 2 ∧
      complexTwoPathBornWeight 1 1 0 0 = 4 ∧
      complexTwoPathBornWeight 1 1 0 Real.pi = 0
  halfConfidenceValues :
    plnConfidenceRevision (1 / 2) (1 / 2) = (2 / 3 : ℝ) ∧
      expConfidenceRevision (1 / 2) (1 / 2) = (3 / 4 : ℝ) ∧
      tanhConfidenceRevision (1 / 2) (1 / 2) = (4 / 5 : ℝ)
  halfConfidenceDistinct :
    plnConfidenceRevision (1 / 2) (1 / 2) ≠
        expConfidenceRevision (1 / 2) (1 / 2) ∧
      expConfidenceRevision (1 / 2) (1 / 2) ≠
        tanhConfidenceRevision (1 / 2) (1 / 2) ∧
      plnConfidenceRevision (1 / 2) (1 / 2) ≠
        tanhConfidenceRevision (1 / 2) (1 / 2)
  goldilocksCarrier :
    (∀ z : KSComplexPhaseCarrier,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ∧
      (¬ ∀ z : MuAlgebra 0,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ∧
      (¬ ∀ z : MuAlgebra 1,
        0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0))
  poolVsChain :
    bernoulliNaturalToMean (Real.log 3) = (3 / 4 : ℝ) ∧
      bernoulliMixtureGeodesic (3 / 4) (3 / 4) (1 / 2) = (3 / 4 : ℝ) ∧
      bernoulliNaturalToMean (Real.log 9) = (9 / 10 : ℝ) ∧
      bernoulliMixtureGeodesic (3 / 4) (3 / 4) (1 / 2) ≠
        bernoulliNaturalToMean (Real.log 9)
  peTTaPath : String
  ceTTaPath : String
  expectedChecks : Nat

/-- The current theorem/runtime bundle for the five didactic witnesses. -/
noncomputable def didacticWitnessProfile : DidacticWitnessProfile where
  marbleBagOneRed := marbleBag_one_red_strength_confidence
  marbleBagBalancedLarge := marbleBag_balanced_large_strength_confidence
  loudspeakerInterference := loudspeaker_interference_values
  halfConfidenceValues := halfConfidence_three_revision_values
  halfConfidenceDistinct := halfConfidence_revision_values_distinct
  goldilocksCarrier := goldilocks_phase_carrier_ablation
  poolVsChain := pool_vs_chain_lr3
  peTTaPath :=
    "/home/zar/claude/hyperon/PeTTa/examples/pln_didactic_witnesses.metta"
  ceTTaPath :=
    "/home/zar/claude/hyperon/CeTTa/tests/test_wmpln_didactic_witnesses.metta"
  expectedChecks := 23

end Mettapedia.PLN.TruthValues.PLNDidacticWitnesses
