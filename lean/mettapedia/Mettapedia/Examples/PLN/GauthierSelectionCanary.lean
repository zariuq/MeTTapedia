import Mathlib.Tactic
import Mettapedia.Examples.PLN.DependenceAwareChainComposition
import Mettapedia.PLN.InferenceControl.EvolutionGuidance

/-!
# Evolution-selection canaries

Small executable fixtures for the PLN interval-dominance selection rule.
-/

namespace Mettapedia.Examples.PLN.GauthierSelectionCanary

open Mettapedia.PLN.InferenceControl.EvolutionGuidance
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

noncomputable section

theorem one_pos : 0 < (1 : ℝ) := by
  norm_num

theorem two_pos : 0 < (2 : ℝ) := by
  norm_num

/-! ## S1 positive: separated fitness evidence ranks -/

def highFitnessEvidence : FitnessEvidence where
  successes := 9
  failures := 1

def lowFitnessEvidence : FitnessEvidence where
  successes := 6
  failures := 4

def highBeatsLowDatum : FitnessSelectionDatum 1 one_pos where
  incumbentEvidence := highFitnessEvidence
  candidateEvidence := lowFitnessEvidence
  incumbentContainment :=
    FitnessContainment.midpoint 1 one_pos highFitnessEvidence
  candidateContainment :=
    FitnessContainment.midpoint 1 one_pos lowFitnessEvidence

theorem high_beats_low_intervalDominanceSelection :
    intervalDominanceSelection
      (fitnessITV 1 one_pos highFitnessEvidence)
      (fitnessITV 1 one_pos lowFitnessEvidence) := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
    ITV.fromWalleyIDMPredictive, highFitnessEvidence, lowFitnessEvidence]

theorem high_beats_low_selection_admissible :
    highBeatsLowDatum.candidateContainment.trueFitness <
      highBeatsLowDatum.incumbentContainment.trueFitness :=
  intervalDominanceSelection_admissible highBeatsLowDatum
    high_beats_low_intervalDominanceSelection

/-! ## S1 interval geometry canaries -/

def separatedIncumbentITV : ITV where
  lower := 8 / 10
  upper := 9 / 10
  credibility := 9 / 10
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def separatedCandidateITV : ITV where
  lower := 5 / 10
  upper := 6 / 10
  credibility := 9 / 10
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

theorem separated_manual_intervalDominanceSelection :
    intervalDominanceSelection separatedIncumbentITV separatedCandidateITV := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  norm_num [separatedIncumbentITV, separatedCandidateITV]

def overlapIncumbentITV : ITV where
  lower := 6 / 10
  upper := 8 / 10
  credibility := 7 / 10
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def overlapCandidateITV : ITV where
  lower := 7 / 10
  upper := 9 / 10
  credibility := 7 / 10
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

theorem overlap_manual_fitnessIntervalsOverlap :
    fitnessIntervalsOverlap overlapIncumbentITV overlapCandidateITV := by
  rw [fitnessIntervalsOverlap_iff]
  norm_num [overlapIncumbentITV, overlapCandidateITV]

theorem overlap_manual_no_forced_discard :
    ∃ incumbentFitness candidateFitness,
      overlapIncumbentITV.lower ≤ incumbentFitness ∧
        incumbentFitness ≤ overlapIncumbentITV.upper ∧
        overlapCandidateITV.lower ≤ candidateFitness ∧
        candidateFitness ≤ overlapCandidateITV.upper ∧
        incumbentFitness ≤ candidateFitness :=
  overlap_no_forced_discard overlapIncumbentITV overlapCandidateITV
    overlap_manual_fitnessIntervalsOverlap

theorem overlap_manual_candidate_can_strictly_win :
    ∃ incumbentFitness candidateFitness,
      overlapIncumbentITV.lower ≤ incumbentFitness ∧
        incumbentFitness ≤ overlapIncumbentITV.upper ∧
        overlapCandidateITV.lower ≤ candidateFitness ∧
        candidateFitness ≤ overlapCandidateITV.upper ∧
        incumbentFitness < candidateFitness :=
  candidate_can_strictly_win_of_interior_overlap
    overlapIncumbentITV overlapCandidateITV
    (by norm_num [overlapIncumbentITV, overlapCandidateITV])
    (by norm_num [overlapIncumbentITV, overlapCandidateITV])

/-! ## S2/S3: Gauthier-scale evidence-budget canaries -/

def gauthierBestSmallN : FitnessEvidence where
  successes := 64
  failures := 36

def gauthierRandomSmallN : FitnessEvidence where
  successes := 63
  failures := 37

theorem gauthier_smallN_fitnessIntervalsOverlap :
    fitnessIntervalsOverlap
      (fitnessITV 2 two_pos gauthierBestSmallN)
      (fitnessITV 2 two_pos gauthierRandomSmallN) := by
  rw [fitnessIntervalsOverlap_iff]
  norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
    ITV.fromWalleyIDMPredictive, gauthierBestSmallN, gauthierRandomSmallN]

theorem gauthier_smallN_best_not_strictly_rank_random :
    ¬ intervalDominanceSelection
      (fitnessITV 2 two_pos gauthierBestSmallN)
      (fitnessITV 2 two_pos gauthierRandomSmallN) := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
    ITV.fromWalleyIDMPredictive, gauthierBestSmallN, gauthierRandomSmallN]

theorem gauthier_smallN_random_not_strictly_rank_best :
    ¬ intervalDominanceSelection
      (fitnessITV 2 two_pos gauthierRandomSmallN)
      (fitnessITV 2 two_pos gauthierBestSmallN) := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
    ITV.fromWalleyIDMPredictive, gauthierBestSmallN, gauthierRandomSmallN]

theorem gauthier_smallN_random_can_strictly_win :
    ∃ bestFitness randomFitness,
      (fitnessITV 2 two_pos gauthierBestSmallN).lower ≤ bestFitness ∧
        bestFitness ≤ (fitnessITV 2 two_pos gauthierBestSmallN).upper ∧
        (fitnessITV 2 two_pos gauthierRandomSmallN).lower ≤ randomFitness ∧
        randomFitness ≤ (fitnessITV 2 two_pos gauthierRandomSmallN).upper ∧
        bestFitness < randomFitness :=
  candidate_can_strictly_win_of_interior_overlap
    (fitnessITV 2 two_pos gauthierBestSmallN)
    (fitnessITV 2 two_pos gauthierRandomSmallN)
    (by
      norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
        ITV.fromWalleyIDMPredictive, gauthierBestSmallN,
        gauthierRandomSmallN])
    (by
      norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
        ITV.fromWalleyIDMPredictive, gauthierBestSmallN,
        gauthierRandomSmallN])

def gauthierBestHighResolution : FitnessEvidence where
  successes := 6435
  failures := 3565

def gauthierRandomHighResolution : FitnessEvidence where
  successes := 6335
  failures := 3665

theorem gauthier_highResolution_budget_counterfactual_ranks :
    intervalDominanceSelection
      (fitnessITV 1 one_pos gauthierBestHighResolution)
      (fitnessITV 1 one_pos gauthierRandomHighResolution) := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
    ITV.fromWalleyIDMPredictive, gauthierBestHighResolution,
    gauthierRandomHighResolution]

theorem gauthier_highResolution_ranks_by_minTrials :
    intervalDominanceSelection
      (fitnessITV 1 one_pos gauthierBestHighResolution)
      (fitnessITV 1 one_pos gauthierRandomHighResolution) :=
  minTrials_for_ranking
    (s := 1) (gap := (1 / 200 : ℝ)) (hs := one_pos) (n := 10000)
    (by norm_num)
    (by norm_num)
    gauthierBestHighResolution
    gauthierRandomHighResolution
    (by norm_num [FitnessEvidence.trials, gauthierBestHighResolution])
    (by norm_num [FitnessEvidence.trials, gauthierRandomHighResolution])
    (by
      norm_num [midpointGap, fitnessITV, FitnessEvidence.toBinaryEvidence,
        FitnessEvidence.trials, ITV.strength, ITV.fromWalleyIDMPredictive,
        gauthierBestHighResolution, gauthierRandomHighResolution])

def gauthierBestSeparatedHundred : FitnessEvidence where
  successes := 90
  failures := 10

def gauthierWeakSeparatedHundred : FitnessEvidence where
  successes := 60
  failures := 40

theorem gauthier_ninety_beats_sixty_intervalDominanceSelection :
    intervalDominanceSelection
      (fitnessITV 2 two_pos gauthierBestSeparatedHundred)
      (fitnessITV 2 two_pos gauthierWeakSeparatedHundred) := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  norm_num [fitnessITV, FitnessEvidence.toBinaryEvidence,
    ITV.fromWalleyIDMPredictive, gauthierBestSeparatedHundred,
    gauthierWeakSeparatedHundred]

/-! ## S2: pooled child evidence canary -/

def pooledCanaryChildren : Fin 2 → FitnessEvidence :=
  fun i =>
    if i = 0 then
      { successes := 1, failures := 0 }
    else
      { successes := 1, failures := 0 }

theorem pooled_two_children_confidence_ge_first :
    (fitnessITV 1 one_pos (pooledCanaryChildren 0)).credibility ≤
      (fitnessITV 1 one_pos
        (pooledChildrenEvidence pooledCanaryChildren)).credibility :=
  pooledChildren_confidence_ge_best_child pooledCanaryChildren 0

theorem pooled_two_children_confidence_strictly_improves_first :
    (fitnessITV 1 one_pos (pooledCanaryChildren 0)).credibility <
      (fitnessITV 1 one_pos
        (pooledChildrenEvidence pooledCanaryChildren)).credibility := by
  norm_num [pooledCanaryChildren, pooledChildrenEvidence, fitnessITV,
    FitnessEvidence.toBinaryEvidence, ITV.fromWalleyIDMPredictive]

/-! ## S3: chain horizon tie-in -/

theorem lowConfidence_threeHop_chainVacuous_tie_in :
    Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition.chainVacuous
      Mettapedia.Examples.PLN.DependenceAwareChainComposition.halfHorizonPolicy
      Mettapedia.Examples.PLN.DependenceAwareChainComposition.lowConfidenceThreeHopChain :=
  Mettapedia.Examples.PLN.DependenceAwareChainComposition.lowConfidence_threeHop_chainVacuous

theorem lowConfidence_threeHop_horizon_width_one_tie_in :
    Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition.chainEnvelopeWidth
        (Mettapedia.PLN.InferenceControl.CertifiedChaining.DependenceAwareChainComposition.horizonEnvelope
          Mettapedia.Examples.PLN.DependenceAwareChainComposition.halfHorizonPolicy
          Mettapedia.Examples.PLN.DependenceAwareChainComposition.lowConfidenceThreeHopChain) =
      1 :=
  Mettapedia.Examples.PLN.DependenceAwareChainComposition.lowConfidence_threeHop_horizon_width_one

end

end Mettapedia.Examples.PLN.GauthierSelectionCanary
