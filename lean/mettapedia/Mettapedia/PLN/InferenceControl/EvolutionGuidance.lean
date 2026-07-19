import Mathlib.Tactic
import Mettapedia.PLN.Evidence.BinaryEvidence
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNAlgorithmicAbductionBridge

/-!
# PLN-guided evolutionary selection

This module welds evolutionary/population fitness evidence onto the existing
PLN interval-ranking surface.  Selection is admissible only when an incumbent's
constructed fitness interval strictly dominates a candidate's interval.
-/

namespace Mettapedia.PLN.InferenceControl.EvolutionGuidance

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.TruthValues.PLNWeightTV

noncomputable section

/-! ## Fitness evidence and intervals -/

/-- Count evidence for a candidate or population fitness estimate. -/
structure FitnessEvidence where
  successes : ℕ
  failures : ℕ
  deriving Repr

namespace FitnessEvidence

/-- Total number of fitness observations. -/
def trials (e : FitnessEvidence) : ℕ :=
  e.successes + e.failures

/-- The binary-evidence carrier for the count record. -/
def toBinaryEvidence (e : FitnessEvidence) : BinaryEvidence where
  pos := (e.successes : ℝ≥0∞)
  neg := (e.failures : ℝ≥0∞)

end FitnessEvidence

/-- Fitness interval from count evidence using the existing Walley IDM
predictive ITV constructor. -/
def fitnessITV (s : ℝ) (hs : 0 < s) (e : FitnessEvidence) : ITV :=
  ITV.fromWalleyIDMPredictive e.toBinaryEvidence s hs

/-! ## Selection predicates -/

theorem priorWeightedLower_one (itv : ITV) :
    priorWeightedLower 1 itv = itv.lower := by
  simp [priorWeightedLower]

theorem priorWeightedUpper_one (itv : ITV) :
    priorWeightedUpper 1 itv = itv.upper := by
  simp [priorWeightedUpper]

theorem priorWeightedPoint_one (x : ℝ) :
    priorWeightedPoint 1 x = x := by
  simp [priorWeightedPoint]

/-- Weighted interval dominance, keeping the algorithmic-prior hook explicit. -/
def weightedIntervalDominanceSelection
    (incumbentPrior candidatePrior : ℝ)
    (incumbent candidate : ITV) : Prop :=
  priorWeightedIntervalStrictlyRanks
    incumbentPrior candidatePrior incumbent candidate

/-- Evolutionary interval dominance at unit priors. -/
def intervalDominanceSelection (incumbent candidate : ITV) : Prop :=
  weightedIntervalDominanceSelection 1 1 incumbent candidate

/-- Unit-prior interval overlap for evolutionary fitness intervals. -/
def fitnessIntervalsOverlap (x y : ITV) : Prop :=
  priorWeightedIntervalsOverlap 1 1 x y

theorem intervalDominanceSelection_iff_endpoint_lt
    (incumbent candidate : ITV) :
    intervalDominanceSelection incumbent candidate ↔
      candidate.upper < incumbent.lower := by
  simp [intervalDominanceSelection, weightedIntervalDominanceSelection,
    priorWeightedIntervalStrictlyRanks, priorWeightedLower_one,
    priorWeightedUpper_one]

theorem fitnessIntervalsOverlap_iff
    (x y : ITV) :
    fitnessIntervalsOverlap x y ↔
      x.lower ≤ y.upper ∧ y.lower ≤ x.upper := by
  simp [fitnessIntervalsOverlap, priorWeightedIntervalsOverlap,
    priorWeightedLower_one, priorWeightedUpper_one]

/-! ## Containment data -/

theorem itv_strength_mem_bounds (itv : ITV) :
    itv.lower ≤ itv.strength ∧ itv.strength ≤ itv.upper := by
  unfold ITV.strength
  constructor <;> nlinarith [itv.lower_le_upper]

/-- A constructed witness that the true fitness value under discussion lies
inside the fitness ITV derived from its evidence. -/
structure FitnessContainment (s : ℝ) (hs : 0 < s)
    (e : FitnessEvidence) where
  trueFitness : ℝ
  mem_fitnessITV :
    (fitnessITV s hs e).lower ≤ trueFitness ∧
      trueFitness ≤ (fitnessITV s hs e).upper

namespace FitnessContainment

/-- Constructor from an explicitly supplied interval point. -/
def ofIntervalPoint
    (s : ℝ) (hs : 0 < s) (e : FitnessEvidence)
    (x : ℝ)
    (hx : (fitnessITV s hs e).lower ≤ x ∧
      x ≤ (fitnessITV s hs e).upper) :
    FitnessContainment s hs e where
  trueFitness := x
  mem_fitnessITV := hx

/-- Midpoint witness.  This is a contained value, not a claim that the world
fitness is the midpoint. -/
def midpoint (s : ℝ) (hs : 0 < s) (e : FitnessEvidence) :
    FitnessContainment s hs e :=
  ofIntervalPoint s hs e (fitnessITV s hs e).strength
    (itv_strength_mem_bounds (fitnessITV s hs e))

end FitnessContainment

/-- A selection datum carries evidence and constructed containment witnesses
for both sides. -/
structure FitnessSelectionDatum (s : ℝ) (hs : 0 < s) where
  incumbentEvidence : FitnessEvidence
  candidateEvidence : FitnessEvidence
  incumbentContainment :
    FitnessContainment s hs incumbentEvidence
  candidateContainment :
    FitnessContainment s hs candidateEvidence

/-! ## S1: admissible dominance and overlap witnesses -/

/-- S1 crown: strict interval dominance makes discarding the candidate safe
relative to the supplied containment witnesses. -/
theorem intervalDominanceSelection_admissible
    {s : ℝ} {hs : 0 < s} (d : FitnessSelectionDatum s hs)
    (hRank :
      intervalDominanceSelection
        (fitnessITV s hs d.incumbentEvidence)
        (fitnessITV s hs d.candidateEvidence)) :
    d.candidateContainment.trueFitness <
      d.incumbentContainment.trueFitness := by
  have hPoint :=
    priorWeightedIntervalStrictlyRanks_point_lt
      (betterPrior := 1) (worsePrior := 1)
      (better := fitnessITV s hs d.incumbentEvidence)
      (worse := fitnessITV s hs d.candidateEvidence)
      (betterPoint := d.incumbentContainment.trueFitness)
      (worsePoint := d.candidateContainment.trueFitness)
      (by norm_num) (by norm_num)
      (by
        simpa [intervalDominanceSelection,
          weightedIntervalDominanceSelection] using hRank)
      d.incumbentContainment.mem_fitnessITV
      d.candidateContainment.mem_fitnessITV
  simpa [priorWeightedPoint_one] using hPoint

/-- If intervals overlap, there are contained values where the candidate ties
or beats the incumbent; a discard is therefore not forced by interval evidence
alone. -/
theorem overlap_no_forced_discard
    (incumbent candidate : ITV)
    (hOverlap : fitnessIntervalsOverlap incumbent candidate) :
    ∃ incumbentFitness candidateFitness,
      incumbent.lower ≤ incumbentFitness ∧
        incumbentFitness ≤ incumbent.upper ∧
        candidate.lower ≤ candidateFitness ∧
        candidateFitness ≤ candidate.upper ∧
        incumbentFitness ≤ candidateFitness := by
  rw [fitnessIntervalsOverlap_iff] at hOverlap
  let z := max incumbent.lower candidate.lower
  have hz_inc_lower : incumbent.lower ≤ z := le_max_left _ _
  have hz_cand_lower : candidate.lower ≤ z := le_max_right _ _
  have hz_inc_upper : z ≤ incumbent.upper :=
    max_le incumbent.lower_le_upper hOverlap.2
  have hz_cand_upper : z ≤ candidate.upper :=
    max_le hOverlap.1 candidate.lower_le_upper
  exact ⟨z, z, hz_inc_lower, hz_inc_upper,
    hz_cand_lower, hz_cand_upper, le_rfl⟩

/-- Interior overlap gives a contained witness where the candidate can be
strictly better than the incumbent. -/
theorem candidate_can_strictly_win_of_interior_overlap
    (incumbent candidate : ITV)
    (hLeft : incumbent.lower < candidate.upper)
    (_hRight : candidate.lower < incumbent.upper) :
    ∃ incumbentFitness candidateFitness,
      incumbent.lower ≤ incumbentFitness ∧
        incumbentFitness ≤ incumbent.upper ∧
        candidate.lower ≤ candidateFitness ∧
        candidateFitness ≤ candidate.upper ∧
        incumbentFitness < candidateFitness := by
  by_cases hLower : incumbent.lower < candidate.lower
  · exact ⟨incumbent.lower, candidate.lower,
      le_rfl, incumbent.lower_le_upper, le_rfl,
      candidate.lower_le_upper, hLower⟩
  · have hCandLower_le : candidate.lower ≤ incumbent.lower :=
      le_of_not_gt hLower
    let witness := (incumbent.lower + candidate.upper) / 2
    have hInc_lt_witness : incumbent.lower < witness := by
      dsimp [witness]
      nlinarith
    have hWitness_le_cand_upper : witness ≤ candidate.upper := by
      dsimp [witness]
      nlinarith
    have hCand_lower_le_witness : candidate.lower ≤ witness :=
      le_trans hCandLower_le (le_of_lt hInc_lt_witness)
    exact ⟨incumbent.lower, witness,
      le_rfl, incumbent.lower_le_upper,
      hCand_lower_le_witness, hWitness_le_cand_upper,
      hInc_lt_witness⟩

/-! ## S2: width gaps, sampling budgets, and pooled evidence -/

/-- Difference between the midpoint strengths of the better and worse
intervals. -/
def midpointGap (better worse : ITV) : ℝ :=
  better.strength - worse.strength

/-- Total width carried by a two-candidate comparison. -/
def totalIntervalWidth (better worse : ITV) : ℝ :=
  better.width + worse.width

/-- S2 crown: strict endpoint ranking is exactly the arithmetic condition that
the total interval width is smaller than twice the midpoint gap. -/
theorem strictRanks_width_gap (better worse : ITV) :
    intervalDominanceSelection better worse ↔
      totalIntervalWidth better worse <
        2 * midpointGap better worse := by
  rw [intervalDominanceSelection_iff_endpoint_lt]
  unfold totalIntervalWidth midpointGap ITV.width ITV.strength
  constructor <;> intro h <;> nlinarith

theorem not_intervalDominanceSelection_of_width_gap_le
    (better worse : ITV)
    (hGap :
      2 * midpointGap better worse ≤ totalIntervalWidth better worse) :
    ¬ intervalDominanceSelection better worse := by
  intro hRank
  rw [strictRanks_width_gap] at hRank
  linarith

theorem fitnessITV_width_eq
    (s : ℝ) (hs : 0 < s) (e : FitnessEvidence) :
    (fitnessITV s hs e).width =
      s / ((e.trials : ℝ) + s) := by
  simp [fitnessITV, FitnessEvidence.toBinaryEvidence,
    FitnessEvidence.trials, ITV.fromWalleyIDMPredictive_width_eq,
    Nat.cast_add]

theorem fitnessITV_credibility_eq_w2c_trials_div_s
    (s : ℝ) (hs : 0 < s) (e : FitnessEvidence) :
    (fitnessITV s hs e).credibility =
      w2c ((e.trials : ℝ) / s) := by
  simp [fitnessITV, FitnessEvidence.toBinaryEvidence,
    FitnessEvidence.trials, ITV.fromWalleyIDMPredictive_credibility,
    w2c, Nat.cast_add]
  field_simp [hs.ne']

theorem fitnessITV_width_eq_one_sub_w2c_trials_div_s
    (s : ℝ) (hs : 0 < s) (e : FitnessEvidence) :
    (fitnessITV s hs e).width =
      1 - w2c ((e.trials : ℝ) / s) := by
  have hsum :
      (fitnessITV s hs e).width + (fitnessITV s hs e).credibility = 1 := by
    simpa [fitnessITV] using
      ITV.fromWalleyIDMPredictive_width_add_credibility
        e.toBinaryEvidence s hs
  rw [fitnessITV_credibility_eq_w2c_trials_div_s] at hsum
  linarith

theorem width_lt_gap_of_trials_gt
    {s gap : ℝ} {n : ℕ}
    (hs : 0 < s) (hgap : 0 < gap)
    (hn : s / gap - s < (n : ℝ)) :
    s / ((n : ℝ) + s) < gap := by
  have hden_pos : 0 < (n : ℝ) + s := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsum : s / gap < (n : ℝ) + s := by
    linarith
  have hmul : s < gap * ((n : ℝ) + s) := by
    have hmul' := (div_lt_iff₀ hgap).mp hsum
    simpa [mul_comm] using hmul'
  exact (div_lt_iff₀ hden_pos).2 hmul

theorem sameTrials_totalIntervalWidth_eq
    {s : ℝ} {hs : 0 < s} {n : ℕ}
    (better worse : FitnessEvidence)
    (hBetter : better.trials = n)
    (hWorse : worse.trials = n) :
    totalIntervalWidth (fitnessITV s hs better) (fitnessITV s hs worse) =
      2 * (s / ((n : ℝ) + s)) := by
  simp [totalIntervalWidth, fitnessITV_width_eq, hBetter, hWorse]
  ring

/-- S2 crown: if the equal-trial evidence budget is above the threshold
`s / gap - s`, and the observed midpoint gap is at least `gap`, the Walley
fitness intervals strictly rank. -/
theorem minTrials_for_ranking
    {s gap : ℝ} {hs : 0 < s} {n : ℕ}
    (hgap : 0 < gap)
    (hn : s / gap - s < (n : ℝ))
    (better worse : FitnessEvidence)
    (hBetter : better.trials = n)
    (hWorse : worse.trials = n)
    (hMid :
      gap ≤ midpointGap (fitnessITV s hs better) (fitnessITV s hs worse)) :
    intervalDominanceSelection
      (fitnessITV s hs better) (fitnessITV s hs worse) := by
  rw [strictRanks_width_gap]
  rw [sameTrials_totalIntervalWidth_eq better worse hBetter hWorse]
  have hwidth := width_lt_gap_of_trials_gt hs hgap hn
  nlinarith

/-- Pool a finite family of child evaluation records by adding all counts. -/
def pooledChildrenEvidence {n : ℕ}
    (children : Fin n → FitnessEvidence) : FitnessEvidence where
  successes := Finset.univ.sum fun i => (children i).successes
  failures := Finset.univ.sum fun i => (children i).failures

theorem child_trials_le_pooledChildren_trials
    {n : ℕ} (children : Fin n → FitnessEvidence) (i : Fin n) :
    (children i).trials ≤ (pooledChildrenEvidence children).trials := by
  unfold pooledChildrenEvidence FitnessEvidence.trials
  change (children i).successes + (children i).failures ≤
    (Finset.univ.sum fun j : Fin n => (children j).successes) +
      (Finset.univ.sum fun j : Fin n => (children j).failures)
  have hSucc :
      (children i).successes ≤
        Finset.univ.sum fun j : Fin n => (children j).successes :=
    by
      have hSucc' :
          (fun j : Fin n => (children j).successes) i ≤
            Finset.univ.sum (fun j : Fin n => (children j).successes) :=
        by
          simpa using
            (Finset.single_le_sum
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => (children j).successes)
              (by intro j _hj; exact Nat.zero_le _)
              (Finset.mem_univ i))
      simpa using hSucc'
  have hFail :
      (children i).failures ≤
        Finset.univ.sum fun j : Fin n => (children j).failures :=
    by
      have hFail' :
          (fun j : Fin n => (children j).failures) i ≤
            Finset.univ.sum (fun j : Fin n => (children j).failures) :=
        by
          simpa using
            (Finset.single_le_sum
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => (children j).failures)
              (by intro j _hj; exact Nat.zero_le _)
              (Finset.mem_univ i))
      simpa using hFail'
  omega

theorem walleyConfidence_mono_trials
    {s : ℝ} (hs : 0 < s) {m n : ℕ} (hmn : m ≤ n) :
    (m : ℝ) / ((m : ℝ) + s) ≤
      (n : ℝ) / ((n : ℝ) + s) := by
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden_m : 0 < (m : ℝ) + s := by linarith
  have hden_n : 0 < (n : ℝ) + s := by linarith
  rw [div_le_div_iff₀ hden_m hden_n]
  have hmn_real : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  nlinarith

theorem fitnessITV_credibility_mono_trials
    {s : ℝ} {hs : 0 < s} {x y : FitnessEvidence}
    (hTrials : x.trials ≤ y.trials) :
    (fitnessITV s hs x).credibility ≤
      (fitnessITV s hs y).credibility := by
  simpa [fitnessITV, FitnessEvidence.toBinaryEvidence,
    FitnessEvidence.trials, ITV.fromWalleyIDMPredictive_credibility,
    Nat.cast_add] using
    (walleyConfidence_mono_trials (s := s) hs
      (m := x.trials) (n := y.trials) hTrials)

/-- S2 crown: pooling all child counts has at least the confidence of any one
child count record.  This is only a confidence/width statement; it makes no
claim about the bias of max-child scoring. -/
theorem pooledChildren_confidence_ge_best_child
    {s : ℝ} {hs : 0 < s} {n : ℕ}
    (children : Fin n → FitnessEvidence) (i : Fin n) :
    (fitnessITV s hs (children i)).credibility ≤
      (fitnessITV s hs (pooledChildrenEvidence children)).credibility :=
  fitnessITV_credibility_mono_trials
    (child_trials_le_pooledChildren_trials children i)

end

end Mettapedia.PLN.InferenceControl.EvolutionGuidance
