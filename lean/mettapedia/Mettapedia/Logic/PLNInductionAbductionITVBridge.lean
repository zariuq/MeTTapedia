import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNDeductionITVBridge

/-!
# PLN Induction and Abduction Credal Intervals

This file lifts the PLN source-rule and sink-rule point formulas into the
existing no-independence deduction ITV surface.  It does not define another
interval semantics: induction and abduction are Bayes-inversion presentations
of deduction, and the credal envelope is the one from `PLNDeductionITVBridge`.
-/

namespace Mettapedia.Logic.PLN

open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLNIndefiniteTruth

/-- Source-rule induction as the existing deduction credal interval after
Bayes-inverting `B → A` into the induced `A → B` coordinate. -/
noncomputable def plnInductionCredalStrengthITV
    (sBA sBC pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        (bayesInversion sBA pA pB) sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    ITV :=
  deductionCredalStrengthITV
    pA pB pC (bayesInversion sBA pA pB) sBC
    hpA hFeas credibility hc

/-- Sink-rule abduction as the existing deduction credal interval after
Bayes-inverting `C → B` into the induced `B → C` coordinate. -/
noncomputable def plnAbductionCredalStrengthITV
    (sAB sCB pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        sAB (bayesInversion sCB pB pC))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    ITV :=
  deductionCredalStrengthITV
    pA pB pC sAB (bayesInversion sCB pB pC)
    hpA hFeas credibility hc

@[simp] theorem plnInductionCredalStrengthITV_lower
    (sBA sBC pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        (bayesInversion sBA pA pB) sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    (plnInductionCredalStrengthITV sBA sBC pA pB pC hpA hFeas
      credibility hc).lower =
      deductionCredalStrengthLower
        pA pB pC (bayesInversion sBA pA pB) sBC :=
  rfl

@[simp] theorem plnInductionCredalStrengthITV_upper
    (sBA sBC pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        (bayesInversion sBA pA pB) sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    (plnInductionCredalStrengthITV sBA sBC pA pB pC hpA hFeas
      credibility hc).upper =
      deductionCredalStrengthUpper
        pA pB pC (bayesInversion sBA pA pB) sBC :=
  rfl

@[simp] theorem plnInductionCredalStrengthITV_width
    (sBA sBC pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        (bayesInversion sBA pA pB) sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    (plnInductionCredalStrengthITV sBA sBC pA pB pC hpA hFeas
      credibility hc).width =
      deductionCredalStrengthUpper
          pA pB pC (bayesInversion sBA pA pB) sBC -
        deductionCredalStrengthLower
          pA pB pC (bayesInversion sBA pA pB) sBC :=
  rfl

@[simp] theorem plnAbductionCredalStrengthITV_lower
    (sAB sCB pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        sAB (bayesInversion sCB pB pC))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    (plnAbductionCredalStrengthITV sAB sCB pA pB pC hpA hFeas
      credibility hc).lower =
      deductionCredalStrengthLower
        pA pB pC sAB (bayesInversion sCB pB pC) :=
  rfl

@[simp] theorem plnAbductionCredalStrengthITV_upper
    (sAB sCB pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        sAB (bayesInversion sCB pB pC))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    (plnAbductionCredalStrengthITV sAB sCB pA pB pC hpA hFeas
      credibility hc).upper =
      deductionCredalStrengthUpper
        pA pB pC sAB (bayesInversion sCB pB pC) :=
  rfl

@[simp] theorem plnAbductionCredalStrengthITV_width
    (sAB sCB pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        sAB (bayesInversion sCB pB pC))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    (plnAbductionCredalStrengthITV sAB sCB pA pB pC hpA hFeas
      credibility hc).width =
      deductionCredalStrengthUpper
          pA pB pC sAB (bayesInversion sCB pB pC) -
        deductionCredalStrengthLower
          pA pB pC sAB (bayesInversion sCB pB pC) :=
  rfl

/-! ## Point-rule membership in the no-independence intervals -/

/-- On the guarded non-edge branch, the deduction implementation used by the
ITV bridge agrees with the raw PLN deduction formula in `PLNDerivation`.

This is only a seam lemma between the two existing deduction surfaces; the
substantive interval fact remains
`simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV`.
-/
theorem simpleDeductionStrengthFormula_eq_plnDeductionStrength_of_consistent
    (pA pB pC sAB sBC : ℝ)
    (hpB_small : pB ≤ 0.99)
    (h_consist : conditionalProbabilityConsistency pA pB sAB ∧
                 conditionalProbabilityConsistency pB pC sBC) :
    simpleDeductionStrengthFormula pA pB pC sAB sBC =
      plnDeductionStrength sAB sBC pB pC := by
  unfold simpleDeductionStrengthFormula plnDeductionStrength
  simp [h_consist]
  have hpB_not_edge : ¬pB > 0.99 := by linarith
  simp [hpB_not_edge]

/-- The PLN source-rule point value is a member of the existing
no-independence induction interval whenever the Bayes-inverted deduction
skeleton satisfies the same explicit admissibility hypotheses as deduction.

This is the rule-family version of the canary below: induction is not assigned
a new interval semantics; it inherits the deduction interval after the
`B → A` premise is Bayes-inverted into `A → B`. -/
theorem plnInductionStrength_mem_credalStrengthITV
    (sBA sBC pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        (bayesInversion sBA pA pB) sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB (bayesInversion sBA pA pB) ∧
        conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB (bayesInversion sBA pA pB) sBC ≤
        pA * (bayesInversion sBA pA pB) * sBC)
    (ht_upper :
      pA * (bayesInversion sBA pA pB) * sBC ≤
        deductionBBranchUpper pA pB (bayesInversion sBA pA pB) sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC (bayesInversion sBA pA pB) sBC ≤
        pA * (1 - bayesInversion sBA pA pB) *
          complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - bayesInversion sBA pA pB) *
          complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC (bayesInversion sBA pA pB) sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      plnInductionCredalStrengthITV
        sBA sBC pA pB pC hpA hFeas credibility hc
    itv.lower ≤ plnInductionStrength sBA sBC pA pB pC ∧
      plnInductionStrength sBA sBC pA pB pC ≤ itv.upper := by
  dsimp [plnInductionCredalStrengthITV]
  have hMem :=
    simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV
      pA pB pC (bayesInversion sBA pA pB) sBC
      hpA hpB_small hFeas h_consist
      ht_lower ht_upper hu_lower hu_upper credibility hc
  have hEq :
      simpleDeductionStrengthFormula
          pA pB pC (bayesInversion sBA pA pB) sBC =
        plnInductionStrength sBA sBC pA pB pC := by
    rw [simpleDeductionStrengthFormula_eq_plnDeductionStrength_of_consistent
      pA pB pC (bayesInversion sBA pA pB) sBC hpB_small h_consist]
    exact (plnInduction_eq_bayes_deduction sBA sBC pA pB pC).symm
  constructor
  · simpa [hEq] using hMem.1
  · simpa [hEq] using hMem.2

/-- The PLN sink-rule point value is a member of the existing no-independence
abduction interval whenever the Bayes-inverted deduction skeleton satisfies
the same explicit admissibility hypotheses as deduction.

This is the sink-rule dual of `plnInductionStrength_mem_credalStrengthITV`.
-/
theorem plnAbductionStrength_mem_credalStrengthITV
    (sAB sCB pA pB pC : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas :
      DeductionBranchFeasibility pA pB pC
        sAB (bayesInversion sCB pB pC))
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
        conditionalProbabilityConsistency pB pC (bayesInversion sCB pB pC))
    (ht_lower :
      deductionBBranchLower pA pB sAB (bayesInversion sCB pB pC) ≤
        pA * sAB * (bayesInversion sCB pB pC))
    (ht_upper :
      pA * sAB * (bayesInversion sCB pB pC) ≤
        deductionBBranchUpper pA pB sAB (bayesInversion sCB pB pC))
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB (bayesInversion sCB pB pC) ≤
        pA * (1 - sAB) *
          complementConditionalFromMarginal pB pC
            (bayesInversion sCB pB pC))
    (hu_upper :
      pA * (1 - sAB) *
          complementConditionalFromMarginal pB pC
            (bayesInversion sCB pB pC) ≤
        deductionNotBBranchUpper pA pB pC sAB
          (bayesInversion sCB pB pC))
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      plnAbductionCredalStrengthITV
        sAB sCB pA pB pC hpA hFeas credibility hc
    itv.lower ≤ plnAbductionStrength sAB sCB pA pB pC ∧
      plnAbductionStrength sAB sCB pA pB pC ≤ itv.upper := by
  dsimp [plnAbductionCredalStrengthITV]
  have hMem :=
    simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV
      pA pB pC sAB (bayesInversion sCB pB pC)
      hpA hpB_small hFeas h_consist
      ht_lower ht_upper hu_lower hu_upper credibility hc
  have hEq :
      simpleDeductionStrengthFormula
          pA pB pC sAB (bayesInversion sCB pB pC) =
        plnAbductionStrength sAB sCB pA pB pC := by
    rw [simpleDeductionStrengthFormula_eq_plnDeductionStrength_of_consistent
      pA pB pC sAB (bayesInversion sCB pB pC) hpB_small h_consist]
    exact (plnAbduction_eq_bayes_deduction sAB sCB pA pB pC).symm
  constructor
  · simpa [hEq] using hMem.1
  · simpa [hEq] using hMem.2

/-! ## Feasible asymmetry canary

The point-rule canary in `PLNDerivation` is lifted here to the
no-independence interval surface.  With `P(A)=P(C)=1/2`, `P(B)=3/4`,
and the same visible premise strengths `1/2, 1/2`, source-rule induction and
sink-rule abduction induce different feasible deduction skeletons:

* induction: `P(B|A)=3/4`, `P(C|B)=1/2`, interval `[0,1]`;
* abduction: `P(B|A)=1/2`, `P(C|B)=1/3`, interval `[1/2,1]`.
-/

theorem inductionAbductionAsymmetry_induction_feasible :
    DeductionBranchFeasibility
      (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)
      (bayesInversion (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ))
      (1 / 2 : ℝ) := by
  constructor <;> norm_num [DeductionBranchFeasibility,
    deductionJointAB, deductionJointBC, bayesInversion]

theorem inductionAbductionAsymmetry_abduction_feasible :
    DeductionBranchFeasibility
      (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)
      (1 / 2 : ℝ)
      (bayesInversion (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)) := by
  constructor <;> norm_num [DeductionBranchFeasibility,
    deductionJointAB, deductionJointBC, bayesInversion]

noncomputable def inductionAsymmetryITV : ITV :=
  plnInductionCredalStrengthITV
    (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)
    (by norm_num)
    inductionAbductionAsymmetry_induction_feasible
    1 (by norm_num)

noncomputable def abductionAsymmetryITV : ITV :=
  plnAbductionCredalStrengthITV
    (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)
    (by norm_num)
    inductionAbductionAsymmetry_abduction_feasible
    1 (by norm_num)

/-- The same visible premise strengths produce a fully open source-rule
interval but a tighter sink-rule interval under non-uniform base rates. -/
theorem plnInductionAbductionITV_asymmetric_canary :
    inductionAsymmetryITV.lower = (0 : ℝ) ∧
      inductionAsymmetryITV.upper = (1 : ℝ) ∧
      inductionAsymmetryITV.width = (1 : ℝ) ∧
      abductionAsymmetryITV.lower = (1 / 2 : ℝ) ∧
      abductionAsymmetryITV.upper = (1 : ℝ) ∧
      abductionAsymmetryITV.width = (1 / 2 : ℝ) ∧
      inductionAsymmetryITV.lower < abductionAsymmetryITV.lower := by
  norm_num [inductionAsymmetryITV, abductionAsymmetryITV,
    plnInductionCredalStrengthITV, plnAbductionCredalStrengthITV,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalStrengthUpper, deductionCredalJointLower,
    deductionCredalJointUpper, deductionBBranchLower,
    deductionBBranchUpper, deductionNotBBranchLower,
    deductionNotBBranchUpper, deductionJointAB, deductionJointBC,
    bayesInversion, ITV.width]

/-- The concrete source-rule and sink-rule point values are members of their
corresponding no-independence intervals.  This is the runnable-canary instance
of the general membership theorems above. -/
theorem plnInductionAbduction_point_values_mem_asymmetry_ITVs :
    inductionAsymmetryITV.lower ≤
        plnInductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ∧
      plnInductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ≤
        inductionAsymmetryITV.upper ∧
      abductionAsymmetryITV.lower ≤
        plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ) ≤
        abductionAsymmetryITV.upper := by
  have hInd :=
    plnInductionStrength_mem_credalStrengthITV
      (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)
      (by norm_num)
      (by norm_num)
      inductionAbductionAsymmetry_induction_feasible
      (by
        constructor <;>
          norm_num [conditionalProbabilityConsistency,
            smallestIntersectionProbability, largestIntersectionProbability,
            bayesInversion])
      (by
        norm_num [deductionBBranchLower, deductionJointAB, deductionJointBC,
          bayesInversion])
      (by
        norm_num [deductionBBranchUpper, deductionJointAB, deductionJointBC,
          bayesInversion])
      (by
        norm_num [deductionNotBBranchLower, deductionJointAB,
          deductionJointBC, complementConditionalFromMarginal,
          bayesInversion])
      (by
        norm_num [deductionNotBBranchUpper, deductionJointAB,
          deductionJointBC, complementConditionalFromMarginal,
          bayesInversion])
      1 (by norm_num)
  have hAbd :=
    plnAbductionStrength_mem_credalStrengthITV
      (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (1 / 2 : ℝ)
      (by norm_num)
      (by norm_num)
      inductionAbductionAsymmetry_abduction_feasible
      (by
        constructor <;>
          norm_num [conditionalProbabilityConsistency,
            smallestIntersectionProbability, largestIntersectionProbability,
            bayesInversion])
      (by
        norm_num [deductionBBranchLower, deductionJointAB, deductionJointBC,
          bayesInversion])
      (by
        norm_num [deductionBBranchUpper, deductionJointAB, deductionJointBC,
          bayesInversion])
      (by
        norm_num [deductionNotBBranchLower, deductionJointAB,
          deductionJointBC, complementConditionalFromMarginal,
          bayesInversion])
      (by
        norm_num [deductionNotBBranchUpper, deductionJointAB,
          deductionJointBC, complementConditionalFromMarginal,
          bayesInversion])
      1 (by norm_num)
  exact ⟨hInd.1, hInd.2, hAbd.1, hAbd.2⟩

/-! ## Abductive-search interval ranking

The next runnable search examples use the same abduction bridge, but read it as
candidate explanation ranking.  A point-valued abduction score is allowed to
suggest an ordering; the interval ordering is stricter and only ranks two
candidates when the worse candidate's upper endpoint is below the better
candidate's lower endpoint.
-/

/-- A candidate `better` is strictly preferred to `worse` only when their
honest credal intervals are separated. -/
def abductionIntervalStrictlyRanks (better worse : ITV) : Prop :=
  worse.upper < better.lower

/-- Two candidate intervals overlap when neither one separates cleanly from the
other.  This is the negative canary for point-only abductive ranking. -/
def abductionIntervalsOverlap (x y : ITV) : Prop :=
  x.lower ≤ y.upper ∧ y.lower ≤ x.upper

theorem abductionSearch_weak_feasible :
    DeductionBranchFeasibility
      (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ)
      (2 / 3 : ℝ)
      (bayesInversion (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ)) := by
  constructor <;> norm_num [DeductionBranchFeasibility,
    deductionJointAB, deductionJointBC, bayesInversion]

theorem abductionSearch_strong_feasible :
    DeductionBranchFeasibility
      (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)
      (2 / 3 : ℝ)
      (bayesInversion (2 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
  constructor <;> norm_num [DeductionBranchFeasibility,
    deductionJointAB, deductionJointBC, bayesInversion]

noncomputable def abductionSearchWeakITV : ITV :=
  plnAbductionCredalStrengthITV
    (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ)
    (by norm_num)
    abductionSearch_weak_feasible
    1 (by norm_num)

noncomputable def abductionSearchStrongITV : ITV :=
  plnAbductionCredalStrengthITV
    (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)
    (by norm_num)
    abductionSearch_strong_feasible
    1 (by norm_num)

/-- A positive abductive-search canary: with the same query prior and left
premise, the strong explanation has both a higher independence-point score and
a credal interval separated from the weak explanation. -/
theorem plnAbductionSearch_strict_interval_ranking_canary :
    abductionSearchWeakITV.lower = (0 : ℝ) ∧
      abductionSearchWeakITV.upper = (1 / 2 : ℝ) ∧
      abductionSearchStrongITV.lower = (2 / 3 : ℝ) ∧
      abductionSearchStrongITV.upper = (1 : ℝ) ∧
      abductionIntervalStrictlyRanks
        abductionSearchStrongITV abductionSearchWeakITV ∧
      plnAbductionStrength
        (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 4 : ℝ) =
        (1 / 4 : ℝ) ∧
      plnAbductionStrength
        (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (5 / 6 : ℝ) := by
  norm_num [abductionSearchWeakITV, abductionSearchStrongITV,
    abductionIntervalStrictlyRanks, plnAbductionCredalStrengthITV,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalStrengthUpper, deductionCredalJointLower,
    deductionCredalJointUpper, deductionBBranchLower,
    deductionBBranchUpper, deductionNotBBranchLower,
    deductionNotBBranchUpper, deductionJointAB, deductionJointBC,
    bayesInversion, plnAbductionStrength, plnDeductionStrength]

theorem abductionSearch_open_feasible :
    DeductionBranchFeasibility
      (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)
      (1 / 2 : ℝ)
      (bayesInversion (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) := by
  constructor <;> norm_num [DeductionBranchFeasibility,
    deductionJointAB, deductionJointBC, bayesInversion]

theorem abductionSearch_betterPoint_feasible :
    DeductionBranchFeasibility
      (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)
      (1 / 2 : ℝ)
      (bayesInversion (2 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) := by
  constructor <;> norm_num [DeductionBranchFeasibility,
    deductionJointAB, deductionJointBC, bayesInversion]

noncomputable def abductionSearchOpenITV : ITV :=
  plnAbductionCredalStrengthITV
    (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)
    (by norm_num)
    abductionSearch_open_feasible
    1 (by norm_num)

noncomputable def abductionSearchBetterPointITV : ITV :=
  plnAbductionCredalStrengthITV
    (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)
    (by norm_num)
    abductionSearch_betterPoint_feasible
    1 (by norm_num)

/-- A negative abductive-search canary: the second explanation has a better
point score, but the intervals overlap, so point-only ranking would overstate
what the evidence justifies. -/
theorem plnAbductionSearch_point_difference_not_interval_ranking_canary :
    plnAbductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
        (1 / 2 : ℝ) ∧
      plnAbductionStrength
        (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      abductionSearchOpenITV.lower = (0 : ℝ) ∧
      abductionSearchOpenITV.upper = (1 : ℝ) ∧
      abductionSearchBetterPointITV.lower = (1 / 2 : ℝ) ∧
      abductionSearchBetterPointITV.upper = (1 : ℝ) ∧
      abductionIntervalsOverlap
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ abductionIntervalStrictlyRanks
          abductionSearchBetterPointITV abductionSearchOpenITV ∧
      ¬ abductionIntervalStrictlyRanks
          abductionSearchOpenITV abductionSearchBetterPointITV := by
  norm_num [abductionSearchOpenITV, abductionSearchBetterPointITV,
    abductionIntervalsOverlap, abductionIntervalStrictlyRanks,
    plnAbductionCredalStrengthITV, deductionCredalStrengthITV,
    deductionCredalStrengthLower, deductionCredalStrengthUpper,
    deductionCredalJointLower, deductionCredalJointUpper,
    deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper,
    deductionJointAB, deductionJointBC, bayesInversion,
    plnAbductionStrength, plnDeductionStrength]

end Mettapedia.Logic.PLN
