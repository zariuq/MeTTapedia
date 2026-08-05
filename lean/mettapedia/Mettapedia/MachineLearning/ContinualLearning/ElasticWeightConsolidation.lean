import Mettapedia.MachineLearning.ContinualLearning.FisherRetentionBridge

/-!
# Elastic-weight consolidation as additive information

Kirkpatrick et al., *Overcoming Catastrophic Forgetting in Neural Networks*
(2016), Equation (3), use a diagonal Fisher-weighted quadratic penalty around
the previous task optimum.  They also observe that penalties from multiple
tasks can be consolidated because a sum of quadratics is again quadratic.

This file makes that consolidation exact for one diagonal coordinate.  Two
anchored penalties combine into a total precision, a precision-weighted
anchor, and a parameter-independent disagreement constant.  The same
calculation gives the unique solution of a quadratic new task plus an old-task
EWC penalty.  Since a diagonal model is a sum of independent coordinates,
these scalar identities are its reusable algebraic core.

The Fisher/Laplace interpretation is local.  Zero precision provides no
retention force, and negative "precision" ceases to be a penalty; both
boundaries are recorded explicitly.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace ElasticWeightConsolidation

/-- One coordinate of Equation (3), with `precision` absorbing the source's
regularization multiplier and diagonal Fisher entry. -/
noncomputable def penalty
    (precision anchor parameter : ℝ) : ℝ :=
  precision / 2 * (parameter - anchor) ^ 2

/-- Precision of two consolidated quadratic penalties. -/
noncomputable def fusedPrecision
    (firstPrecision secondPrecision : ℝ) : ℝ :=
  firstPrecision + secondPrecision

/-- Information-weighted anchor of two penalties. -/
noncomputable def fusedAnchor
    (firstPrecision firstAnchor secondPrecision secondAnchor : ℝ) : ℝ :=
  (firstPrecision * firstAnchor + secondPrecision * secondAnchor) /
    fusedPrecision firstPrecision secondPrecision

/-- Parameter-independent cost incurred when two task anchors disagree. -/
noncomputable def fusionConstant
    (firstPrecision firstAnchor secondPrecision secondAnchor : ℝ) : ℝ :=
  firstPrecision * secondPrecision /
      (2 * fusedPrecision firstPrecision secondPrecision) *
    (firstAnchor - secondAnchor) ^ 2

/-- Exact source consolidation: a pair of EWC penalties is one fused penalty
plus a constant independent of the candidate parameter. -/
theorem penalty_add_eq_fusedPenalty_add_constant
    (firstPrecision firstAnchor secondPrecision secondAnchor parameter : ℝ)
    (totalNonzero :
      fusedPrecision firstPrecision secondPrecision ≠ 0) :
    penalty firstPrecision firstAnchor parameter +
        penalty secondPrecision secondAnchor parameter =
      penalty (fusedPrecision firstPrecision secondPrecision)
          (fusedAnchor firstPrecision firstAnchor
            secondPrecision secondAnchor)
          parameter +
        fusionConstant firstPrecision firstAnchor
          secondPrecision secondAnchor := by
  unfold fusedPrecision at totalNonzero
  unfold penalty fusedAnchor fusionConstant fusedPrecision
  field_simp [totalNonzero]
  ring

/-- The fused anchor satisfies the weighted stationarity equation. -/
theorem fusedAnchor_stationary
    (firstPrecision firstAnchor secondPrecision secondAnchor : ℝ)
    (totalNonzero :
      fusedPrecision firstPrecision secondPrecision ≠ 0) :
    firstPrecision *
          (fusedAnchor firstPrecision firstAnchor
            secondPrecision secondAnchor - firstAnchor) +
        secondPrecision *
          (fusedAnchor firstPrecision firstAnchor
            secondPrecision secondAnchor - secondAnchor) =
      0 := by
  unfold fusedPrecision at totalNonzero
  unfold fusedAnchor fusedPrecision
  field_simp [totalNonzero]
  ring

/-- Nonnegative source precisions give a nonnegative disagreement constant. -/
theorem fusionConstant_nonnegative
    (firstPrecision firstAnchor secondPrecision secondAnchor : ℝ)
    (firstNonnegative : 0 ≤ firstPrecision)
    (secondNonnegative : 0 ≤ secondPrecision)
    (somePrecision : 0 < firstPrecision + secondPrecision) :
    0 ≤ fusionConstant firstPrecision firstAnchor
      secondPrecision secondAnchor := by
  unfold fusionConstant fusedPrecision
  positivity

/-- The scalar sufficient statistic for a consolidated EWC penalty:
`information = precision * anchor`.  These are natural Gaussian-information
coordinates and add without retaining every task anchor. -/
structure Information where
  precision : ℝ
  weightedAnchor : ℝ

namespace Information

@[ext] theorem ext'
    (first second : Information)
    (precisionEqual : first.precision = second.precision)
    (weightedAnchorEqual :
      first.weightedAnchor = second.weightedAnchor) :
    first = second := by
  cases first
  cases second
  simp_all

instance : Zero Information := ⟨⟨0, 0⟩⟩

instance : Add Information where
  add first second :=
    ⟨first.precision + second.precision,
      first.weightedAnchor + second.weightedAnchor⟩

@[simp] theorem zero_precision : (0 : Information).precision = 0 := rfl

@[simp] theorem zero_weightedAnchor :
    (0 : Information).weightedAnchor = 0 := rfl

@[simp] theorem add_precision (first second : Information) :
    (first + second).precision =
      first.precision + second.precision := rfl

@[simp] theorem add_weightedAnchor (first second : Information) :
    (first + second).weightedAnchor =
      first.weightedAnchor + second.weightedAnchor := rfl

instance : AddCommMonoid Information where
  zero_add information := by
    apply Information.ext' <;> simp
  add_zero information := by
    apply Information.ext' <;> simp
  add_assoc first second third := by
    apply Information.ext' <;> simp [add_assoc]
  add_comm first second := by
    apply Information.ext' <;> simp [add_comm]
  nsmul := nsmulRec

/-- Convert a precision/anchor pair to additive information coordinates. -/
noncomputable def ofAnchor (precision anchor : ℝ) : Information :=
  ⟨precision, precision * anchor⟩

/-- Recover the consolidated anchor when total precision is nonzero. -/
noncomputable def anchor (information : Information) : ℝ :=
  information.weightedAnchor / information.precision

@[simp] theorem ofAnchor_precision (precision anchor : ℝ) :
    (ofAnchor precision anchor).precision = precision := rfl

@[simp] theorem ofAnchor_weightedAnchor (precision anchor : ℝ) :
    (ofAnchor precision anchor).weightedAnchor =
      precision * anchor := rfl

/-- Adding information packets recovers the source's fused precision. -/
theorem ofAnchor_add_precision
    (firstPrecision firstAnchor secondPrecision secondAnchor : ℝ) :
    (ofAnchor firstPrecision firstAnchor +
      ofAnchor secondPrecision secondAnchor).precision =
        fusedPrecision firstPrecision secondPrecision := rfl

/-- Adding information packets recovers the source's fused anchor. -/
theorem anchor_ofAnchor_add
    (firstPrecision firstAnchor secondPrecision secondAnchor : ℝ) :
    anchor
        (ofAnchor firstPrecision firstAnchor +
          ofAnchor secondPrecision secondAnchor) =
      fusedAnchor firstPrecision firstAnchor
        secondPrecision secondAnchor := by
  rfl

end Information

/-! ## Quadratic new-task solution -/

/-- A quadratic new-task model plus the old-task EWC penalty. -/
noncomputable def twoTaskObjective
    (newCurvature newAnchor oldPrecision oldAnchor parameter : ℝ) : ℝ :=
  penalty newCurvature newAnchor parameter +
    penalty oldPrecision oldAnchor parameter

/-- Closed-form consolidated parameter. -/
noncomputable def consolidatedParameter
    (newCurvature newAnchor oldPrecision oldAnchor : ℝ) : ℝ :=
  fusedAnchor newCurvature newAnchor oldPrecision oldAnchor

/-- The combined objective is a positive quadratic around the consolidated
parameter plus a constant. -/
theorem twoTaskObjective_eq_consolidated
    (newCurvature newAnchor oldPrecision oldAnchor parameter : ℝ)
    (totalNonzero : newCurvature + oldPrecision ≠ 0) :
    twoTaskObjective newCurvature newAnchor
        oldPrecision oldAnchor parameter =
      penalty (newCurvature + oldPrecision)
          (consolidatedParameter newCurvature newAnchor
            oldPrecision oldAnchor)
          parameter +
        fusionConstant newCurvature newAnchor
          oldPrecision oldAnchor := by
  exact penalty_add_eq_fusedPenalty_add_constant
    newCurvature newAnchor oldPrecision oldAnchor parameter totalNonzero

/-- With positive total curvature, the consolidated parameter globally
minimizes the two-task quadratic objective. -/
theorem consolidatedParameter_minimizes
    (newCurvature newAnchor oldPrecision oldAnchor candidate : ℝ)
    (totalPositive : 0 < newCurvature + oldPrecision) :
    twoTaskObjective newCurvature newAnchor oldPrecision oldAnchor
        (consolidatedParameter newCurvature newAnchor
          oldPrecision oldAnchor) ≤
      twoTaskObjective newCurvature newAnchor
        oldPrecision oldAnchor candidate := by
  have totalNonzero : newCurvature + oldPrecision ≠ 0 :=
    ne_of_gt totalPositive
  rw [twoTaskObjective_eq_consolidated _ _ _ _ _ totalNonzero,
    twoTaskObjective_eq_consolidated _ _ _ _ _ totalNonzero]
  unfold penalty
  have squareNonnegative :
      0 ≤
        (candidate -
          consolidatedParameter newCurvature newAnchor
            oldPrecision oldAnchor) ^ 2 :=
    sq_nonneg _
  nlinarith

/-- The global minimizer is unique when total curvature is positive. -/
theorem consolidatedParameter_unique
    (newCurvature newAnchor oldPrecision oldAnchor candidate : ℝ)
    (totalPositive : 0 < newCurvature + oldPrecision)
    (sameObjective :
      twoTaskObjective newCurvature newAnchor oldPrecision oldAnchor
          candidate =
        twoTaskObjective newCurvature newAnchor oldPrecision oldAnchor
          (consolidatedParameter newCurvature newAnchor
            oldPrecision oldAnchor)) :
    candidate =
      consolidatedParameter newCurvature newAnchor
        oldPrecision oldAnchor := by
  have totalNonzero : newCurvature + oldPrecision ≠ 0 :=
    ne_of_gt totalPositive
  rw [twoTaskObjective_eq_consolidated _ _ _ _ _ totalNonzero,
    twoTaskObjective_eq_consolidated _ _ _ _ _ totalNonzero] at sameObjective
  unfold penalty at sameObjective
  have squareZero :
      (candidate -
        consolidatedParameter newCurvature newAnchor
          oldPrecision oldAnchor) ^ 2 = 0 := by
    nlinarith
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp squareZero)

/-- With no old-task precision, the new-task optimum is recovered exactly. -/
@[simp] theorem consolidatedParameter_zeroOldPrecision
    (newCurvature newAnchor oldAnchor : ℝ)
    (newCurvatureNonzero : newCurvature ≠ 0) :
    consolidatedParameter newCurvature newAnchor 0 oldAnchor =
      newAnchor := by
  unfold consolidatedParameter fusedAnchor fusedPrecision
  field_simp [newCurvatureNonzero]
  ring

/-- With no new-task curvature, the old anchor is retained exactly. -/
@[simp] theorem consolidatedParameter_zeroNewCurvature
    (newAnchor oldPrecision oldAnchor : ℝ)
    (oldPrecisionNonzero : oldPrecision ≠ 0) :
    consolidatedParameter 0 newAnchor oldPrecision oldAnchor =
      oldAnchor := by
  unfold consolidatedParameter fusedAnchor fusedPrecision
  field_simp [oldPrecisionNonzero]
  ring

/-! ## Executable fixtures and boundaries -/

/-- Equal precision at anchors zero and two consolidates at one, with a
unit disagreement constant. -/
theorem equalPrecision_fusion (parameter : ℝ) :
    penalty 1 0 parameter + penalty 1 2 parameter =
      penalty 2 1 parameter + 1 := by
  norm_num [penalty]
  ring

theorem threeToOne_precision_solution :
    consolidatedParameter 1 2 3 0 = 1 / 2 := by
  norm_num [consolidatedParameter, fusedAnchor, fusedPrecision]

/-- A zero Fisher entry exerts no retention force at any displacement. -/
theorem zeroPrecision_does_not_protect (anchor parameter : ℝ) :
    penalty 0 anchor parameter = 0 := by
  simp [penalty]

/-- Negative "precision" is not a penalty: moving away can lower its value. -/
theorem negativePrecision_lowers_objective :
    penalty (-1) 0 2 < penalty (-1) 0 0 := by
  norm_num [penalty]

#print axioms penalty_add_eq_fusedPenalty_add_constant
#print axioms fusedAnchor_stationary
#print axioms fusionConstant_nonnegative
#print axioms Information.anchor_ofAnchor_add
#print axioms consolidatedParameter_minimizes
#print axioms consolidatedParameter_unique
#print axioms equalPrecision_fusion
#print axioms zeroPrecision_does_not_protect
#print axioms negativePrecision_lowers_objective

end ElasticWeightConsolidation

end Mettapedia.MachineLearning.ContinualLearning
