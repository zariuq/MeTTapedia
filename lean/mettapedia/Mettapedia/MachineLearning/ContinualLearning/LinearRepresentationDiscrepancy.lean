import Mathlib

/-!
# Linear representation discrepancy

Kim, Kim, and Sohn, *Measuring Representational Shifts in Continual Learning:
A Linear Transformation Perspective* (ICML 2025, arXiv:2505.20970), define
representation discrepancy by minimizing an alignment error over linear
transformations.  Their Lemma 2 bounds the reduced alignment objective

`c₁ ‖X‖ + c₂ ‖X - A‖`

using the witness `X = c₂² / (c₁² + c₂²) • A`.  This file proves that bound
for every real normed space, rather than only for square matrices.

The resulting dimensionless shape is

`f(ω) = (ω² + ω) / (ω² + 1)`.

We additionally determine its exact global maximum, its unique maximizer,
and an explicit saturation error.  The exact maximum is
`(1 + √2) / 2`, attained at `ω = 1 + √2`.  Consequently the larger value
`1 + √2 / 4` displayed as the peak in Proposition 1 of the source is not
attained by its stated shape function.  This distinction matters when the
bound is used to set a finite representation-drift budget.

The witness is only an upper-bound construction for the nonsquared norm
objective.  A scalar counterexample below shows that it need not minimize
that objective.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace LinearRepresentationDiscrepancy

noncomputable section

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- The reduced alignment objective from Lemma 2 of the source. -/
def alignmentObjective
    (firstWeight secondWeight : ℝ) (aligned reference : State) : ℝ :=
  firstWeight * ‖aligned‖ + secondWeight * ‖aligned - reference‖

/-- The infimum form of the reduced representation-alignment discrepancy. -/
def alignmentDiscrepancy
    (firstWeight secondWeight : ℝ) (reference : State) : ℝ :=
  sInf
    (Set.range
      (fun aligned =>
        alignmentObjective firstWeight secondWeight aligned reference))

/-- The explicit suboptimal witness used to prove the source bound. -/
def witnessCoefficient (firstWeight secondWeight : ℝ) : ℝ :=
  secondWeight ^ 2 / (firstWeight ^ 2 + secondWeight ^ 2)

/-- Scale the reference by the source's witness coefficient. -/
def alignmentWitness
    (firstWeight secondWeight : ℝ) (reference : State) : State :=
  witnessCoefficient firstWeight secondWeight • reference

/-- The dimensionless factor appearing in the source's Theorem 1. -/
def alignmentShape (ratio : ℝ) : ℝ :=
  (ratio ^ 2 + ratio) / (ratio ^ 2 + 1)

omit [NormedSpace ℝ State] in
/-- Nonnegative weights make every alignment cost nonnegative. -/
theorem alignmentObjective_nonnegative
    {firstWeight secondWeight : ℝ}
    (first_nonnegative : 0 ≤ firstWeight)
    (second_nonnegative : 0 ≤ secondWeight)
    (aligned reference : State) :
    0 ≤ alignmentObjective
      firstWeight secondWeight aligned reference := by
  exact
    add_nonneg
      (mul_nonneg first_nonnegative (norm_nonneg _))
      (mul_nonneg second_nonnegative (norm_nonneg _))

omit [NormedSpace ℝ State] in
/-- The infimum is bounded above by every concrete alignment. -/
theorem alignmentDiscrepancy_le_objective
    {firstWeight secondWeight : ℝ}
    (first_nonnegative : 0 ≤ firstWeight)
    (second_nonnegative : 0 ≤ secondWeight)
    (aligned reference : State) :
    alignmentDiscrepancy firstWeight secondWeight reference ≤
      alignmentObjective firstWeight secondWeight aligned reference := by
  unfold alignmentDiscrepancy
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro value ⟨point, rfl⟩
    exact
      alignmentObjective_nonnegative
        first_nonnegative second_nonnegative point reference
  · exact ⟨aligned, rfl⟩

/-- Positive weights give a positive denominator to the witness. -/
theorem weightSquares_add_pos
    {firstWeight secondWeight : ℝ}
    (first_positive : 0 < firstWeight)
    (second_positive : 0 < secondWeight) :
    0 < firstWeight ^ 2 + secondWeight ^ 2 := by
  positivity

/-- The source witness coefficient is nonnegative. -/
theorem witnessCoefficient_nonnegative
    {firstWeight secondWeight : ℝ}
    (first_positive : 0 < firstWeight)
    (second_positive : 0 < secondWeight) :
    0 ≤ witnessCoefficient firstWeight secondWeight := by
  unfold witnessCoefficient
  positivity

/-- The source witness coefficient is at most one. -/
theorem witnessCoefficient_le_one
    {firstWeight secondWeight : ℝ}
    (first_positive : 0 < firstWeight)
    (second_positive : 0 < secondWeight) :
    witnessCoefficient firstWeight secondWeight ≤ 1 := by
  unfold witnessCoefficient
  apply
    (div_le_one
      (weightSquares_add_pos first_positive second_positive)).2
  nlinarith [sq_nonneg firstWeight]

/-- Exact value of the alignment objective at the source witness. -/
theorem alignmentObjective_witness_eq
    {firstWeight secondWeight : ℝ}
    (first_positive : 0 < firstWeight)
    (second_positive : 0 < secondWeight)
    (reference : State) :
    alignmentObjective firstWeight secondWeight
        (alignmentWitness firstWeight secondWeight reference) reference =
      (firstWeight * secondWeight * (firstWeight + secondWeight) /
          (firstWeight ^ 2 + secondWeight ^ 2)) *
        ‖reference‖ := by
  have coefficient_nonnegative :=
    witnessCoefficient_nonnegative first_positive second_positive
  have coefficient_le_one :=
    witnessCoefficient_le_one first_positive second_positive
  rw [alignmentObjective, alignmentWitness, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg coefficient_nonnegative]
  have subtraction :
      witnessCoefficient firstWeight secondWeight • reference - reference =
        (witnessCoefficient firstWeight secondWeight - 1) • reference := by
    rw [sub_smul, one_smul]
  rw [subtraction, norm_smul, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr coefficient_le_one)]
  unfold witnessCoefficient
  field_simp
  ring

/-- The dimensional coefficient is the source's shape evaluated at the
weight ratio. -/
theorem sourceBoundCoefficient_eq_shape
    {firstWeight secondWeight : ℝ}
    (first_positive : 0 < firstWeight)
    (second_positive : 0 < secondWeight) :
    firstWeight * secondWeight * (firstWeight + secondWeight) /
        (firstWeight ^ 2 + secondWeight ^ 2) =
      secondWeight * alignmentShape (firstWeight / secondWeight) := by
  have second_ne : secondWeight ≠ 0 := ne_of_gt second_positive
  have denominator_ne :
      firstWeight ^ 2 + secondWeight ^ 2 ≠ 0 :=
    ne_of_gt (weightSquares_add_pos first_positive second_positive)
  unfold alignmentShape
  field_simp

/-- Normed-space generalization of the source's Lemma 2 bound. -/
theorem alignmentDiscrepancy_le_sourceBound
    {firstWeight secondWeight : ℝ}
    (first_positive : 0 < firstWeight)
    (second_positive : 0 < secondWeight)
    (reference : State) :
    alignmentDiscrepancy firstWeight secondWeight reference ≤
      secondWeight * alignmentShape (firstWeight / secondWeight) *
        ‖reference‖ := by
  calc
    alignmentDiscrepancy firstWeight secondWeight reference ≤
        alignmentObjective firstWeight secondWeight
          (alignmentWitness firstWeight secondWeight reference)
          reference :=
      alignmentDiscrepancy_le_objective
        (le_of_lt first_positive) (le_of_lt second_positive) _ _
    _ =
        (firstWeight * secondWeight * (firstWeight + secondWeight) /
            (firstWeight ^ 2 + secondWeight ^ 2)) *
          ‖reference‖ :=
      alignmentObjective_witness_eq
        first_positive second_positive reference
    _ =
        secondWeight * alignmentShape (firstWeight / secondWeight) *
          ‖reference‖ := by
      rw [sourceBoundCoefficient_eq_shape first_positive second_positive]

/-- `√2` is strictly above one. -/
theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have square :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have nonnegative := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- `√2` is strictly below two. -/
theorem sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) := by
  have square :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have nonnegative := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- The exact global maximum of the source shape. -/
theorem alignmentShape_le_exactPeak (ratio : ℝ) :
    alignmentShape ratio ≤ (1 + Real.sqrt 2) / 2 := by
  let root : ℝ := Real.sqrt 2
  have root_square : root ^ 2 = 2 := by
    dsimp [root]
    norm_num
  have root_sub_one_nonnegative : 0 ≤ root - 1 :=
    sub_nonneg.mpr (le_of_lt one_lt_sqrt_two)
  have square_nonnegative :
      0 ≤
        (root - 1) *
          (ratio - (1 + root)) ^ 2 :=
    mul_nonneg root_sub_one_nonnegative (sq_nonneg _)
  have square_identity :
      2 *
          (((1 + root) / 2) * (ratio ^ 2 + 1) -
            (ratio ^ 2 + ratio)) =
        (root - 1) * (ratio - (1 + root)) ^ 2 := by
    nlinarith
  have multiplied_bound :
      ratio ^ 2 + ratio ≤
        ((1 + root) / 2) * (ratio ^ 2 + 1) := by
    nlinarith [square_nonnegative]
  have denominator_positive : 0 < ratio ^ 2 + 1 := by
    positivity
  rw [alignmentShape]
  exact (div_le_iff₀ denominator_positive).2 multiplied_bound

/-- The exact peak is attained. -/
theorem alignmentShape_at_exactPeak :
    alignmentShape (1 + Real.sqrt 2) =
      (1 + Real.sqrt 2) / 2 := by
  let root : ℝ := Real.sqrt 2
  have root_square : root ^ 2 = 2 := by
    dsimp [root]
    norm_num
  have denominator_ne : (1 + root) ^ 2 + 1 ≠ 0 := by
    positivity
  rw [alignmentShape]
  change
    ((1 + root) ^ 2 + (1 + root)) /
          ((1 + root) ^ 2 + 1) =
      _
  field_simp
  nlinarith

/-- The peak is unique. -/
theorem alignmentShape_eq_exactPeak_iff (ratio : ℝ) :
    alignmentShape ratio = (1 + Real.sqrt 2) / 2 ↔
      ratio = 1 + Real.sqrt 2 := by
  let root : ℝ := Real.sqrt 2
  have root_square : root ^ 2 = 2 := by
    dsimp [root]
    norm_num
  have root_sub_one_positive : 0 < root - 1 :=
    sub_pos.mpr one_lt_sqrt_two
  have denominator_positive : 0 < ratio ^ 2 + 1 := by
    positivity
  constructor
  · intro shape_eq
    have multiplied_eq :
        ratio ^ 2 + ratio =
          ((1 + root) / 2) * (ratio ^ 2 + 1) := by
      rw [alignmentShape] at shape_eq
      exact (div_eq_iff (ne_of_gt denominator_positive)).mp shape_eq
    have square_identity :
        2 *
            (((1 + root) / 2) * (ratio ^ 2 + 1) -
              (ratio ^ 2 + ratio)) =
          (root - 1) * (ratio - (1 + root)) ^ 2 := by
      nlinarith
    have square_zero : (ratio - (1 + root)) ^ 2 = 0 := by
      nlinarith
    nlinarith
  · rintro rfl
    exact alignmentShape_at_exactPeak

/-- Exact deviation of the shape from its asymptotic value. -/
theorem alignmentShape_sub_one (ratio : ℝ) :
    alignmentShape ratio - 1 =
      (ratio - 1) / (ratio ^ 2 + 1) := by
  unfold alignmentShape
  have denominator_ne : ratio ^ 2 + 1 ≠ 0 := by
    positivity
  field_simp
  ring

/-- Beyond ratio one, the shape lies above its limiting value. -/
theorem one_le_alignmentShape
    {ratio : ℝ} (ratio_at_least_one : 1 ≤ ratio) :
    1 ≤ alignmentShape ratio := by
  rw [← sub_nonneg, alignmentShape_sub_one]
  exact
    div_nonneg
      (sub_nonneg.mpr ratio_at_least_one)
      (by positivity)

/-- A finite saturation certificate: after ratio one, the excess over the
limit is at most the reciprocal ratio. -/
theorem alignmentShape_sub_one_le_inv
    {ratio : ℝ} (ratio_at_least_one : 1 ≤ ratio) :
    alignmentShape ratio - 1 ≤ 1 / ratio := by
  have ratio_positive : 0 < ratio :=
    lt_of_lt_of_le zero_lt_one ratio_at_least_one
  rw [alignmentShape_sub_one]
  apply
    (div_le_div_iff₀
      (show 0 < ratio ^ 2 + 1 by positivity)
      ratio_positive).2
  nlinarith

/-- The peak value printed in Proposition 1 is strictly above the exact
maximum of its stated shape function. -/
theorem exactPeak_lt_sourceDisplayedPeak :
    (1 + Real.sqrt 2) / 2 <
      1 + Real.sqrt 2 / 4 := by
  nlinarith [sqrt_two_lt_two]

/-- Therefore the source-displayed value is not attained by the stated shape
function at any ratio. -/
theorem alignmentShape_ne_sourceDisplayedPeak (ratio : ℝ) :
    alignmentShape ratio ≠ 1 + Real.sqrt 2 / 4 := by
  have upper := alignmentShape_le_exactPeak ratio
  have strict := exactPeak_lt_sourceDisplayedPeak
  nlinarith

section Fixtures

/-- Positive scalar fixture: the witness and its certified objective are
computed exactly. -/
theorem scalar_witness :
    alignmentWitness (State := ℝ) 2 1 1 = 1 / 5 ∧
      alignmentObjective 2 1
          (alignmentWitness (State := ℝ) 2 1 1) 1 =
        6 / 5 ∧
      alignmentShape 2 = 6 / 5 := by
  norm_num [alignmentWitness, witnessCoefficient, alignmentObjective,
    alignmentShape, Real.norm_eq_abs]

/-- Negative fixture: the source witness need not minimize the nonsquared
norm objective.  At weights `(2, 1)`, alignment zero costs `1`, strictly less
than the witness cost `6/5`. -/
theorem sourceWitness_not_minimizer :
    alignmentObjective 2 1
        (0 : ℝ) 1 <
      alignmentObjective 2 1
        (alignmentWitness (State := ℝ) 2 1 1) 1 := by
  norm_num [alignmentWitness, witnessCoefficient, alignmentObjective,
    Real.norm_eq_abs]

end Fixtures

end

end LinearRepresentationDiscrepancy

end Mettapedia.MachineLearning.ContinualLearning

#print axioms
  Mettapedia.MachineLearning.ContinualLearning.LinearRepresentationDiscrepancy.alignmentDiscrepancy_le_sourceBound
#print axioms
  Mettapedia.MachineLearning.ContinualLearning.LinearRepresentationDiscrepancy.alignmentShape_eq_exactPeak_iff
#print axioms
  Mettapedia.MachineLearning.ContinualLearning.LinearRepresentationDiscrepancy.alignmentShape_ne_sourceDisplayedPeak
