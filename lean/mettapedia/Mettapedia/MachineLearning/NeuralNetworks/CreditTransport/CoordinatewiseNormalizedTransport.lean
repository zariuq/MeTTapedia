import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditSpectralGeometry

/-!
# Coordinatewise normalized optimizer transport

For a frozen nonnegative moment state, the normalized direction is

`credit i / sqrt (moment i + stabilizer)`.

Two different geometric comparisons must not be conflated:

* positive rescaling of raw credit survives transport through the same frozen
  moment state exactly;
* the common diagonal normalization can rotate the transported direction away
  from the raw direction, with the sharp Kantorovich bound determined by the
  moment spread;
* different moment states can rotate two collinear raw credits apart.  Their
  displacement error is controlled by the pointwise divergence of the two
  inverse-root moment scales.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CoordinatewiseNormalizedTransport

open scoped BigOperators
open SettledCreditSpectralGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Inverse square-root scale associated with a frozen second-moment state. -/
def inverseRootScale (stabilizer : ℝ) (moment : ι → ℝ) : ι → ℝ :=
  fun index => 1 / Real.sqrt (moment index + stabilizer)

/-- Per-coordinate normalized direction before the global learning-rate
scalar and decoupled weight decay. -/
def normalizedDisplacement
    (stabilizer : ℝ) (moment credit : ι → ℝ) : ι → ℝ :=
  diagonalScale (inverseRootScale stabilizer moment) credit

set_option linter.unusedSectionVars false in
theorem normalizedDisplacement_congr_credit
    (stabilizer : ℝ) (moment first second : ι → ℝ)
    (credits_eq : first = second) :
    normalizedDisplacement stabilizer moment first =
      normalizedDisplacement stabilizer moment second := by
  rw [credits_eq]

set_option linter.unusedSectionVars false in
/-- Positive proportionality survives a fixed moment state exactly.  Hence no
nontrivial moment-spread degradation theorem can hold for the cosine between
two displacements using the same state. -/
theorem normalizedDisplacement_smul
    (stabilizer scale : ℝ) (moment credit : ι → ℝ) :
    normalizedDisplacement stabilizer moment (scale • credit) =
      scale • normalizedDisplacement stabilizer moment credit := by
  funext index
  simp [normalizedDisplacement, diagonalScale]
  ring

/-- Under a shared moment state, positively proportional raw credits produce
displacements with cosine exactly one. -/
theorem sameMoment_proportional_displacement_cosine_eq_one
    (stabilizer scale : ℝ) (moment credit : ι → ℝ)
    (scale_pos : 0 < scale)
    (displacement_normSq_pos :
      0 < coordinateNormSq
        (normalizedDisplacement stabilizer moment credit)) :
    coordinateCosine
        (normalizedDisplacement stabilizer moment (scale • credit))
        (normalizedDisplacement stabilizer moment credit) = 1 := by
  rw [normalizedDisplacement_smul]
  exact coordinateCosine_pos_smul_self _ _ scale_pos displacement_normSq_pos

/-- The originally proposed same-state degradation claim is impossible: under
a shared moment state, no positively proportional pair can have displacement
cosine strictly below one. -/
theorem not_sameMoment_proportional_displacement_cosine_lt_one
    (stabilizer scale : ℝ) (moment credit : ι → ℝ)
    (scale_pos : 0 < scale)
    (displacement_normSq_pos :
      0 < coordinateNormSq
        (normalizedDisplacement stabilizer moment credit)) :
    ¬ coordinateCosine
        (normalizedDisplacement stabilizer moment (scale • credit))
        (normalizedDisplacement stabilizer moment credit) < 1 := by
  rw [sameMoment_proportional_displacement_cosine_eq_one stabilizer scale
    moment credit scale_pos displacement_normSq_pos]
  exact lt_irrefl _

set_option linter.unusedSectionVars false in
/-- Moment bounds give the corresponding inverse-root scaling interval. -/
theorem inverseRootScale_mem
    (stabilizer : ℝ) (moment : ι → ℝ)
    {momentLower momentUpper : ℝ}
    (stabilizer_pos : 0 < stabilizer)
    (momentLower_nonneg : 0 ≤ momentLower)
    (momentLower_le_momentUpper : momentLower ≤ momentUpper)
    (moment_mem : ∀ index,
      momentLower ≤ moment index ∧ moment index ≤ momentUpper) :
    ∀ index,
      1 / Real.sqrt (momentUpper + stabilizer) ≤
          inverseRootScale stabilizer moment index ∧
        inverseRootScale stabilizer moment index ≤
          1 / Real.sqrt (momentLower + stabilizer) := by
  intro index
  have lower_sum_pos : 0 < momentLower + stabilizer :=
    add_pos_of_nonneg_of_pos momentLower_nonneg stabilizer_pos
  have index_sum_pos : 0 < moment index + stabilizer := by
    linarith [(moment_mem index).1]
  have upper_sum_pos : 0 < momentUpper + stabilizer := by
    linarith
  have lower_sqrt_pos := Real.sqrt_pos.2 lower_sum_pos
  have index_sqrt_pos := Real.sqrt_pos.2 index_sum_pos
  have upper_sqrt_pos := Real.sqrt_pos.2 upper_sum_pos
  constructor
  · apply one_div_le_one_div_of_le index_sqrt_pos
    apply Real.sqrt_le_sqrt
    linarith [(moment_mem index).2]
  · apply one_div_le_one_div_of_le lower_sqrt_pos
    apply Real.sqrt_le_sqrt
    linarith [(moment_mem index).1]

/-- Sharp lower bound on the cosine between a raw credit and its normalized
displacement under one frozen moment state.  This is where coordinatewise
moment spread enters; it does not degrade proportionality between two credits
transported through that same state. -/
theorem momentSpreadFactor_le_raw_displacement_cosine
    (stabilizer : ℝ) (moment credit : ι → ℝ)
    {momentLower momentUpper : ℝ}
    (stabilizer_pos : 0 < stabilizer)
    (momentLower_nonneg : 0 ≤ momentLower)
    (momentLower_le_momentUpper : momentLower ≤ momentUpper)
    (moment_mem : ∀ index,
      momentLower ≤ moment index ∧ moment index ≤ momentUpper)
    (credit_normSq_pos : 0 < coordinateNormSq credit) :
    let lowerScale := 1 / Real.sqrt (momentUpper + stabilizer)
    let upperScale := 1 / Real.sqrt (momentLower + stabilizer)
    2 * Real.sqrt (lowerScale * upperScale) /
        (lowerScale + upperScale) ≤
      coordinateCosine
        (normalizedDisplacement stabilizer moment credit) credit := by
  dsimp only
  have lower_sum_pos : 0 < momentLower + stabilizer :=
    add_pos_of_nonneg_of_pos momentLower_nonneg stabilizer_pos
  have upper_sum_pos : 0 < momentUpper + stabilizer := by
    linarith
  have lowerScale_pos :
      0 < 1 / Real.sqrt (momentUpper + stabilizer) := by positivity
  have scale_order :
      1 / Real.sqrt (momentUpper + stabilizer) ≤
        1 / Real.sqrt (momentLower + stabilizer) := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 lower_sum_pos)
    apply Real.sqrt_le_sqrt
    linarith
  apply kantorovichFactor_le_coordinateCosine_diagonalScale
    (inverseRootScale stabilizer moment) credit lowerScale_pos scale_order
  · exact inverseRootScale_mem stabilizer moment stabilizer_pos
      momentLower_nonneg momentLower_le_momentUpper moment_mem
  · exact credit_normSq_pos

/-- Pointwise divergence of the inverse-root representations of two moment
states.  This is the state quantity that directly controls normalized-step
divergence. -/
def InverseRootDivergenceAtMost
    (stabilizer : ℝ) (first second : ι → ℝ) (divergence : ℝ) : Prop :=
  ∀ index,
    |inverseRootScale stabilizer first index -
      inverseRootScale stabilizer second index| ≤ divergence

/-- Different moment states perturb a normalized displacement by at most the
inverse-root state divergence times the raw-credit norm, in squared form. -/
theorem normalizedDisplacement_sub_normSq_le
    (stabilizer : ℝ) (first second credit : ι → ℝ)
    (divergence : ℝ) (divergence_nonneg : 0 ≤ divergence)
    (moment_divergence :
      InverseRootDivergenceAtMost stabilizer first second divergence) :
    coordinateNormSq
        (normalizedDisplacement stabilizer first credit -
          normalizedDisplacement stabilizer second credit) ≤
      divergence ^ 2 * coordinateNormSq credit := by
  rw [coordinateNormSq_apply, coordinateNormSq_apply, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  have hdiff := moment_divergence index
  have hsquare :
      (inverseRootScale stabilizer first index -
          inverseRootScale stabilizer second index) ^ 2 ≤ divergence ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg divergence_nonneg]
    exact hdiff
  have hcredit := mul_le_mul_of_nonneg_right hsquare (sq_nonneg (credit index))
  change
    (inverseRootScale stabilizer first index * credit index -
        inverseRootScale stabilizer second index * credit index) ^ 2 ≤
      divergence ^ 2 * credit index ^ 2
  calc
    _ = (inverseRootScale stabilizer first index -
          inverseRootScale stabilizer second index) ^ 2 * credit index ^ 2 := by
        ring
    _ ≤ _ := hcredit

/-- Ratio of the inverse-root scales carried by two optimizer states. -/
def relativeInverseRootScale
    (stabilizer : ℝ) (first second : ι → ℝ) : ι → ℝ :=
  fun index => inverseRootScale stabilizer first index /
    inverseRootScale stabilizer second index

set_option linter.unusedSectionVars false in
/-- If the reference inverse-root scale is nonzero, changing optimizer state
is exactly a positive diagonal transport of the reference displacement. -/
theorem normalizedDisplacement_eq_relative_diagonalScale
    (stabilizer : ℝ) (first second credit : ι → ℝ)
    (second_scale_ne : ∀ index,
      inverseRootScale stabilizer second index ≠ 0) :
    normalizedDisplacement stabilizer first credit =
      diagonalScale (relativeInverseRootScale stabilizer first second)
        (normalizedDisplacement stabilizer second credit) := by
  funext index
  simp only [normalizedDisplacement, diagonalScale_apply,
    relativeInverseRootScale]
  field_simp [second_scale_ne index]

set_option linter.unusedSectionVars false in
/-- An absolute inverse-root state divergence `delta`, relative to a positive
reference scale floor `minimum`, places the induced scale ratio in the
explicit interval `1 ± delta / minimum`. -/
theorem relativeInverseRootScale_mem_of_divergence
    (stabilizer : ℝ) (first second : ι → ℝ)
    (divergence minimum : ℝ)
    (divergence_nonneg : 0 ≤ divergence)
    (minimum_pos : 0 < minimum)
    (second_scale_lower : ∀ index,
      minimum ≤ inverseRootScale stabilizer second index)
    (moment_divergence :
      InverseRootDivergenceAtMost stabilizer first second divergence) :
    ∀ index,
      1 - divergence / minimum ≤
          relativeInverseRootScale stabilizer first second index ∧
        relativeInverseRootScale stabilizer first second index ≤
          1 + divergence / minimum := by
  intro index
  let firstScale := inverseRootScale stabilizer first index
  let secondScale := inverseRootScale stabilizer second index
  have second_pos : 0 < secondScale :=
    minimum_pos.trans_le (second_scale_lower index)
  have quotient_nonneg : 0 ≤ divergence / minimum := div_nonneg
    divergence_nonneg minimum_pos.le
  have quotient_times_minimum :
      divergence / minimum * minimum = divergence := by
    field_simp
  have divergence_le_scaled :
      divergence ≤ divergence / minimum * secondScale := by
    calc
      divergence = divergence / minimum * minimum :=
        quotient_times_minimum.symm
      _ ≤ divergence / minimum * secondScale :=
        mul_le_mul_of_nonneg_left (second_scale_lower index) quotient_nonneg
  have difference_bounds :
      -divergence ≤ firstScale - secondScale ∧
        firstScale - secondScale ≤ divergence := by
    rw [← abs_le]
    exact moment_divergence index
  constructor
  · change 1 - divergence / minimum ≤ firstScale / secondScale
    rw [le_div_iff₀ second_pos]
    nlinarith
  · change firstScale / secondScale ≤ 1 + divergence / minimum
    rw [div_le_iff₀ second_pos]
    nlinarith

/-- Corrected differing-state cosine theorem.  If the two inverse-root moment
representations differ by at most `delta`, and the reference representation
has scale floor `minimum > delta`, then the two normalized displacements obey
the sharp diagonal Kantorovich bound for the relative interval
`1 ± delta / minimum`. -/
theorem momentDivergenceFactor_le_displacement_cosine
    (stabilizer : ℝ) (first second credit : ι → ℝ)
    (divergence minimum : ℝ)
    (divergence_nonneg : 0 ≤ divergence)
    (minimum_pos : 0 < minimum)
    (divergence_lt_minimum : divergence < minimum)
    (second_scale_lower : ∀ index,
      minimum ≤ inverseRootScale stabilizer second index)
    (moment_divergence :
      InverseRootDivergenceAtMost stabilizer first second divergence)
    (second_displacement_normSq_pos :
      0 < coordinateNormSq
        (normalizedDisplacement stabilizer second credit)) :
    let lower := 1 - divergence / minimum
    let upper := 1 + divergence / minimum
    2 * Real.sqrt (lower * upper) / (lower + upper) ≤
      coordinateCosine
        (normalizedDisplacement stabilizer first credit)
        (normalizedDisplacement stabilizer second credit) := by
  dsimp only
  have lower_pos : 0 < 1 - divergence / minimum := by
    rw [sub_pos, div_lt_one minimum_pos]
    exact divergence_lt_minimum
  have interval_order :
      1 - divergence / minimum ≤ 1 + divergence / minimum := by
    have := div_nonneg divergence_nonneg minimum_pos.le
    linarith
  have second_scale_ne : ∀ index,
      inverseRootScale stabilizer second index ≠ 0 := fun index =>
    ne_of_gt (minimum_pos.trans_le (second_scale_lower index))
  rw [normalizedDisplacement_eq_relative_diagonalScale stabilizer first second
    credit second_scale_ne]
  apply kantorovichFactor_le_coordinateCosine_diagonalScale
    (relativeInverseRootScale stabilizer first second)
    (normalizedDisplacement stabilizer second credit)
    lower_pos interval_order
  · exact relativeInverseRootScale_mem_of_divergence stabilizer first second
      divergence minimum divergence_nonneg minimum_pos second_scale_lower
      moment_divergence
  · exact second_displacement_normSq_pos

/-! ## Different-state counterexample -/

namespace DivergentStateWitness

def rawCredit : Fin 2 → ℝ := ![1, 1]

def firstMoment : Fin 2 → ℝ := ![0, 3]

def secondMoment : Fin 2 → ℝ := ![3, 0]

theorem firstDisplacement :
    normalizedDisplacement 1 firstMoment rawCredit = ![1, 1 / 2] := by
  funext index
  fin_cases index <;>
    norm_num [normalizedDisplacement, inverseRootScale, diagonalScale,
      firstMoment, rawCredit]

theorem secondDisplacement :
    normalizedDisplacement 1 secondMoment rawCredit = ![1 / 2, 1] := by
  funext index
  fin_cases index <;>
    norm_num [normalizedDisplacement, inverseRootScale, diagonalScale,
      secondMoment, rawCredit]

/-- Collinear raw credits can yield displacement cosine `4/5` under different
moment states, a gap of `1/5` from perfect alignment. -/
theorem collinear_raw_displacement_cosine_eq_four_fifths :
    coordinateCosine
        (normalizedDisplacement 1 firstMoment rawCredit)
        (normalizedDisplacement 1 secondMoment rawCredit) = 4 / 5 := by
  rw [firstDisplacement, secondDisplacement]
  norm_num [coordinateCosine, coordinateInner, coordinateNormSq,
    Fin.sum_univ_two]

theorem inverseRoot_divergence_eq_half :
    InverseRootDivergenceAtMost 1 firstMoment secondMoment (1 / 2) := by
  intro index
  fin_cases index <;>
    norm_num [InverseRootDivergenceAtMost, inverseRootScale,
      firstMoment, secondMoment]

end DivergentStateWitness

#print axioms normalizedDisplacement_smul
#print axioms sameMoment_proportional_displacement_cosine_eq_one
#print axioms not_sameMoment_proportional_displacement_cosine_lt_one
#print axioms inverseRootScale_mem
#print axioms momentSpreadFactor_le_raw_displacement_cosine
#print axioms normalizedDisplacement_sub_normSq_le
#print axioms momentDivergenceFactor_le_displacement_cosine
#print axioms DivergentStateWitness.collinear_raw_displacement_cosine_eq_four_fifths

end
end CoordinatewiseNormalizedTransport

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
