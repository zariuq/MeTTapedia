import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.TransferRigidity
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LocalityCeiling

/-!
# Degree-two interference Gram diagnostic

The degree-two interference Gram form pairs curvature commutators with the
Frobenius inner product.  Its diagonal entries are nonnegative and vanish
exactly for commuting task pairs, so the labeled diagonal determines the
pairwise conflict graph.  It does not determine the Hessians: scalar identity
shifts leave every commutator unchanged.

The separate predictive-coding locality theorem proves the finite-speed bound
`distance ≤ sweeps * bandwidth`.  Expressions involving
`sqrt(condition) * log(1 / residual)` require additional analytic decay and
conditioning hypotheses and remain a physics-motivated analogy here, not a
consequence of the sealed locality theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-- Frobenius pairing of two task-pair curvature commutators. -/
noncomputable def interferenceGramEntry
    {Index : Type*} [Fintype Index]
    (first second third fourth : Matrix Index Index ℝ) : ℝ :=
  Matrix.trace
    ((matrixCommutator first second).transpose *
      matrixCommutator third fourth)

/-- Diagonal degree-two Gram moment for one pair of tasks. -/
noncomputable def pairwiseInterferenceEnergy
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) : ℝ :=
  interferenceGramEntry first second first second

/-- The interference Gram form is symmetric under exchange of its two
task-pair arguments. -/
theorem interferenceGramEntry_comm
    {Index : Type*} [Fintype Index]
    (first second third fourth : Matrix Index Index ℝ) :
    interferenceGramEntry first second third fourth =
      interferenceGramEntry third fourth first second := by
  unfold interferenceGramEntry
  let firstCommutator := matrixCommutator first second
  let secondCommutator := matrixCommutator third fourth
  calc
    Matrix.trace (firstCommutator.transpose * secondCommutator) =
        Matrix.trace (secondCommutator * firstCommutator.transpose) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (secondCommutator * firstCommutator.transpose).transpose := by
      rw [Matrix.trace_transpose]
    _ = Matrix.trace (firstCommutator * secondCommutator.transpose) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = Matrix.trace (secondCommutator.transpose * firstCommutator) :=
      Matrix.trace_mul_comm _ _

/-- Every diagonal interference moment is nonnegative. -/
theorem pairwiseInterferenceEnergy_nonneg
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) :
    0 ≤ pairwiseInterferenceEnergy first second := by
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self
    (matrixCommutator first second)
  have htrace := hpositive.trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at htrace
  simpa [pairwiseInterferenceEnergy, interferenceGramEntry] using htrace

/-- Exact degree-two certificate: the diagonal moment vanishes if and only if
the task curvatures commute. -/
theorem pairwiseInterferenceEnergy_eq_zero_iff_commute
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) :
    pairwiseInterferenceEnergy first second = 0 ↔
      Commute first second := by
  rw [pairwiseInterferenceEnergy, interferenceGramEntry]
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff]
  unfold matrixCommutator Commute SemiconjBy
  constructor
  · intro hzero
    have hproduct : second * first = first * second :=
      sub_eq_zero.mp hzero
    exact hproduct.symm
  · intro hcommute
    apply sub_eq_zero.mpr
    exact hcommute.symm

/-- Equivalently, strict positive diagonal energy detects exactly the
noncommuting edges of the pairwise task-conflict graph. -/
theorem pairwiseInterferenceEnergy_pos_iff_not_commute
    {Index : Type*} [Fintype Index]
    (first second : Matrix Index Index ℝ) :
    0 < pairwiseInterferenceEnergy first second ↔
      ¬ Commute first second := by
  constructor
  · intro hpositive hcommute
    have hzero :=
      (pairwiseInterferenceEnergy_eq_zero_iff_commute first second).2 hcommute
    linarith
  · intro hnot
    have hnonneg := pairwiseInterferenceEnergy_nonneg first second
    have hne : pairwiseInterferenceEnergy first second ≠ 0 := by
      intro hzero
      exact hnot
        ((pairwiseInterferenceEnergy_eq_zero_iff_commute first second).1 hzero)
    exact lt_of_le_of_ne hnonneg hne.symm

/-- Closed form for the rank-one normal form: obliqueness contributes twice
the squared cross-coordinate product. -/
theorem rankOne_pairwiseInterferenceEnergy_exact (x y : ℝ) :
    pairwiseInterferenceEnergy axisRankOneCurvature
        (directionRankOneCurvature x y) =
      2 * (x * y) ^ 2 := by
  unfold pairwiseInterferenceEnergy interferenceGramEntry matrixCommutator
  simp [axisRankOneCurvature, directionRankOneCurvature,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Positive fixture: parallel rank-one tasks have zero degree-two energy. -/
theorem parallel_rankOne_interferenceEnergy_zero_positiveExample (x : ℝ) :
    pairwiseInterferenceEnergy axisRankOneCurvature
      (directionRankOneCurvature x 0) = 0 := by
  rw [rankOne_pairwiseInterferenceEnergy_exact]
  ring

/-- Negative fixture: the unit oblique pair has strictly positive energy. -/
theorem unitOblique_interferenceEnergy_positive_negativeExample :
    pairwiseInterferenceEnergy axisRankOneCurvature
      (directionRankOneCurvature 1 1) = 2 := by
  norm_num [rankOne_pairwiseInterferenceEnergy_exact]

/-- Scalar identity shifts cancel from every commutator.  Thus the
degree-two conflict graph cannot recover absolute curvature spectra. -/
theorem matrixCommutator_add_scalarIdentity
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (first second : Matrix Index Index ℝ) (firstShift secondShift : ℝ) :
    matrixCommutator
        (first + firstShift • (1 : Matrix Index Index ℝ))
        (second + secondShift • (1 : Matrix Index Index ℝ)) =
      matrixCommutator first second := by
  simp [matrixCommutator, Matrix.mul_add, Matrix.add_mul]
  module

/-! ## Exact locality content versus the analytic analogy -/

/-- Restatement of the sealed nonlinear locality crown: exact inference at a
node `distance` edges from the input requires the dependency wavefront to
reach it.  No condition number, residual tolerance, or logarithmic decay law
is inferred. -/
theorem sealedLocality_requires_distance_le_sweeps_mul_bandwidth
    (distance bandwidth sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step bandwidth)
    (hsettle₀ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettle₁ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0)) :
    distance ≤ sweeps * bandwidth := by
  exact bandwidth_rule_exact_unitChainPosterior_requires_reach
    distance bandwidth sweeps step hbandwidth hsettle₀ hsettle₁

#print axioms pairwiseInterferenceEnergy_eq_zero_iff_commute
#print axioms pairwiseInterferenceEnergy_pos_iff_not_commute
#print axioms rankOne_pairwiseInterferenceEnergy_exact
#print axioms matrixCommutator_add_scalarIdentity
#print axioms sealedLocality_requires_distance_le_sweeps_mul_bandwidth

end Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry
