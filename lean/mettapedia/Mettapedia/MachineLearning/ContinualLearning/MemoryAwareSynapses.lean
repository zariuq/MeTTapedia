import Mettapedia.MachineLearning.ContinualLearning.ElasticWeightConsolidation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Memory-aware synapses: online output sensitivity and its boundaries

Aljundi et al., *Memory Aware Synapses: Learning what (not) to forget*
(2017), Equations (1)--(3), estimate a parameter's importance by averaging the
norm of the learned output function's derivative with respect to that
parameter.  The average can be updated online and does not require labels.
The resulting importance weights a quadratic consolidation penalty.

For a vector-valued output, the source proposes a cheaper one-backward-pass
surrogate: differentiate the squared Euclidean norm of the output.  This file
proves its exact directional expansion and Cauchy upper bound, but also records
the missing converse.  A tangent orthogonal to the current output has nonzero
vector sensitivity while the squared-output surrogate is exactly zero.

The final section proves a second boundary important for architecture
comparisons: output sensitivity is parameterization-dependent.  A two-factor
rescaling can preserve the represented function exactly while transferring
importance between its factors.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace MemoryAwareSynapses

noncomputable section

open scoped InnerProductSpace

/-! ## Online sensitivity evidence -/

/-- Constant-memory sufficient statistics for the source's online average. -/
structure SensitivityEvidence where
  count : ℕ
  totalMagnitude : ℝ

namespace SensitivityEvidence

instance : Zero SensitivityEvidence := ⟨⟨0, 0⟩⟩

instance : Add SensitivityEvidence where
  add first second :=
    ⟨first.count + second.count,
      first.totalMagnitude + second.totalMagnitude⟩

@[ext] theorem ext'
    (first second : SensitivityEvidence)
    (countEqual : first.count = second.count)
    (totalEqual : first.totalMagnitude = second.totalMagnitude) :
    first = second := by
  cases first
  cases second
  simp_all

instance : AddCommMonoid SensitivityEvidence where
  zero_add evidence := by
    apply ext'
    · exact Nat.zero_add evidence.count
    · exact _root_.zero_add evidence.totalMagnitude
  add_zero evidence := by
    apply ext'
    · exact Nat.add_zero evidence.count
    · exact _root_.add_zero evidence.totalMagnitude
  add_assoc first second third := by
    apply ext'
    · exact Nat.add_assoc first.count second.count third.count
    · exact _root_.add_assoc first.totalMagnitude
        second.totalMagnitude third.totalMagnitude
  add_comm first second := by
    apply ext'
    · exact Nat.add_comm first.count second.count
    · exact _root_.add_comm first.totalMagnitude second.totalMagnitude
  nsmul := nsmulRec

/-- One scalar derivative-magnitude observation. -/
noncomputable def observe (sensitivity : ℝ) : SensitivityEvidence :=
  ⟨1, |sensitivity|⟩

/-- Average magnitude in Equation (2).  A nonempty certificate is required
before this totalized quotient is used as an empirical mean. -/
noncomputable def mean (evidence : SensitivityEvidence) : ℝ :=
  evidence.totalMagnitude / evidence.count

/-- Executable evidence obtained by assimilating every sample once. -/
noncomputable def ofList (sensitivities : List ℝ) :
    SensitivityEvidence :=
  (sensitivities.map observe).sum

@[simp] theorem zero_count : (0 : SensitivityEvidence).count = 0 := rfl

@[simp] theorem zero_totalMagnitude :
    (0 : SensitivityEvidence).totalMagnitude = 0 := rfl

@[simp] theorem add_count (first second : SensitivityEvidence) :
    (first + second).count = first.count + second.count := rfl

@[simp] theorem add_totalMagnitude
    (first second : SensitivityEvidence) :
    (first + second).totalMagnitude =
      first.totalMagnitude + second.totalMagnitude := rfl

@[simp] theorem observe_count (sensitivity : ℝ) :
    (observe sensitivity).count = 1 := rfl

@[simp] theorem observe_totalMagnitude (sensitivity : ℝ) :
    (observe sensitivity).totalMagnitude = |sensitivity| := rfl

@[simp] theorem ofList_nil : ofList [] = 0 := by
  rfl

@[simp] theorem ofList_cons
    (sensitivity : ℝ) (sensitivities : List ℝ) :
    ofList (sensitivity :: sensitivities) =
      observe sensitivity + ofList sensitivities := by
  rfl

/-- Exactly-once chunking: distributed batches merge to the same online
evidence as their concatenation. -/
@[simp] theorem ofList_append
    (first second : List ℝ) :
    ofList (first ++ second) = ofList first + ofList second := by
  simp [ofList, List.map_append]

theorem ofList_count (sensitivities : List ℝ) :
    (ofList sensitivities).count = sensitivities.length := by
  induction sensitivities with
  | nil =>
      simp
  | cons sensitivity sensitivities inductionHypothesis =>
      simp [inductionHypothesis, Nat.add_comm]

theorem ofList_totalMagnitude (sensitivities : List ℝ) :
    (ofList sensitivities).totalMagnitude =
      (sensitivities.map abs).sum := by
  induction sensitivities with
  | nil =>
      simp
  | cons sensitivity sensitivities inductionHypothesis =>
      simp [inductionHypothesis]

/-- The exact online recurrence after observing one more sample. -/
theorem mean_add_observation
    (evidence : SensitivityEvidence) (sensitivity : ℝ) :
    mean (evidence + observe sensitivity) =
      (evidence.totalMagnitude + |sensitivity|) /
        (evidence.count + 1) := by
  simp [mean, observe, Nat.cast_add, Nat.cast_one]

theorem ofList_totalMagnitude_nonnegative
    (sensitivities : List ℝ) :
    0 ≤ (ofList sensitivities).totalMagnitude := by
  rw [ofList_totalMagnitude]
  exact List.sum_nonneg (by
    intro value valueMem
    obtain ⟨sensitivity, _, rfl⟩ := List.mem_map.mp valueMem
    exact abs_nonneg sensitivity)

theorem mean_nonnegative
    (evidence : SensitivityEvidence)
    (totalNonnegative : 0 ≤ evidence.totalMagnitude) :
    0 ≤ mean evidence := by
  exact div_nonneg totalNonnegative (Nat.cast_nonneg evidence.count)

/-- Reusing one sample increments the count once beyond once-each
assimilation. -/
theorem duplicate_observation_count_exact_excess
    (evidence : SensitivityEvidence) (sensitivity : ℝ) :
    (evidence + observe sensitivity + observe sensitivity).count =
      (evidence + observe sensitivity).count + 1 := by
  rfl

/-- Reusing one sample adds exactly one extra magnitude beyond once-each
assimilation. -/
theorem duplicate_observation_total_exact_excess
    (evidence : SensitivityEvidence) (sensitivity : ℝ) :
    (evidence + observe sensitivity + observe sensitivity).totalMagnitude =
      (evidence + observe sensitivity).totalMagnitude +
        |sensitivity| := by
  rfl

end SensitivityEvidence

/-! ## Vector output sensitivity and the squared-norm surrogate -/

variable {Output : Type*}
  [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]

/-- Equation (2)'s per-sample magnitude for one parameter's output tangent. -/
noncomputable def vectorSensitivity (tangent : Output) : ℝ :=
  ‖tangent‖

/-- Magnitude of the proposed one-backward-pass squared-output derivative. -/
noncomputable def squaredNormSensitivity
    (output tangent : Output) : ℝ :=
  |2 * ⟪output, tangent⟫_ℝ|

/-- Exact perturbation size for the vector-output linearization in Equation
(1). -/
theorem norm_parameterPerturbation
    (parameterChange : ℝ) (tangent : Output) :
    ‖parameterChange • tangent‖ =
      |parameterChange| * vectorSensitivity tangent := by
  simp [vectorSensitivity, norm_smul, Real.norm_eq_abs]

/-- Exact finite expansion behind the squared-output derivative. -/
theorem squaredNorm_perturbation_expansion
    (output tangent : Output) (parameterChange : ℝ) :
    ‖output + parameterChange • tangent‖ ^ 2 =
      ‖output‖ ^ 2 +
        2 * parameterChange * ⟪output, tangent⟫_ℝ +
        parameterChange ^ 2 * ‖tangent‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
  rw [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The efficient scalar surrogate is controlled by vector sensitivity and
current output magnitude. -/
theorem squaredNormSensitivity_le
    (output tangent : Output) :
    squaredNormSensitivity output tangent ≤
      2 * ‖output‖ * vectorSensitivity tangent := by
  unfold squaredNormSensitivity vectorSensitivity
  calc
    |2 * ⟪output, tangent⟫_ℝ| =
        2 * |⟪output, tangent⟫_ℝ| := by
          rw [abs_mul]
          norm_num
    _ ≤ 2 * (‖output‖ * ‖tangent‖) := by
      exact mul_le_mul_of_nonneg_left
        (abs_real_inner_le_norm output tangent) (by norm_num)
    _ = 2 * ‖output‖ * ‖tangent‖ := by ring

theorem squaredNormSensitivity_eq_zero_of_orthogonal
    (output tangent : Output)
    (orthogonal : ⟪output, tangent⟫_ℝ = 0) :
    squaredNormSensitivity output tangent = 0 := by
  simp [squaredNormSensitivity, orthogonal]

/-- Joint output/tangent rescaling changes the squared-output surrogate
quadratically. -/
theorem squaredNormSensitivity_smul
    (scale : ℝ) (output tangent : Output) :
    squaredNormSensitivity (scale • output) (scale • tangent) =
      |scale| ^ 2 * squaredNormSensitivity output tangent := by
  simp only [squaredNormSensitivity, real_inner_smul_left,
    real_inner_smul_right, abs_mul]
  ring

private def firstAxis : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 1

private def secondAxis : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 1 1

private theorem secondAxis_ne_zero : secondAxis ≠ 0 := by
  intro zero
  have coordinate :=
    congrArg (fun vector : EuclideanSpace ℝ (Fin 2) => vector 1) zero
  norm_num [secondAxis, PiLp.single_apply] at coordinate

/-- Sharp negative fixture for the efficient surrogate: the true vector
tangent is nonzero, but orthogonality to the current output makes the
squared-output derivative vanish. -/
theorem orthogonal_tangent_surrogate_blindSpot :
    0 < vectorSensitivity secondAxis ∧
      squaredNormSensitivity firstAxis secondAxis = 0 := by
  constructor
  · exact norm_pos_iff.mpr secondAxis_ne_zero
  · apply squaredNormSensitivity_eq_zero_of_orthogonal
    simp [firstAxis, secondAxis, EuclideanSpace.inner_single_left]

/-! ## Local active-unit / Hebbian correspondence -/

/-- Squared output of one active scalar linear unit. -/
noncomputable def localSquaredOutput
    (input weight : ℝ) : ℝ :=
  (input * weight) ^ 2

/-- Exact finite perturbation identity behind Equation (5).  The coefficient
of `weightChange` is twice pre-synaptic activity times post-synaptic
activity; the remaining term is explicitly quadratic. -/
theorem localSquaredOutput_perturbation_expansion
    (input weight weightChange : ℝ) :
    localSquaredOutput input (weight + weightChange) =
      localSquaredOutput input weight +
        weightChange * (2 * input * (input * weight)) +
        weightChange ^ 2 * input ^ 2 := by
  unfold localSquaredOutput
  ring

/-! ## Quadratic consolidation bridge -/

/-- Equation (3)'s scalar MAS consolidation term. -/
noncomputable def consolidationPenalty
    (strength importance anchor parameter : ℝ) : ℝ :=
  strength * importance * (parameter - anchor) ^ 2

/-- MAS, SI, and EWC share the same diagonal quadratic penalty once their
different importance estimators have produced a coefficient. -/
theorem consolidationPenalty_eq_ewcPenalty
    (strength importance anchor parameter : ℝ) :
    consolidationPenalty strength importance anchor parameter =
      ElasticWeightConsolidation.penalty
        (2 * strength * importance) anchor parameter := by
  unfold consolidationPenalty ElasticWeightConsolidation.penalty
  ring

theorem consolidationPenalty_nonnegative
    {strength importance : ℝ} (anchor parameter : ℝ)
    (strengthNonnegative : 0 ≤ strength)
    (importanceNonnegative : 0 ≤ importance) :
    0 ≤ consolidationPenalty strength importance anchor parameter := by
  unfold consolidationPenalty
  positivity

/-! ## Parameterization dependence -/

/-- A scalar two-factor representation of the same input-output map. -/
noncomputable def twoFactorOutput
    (first second input : ℝ) : ℝ :=
  first * second * input

/-- Sensitivity of the output to the first factor. -/
noncomputable def firstFactorSensitivity
    (second input : ℝ) : ℝ :=
  |second * input|

/-- Sensitivity of the output to the second factor. -/
noncomputable def secondFactorSensitivity
    (first input : ℝ) : ℝ :=
  |first * input|

/-- Reciprocal factor rescaling preserves the represented function exactly. -/
theorem twoFactorOutput_rescale
    (first second input scale : ℝ) (scaleNonzero : scale ≠ 0) :
    twoFactorOutput (scale * first) (second / scale) input =
      twoFactorOutput first second input := by
  unfold twoFactorOutput
  field_simp [scaleNonzero]

/-- Concrete separation witness: the same scalar function can assign four
times as much first-factor sensitivity under one parameterization as another. -/
theorem sameFunction_differentImportance :
    twoFactorOutput 1 1 1 = twoFactorOutput 2 (1 / 2) 1 ∧
      firstFactorSensitivity 1 1 = 1 ∧
      firstFactorSensitivity (1 / 2) 1 = 1 / 2 ∧
      secondFactorSensitivity 1 1 = 1 ∧
      secondFactorSensitivity 2 1 = 2 := by
  norm_num [
    twoFactorOutput,
    firstFactorSensitivity,
    secondFactorSensitivity
  ]

#print axioms SensitivityEvidence.ofList_append
#print axioms SensitivityEvidence.mean_add_observation
#print axioms squaredNorm_perturbation_expansion
#print axioms squaredNormSensitivity_le
#print axioms squaredNormSensitivity_smul
#print axioms orthogonal_tangent_surrogate_blindSpot
#print axioms localSquaredOutput_perturbation_expansion
#print axioms consolidationPenalty_eq_ewcPenalty
#print axioms twoFactorOutput_rescale
#print axioms sameFunction_differentImportance

end

end MemoryAwareSynapses

end Mettapedia.MachineLearning.ContinualLearning
