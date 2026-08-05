import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.PEPITAAntialignment
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Direct random target projection

Frenkel, Lefebvre, and Bol, *Learning without feedback: Direct random target
projection* (Frontiers in Neuroscience 2021, arXiv:1909.01311), use the one-hot
class target as a feedforward surrogate for the sign of the output error.  For
one repeatedly presented training example, their linear-network analysis shows
that the downstream forward product becomes rank one.  The backpropagated
modulatory signal is then a positive scalar multiple of the fixed
target-projection signal.

This file separates three pieces of that argument.

* Strictly interior sigmoid/softmax probabilities give a time-independent
  componentwise error-sign pattern.  Any nontrivial nonnegative accumulation
  of errors with the same label has positive dot product with the current
  error.
* A rank-one downstream map `-scale * accumulator * projectedTargetᵀ` sends the
  backpropagated signal to an exact positive multiple of `projectedTarget`.
  This yields a direct proof of acute DRTP/BP alignment without introducing a
  pseudoinverse.
* The source's alternative pseudoinverse calculation is repaired.  For a
  Moore--Penrose inverse, `P P⁺` is an orthogonal projection, not generally the
  identity.  The exact alignment is projected error energy; strict positivity
  requires the error to have nonzero component in the forward range.

The source's single-example, zero-initialization, linear-hidden-layer, and
strictly interior output hypotheses remain explicit.  The results do not claim
multi-example alignment, nonlinear convergence, or classification efficacy.

Source artifact SHA-256:
`dadb3712653cda631bac18d54f2def8661f956b0a9c0673c01158d6ecb18a841`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace DirectRandomTargetProjection

open scoped BigOperators Matrix

/-! ## A one-hot target is an exact error-sign surrogate -/

variable {classes : Type} [DecidableEq classes]

/-- One-hot target for the supplied class label. -/
def oneHotTarget (label : classes) : classes → ℝ :=
  fun c => if c = label then 1 else 0

/-- The label-dependent sign pattern: positive at the target class and
negative elsewhere. -/
def targetErrorSign (label : classes) : classes → ℝ :=
  fun c => if c = label then 1 else -1

/-- The one-hot target is exactly the shifted and rescaled sign pattern used
in the source comparison with sign-DFA. -/
theorem oneHotTarget_eq_shiftedErrorSign
    (label c : classes) :
    oneHotTarget label c = (1 + targetErrorSign label c) / 2 := by
  by_cases hc : c = label <;>
    simp [oneHotTarget, targetErrorSign, hc]

/-- Classification error `target - output`. -/
def classificationError
    (label : classes) (output : classes → ℝ) : classes → ℝ :=
  oneHotTarget label - output

/-- Every output coordinate lies strictly between zero and one. -/
def InteriorProbabilities (output : classes → ℝ) : Prop :=
  ∀ c, 0 < output c ∧ output c < 1

/-- The target-class error is strictly positive for an interior output. -/
theorem classificationError_label_pos
    (label : classes) (output : classes → ℝ)
    (hinterior : InteriorProbabilities output) :
    0 < classificationError label output label := by
  simpa [classificationError, oneHotTarget] using
    (hinterior label).2

/-- Every non-target error is strictly negative for an interior output. -/
theorem classificationError_other_neg
    (label c : classes) (output : classes → ℝ)
    (hinterior : InteriorProbabilities output)
    (hne : c ≠ label) :
    classificationError label output c < 0 := by
  simpa [classificationError, oneHotTarget, hne] using
    (hinterior c).1

section FiniteClasses

variable [Fintype classes]

/-- Error vectors from any two interior predictions of the same label have
strictly positive dot product. -/
theorem sameLabel_classificationError_dot_pos
    (label : classes) (first second : classes → ℝ)
    (hfirst : InteriorProbabilities first)
    (hsecond : InteriorProbabilities second) :
    0 <
      classificationError label first ⬝ᵥ
        classificationError label second := by
  apply Finset.sum_pos'
  · intro c _
    by_cases hc : c = label
    · subst c
      exact
        (mul_pos
          (classificationError_label_pos label first hfirst)
          (classificationError_label_pos label second hsecond)).le
    · exact
        (mul_pos_of_neg_of_neg
          (classificationError_other_neg label c first hfirst hc)
          (classificationError_other_neg label c second hsecond hc)).le
  · exact
      ⟨label, Finset.mem_univ label,
        mul_pos
          (classificationError_label_pos label first hfirst)
          (classificationError_label_pos label second hsecond)⟩

variable {history : Type} [Fintype history]

/-- Nonnegative weighted history of same-label output errors.  This abstracts
the source output-layer accumulator after repeated presentation of one
example. -/
def errorAccumulator
    (label : classes)
    (weight : history → ℝ)
    (outputs : history → classes → ℝ) :
    classes → ℝ :=
  fun c =>
    ∑ j, weight j * classificationError label (outputs j) c

/-- Dotting the current error with the accumulated history distributes into
the chronological weighted sum of pairwise alignments. -/
theorem classificationError_dot_errorAccumulator
    (label : classes) (current : classes → ℝ)
    (weight : history → ℝ)
    (outputs : history → classes → ℝ) :
    classificationError label current ⬝ᵥ
        errorAccumulator label weight outputs =
      ∑ j,
        weight j *
          (classificationError label current ⬝ᵥ
            classificationError label (outputs j)) := by
  simp only [dotProduct, errorAccumulator, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Any nontrivial nonnegative accumulation of same-label interior errors has
strictly positive overlap with the current error. -/
theorem classificationError_dot_errorAccumulator_pos
    (label : classes) (current : classes → ℝ)
    (weight : history → ℝ)
    (outputs : history → classes → ℝ)
    (hcurrent : InteriorProbabilities current)
    (houtputs : ∀ j, InteriorProbabilities (outputs j))
    (hweight : ∀ j, 0 ≤ weight j)
    (j₀ : history) (hj₀ : 0 < weight j₀) :
    0 <
      classificationError label current ⬝ᵥ
        errorAccumulator label weight outputs := by
  rw [classificationError_dot_errorAccumulator]
  apply Finset.sum_pos'
  · intro j _
    exact
      mul_nonneg (hweight j)
        (sameLabel_classificationError_dot_pos
          label current (outputs j) hcurrent (houtputs j)).le
  · exact
      ⟨j₀, Finset.mem_univ j₀,
        mul_pos hj₀
          (sameLabel_classificationError_dot_pos
            label current (outputs j₀) hcurrent (houtputs j₀))⟩

end FiniteClasses

/-! ## Rank-one forward alignment -/

variable {output hidden : Type} [Fintype output]

/-- Rank-one downstream forward map obtained in the source's repeated
single-example linear dynamics. -/
def rankOneForward
    (scale : ℝ)
    (outputAccumulator : output → ℝ)
    (projectedTarget : hidden → ℝ) :
    Matrix output hidden ℝ :=
  fun i j => -scale * outputAccumulator i * projectedTarget j

/-- Backpropagated modulatory signal through a downstream linear map. -/
def bpModulatorySignal
    (forward : Matrix output hidden ℝ)
    (error : output → ℝ) :
    hidden → ℝ :=
  -(forward.transpose *ᵥ error)

/-- The backpropagated signal of the rank-one map is an exact scalar multiple
of the DRTP target projection. -/
theorem bpModulatorySignal_rankOneForward
    (scale : ℝ)
    (outputAccumulator : output → ℝ)
    (projectedTarget : hidden → ℝ)
    (error : output → ℝ) :
    bpModulatorySignal
        (rankOneForward scale outputAccumulator projectedTarget) error =
      (scale * (outputAccumulator ⬝ᵥ error)) • projectedTarget := by
  funext j
  simp only [bpModulatorySignal, rankOneForward, Matrix.mulVec,
    Matrix.transpose_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct]
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [Fintype hidden]

/-- Exact BP/DRTP dot product for the source rank-one factorization. -/
theorem rankOneForward_alignment_formula
    (scale : ℝ)
    (outputAccumulator : output → ℝ)
    (projectedTarget : hidden → ℝ)
    (error : output → ℝ) :
    bpModulatorySignal
        (rankOneForward scale outputAccumulator projectedTarget) error
          ⬝ᵥ projectedTarget =
      (scale * (outputAccumulator ⬝ᵥ error)) *
        (projectedTarget ⬝ᵥ projectedTarget) := by
  rw [bpModulatorySignal_rankOneForward]
  simp

/-- Positive scale, positive accumulator/error overlap, and a nonzero target
projection imply a strictly acute BP/DRTP angle. -/
theorem rankOneForward_alignment_pos
    (scale : ℝ)
    (outputAccumulator : output → ℝ)
    (projectedTarget : hidden → ℝ)
    (error : output → ℝ)
    (hscale : 0 < scale)
    (haccumulator : 0 < outputAccumulator ⬝ᵥ error)
    (hprojection : projectedTarget ≠ 0) :
    0 <
      bpModulatorySignal
          (rankOneForward scale outputAccumulator projectedTarget) error
        ⬝ᵥ projectedTarget := by
  rw [rankOneForward_alignment_formula]
  have hnonneg :
      0 ≤ projectedTarget ⬝ᵥ projectedTarget :=
    Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (projectedTarget i)
  have hne :
      projectedTarget ⬝ᵥ projectedTarget ≠ 0 := by
    intro hz
    exact hprojection (dotProduct_self_eq_zero.mp hz)
  have hself :
      0 < projectedTarget ⬝ᵥ projectedTarget :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  exact mul_pos (mul_pos hscale haccumulator) hself

/-- Crown composition: the same-label history theorem supplies the positive
accumulator/error premise needed by the rank-one DRTP alignment theorem. -/
theorem rankOneForward_alignment_pos_of_sameLabel_history
    {classes history : Type}
    [Fintype classes] [DecidableEq classes] [Fintype history]
    (label : classes)
    (current : classes → ℝ)
    (weight : history → ℝ)
    (outputs : history → classes → ℝ)
    (projectedTarget : hidden → ℝ)
    (scale : ℝ)
    (hcurrent : InteriorProbabilities current)
    (houtputs : ∀ j, InteriorProbabilities (outputs j))
    (hweight : ∀ j, 0 ≤ weight j)
    (j₀ : history) (hj₀ : 0 < weight j₀)
    (hprojection : projectedTarget ≠ 0)
    (hscale : 0 < scale) :
    0 <
      bpModulatorySignal
          (rankOneForward scale
            (errorAccumulator label weight outputs)
            projectedTarget)
          (classificationError label current)
        ⬝ᵥ projectedTarget := by
  apply rankOneForward_alignment_pos
  · exact hscale
  · rw [dotProduct_comm]
    exact
      classificationError_dot_errorAccumulator_pos
        label current weight outputs hcurrent houtputs hweight j₀ hj₀
  · exact hprojection

/-! ## The Moore--Penrose projection boundary -/

/-- The four Penrose equations over finite real matrices. -/
structure IsMoorePenroseInverse
    {rows cols : Type} [Fintype rows] [Fintype cols]
    (forward : Matrix rows cols ℝ)
    (inverse : Matrix cols rows ℝ) : Prop where
  forward_inverse_forward :
    forward * inverse * forward = forward
  inverse_forward_inverse :
    inverse * forward * inverse = inverse
  forward_inverse_symmetric :
    (forward * inverse).transpose = forward * inverse
  inverse_forward_symmetric :
    (inverse * forward).transpose = inverse * forward

/-- The forward-side Moore--Penrose product is idempotent. -/
theorem IsMoorePenroseInverse.forward_inverse_idempotent
    {rows cols : Type} [Fintype rows] [Fintype cols]
    {forward : Matrix rows cols ℝ}
    {inverse : Matrix cols rows ℝ}
    (hmp : IsMoorePenroseInverse forward inverse) :
    (forward * inverse) * (forward * inverse) =
      forward * inverse := by
  rw [← Matrix.mul_assoc, hmp.forward_inverse_forward]

/-- A symmetric idempotent matrix measures only projected energy. -/
theorem symmetricIdempotent_energy_eq
    {index : Type} [Fintype index]
    {projection : Matrix index index ℝ}
    (hsymmetric : projection.transpose = projection)
    (hidempotent : projection * projection = projection)
    (x : index → ℝ) :
    x ⬝ᵥ (projection *ᵥ x) =
      (projection *ᵥ x) ⬝ᵥ (projection *ᵥ x) := by
  have hproduct :
      projection.transpose * projection = projection := by
    rw [hsymmetric, hidempotent]
  calc
    x ⬝ᵥ (projection *ᵥ x) =
        x ⬝ᵥ ((projection.transpose * projection) *ᵥ x) := by
      rw [hproduct]
    _ =
        x ⬝ᵥ
          (projection.transpose *ᵥ (projection *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec]
    _ =
        (projection *ᵥ x) ⬝ᵥ
          (projection *ᵥ x) := by
      rw [Matrix.dotProduct_transpose_mulVec]

/-- Corrected pseudoinverse alignment identity.  The energy is that of the
forward-range projection, not automatically the full error norm. -/
theorem moorePenrose_relation_alignment_eq_projectedEnergy
    {rows cols : Type} [Fintype rows] [Fintype cols]
    {forward : Matrix rows cols ℝ}
    {inverse : Matrix cols rows ℝ}
    (hmp : IsMoorePenroseInverse forward inverse)
    (scale : ℝ)
    (error : rows → ℝ)
    (projectedTarget : cols → ℝ)
    (hrelation :
      projectedTarget =
        -((1 / scale) • (inverse *ᵥ error))) :
    bpModulatorySignal forward error ⬝ᵥ projectedTarget =
      (1 / scale) *
        (((forward * inverse) *ᵥ error) ⬝ᵥ
          ((forward * inverse) *ᵥ error)) := by
  rw [hrelation]
  simp only [bpModulatorySignal, neg_dotProduct_neg, dotProduct_smul]
  rw [Matrix.mulVec_transpose]
  rw [← Matrix.dotProduct_mulVec]
  rw [Matrix.mulVec_mulVec]
  rw [symmetricIdempotent_energy_eq
    hmp.forward_inverse_symmetric
    hmp.forward_inverse_idempotent]
  ring

/-- The corrected source argument is strictly positive exactly when the
forward-range component of the error is nonzero. -/
theorem moorePenrose_relation_alignment_pos
    {rows cols : Type} [Fintype rows] [Fintype cols]
    {forward : Matrix rows cols ℝ}
    {inverse : Matrix cols rows ℝ}
    (hmp : IsMoorePenroseInverse forward inverse)
    (scale : ℝ) (hscale : 0 < scale)
    (error : rows → ℝ)
    (projectedTarget : cols → ℝ)
    (hrelation :
      projectedTarget =
        -((1 / scale) • (inverse *ᵥ error)))
    (hprojectedError :
      (forward * inverse) *ᵥ error ≠ 0) :
    0 <
      bpModulatorySignal forward error ⬝ᵥ projectedTarget := by
  rw [moorePenrose_relation_alignment_eq_projectedEnergy
    hmp scale error projectedTarget hrelation]
  let projected := (forward * inverse) *ᵥ error
  have hnonneg :
      0 ≤ projected ⬝ᵥ projected :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (projected i)
  have hne : projected ⬝ᵥ projected ≠ 0 := by
    intro hz
    exact hprojectedError (dotProduct_self_eq_zero.mp hz)
  have hself : 0 < projected ⬝ᵥ projected :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  exact mul_pos (one_div_pos.mpr hscale) hself

/-! ## Positive and negative fixtures -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- A nontrivial rank-one orthogonal projection. -/
def coordinateProjection : Mat2 :=
  !![1, 0; 0, 0]

/-- The coordinate projection is its own Moore--Penrose inverse. -/
theorem coordinateProjection_self_moorePenrose :
    IsMoorePenroseInverse coordinateProjection coordinateProjection := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [coordinateProjection, Matrix.mul_apply, Fin.sum_univ_two]

/-- A Moore--Penrose product need not be the identity.  This is the exact
boundary omitted by the source's final displayed alignment calculation. -/
theorem moorePenrose_forward_inverse_need_not_be_identity :
    coordinateProjection * coordinateProjection ≠ (1 : Mat2) := by
  intro heq
  have h11 :=
    congrFun (congrFun heq (1 : Fin 2)) (1 : Fin 2)
  norm_num [coordinateProjection, Matrix.mul_apply,
    Fin.sum_univ_two] at h11

def rangeOrthogonalError : Fin 2 → ℝ :=
  ![0, 1]

/-- A nonzero error can have zero component in the forward range, so the
nonzero-projection premise for strict alignment is necessary. -/
theorem nonzeroError_can_have_zero_forwardProjection :
    rangeOrthogonalError ≠ 0 ∧
      (coordinateProjection * coordinateProjection) *ᵥ
          rangeOrthogonalError = 0 := by
  constructor
  · intro heq
    have h1 := congrFun heq (1 : Fin 2)
    norm_num [rangeOrthogonalError] at h1
  · ext i
    fin_cases i <;>
      norm_num [coordinateProjection, rangeOrthogonalError,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def positiveFixtureError : Fin 2 → ℝ :=
  ![1, 1]

def positiveFixtureTarget : Fin 2 → ℝ :=
  ![-1, 0]

/-- In-range error gives a strictly positive, exactly computable alignment. -/
theorem coordinateProjection_positive_alignment :
    positiveFixtureTarget =
        -((1 / (1 : ℝ)) •
          (coordinateProjection *ᵥ positiveFixtureError)) ∧
      bpModulatorySignal coordinateProjection positiveFixtureError ⬝ᵥ
          positiveFixtureTarget = 1 := by
  have hrelation :
      positiveFixtureTarget =
        -((1 / (1 : ℝ)) •
          (coordinateProjection *ᵥ positiveFixtureError)) := by
    ext i
    fin_cases i <;>
      norm_num [coordinateProjection, positiveFixtureError,
        positiveFixtureTarget, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  constructor
  · exact hrelation
  · rw [moorePenrose_relation_alignment_eq_projectedEnergy
      coordinateProjection_self_moorePenrose
      1 positiveFixtureError positiveFixtureTarget hrelation]
    norm_num [coordinateProjection, positiveFixtureError,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

abbrev OneClass := Fin 1

def boundaryProbability : OneClass → ℝ :=
  fun _ => 1

/-- At a saturated probability boundary, the classification error can vanish;
strict alignment therefore needs the source's interior-output premise. -/
theorem saturated_probability_has_zero_error :
    classificationError (0 : OneClass) boundaryProbability = 0 := by
  funext c
  fin_cases c
  norm_num [classificationError, oneHotTarget, boundaryProbability]

#print axioms sameLabel_classificationError_dot_pos
#print axioms classificationError_dot_errorAccumulator_pos
#print axioms rankOneForward_alignment_pos_of_sameLabel_history
#print axioms IsMoorePenroseInverse.forward_inverse_idempotent
#print axioms moorePenrose_relation_alignment_eq_projectedEnergy
#print axioms moorePenrose_relation_alignment_pos
#print axioms moorePenrose_forward_inverse_need_not_be_identity
#print axioms nonzeroError_can_have_zero_forwardProjection
#print axioms coordinateProjection_positive_alignment
#print axioms saturated_probability_has_zero_error

end DirectRandomTargetProjection

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
