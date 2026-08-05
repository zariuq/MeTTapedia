import Mettapedia.MachineLearning.ContinualLearning.ContinualLowRankRouting
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RoutingExpansion

/-!
# Decomposed prompt expansion and its orthogonality boundary

Smith et al., *CODA-Prompt: COntinual Decomposed Attention-based Prompting
for Rehearsal-Free Continual Learning* (CVPR 2023, arXiv:2211.13218), form a
prompt as a weighted sum of prompt components (Equation 3).  Each component
has its own key and attention vector, so appending fresh components does not
alter the previously computed component weights (Equations 4--5).  The source
also penalizes `‖B Bᵀ - I‖` for its prompt, key, and attention matrices
(Equation 6).

This file extracts the exact finite algebra.  Componentwise weighting is
prefix-stable under expansion, while the assembled prompt splits into the old
and fresh contributions.  These facts must not be conflated: unchanged old
weights do not imply unchanged behavior when the fresh contribution is
nonzero.  A globally normalized router has a different boundary; the existing
softmax-expansion theorem is imported and an executable fixture shows the old
weight changing despite frozen old mass.

Equation 6 is represented by a squared Frobenius penalty so that its zero set
is exact.  It vanishes precisely when the row Gram matrix is the identity,
equivalently when the component rows are orthonormal.  Identity and repeated-
row fixtures expose both sides of the boundary.

No claim is made here about learned cosine similarities, differentiability of
the complete transformer, reduced forgetting, privacy, or benchmark accuracy.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace DecomposedPromptComponents

open scoped BigOperators

open ContinualLowRankRouting
open Mettapedia.MachineLearning.NeuralNetworks.Architecture

/-! ## Componentwise prompt construction -/

/-- One prompt component together with its complete component-local weighting
function.  The source's key, attention vector, query, and cosine match are
composed into `weight`; `tensor` is the prompt component itself. -/
structure PromptComponent (Query Tensor : Type*) where
  weight : Query → ℝ
  tensor : Tensor

/-- Component weights in the same order as their prompt tensors. -/
def componentWeights
    {Query Tensor : Type*}
    (query : Query)
    (components : List (PromptComponent Query Tensor)) :
    List ℝ :=
  components.map fun component => component.weight query

/-- Equation 3, generalized from prompt matrices to any real module. -/
def assembledPrompt
    {Query Tensor : Type*}
    [AddCommMonoid Tensor] [Module ℝ Tensor]
    (query : Query)
    (components : List (PromptComponent Query Tensor)) :
    Tensor :=
  (components.map fun component =>
    component.weight query • component.tensor).sum

/-- Appending prompt components appends their independently computed weights.
No old component weight is renormalized. -/
theorem componentWeights_append
    {Query Tensor : Type*}
    (query : Query)
    (old fresh : List (PromptComponent Query Tensor)) :
    componentWeights query (old ++ fresh) =
      componentWeights query old ++ componentWeights query fresh := by
  simp [componentWeights]

/-- Source expansion claim in observable prefix form: every old component
weight is bit-for-bit the old weight after fresh components are appended. -/
theorem componentWeights_take_old_after_append
    {Query Tensor : Type*}
    (query : Query)
    (old fresh : List (PromptComponent Query Tensor)) :
    (componentWeights query (old ++ fresh)).take old.length =
      componentWeights query old := by
  simp [componentWeights]

/-- The assembled prompt over old and fresh components is the additive sum of
the two separately assembled prompts. -/
theorem assembledPrompt_append
    {Query Tensor : Type*}
    [AddCommMonoid Tensor] [Module ℝ Tensor]
    (query : Query)
    (old fresh : List (PromptComponent Query Tensor)) :
    assembledPrompt query (old ++ fresh) =
      assembledPrompt query old + assembledPrompt query fresh := by
  simp [assembledPrompt, List.sum_append]

/-- Expansion preserves the complete assembled prompt exactly when the fresh
weighted contribution vanishes.  Frozen old weights alone are insufficient. -/
theorem assembledPrompt_append_eq_old_iff
    {Query Tensor : Type*}
    [AddCommGroup Tensor] [Module ℝ Tensor]
    (query : Query)
    (old fresh : List (PromptComponent Query Tensor)) :
    assembledPrompt query (old ++ fresh) = assembledPrompt query old ↔
      assembledPrompt query fresh = 0 := by
  rw [assembledPrompt_append]
  exact add_eq_left

/-! ## Equation 6's exact zero set -/

variable
  {Component Feature : Type*}
  [Fintype Component] [DecidableEq Component]
  [Fintype Feature]

/-- Squared-Frobenius form of the source orthogonality penalty.  Squaring does
not change its zero set and keeps finite fixtures algebraic. -/
def codaOrthogonalityPenalty
    (matrix : Matrix Component Feature ℝ) :
    ℝ :=
  frobeniusSquared (matrix * matrix.transpose - 1)

/-- Explicit row-orthonormality predicate for a finite component matrix. -/
def RowsOrthonormal
    (matrix : Matrix Component Feature ℝ) : Prop :=
  ∀ first second,
    (∑ feature, matrix first feature * matrix second feature) =
      if first = second then 1 else 0

/-- The squared penalty vanishes exactly at the advertised Gram identity. -/
theorem codaOrthogonalityPenalty_eq_zero_iff
    (matrix : Matrix Component Feature ℝ) :
    codaOrthogonalityPenalty matrix = 0 ↔
      matrix * matrix.transpose = 1 := by
  rw [codaOrthogonalityPenalty, frobeniusSquared_eq_zero_iff]
  exact sub_eq_zero

omit [Fintype Component] in
/-- The row Gram matrix is the identity exactly when the component rows are
orthonormal in coordinates. -/
theorem gramIdentity_iff_rowsOrthonormal
    (matrix : Matrix Component Feature ℝ) :
    matrix * matrix.transpose = 1 ↔ RowsOrthonormal matrix := by
  constructor
  · intro gram_identity first second
    have entry := congrFun (congrFun gram_identity first) second
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
      using entry
  · intro rows_orthonormal
    ext first second
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
      using rows_orthonormal first second

/-- Equation 6's complete finite zero characterization. -/
theorem codaOrthogonalityPenalty_eq_zero_iff_rowsOrthonormal
    (matrix : Matrix Component Feature ℝ) :
    codaOrthogonalityPenalty matrix = 0 ↔ RowsOrthonormal matrix := by
  rw [codaOrthogonalityPenalty_eq_zero_iff,
    gramIdentity_iff_rowsOrthonormal]

/-! ## Executable positive and negative fixtures -/

/-- Two identical component rows, used to expose the nonorthogonal boundary. -/
def repeatedRowMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ column => if column = 0 then 1 else 0

/-- Orthonormal identity rows give zero Equation 6 penalty. -/
theorem identity_penalty_zero :
    codaOrthogonalityPenalty
      (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  simp [codaOrthogonalityPenalty, frobeniusSquared, entrywisePairing]

/-- Repeating the same unit row gives squared penalty two, not zero. -/
theorem repeated_row_penalty_eq_two :
    codaOrthogonalityPenalty repeatedRowMatrix = 2 := by
  norm_num [codaOrthogonalityPenalty, frobeniusSquared, entrywisePairing,
    repeatedRowMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, Fin.sum_univ_two]

/-- Old component weights are preserved while the assembled scalar prompt
changes from two to fourteen.  This is the strict boundary between
coefficient retention and behavior retention. -/
theorem scalar_expansion_preserves_old_weights_but_changes_prompt :
    let old : List (PromptComponent Unit ℝ) :=
      [⟨fun _ => 1, 2⟩]
    let fresh : List (PromptComponent Unit ℝ) :=
      [⟨fun _ => 3, 4⟩]
    componentWeights () (old ++ fresh) = [1, 3] ∧
      (componentWeights () (old ++ fresh)).take old.length = [1] ∧
      assembledPrompt () old = 2 ∧
      assembledPrompt () (old ++ fresh) = 14 ∧
      assembledPrompt () (old ++ fresh) ≠ assembledPrompt () old := by
  norm_num [componentWeights, assembledPrompt]

/-- If component weights were instead normalized globally, registering unit
new mass would halve the frozen old unit weight.  This is precisely the
normalization boundary proved generally by `finiteSoftmaxExpansion_strictly_decreases`. -/
theorem globallyNormalized_expansion_changes_old_weight :
    expandedRouteWeight 1 1 1 = (1 / 2 : ℝ) ∧
      normalizedRouteWeight 1 1 = 1 ∧
      expandedRouteWeight 1 1 1 ≠ normalizedRouteWeight 1 1 := by
  norm_num [expandedRouteWeight, normalizedRouteWeight]

#print axioms componentWeights_append
#print axioms componentWeights_take_old_after_append
#print axioms assembledPrompt_append
#print axioms assembledPrompt_append_eq_old_iff
#print axioms codaOrthogonalityPenalty_eq_zero_iff
#print axioms gramIdentity_iff_rowsOrthonormal
#print axioms codaOrthogonalityPenalty_eq_zero_iff_rowsOrthonormal
#print axioms identity_penalty_zero
#print axioms repeated_row_penalty_eq_two
#print axioms scalar_expansion_preserves_old_weights_but_changes_prompt
#print axioms globallyNormalized_expansion_changes_old_weight

end DecomposedPromptComponents

end Mettapedia.MachineLearning.ContinualLearning
