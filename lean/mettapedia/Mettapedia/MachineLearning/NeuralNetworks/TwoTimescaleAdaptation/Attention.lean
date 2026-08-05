import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Model
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Concrete attention instances and the softmax boundary

Linear attention is defined here as a computation, not as a linear map.  Each
context item contributes an outer-product matrix, the context state is the
sum of those matrices, and a fixed query reads that state.  Additivity and
linearity are proved for those definitions before the resulting readout is
packaged as an instance of `LinearEffectModel`.

Softmax attention has a different boundary.  Concatenating contexts also
changes the shared normalizer, so its readout is a normalized mixture rather
than a sum.  A two-token counterexample and a general two-context error bound
make that failure explicit.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

/-! ## Linear attention, defined concretely -/

/-- One key-feature/value pair in a linear-attention context. -/
structure LinearAttentionItem (Key Value : Type*) where
  keyFeature : Key → ℝ
  value : Value → ℝ

/-- The outer-product state contribution of one context item. -/
def linearAttentionContribution {Key Value : Type*}
    (item : LinearAttentionItem Key Value) : Matrix Key Value ℝ :=
  fun key value => item.keyFeature key * item.value value

/-- The recurrent linear-attention state `S = ∑ⱼ φ(kⱼ) vⱼᵀ`. -/
def accumulatedLinearAttentionState {Key Value : Type*}
    (context : List (LinearAttentionItem Key Value)) : Matrix Key Value ℝ :=
  (context.map linearAttentionContribution).sum

/-- A fixed query reads the accumulated state by contracting its key axis. -/
def linearAttentionReadout {Key Value : Type*} [Fintype Key]
    (query : Key → ℝ) (state : Matrix Key Value ℝ) : Value → ℝ :=
  fun value => ∑ key, query key * state key value

/-- The complete context computation, before any linear-map packaging. -/
def linearAttentionContextEffect {Key Value : Type*} [Fintype Key]
    (query : Key → ℝ) (context : List (LinearAttentionItem Key Value)) :
    Value → ℝ :=
  linearAttentionReadout query (accumulatedLinearAttentionState context)

/-- Appending context items adds their accumulated outer-product states. -/
theorem accumulatedLinearAttentionState_append {Key Value : Type*}
    (left right : List (LinearAttentionItem Key Value)) :
    accumulatedLinearAttentionState (left ++ right) =
      accumulatedLinearAttentionState left +
        accumulatedLinearAttentionState right := by
  simp [accumulatedLinearAttentionState, List.sum_append]

/-- The concrete query contraction preserves addition of states. -/
theorem linearAttentionReadout_add {Key Value : Type*} [Fintype Key]
    (query : Key → ℝ) (left right : Matrix Key Value ℝ) :
    linearAttentionReadout query (left + right) =
      linearAttentionReadout query left + linearAttentionReadout query right := by
  funext value
  simp only [linearAttentionReadout, Matrix.add_apply, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

/-- The concrete query contraction preserves scalar multiplication. -/
theorem linearAttentionReadout_smul {Key Value : Type*} [Fintype Key]
    (query : Key → ℝ) (scalar : ℝ) (state : Matrix Key Value ℝ) :
    linearAttentionReadout query (scalar • state) =
      scalar • linearAttentionReadout query state := by
  funext value
  simp only [linearAttentionReadout, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro key _
  ring

/-- A linear-attention context effect is exactly additive under context
concatenation. -/
theorem linearAttentionContextEffect_append {Key Value : Type*} [Fintype Key]
    (query : Key → ℝ)
    (left right : List (LinearAttentionItem Key Value)) :
    linearAttentionContextEffect query (left ++ right) =
      linearAttentionContextEffect query left +
        linearAttentionContextEffect query right := by
  rw [linearAttentionContextEffect, accumulatedLinearAttentionState_append,
    linearAttentionReadout_add]
  rfl

/-- Only after the concrete proofs, package query contraction as a linear map. -/
noncomputable def linearAttentionReadoutLinearMap
    {Key Value : Type*} [Fintype Key] (query : Key → ℝ) :
    Matrix Key Value ℝ →ₗ[ℝ] (Value → ℝ) where
  toFun := linearAttentionReadout query
  map_add' := linearAttentionReadout_add query
  map_smul' := linearAttentionReadout_smul query

/-- Linear attention supplies both the persistent and fast-state effect maps
of the abstract two-timescale interface. -/
noncomputable def linearAttentionEffectModel
    {Key Value : Type*} [Fintype Key] (query : Key → ℝ) :
    LinearEffectModel (Matrix Key Value ℝ) (Matrix Key Value ℝ) (Value → ℝ) where
  slowEffect := linearAttentionReadoutLinearMap query
  fastEffect := linearAttentionReadoutLinearMap query

/-- The packaged fast effect is the previously proved concrete computation. -/
theorem linearAttentionEffectModel_fastEffect_eq_contextEffect
    {Key Value : Type*} [Fintype Key] (query : Key → ℝ)
    (context : List (LinearAttentionItem Key Value)) :
    (linearAttentionEffectModel query).fastEffect
        (accumulatedLinearAttentionState context) =
      linearAttentionContextEffect query context := by
  rfl

/-- Positive fixture: two scalar context items contribute by ordinary
addition. -/
theorem scalarLinearAttention_additive :
    linearAttentionContextEffect (fun _ : Fin 1 => 1)
        [⟨fun _ => 1, fun _ => 2⟩, ⟨fun _ => 1, fun _ => 3⟩] 0 = 5 := by
  norm_num [linearAttentionContextEffect, linearAttentionReadout,
    accumulatedLinearAttentionState, linearAttentionContribution]

/-! ## Softmax is normalized, not additive -/

/-- Unnormalized exponential mass of a scored scalar context. -/
noncomputable def softmaxMass (context : List (ℝ × ℝ)) : ℝ :=
  (context.map fun item => Real.exp item.1).sum

/-- Exponentially weighted scalar numerator. -/
noncomputable def softmaxNumerator (context : List (ℝ × ℝ)) : ℝ :=
  (context.map fun item => Real.exp item.1 * item.2).sum

/-- Scalar softmax attention.  The pair fields are score and value. -/
noncomputable def scalarSoftmaxAttention (context : List (ℝ × ℝ)) : ℝ :=
  softmaxNumerator context / softmaxMass context

/-- The algebraic operation induced by combining two already-normalized
contexts with positive normalizer masses. -/
noncomputable def normalizedContextMerge
    (leftMass rightMass leftValue rightValue : ℝ) : ℝ :=
  (leftMass * leftValue + rightMass * rightValue) /
    (leftMass + rightMass)

/-- Concatenated softmax attention is a mass-weighted merge, not addition. -/
theorem scalarSoftmaxAttention_append
    (left right : List (ℝ × ℝ))
    (hleft : softmaxMass left ≠ 0) (hright : softmaxMass right ≠ 0)
    (hsum : softmaxMass left + softmaxMass right ≠ 0) :
    scalarSoftmaxAttention (left ++ right) =
      normalizedContextMerge (softmaxMass left) (softmaxMass right)
        (scalarSoftmaxAttention left) (scalarSoftmaxAttention right) := by
  have hmass : softmaxMass (left ++ right) =
      softmaxMass left + softmaxMass right := by
    simp [softmaxMass, List.sum_append]
  have hnum : softmaxNumerator (left ++ right) =
      softmaxNumerator left + softmaxNumerator right := by
    simp [softmaxNumerator, List.sum_append]
  rw [scalarSoftmaxAttention, hmass, hnum]
  unfold normalizedContextMerge scalarSoftmaxAttention
  field_simp [hleft, hright, hsum]

/-- Exact defect from pretending a normalized merge were additive. -/
theorem normalizedContextMerge_sub_add_exact
    (leftMass rightMass leftValue rightValue : ℝ)
    (hmass : leftMass + rightMass ≠ 0) :
    normalizedContextMerge leftMass rightMass leftValue rightValue -
        (leftValue + rightValue) =
      -(rightMass * leftValue + leftMass * rightValue) /
        (leftMass + rightMass) := by
  unfold normalizedContextMerge
  field_simp
  ring

/-- For positive masses, the nonadditivity defect is bounded by the sum of
the component magnitudes. -/
theorem abs_normalizedContextMerge_sub_add_le
    (leftMass rightMass leftValue rightValue : ℝ)
    (hleft : 0 < leftMass) (hright : 0 < rightMass) :
    |normalizedContextMerge leftMass rightMass leftValue rightValue -
        (leftValue + rightValue)| ≤ |leftValue| + |rightValue| := by
  have hsum : 0 < leftMass + rightMass := add_pos hleft hright
  rw [normalizedContextMerge_sub_add_exact _ _ _ _ hsum.ne', abs_div,
    abs_neg, abs_of_pos hsum]
  calc
    |rightMass * leftValue + leftMass * rightValue| /
          (leftMass + rightMass) ≤
        (|rightMass * leftValue| + |leftMass * rightValue|) /
          (leftMass + rightMass) :=
      (div_le_div_iff_of_pos_right hsum).2 (abs_add_le _ _)
    _ = (rightMass * |leftValue| + leftMass * |rightValue|) /
          (leftMass + rightMass) := by
      rw [abs_mul, abs_mul, abs_of_pos hright, abs_of_pos hleft]
    _ ≤ |leftValue| + |rightValue| := by
      rw [div_le_iff₀ hsum]
      nlinarith [abs_nonneg leftValue, abs_nonneg rightValue]

/-- Explicit negative fixture: two unit-score singleton contexts read as one
and three separately, but their concatenation reads as two rather than four. -/
theorem scalarSoftmaxAttention_not_additive :
    scalarSoftmaxAttention [(0, 1)] = 1 ∧
      scalarSoftmaxAttention [(0, 3)] = 3 ∧
      scalarSoftmaxAttention ([(0, 1)] ++ [(0, 3)]) = 2 ∧
      scalarSoftmaxAttention ([(0, 1)] ++ [(0, 3)]) ≠
        scalarSoftmaxAttention [(0, 1)] +
          scalarSoftmaxAttention [(0, 3)] := by
  norm_num [scalarSoftmaxAttention, softmaxMass, softmaxNumerator]

#print axioms linearAttentionContextEffect_append
#print axioms linearAttentionEffectModel_fastEffect_eq_contextEffect
#print axioms abs_normalizedContextMerge_sub_add_le
#print axioms scalarSoftmaxAttention_not_additive

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
