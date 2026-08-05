import Mathlib

/-!
# Scaled dot-product attention

Vaswani et al., *Attention Is All You Need* (arXiv:1706.03762),
define scaled dot-product attention in equation (1) as

`softmax(Q Kᵀ / sqrt(dₖ)) V`.

This file gives the finite exact-real semantics of one query row over an
arbitrary finite key set.  Beyond recovering the source equation, it proves
that the softmax weights are nonnegative affine weights, that the readout is
invariant under a common score shift, and that constant values are preserved.
A negative fixture shows an important multiset boundary: duplicating one
equally scored key changes the readout even though no new value is introduced.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Key Feature Value : Type*}

/-- Dot product of one query and key. -/
def attentionDotScore [Fintype Feature]
    (query key : Feature → ℝ) : ℝ :=
  ∑ feature, query feature * key feature

/-- The source paper's `1 / sqrt(dₖ)` score scaling. -/
def scaledAttentionDotScore [Fintype Feature]
    (query key : Feature → ℝ) : ℝ :=
  attentionDotScore query key / Real.sqrt (Fintype.card Feature)

/-- Softmax normalizing mass for one attention row. -/
def attentionMass [Fintype Key] (score : Key → ℝ) : ℝ :=
  ∑ key, Real.exp (score key)

/-- One normalized attention weight. -/
def attentionWeight [Fintype Key]
    (score : Key → ℝ) (key : Key) : ℝ :=
  Real.exp (score key) / attentionMass score

/-- One exact-real softmax attention row. -/
def softmaxAttention [Fintype Key]
    [NormedAddCommGroup (Value → ℝ)] [NormedSpace ℝ (Value → ℝ)]
    (score : Key → ℝ) (value : Key → Value → ℝ) : Value → ℝ :=
  ∑ key, attentionWeight score key • value key

/-- Equation (1), specialized to a single query row. -/
def scaledDotProductAttention [Fintype Key] [Fintype Feature]
    [NormedAddCommGroup (Value → ℝ)] [NormedSpace ℝ (Value → ℝ)]
    (query : Feature → ℝ) (keys : Key → Feature → ℝ)
    (values : Key → Value → ℝ) : Value → ℝ :=
  softmaxAttention
    (fun key => scaledAttentionDotScore query (keys key))
    values

theorem attentionMass_pos [Fintype Key] [Nonempty Key]
    (score : Key → ℝ) :
    0 < attentionMass score := by
  classical
  exact Finset.sum_pos (fun key _ => Real.exp_pos (score key))
    (Finset.univ_nonempty)

theorem attentionWeight_pos [Fintype Key] [Nonempty Key]
    (score : Key → ℝ) (key : Key) :
    0 < attentionWeight score key := by
  exact div_pos (Real.exp_pos _) (attentionMass_pos score)

/-- Softmax produces affine weights exactly. -/
theorem sum_attentionWeight_eq_one [Fintype Key] [Nonempty Key]
    (score : Key → ℝ) :
    ∑ key, attentionWeight score key = 1 := by
  rw [show (∑ key, attentionWeight score key) =
      attentionMass score / attentionMass score by
    simp [attentionWeight, attentionMass, Finset.sum_div]]
  exact div_self (ne_of_gt (attentionMass_pos score))

/-- Attention preserves a constant value family because its weights are
affine. -/
theorem softmaxAttention_const [Fintype Key] [Nonempty Key]
    [NormedAddCommGroup (Value → ℝ)] [NormedSpace ℝ (Value → ℝ)]
    (score : Key → ℝ) (value : Value → ℝ) :
    softmaxAttention score (fun _ => value) = value := by
  rw [softmaxAttention, ← Finset.sum_smul]
  rw [sum_attentionWeight_eq_one]
  simp

/-- Adding a common logit offset multiplies the softmax mass by a common
positive factor. -/
theorem attentionMass_add_const [Fintype Key]
    (score : Key → ℝ) (offset : ℝ) :
    attentionMass (fun key => score key + offset) =
      attentionMass score * Real.exp offset := by
  simp [attentionMass, Real.exp_add, Finset.sum_mul]

/-- Softmax attention weights are invariant under a common score shift. -/
theorem attentionWeight_add_const [Fintype Key] [Nonempty Key]
    (score : Key → ℝ) (offset : ℝ) (key : Key) :
    attentionWeight (fun item => score item + offset) key =
      attentionWeight score key := by
  rw [attentionWeight, attentionWeight, attentionMass_add_const,
    Real.exp_add]
  field_simp [ne_of_gt (attentionMass_pos score), Real.exp_ne_zero]

/-- Therefore the full readout is invariant under a common score shift. -/
theorem softmaxAttention_add_const [Fintype Key] [Nonempty Key]
    [NormedAddCommGroup (Value → ℝ)] [NormedSpace ℝ (Value → ℝ)]
    (score : Key → ℝ) (offset : ℝ) (values : Key → Value → ℝ) :
    softmaxAttention (fun key => score key + offset) values =
      softmaxAttention score values := by
  apply Finset.sum_congr rfl
  intro key _
  rw [attentionWeight_add_const]

/-- With one feature, scaled dot-product attention has no numerical scaling:
`sqrt(1) = 1`. -/
theorem scaledAttentionDotScore_fin_one
    (query key : Fin 1 → ℝ) :
    scaledAttentionDotScore query key =
      query 0 * key 0 := by
  simp [scaledAttentionDotScore, attentionDotScore]

/-! ## Multiset boundary -/

def twoUniformScores : Fin 2 → ℝ := ![0, 0]

def twoValues : Fin 2 → Fin 1 → ℝ := ![![0], ![2]]

def threeUniformScores : Fin 3 → ℝ := ![0, 0, 0]

def duplicatedSecondValue : Fin 3 → Fin 1 → ℝ :=
  ![![0], ![2], ![2]]

/-- Duplicating one equally scored key changes attention from `1` to `4/3`.
The key collection therefore has multiset, not set, semantics. -/
theorem duplicate_key_changes_attention :
    softmaxAttention twoUniformScores twoValues 0 = 1 ∧
      softmaxAttention threeUniformScores duplicatedSecondValue 0 = 4 / 3 ∧
      softmaxAttention twoUniformScores twoValues 0 ≠
        softmaxAttention threeUniformScores duplicatedSecondValue 0 := by
  simp [softmaxAttention, attentionWeight, attentionMass,
    twoUniformScores, twoValues, threeUniformScores,
    duplicatedSecondValue, Fin.sum_univ_succ]
  norm_num

#print axioms sum_attentionWeight_eq_one
#print axioms softmaxAttention_const
#print axioms attentionWeight_add_const
#print axioms softmaxAttention_add_const
#print axioms scaledAttentionDotScore_fin_one
#print axioms duplicate_key_changes_attention

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
