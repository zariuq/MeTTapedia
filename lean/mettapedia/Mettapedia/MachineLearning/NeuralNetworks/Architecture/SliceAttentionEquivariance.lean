import Mettapedia.MachineLearning.NeuralNetworks.Architecture.EncoderEquivariance
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.ScaledDotProductAttention

/-!
# Equivariance of finite vector-slice attention

Structured weight-space attention treats rows and columns of weight matrices
as vectors.  This file proves the exact transport laws needed for those
slice-level operations:

* a dot product is invariant under a shared feature-coordinate relabeling;
* its standard square-root scaling is invariant as well;
* softmax mass and weights commute with key relabeling;
* a complete scaled dot-product attention row commutes with independent key,
  feature, and output-feature relabelings.

The negative fixture changes only the query coordinates while keeping the key
coordinates fixed.  Its dot product changes from one to zero, recording why
the feature transport must be shared.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

universe uKeyLeft uKeyRight uFeatureLeft uFeatureRight
  uValueLeft uValueRight uScalar

/-- Transport both axes of a row-indexed feature family. -/
def transportMatrix
    {RowLeft : Type*} {RowRight : Type*}
    {ColumnLeft : Type*} {ColumnRight : Type*}
    {Scalar : Type uScalar}
    (rowRelabel : RowLeft ≃ RowRight)
    (columnRelabel : ColumnLeft ≃ ColumnRight)
    (matrix : RowLeft → ColumnLeft → Scalar) :
    RowRight → ColumnRight → Scalar :=
  fun row column =>
    matrix (rowRelabel.symm row) (columnRelabel.symm column)

@[simp] theorem transportMatrix_apply
    {RowLeft : Type*} {RowRight : Type*}
    {ColumnLeft : Type*} {ColumnRight : Type*}
    {Scalar : Type uScalar}
    (rowRelabel : RowLeft ≃ RowRight)
    (columnRelabel : ColumnLeft ≃ ColumnRight)
    (matrix : RowLeft → ColumnLeft → Scalar)
    (row : RowLeft) (column : ColumnLeft) :
    transportMatrix rowRelabel columnRelabel matrix
        (rowRelabel row) (columnRelabel column) =
      matrix row column := by
  simp [transportMatrix]

/-- Shared feature-coordinate transport preserves a finite dot product. -/
theorem attentionDotScore_transport
    {FeatureLeft : Type uFeatureLeft}
    {FeatureRight : Type uFeatureRight}
    [Fintype FeatureLeft] [Fintype FeatureRight]
    (featureRelabel : FeatureLeft ≃ FeatureRight)
    (query key : FeatureLeft → ℝ) :
    attentionDotScore
        (transportRows featureRelabel query)
        (transportRows featureRelabel key) =
      attentionDotScore query key := by
  unfold attentionDotScore
  symm
  apply Fintype.sum_equiv featureRelabel
  intro feature
  simp [transportRows]

/-- Shared feature transport also preserves the standard `sqrt(d)`-scaled
dot product. -/
theorem scaledAttentionDotScore_transport
    {FeatureLeft : Type uFeatureLeft}
    {FeatureRight : Type uFeatureRight}
    [Fintype FeatureLeft] [Fintype FeatureRight]
    (featureRelabel : FeatureLeft ≃ FeatureRight)
    (query key : FeatureLeft → ℝ) :
    scaledAttentionDotScore
        (transportRows featureRelabel query)
        (transportRows featureRelabel key) =
      scaledAttentionDotScore query key := by
  unfold scaledAttentionDotScore
  rw [attentionDotScore_transport]
  rw [← Fintype.card_congr featureRelabel]

/-- Reindexing a finite score family preserves its softmax normalizer. -/
theorem attentionMass_transport
    {KeyLeft : Type uKeyLeft} {KeyRight : Type uKeyRight}
    [Fintype KeyLeft] [Fintype KeyRight]
    (keyRelabel : KeyLeft ≃ KeyRight)
    (score : KeyLeft → ℝ) :
    attentionMass (transportRows keyRelabel score) =
      attentionMass score := by
  unfold attentionMass
  symm
  apply Fintype.sum_equiv keyRelabel
  intro key
  simp [transportRows]

/-- A softmax weight follows its key under key-set relabeling. -/
theorem attentionWeight_transport
    {KeyLeft : Type uKeyLeft} {KeyRight : Type uKeyRight}
    [Fintype KeyLeft] [Fintype KeyRight]
    (keyRelabel : KeyLeft ≃ KeyRight)
    (score : KeyLeft → ℝ) (key : KeyLeft) :
    attentionWeight (transportRows keyRelabel score)
        (keyRelabel key) =
      attentionWeight score key := by
  simp [attentionWeight, transportRows, attentionMass_transport]

/-- Softmax aggregation commutes with simultaneous key and output-feature
relabeling. -/
theorem softmaxAttention_transport
    {KeyLeft : Type uKeyLeft} {KeyRight : Type uKeyRight}
    {ValueLeft : Type uValueLeft} {ValueRight : Type uValueRight}
    [Fintype KeyLeft] [Fintype KeyRight]
    [Fintype ValueLeft] [Fintype ValueRight]
    (keyRelabel : KeyLeft ≃ KeyRight)
    (valueRelabel : ValueLeft ≃ ValueRight)
    (score : KeyLeft → ℝ)
    (values : KeyLeft → ValueLeft → ℝ)
    (value : ValueLeft) :
    softmaxAttention
        (transportRows keyRelabel score)
        (transportMatrix keyRelabel valueRelabel values)
        (valueRelabel value) =
      softmaxAttention score values value := by
  simp only [softmaxAttention, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv keyRelabel
  intro key
  rw [attentionWeight_transport]
  simp [transportMatrix]

/-- A complete finite scaled dot-product attention row is equivariant under
independent relabelings of its key set, shared query/key feature coordinates,
and output-value coordinates. -/
theorem scaledDotProductAttention_transport
    {KeyLeft : Type uKeyLeft} {KeyRight : Type uKeyRight}
    {FeatureLeft : Type uFeatureLeft}
    {FeatureRight : Type uFeatureRight}
    {ValueLeft : Type uValueLeft} {ValueRight : Type uValueRight}
    [Fintype KeyLeft] [Fintype KeyRight]
    [Fintype FeatureLeft] [Fintype FeatureRight]
    [Fintype ValueLeft] [Fintype ValueRight]
    (keyRelabel : KeyLeft ≃ KeyRight)
    (featureRelabel : FeatureLeft ≃ FeatureRight)
    (valueRelabel : ValueLeft ≃ ValueRight)
    (query : FeatureLeft → ℝ)
    (keys : KeyLeft → FeatureLeft → ℝ)
    (values : KeyLeft → ValueLeft → ℝ)
    (value : ValueLeft) :
    scaledDotProductAttention
        (transportRows featureRelabel query)
        (transportMatrix keyRelabel featureRelabel keys)
        (transportMatrix keyRelabel valueRelabel values)
        (valueRelabel value) =
      scaledDotProductAttention query keys values value := by
  have scoreEq :
      (fun key =>
        scaledAttentionDotScore
          (transportRows featureRelabel query)
          (transportMatrix keyRelabel featureRelabel keys key)) =
        transportRows keyRelabel
          (fun key => scaledAttentionDotScore query (keys key)) := by
    funext transportedKey
    obtain ⟨key, rfl⟩ := keyRelabel.surjective transportedKey
    have keySliceEq :
        transportMatrix keyRelabel featureRelabel keys
            (keyRelabel key) =
          transportRows featureRelabel (keys key) := by
      funext feature
      simp [transportMatrix, transportRows]
    rw [keySliceEq]
    simpa [transportRows] using
      scaledAttentionDotScore_transport featureRelabel query (keys key)
  unfold scaledDotProductAttention
  rw [scoreEq]
  exact
    softmaxAttention_transport
      keyRelabel valueRelabel
      (fun key => scaledAttentionDotScore query (keys key))
      values value

namespace SliceAttentionFixtures

def featureSwap : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

def firstBasis : Fin 2 → ℝ :=
  ![1, 0]

/-- Relabeling only the query while leaving the key fixed breaks the shared
feature-coordinate transport law. -/
theorem queryOnlySwap_changes_dotScore :
    attentionDotScore
        (transportRows featureSwap firstBasis)
        firstBasis = 0 ∧
      attentionDotScore firstBasis firstBasis = 1 := by
  norm_num
    [attentionDotScore, transportRows, featureSwap, firstBasis,
      Equiv.swap_apply_def, Fin.sum_univ_two]

/-- Relabeling both operands restores the dot product exactly. -/
theorem sharedSwap_preserves_dotScore :
    attentionDotScore
        (transportRows featureSwap firstBasis)
        (transportRows featureSwap firstBasis) =
      attentionDotScore firstBasis firstBasis :=
  attentionDotScore_transport featureSwap firstBasis firstBasis

end SliceAttentionFixtures

#print axioms attentionDotScore_transport
#print axioms scaledAttentionDotScore_transport
#print axioms attentionWeight_transport
#print axioms softmaxAttention_transport
#print axioms scaledDotProductAttention_transport
#print axioms SliceAttentionFixtures.queryOnlySwap_changes_dotScore
#print axioms SliceAttentionFixtures.sharedSwap_preserves_dotScore

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
