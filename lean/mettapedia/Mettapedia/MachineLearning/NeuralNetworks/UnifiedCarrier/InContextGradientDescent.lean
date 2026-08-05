import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.FastWeightMemory

/-!
# In-context linear attention as a gradient update

Von Oswald et al. (2023), *Transformers Learn In-Context by Gradient
Descent*, Proposition 1 and Equations (2)--(8), give a one-head linear
self-attention construction whose token update realizes one finite-batch
linear-regression gradient step.

This file isolates the exact finite algebra for arbitrary sample, input, and
output coordinates.  The residual outer-product matrix is the closed form in
the source's Equation (7).  Linear attention stores its negation as a
fast-weight memory, so updating a token target is exactly subtracting the
weight-change prediction.  Initializing the query target with the negative
pre-update prediction therefore makes the negated output equal the
post-update prediction.  At zero initial weight this specializes to the
source's kernel-smoothing interpretation.

The source construction uses linear, unnormalized attention and a nonempty
training batch.  A concrete negative fixture shows why including a zero-target
query among the keys and values changes the update when the initial weight is
nonzero.  No claim about softmax attention, learned weight discovery,
multi-layer approximation, or empirical in-context performance follows from
these identities.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace InContextGradientDescent

noncomputable section

open scoped BigOperators

variable {Sample Key Value : Type*} [Fintype Sample] [Fintype Key]

abbrev Input (Key : Type*) := Key → ℝ

abbrev Output (Value : Type*) := Value → ℝ

/-- Per-example prediction residual `W x_i - y_i`. -/
def residual
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (sample : Sample) : Output Value :=
  Matrix.mulVec weight (input sample) - target sample

/-- Sum of the residual/input outer products in Equation (7). -/
def batchOuter
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value) :
    Matrix Value Key ℝ :=
  ∑ sample,
    Matrix.vecMulVec
      (residual weight input target sample) (input sample)

/-- The source's finite-batch weight change
`-(rate / batchSize) * sum_i (W x_i - y_i) x_i^T`. -/
def sourceGradientChange
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value) :
    Matrix Value Key ℝ :=
  -((rate / (Fintype.card Sample : ℝ)) •
    batchOuter weight input target)

/-- The one-head linear-attention fast-weight matrix in the construction. -/
def linearAttentionMemory
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value) :
    Matrix Value Key ℝ :=
  (rate / (Fintype.card Sample : ℝ)) •
    batchOuter weight input target

/-- The target-coordinate correction returned by linear attention at a
query. -/
def linearAttentionCorrection
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) : Output Value :=
  (rate / (Fintype.card Sample : ℝ)) •
    ∑ sample,
      (input sample ⬝ᵥ query) •
        residual weight input target sample

/-- The post-gradient-step weight. -/
def updatedWeight
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value) :
    Matrix Value Key ℝ :=
  weight + sourceGradientChange rate weight input target

/-- Update one token's target coordinates by the constructed attention
head. -/
def tokenTargetAfter
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key)
    (initialTarget : Output Value) : Output Value :=
  initialTarget +
    linearAttentionCorrection rate weight input target query

/-- Query-token convention from Proposition 1: initialize the target
coordinates with the negative pre-update prediction. -/
def queryTokenTargetAfter
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) : Output Value :=
  tokenTargetAfter rate weight input target query
    (-(Matrix.mulVec weight query))

/-- The zero-initial-weight specialization in Appendix A.8. -/
def kernelSmoother
    (rate : ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) : Output Value :=
  (rate / (Fintype.card Sample : ℝ)) •
    ∑ sample,
      (input sample ⬝ᵥ query) • target sample

/-- What results if a zero-target query is also admitted to the key/value
set while retaining the training-batch normalization.  The extra term
vanishes at zero initial weight but not in general. -/
def fullAttentionCorrectionIncludingZeroTargetQuery
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) : Output Value :=
  linearAttentionCorrection rate weight input target query +
    (rate / (Fintype.card Sample : ℝ)) •
      ((query ⬝ᵥ query) • Matrix.mulVec weight query)

/-- Multiplying the residual outer-product sum by a query yields the
attention contribution sum. -/
theorem batchOuter_mulVec
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) :
    Matrix.mulVec (batchOuter weight input target) query =
      ∑ sample,
        (input sample ⬝ᵥ query) •
          residual weight input target sample := by
  classical
  simp [batchOuter, Matrix.sum_mulVec, Matrix.vecMulVec_mulVec]

/-- The fast-weight read is exactly the one-head linear-attention
correction. -/
theorem read_linearAttentionMemory
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) :
    FastWeightMemory.read
        (linearAttentionMemory rate weight input target) query =
      linearAttentionCorrection rate weight input target query := by
  rw [FastWeightMemory.read, linearAttentionMemory,
    Matrix.smul_mulVec, batchOuter_mulVec]
  rfl

/-- The attention memory is the negative of the source gradient change. -/
theorem linearAttentionMemory_eq_neg_sourceGradientChange
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value) :
    linearAttentionMemory rate weight input target =
      -sourceGradientChange rate weight input target := by
  simp [linearAttentionMemory, sourceGradientChange]

/-- Prediction change and attention correction have opposite signs. -/
theorem sourceGradientChange_mulVec
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) :
    Matrix.mulVec
        (sourceGradientChange rate weight input target) query =
      -linearAttentionCorrection rate weight input target query := by
  rw [sourceGradientChange, Matrix.neg_mulVec, Matrix.smul_mulVec,
    batchOuter_mulVec]
  rfl

/-- Proposition 1 for arbitrary token target coordinates: the constructed
attention update subtracts the prediction induced by the gradient change. -/
theorem tokenTargetAfter_eq_sub_gradientPrediction
    [Nonempty Sample]
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key)
    (initialTarget : Output Value) :
    tokenTargetAfter rate weight input target query initialTarget =
      initialTarget -
        Matrix.mulVec
          (sourceGradientChange rate weight input target) query := by
  rw [tokenTargetAfter, sourceGradientChange_mulVec]
  module

/-- Proposition 1's query-token crown: negating the updated query target
recovers the post-gradient-step linear-model prediction. -/
theorem queryTokenTargetAfter_eq_neg_updatedPrediction
    [Nonempty Sample]
    (rate : ℝ)
    (weight : Matrix Value Key ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) :
    queryTokenTargetAfter rate weight input target query =
      -(Matrix.mulVec
        (updatedWeight rate weight input target) query) := by
  rw [queryTokenTargetAfter,
    tokenTargetAfter_eq_sub_gradientPrediction,
    updatedWeight, Matrix.add_mulVec]
  module

/-- Appendix A.8: at zero initial weight, the negated query-token output is
the finite kernel smoother using the input dot product. -/
theorem neg_queryTokenTargetAfter_zeroWeight_eq_kernelSmoother
    [Nonempty Sample]
    (rate : ℝ)
    (input : Sample → Input Key)
    (target : Sample → Output Value)
    (query : Input Key) :
    -queryTokenTargetAfter rate
        (0 : Matrix Value Key ℝ) input target query =
      kernelSmoother rate input target query := by
  classical
  simp [queryTokenTargetAfter, tokenTargetAfter,
    linearAttentionCorrection, residual, kernelSmoother]

/-! ## Executable source and boundary fixtures -/

abbrev One := Fin 1

def scalarWeight (value : ℝ) : Matrix One One ℝ :=
  fun _ _ => value

def scalarInput (value : ℝ) : One → Input One :=
  fun _ _ => value

def scalarTarget (value : ℝ) : One → Output One :=
  fun _ _ => value

def scalarQuery (value : ℝ) : Input One :=
  fun _ => value

/-- With `W = 1`, training pair `(2, 5)`, rate one, and query `3`, one
gradient step changes the scalar weight to `7`; the attention query token
therefore reads out `21`. -/
theorem oneSample_queryToken_recovers_gradientPrediction :
    -queryTokenTargetAfter 1
        (scalarWeight 1) (scalarInput 2) (scalarTarget 5)
        (scalarQuery 3) 0 =
      21 := by
  norm_num [queryTokenTargetAfter, tokenTargetAfter,
    linearAttentionCorrection, residual, scalarWeight, scalarInput,
    scalarTarget, scalarQuery, Matrix.mulVec, dotProduct]

/-- Training residual is zero in this fixture, but admitting the zero-target
query to the key/value set adds a nonzero residual term.  Full
self-attention therefore does not recover the training-only gradient
construction at a nonzero initial weight. -/
theorem full_attention_query_contamination :
    fullAttentionCorrectionIncludingZeroTargetQuery 1
        (scalarWeight 1) (scalarInput 1) (scalarTarget 1)
        (scalarQuery 1) 0 ≠
      linearAttentionCorrection 1
        (scalarWeight 1) (scalarInput 1) (scalarTarget 1)
        (scalarQuery 1) 0 := by
  norm_num [fullAttentionCorrectionIncludingZeroTargetQuery,
    linearAttentionCorrection, residual, scalarWeight, scalarInput,
    scalarTarget, scalarQuery, Matrix.mulVec, dotProduct]

#print axioms read_linearAttentionMemory
#print axioms linearAttentionMemory_eq_neg_sourceGradientChange
#print axioms sourceGradientChange_mulVec
#print axioms tokenTargetAfter_eq_sub_gradientPrediction
#print axioms queryTokenTargetAfter_eq_neg_updatedPrediction
#print axioms neg_queryTokenTargetAfter_zeroWeight_eq_kernelSmoother
#print axioms oneSample_queryToken_recovers_gradientPrediction
#print axioms full_attention_query_contamination

end

end InContextGradientDescent

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
