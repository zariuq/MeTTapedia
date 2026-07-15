import Mathlib.Tactic
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianOperator

/-!
# Observational and interventional causal-direction boundary for quadratic PC

This file isolates the cheapest decisive causal-identifiability test for
linear-Gaussian predictive coding.  A positive-definite observational
covariance is fitted in the two distinct orientations `X → Y` and `Y → X`.
Although their residual operators are different, both fitted
precision-weighted residual energies reduce pointwise to the same Mahalanobis
quadratic.  Consequently no finite observational batch can distinguish the
orientations by this energy when root and residual variances are fitted
freely.

Here "Gaussian" describes the quadratic residual energy, not a hypothesis on
the samples: the batch equality below quantifies over arbitrary real-valued
data.  The final sections record the exact scope boundary.  Requiring equal
structural-noise variances can distinguish every correlated two-node
covariance for which one orientation satisfies the restriction.  Independence
with equal marginal variances remains an explicit negative example.  We then
separate conditioning from intervention by applying one direction-agnostic
operation: clamp a node and delete that node's own residual term.

The intervention semantics follows Pearl, *The Do-Calculus Revisited* (2012):
the local PDF checked on 2026-07-15 had SHA-256
`04fb655521992f035f73f6657e2bfc5d3f757e7242e74d110f30a6f646502afa`.
The structural-equation frame is also checked against Halpern,
*Axiomatizing Causal Reasoning* (2000), local PDF SHA-256
`af8987f17d4dafe51f9ff46af7d817ec172f1bf748e138a4bb4b24b4ceefca5a`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Positive observational covariance -/

/-- A centered positive-definite covariance for two scalar observations. -/
structure PositiveBivariateCovariance where
  varX : ℝ
  varY : ℝ
  covXY : ℝ
  varX_pos : 0 < varX
  varY_pos : 0 < varY
  determinant_positive : 0 < varX * varY - covXY ^ 2

namespace PositiveBivariateCovariance

/-- Determinant of the observational covariance matrix. -/
noncomputable def determinant (covariance : PositiveBivariateCovariance) : ℝ :=
  covariance.varX * covariance.varY - covariance.covXY ^ 2

theorem determinant_pos (covariance : PositiveBivariateCovariance) :
    0 < covariance.determinant :=
  covariance.determinant_positive

theorem varX_ne_zero (covariance : PositiveBivariateCovariance) :
    covariance.varX ≠ 0 :=
  ne_of_gt covariance.varX_pos

theorem varY_ne_zero (covariance : PositiveBivariateCovariance) :
    covariance.varY ≠ 0 :=
  ne_of_gt covariance.varY_pos

theorem determinant_ne_zero (covariance : PositiveBivariateCovariance) :
    covariance.determinant ≠ 0 :=
  ne_of_gt covariance.determinant_pos

/-! ## The two fitted orientations -/

/-- Regression coefficient fitted from the covariance in direction `X → Y`. -/
noncomputable def forwardCoefficient
    (covariance : PositiveBivariateCovariance) : ℝ :=
  covariance.covXY / covariance.varX

/-- Conditional residual variance fitted in direction `X → Y`. -/
noncomputable def forwardResidualVariance
    (covariance : PositiveBivariateCovariance) : ℝ :=
  covariance.determinant / covariance.varX

/-- Regression coefficient fitted from the covariance in direction `Y → X`. -/
noncomputable def reverseCoefficient
    (covariance : PositiveBivariateCovariance) : ℝ :=
  covariance.covXY / covariance.varY

/-- Conditional residual variance fitted in direction `Y → X`. -/
noncomputable def reverseResidualVariance
    (covariance : PositiveBivariateCovariance) : ℝ :=
  covariance.determinant / covariance.varY

theorem forwardResidualVariance_pos
    (covariance : PositiveBivariateCovariance) :
    0 < covariance.forwardResidualVariance :=
  div_pos covariance.determinant_pos covariance.varX_pos

theorem reverseResidualVariance_pos
    (covariance : PositiveBivariateCovariance) :
    0 < covariance.reverseResidualVariance :=
  div_pos covariance.determinant_pos covariance.varY_pos

/-- Residual operator for `X → Y`: root residual `x`, then `y - βx`. -/
noncomputable def forwardResidualMatrix
    (covariance : PositiveBivariateCovariance) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; -covariance.forwardCoefficient, 1]

/-- Residual operator for `Y → X`: root residual `y`, then `x - γy`. -/
noncomputable def reverseResidualMatrix
    (covariance : PositiveBivariateCovariance) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, -covariance.reverseCoefficient]

/-- The two oriented residual operators are genuinely distinct, independently
of their fitted coefficients. -/
theorem forwardResidualMatrix_ne_reverseResidualMatrix
    (covariance : PositiveBivariateCovariance) :
    covariance.forwardResidualMatrix ≠ covariance.reverseResidualMatrix := by
  intro h
  have h00 := congrArg (fun matrix => matrix 0 0) h
  norm_num [forwardResidualMatrix, reverseResidualMatrix] at h00

/-! ## Covariance-only energy and pointwise observational equivalence -/

/-- Precision-weighted residual energy of the fitted direction `X → Y`. -/
noncomputable def forwardGaussianPCEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  x ^ 2 / covariance.varX +
    (y - covariance.forwardCoefficient * x) ^ 2 /
      covariance.forwardResidualVariance

/-- Precision-weighted residual energy of the fitted direction `Y → X`. -/
noncomputable def reverseGaussianPCEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  y ^ 2 / covariance.varY +
    (x - covariance.reverseCoefficient * y) ^ 2 /
      covariance.reverseResidualVariance

/-- Mahalanobis quadratic determined solely by the observational covariance. -/
noncomputable def observationalMahalanobisEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  (covariance.varY * x ^ 2 - 2 * covariance.covXY * x * y +
      covariance.varX * y ^ 2) / covariance.determinant

/-- The forward fitted energy depends on the data model only through the
observational covariance. -/
theorem forwardGaussianPCEnergy_eq_observationalMahalanobis
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.forwardGaussianPCEnergy x y =
      covariance.observationalMahalanobisEnergy x y := by
  unfold forwardGaussianPCEnergy forwardCoefficient forwardResidualVariance
    observationalMahalanobisEnergy determinant
  have hdet : covariance.varX * covariance.varY - covariance.covXY ^ 2 ≠ 0 :=
    ne_of_gt covariance.determinant_positive
  field_simp [covariance.varX_ne_zero, hdet]
  field_simp [hdet]
  ring

/-- The reverse fitted energy is the same covariance-only quadratic. -/
theorem reverseGaussianPCEnergy_eq_observationalMahalanobis
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.reverseGaussianPCEnergy x y =
      covariance.observationalMahalanobisEnergy x y := by
  unfold reverseGaussianPCEnergy reverseCoefficient reverseResidualVariance
    observationalMahalanobisEnergy determinant
  have hdet : covariance.varX * covariance.varY - covariance.covXY ^ 2 ≠ 0 :=
    ne_of_gt covariance.determinant_positive
  have hdetReverse :
      covariance.varY * covariance.varX - covariance.covXY ^ 2 ≠ 0 := by
    rwa [mul_comm covariance.varY covariance.varX]
  field_simp [covariance.varY_ne_zero, hdet, hdetReverse]
  ring

/-- The distinct fitted orientations have identical energy for every
observation, not merely the same optimum or expectation. -/
theorem forwardGaussianPCEnergy_eq_reverseGaussianPCEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.forwardGaussianPCEnergy x y =
      covariance.reverseGaussianPCEnergy x y := by
  rw [covariance.forwardGaussianPCEnergy_eq_observationalMahalanobis,
    covariance.reverseGaussianPCEnergy_eq_observationalMahalanobis]

/-- Energy separation by at least one observational sample. -/
def SeparatesDirectionsByEnergy
    (covariance : PositiveBivariateCovariance) : Prop :=
  ∃ x y : ℝ,
    covariance.forwardGaussianPCEnergy x y ≠
      covariance.reverseGaussianPCEnergy x y

/-- Causal-identifiability boundary: freely fitting root and residual
variances makes the two Gaussian directions observationally inseparable by
predictive-coding energy. -/
theorem not_separatesDirectionsByEnergy
    (covariance : PositiveBivariateCovariance) :
    ¬ covariance.SeparatesDirectionsByEnergy := by
  rintro ⟨x, y, hne⟩
  exact hne (covariance.forwardGaussianPCEnergy_eq_reverseGaussianPCEnergy x y)

/-- Pointwise equality lifts to every finite observational batch. -/
theorem forward_batchEnergy_eq_reverse_batchEnergy
    {Sample : Type*} [Fintype Sample]
    (covariance : PositiveBivariateCovariance) (x y : Sample → ℝ) :
    ∑ sample,
        covariance.forwardGaussianPCEnergy (x sample) (y sample) =
      ∑ sample,
        covariance.reverseGaussianPCEnergy (x sample) (y sample) := by
  apply Finset.sum_congr rfl
  intro sample _
  exact covariance.forwardGaussianPCEnergy_eq_reverseGaussianPCEnergy
    (x sample) (y sample)

/-- Crown result: the two fitted DAG orientations use distinct residual
operators but the same observational energy on every finite batch. -/
theorem distinct_orientations_same_observational_batchEnergy
    {Sample : Type*} [Fintype Sample]
    (covariance : PositiveBivariateCovariance) (x y : Sample → ℝ) :
    covariance.forwardResidualMatrix ≠ covariance.reverseResidualMatrix ∧
      (∑ sample,
          covariance.forwardGaussianPCEnergy (x sample) (y sample)) =
        ∑ sample,
          covariance.reverseGaussianPCEnergy (x sample) (y sample) :=
  ⟨covariance.forwardResidualMatrix_ne_reverseResidualMatrix,
    covariance.forward_batchEnergy_eq_reverse_batchEnergy x y⟩

/-! ## Equal structural-noise boundary -/

/-- The fitted `X → Y` orientation obeys a common variance for its root and
conditional structural noises. -/
def ForwardEqualNoiseCompatible
    (covariance : PositiveBivariateCovariance) : Prop :=
  covariance.varX = covariance.forwardResidualVariance

/-- The fitted `Y → X` orientation obeys a common variance for its root and
conditional structural noises. -/
def ReverseEqualNoiseCompatible
    (covariance : PositiveBivariateCovariance) : Prop :=
  covariance.varY = covariance.reverseResidualVariance

theorem forwardEqualNoiseCompatible_iff
    (covariance : PositiveBivariateCovariance) :
    covariance.ForwardEqualNoiseCompatible ↔
      covariance.varX ^ 2 = covariance.determinant := by
  unfold ForwardEqualNoiseCompatible forwardResidualVariance
  field_simp [covariance.varX_ne_zero]

theorem reverseEqualNoiseCompatible_iff
    (covariance : PositiveBivariateCovariance) :
    covariance.ReverseEqualNoiseCompatible ↔
      covariance.varY ^ 2 = covariance.determinant := by
  unfold ReverseEqualNoiseCompatible reverseResidualVariance
  field_simp [covariance.varY_ne_zero]

/-- With nonzero covariance, the equal-structural-noise restriction cannot fit
both orientations.  Thus that additional assumption escapes the free-variance
impossibility. -/
theorem correlated_not_both_equalNoiseCompatible
    (covariance : PositiveBivariateCovariance)
    (hcorrelated : covariance.covXY ≠ 0) :
    ¬ (covariance.ForwardEqualNoiseCompatible ∧
        covariance.ReverseEqualNoiseCompatible) := by
  rintro ⟨hforward, hreverse⟩
  rw [covariance.forwardEqualNoiseCompatible_iff] at hforward
  rw [covariance.reverseEqualNoiseCompatible_iff] at hreverse
  have hsq : covariance.varX ^ 2 = covariance.varY ^ 2 := hforward.trans hreverse.symm
  have hsum_pos : 0 < covariance.varX + covariance.varY :=
    add_pos covariance.varX_pos covariance.varY_pos
  have hvars : covariance.varX = covariance.varY := by
    nlinarith
  unfold determinant at hforward
  rw [hvars] at hforward
  have : covariance.covXY ^ 2 = 0 := by
    nlinarith
  exact hcorrelated (sq_eq_zero_iff.mp this)

/-! ## Exact positive and negative fixtures -/

/-- Covariance of `X = ε₁`, `Y = X + ε₂` with independent unit-variance
structural noises. -/
noncomputable def unitNoiseForwardCovariance : PositiveBivariateCovariance where
  varX := 1
  varY := 2
  covXY := 1
  varX_pos := by norm_num
  varY_pos := by norm_num
  determinant_positive := by norm_num

theorem unitNoiseForwardCovariance_forwardCompatible :
    unitNoiseForwardCovariance.ForwardEqualNoiseCompatible := by
  norm_num [ForwardEqualNoiseCompatible, forwardResidualVariance,
    determinant, unitNoiseForwardCovariance]

theorem unitNoiseForwardCovariance_reverseNotCompatible :
    ¬ unitNoiseForwardCovariance.ReverseEqualNoiseCompatible := by
  norm_num [ReverseEqualNoiseCompatible, reverseResidualVariance,
    determinant, unitNoiseForwardCovariance]

/-- Independent variables of equal variance are compatible with the equal-noise
restriction in both orientations. -/
noncomputable def independentEqualVarianceCovariance :
    PositiveBivariateCovariance where
  varX := 1
  varY := 1
  covXY := 0
  varX_pos := by norm_num
  varY_pos := by norm_num
  determinant_positive := by norm_num

theorem independentEqualVarianceCovariance_bothCompatible :
    independentEqualVarianceCovariance.ForwardEqualNoiseCompatible ∧
      independentEqualVarianceCovariance.ReverseEqualNoiseCompatible := by
  constructor <;>
    norm_num [ForwardEqualNoiseCompatible, ReverseEqualNoiseCompatible,
      forwardResidualVariance, reverseResidualVariance, determinant,
      independentEqualVarianceCovariance]

/-! ## A uniform node-residual intervention operation -/

/-- A two-node quadratic residual model whose rows are indexed by the node
whose structural residual they encode: row `0` belongs to `X`, row `1` to
`Y`.  The distinguished coefficient condition makes `Y` a valid free
coordinate after clamping `X`. -/
structure TwoNodeQuadraticResidualModel where
  residualMatrix : Matrix (Fin 2) (Fin 2) ℝ
  residualVariance : Fin 2 → ℝ
  residualVariance_pos : ∀ node, 0 < residualVariance node
  ySelfCoefficient : residualMatrix 1 1 = 1

namespace TwoNodeQuadraticResidualModel

/-- The diagonal half-precision used by the conventional quadratic energy. -/
noncomputable def residualPrecision
    (model : TwoNodeQuadraticResidualModel) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun node => (2 * model.residualVariance node)⁻¹

theorem residualPrecision_posDef
    (model : TwoNodeQuadraticResidualModel) :
    model.residualPrecision.PosDef := by
  unfold residualPrecision
  apply Matrix.PosDef.diagonal
  intro node
  exact inv_pos.mpr (mul_pos (by norm_num) (model.residualVariance_pos node))

/-- One node's precision-weighted structural residual contribution. -/
noncomputable def residualContribution
    (model : TwoNodeQuadraticResidualModel) (node : Fin 2)
    (state : Fin 2 → ℝ) : ℝ :=
  (model.residualMatrix.mulVec state node) ^ 2 /
    (2 * model.residualVariance node)

/-- Full half-normalized quadratic residual energy. -/
noncomputable def energy
    (model : TwoNodeQuadraticResidualModel) (state : Fin 2 → ℝ) : ℝ :=
  let residual := model.residualMatrix.mulVec state
  residual ⬝ᵥ model.residualPrecision.mulVec residual

theorem energy_eq_sum_residualContribution
    (model : TwoNodeQuadraticResidualModel) (state : Fin 2 → ℝ) :
    model.energy state = ∑ node, model.residualContribution node state := by
  simp [energy, residualPrecision, residualContribution, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
  ring

/-- Clamping changes one state coordinate but retains every residual term. -/
noncomputable def clamp
    (model : TwoNodeQuadraticResidualModel) (node : Fin 2) (value : ℝ)
    (state : Fin 2 → ℝ) : ℝ :=
  model.energy (Function.update state node value)

/-- Intervention is one orientation-independent operation: clamp the node and
delete exactly the residual term owned by that node. -/
noncomputable def intervene
    (model : TwoNodeQuadraticResidualModel) (node : Fin 2) (value : ℝ)
    (state : Fin 2 → ℝ) : ℝ :=
  ∑ residualNode ∈ (Finset.univ : Finset (Fin 2)).erase node,
    model.residualContribution residualNode (Function.update state node value)

end TwoNodeQuadraticResidualModel

/-- A two-coordinate state in the fixed node order `(X,Y)`. -/
noncomputable def twoNodeState (x y : ℝ) : Fin 2 → ℝ := ![x, y]

/-- Node-indexed residual model for `X → Y`. -/
noncomputable def forwardNodeResidualModel
    (covariance : PositiveBivariateCovariance) :
    TwoNodeQuadraticResidualModel where
  residualMatrix := !![1, 0; -covariance.forwardCoefficient, 1]
  residualVariance := ![covariance.varX, covariance.forwardResidualVariance]
  residualVariance_pos := by
    intro node
    fin_cases node
    · exact covariance.varX_pos
    · exact covariance.forwardResidualVariance_pos
  ySelfCoefficient := by simp

/-- Node-indexed residual model for `Y → X`.  Row `0` is now the residual of
`X`, so deleting row `0` implements the same intervention as in the forward
model without reordering or inspecting the orientation. -/
noncomputable def reverseNodeResidualModel
    (covariance : PositiveBivariateCovariance) :
    TwoNodeQuadraticResidualModel where
  residualMatrix := !![1, -covariance.reverseCoefficient; 0, 1]
  residualVariance := ![covariance.reverseResidualVariance, covariance.varY]
  residualVariance_pos := by
    intro node
    fin_cases node
    · exact covariance.reverseResidualVariance_pos
    · exact covariance.varY_pos
  ySelfCoefficient := by simp

/-- On correlated data the node-indexed residual mechanisms are genuinely
distinct; the asymmetry is in the DAG adapters, not in `intervene`. -/
theorem forwardNodeResidualMatrix_ne_reverseNodeResidualMatrix
    (covariance : PositiveBivariateCovariance)
    (hcorrelated : covariance.covXY ≠ 0) :
    (forwardNodeResidualModel covariance).residualMatrix ≠
      (reverseNodeResidualModel covariance).residualMatrix := by
  intro h
  have h01 := congrArg (fun matrix => matrix 0 1) h
  simp [forwardNodeResidualModel, reverseNodeResidualModel,
    reverseCoefficient] at h01
  exact hcorrelated (h01.resolve_right covariance.varY_ne_zero)

/-- Half-normalized observational energy of `X → Y`, expressed through the
uniform clamp operation. -/
noncomputable def forwardClampedEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  (forwardNodeResidualModel covariance).clamp 0 x (twoNodeState 0 y)

/-- Half-normalized observational energy of `Y → X`, expressed through the
same uniform clamp operation. -/
noncomputable def reverseClampedEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  (reverseNodeResidualModel covariance).clamp 0 x (twoNodeState 0 y)

theorem forwardClampedEnergy_eq_half_observational
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.forwardClampedEnergy x y =
      (1 / 2) * covariance.forwardGaussianPCEnergy x y := by
  simp [forwardClampedEnergy, TwoNodeQuadraticResidualModel.clamp,
    TwoNodeQuadraticResidualModel.energy_eq_sum_residualContribution,
    TwoNodeQuadraticResidualModel.residualContribution,
    forwardNodeResidualModel, twoNodeState, Matrix.mulVec,
    Fin.sum_univ_two, Function.update, forwardGaussianPCEnergy]
  ring

theorem reverseClampedEnergy_eq_half_observational
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.reverseClampedEnergy x y =
      (1 / 2) * covariance.reverseGaussianPCEnergy x y := by
  simp [reverseClampedEnergy, TwoNodeQuadraticResidualModel.clamp,
    TwoNodeQuadraticResidualModel.energy_eq_sum_residualContribution,
    TwoNodeQuadraticResidualModel.residualContribution,
    reverseNodeResidualModel, twoNodeState, Matrix.mulVec,
    Fin.sum_univ_two, Function.update, reverseGaussianPCEnergy]
  ring

/-- The uniform clamped energies remain observationally direction-blind. -/
theorem forwardClampedEnergy_eq_reverseClampedEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.forwardClampedEnergy x y =
      covariance.reverseClampedEnergy x y := by
  rw [covariance.forwardClampedEnergy_eq_half_observational,
    covariance.reverseClampedEnergy_eq_half_observational,
    covariance.forwardGaussianPCEnergy_eq_reverseGaussianPCEnergy]

/-! ## I1: clamp is conditioning -/

/-- A scalar represented in the operator theorem's one-coordinate Euclidean
latent space. -/
noncomputable def scalarUnitLatent (value : ℝ) : EuclideanSpace ℝ Unit :=
  WithLp.toLp 2 fun _ => value

@[simp] theorem scalarUnitLatent_apply (value : ℝ) :
    scalarUnitLatent value () = value := rfl

theorem scalarUnitLatent_eq_iff (value : ℝ) (point : EuclideanSpace ℝ Unit) :
    scalarUnitLatent value = point ↔ value = point () := by
  constructor
  · intro h
    exact congrArg (fun state => state ()) h
  · intro h
    apply PiLp.ext
    intro coordinate
    cases coordinate
    exact h

namespace TwoNodeQuadraticResidualModel

/-- Operator-level affine residual model obtained by clamping `X=x` and
retaining both node residuals.  This is a generic adapter: it contains no
orientation case split. -/
noncomputable def xClampOperatorModel
    (model : TwoNodeQuadraticResidualModel) (x : ℝ) :
    LinearGaussianOperatorModel Unit (Fin 2) where
  residualMatrix := fun residualNode _ => model.residualMatrix residualNode 1
  residualPrecision := model.residualPrecision
  residualOffset := fun residualNode => model.residualMatrix residualNode 0 * x
  residualMatrix_injective := by
    intro u v huv
    funext coordinate
    cases coordinate
    have hy := congrFun huv (1 : Fin 2)
    simpa [Matrix.mulVec, model.ySelfCoefficient] using hy
  residualPrecision_posDef := model.residualPrecision_posDef

theorem xClampOperatorModel_residual
    (model : TwoNodeQuadraticResidualModel) (x y : ℝ) :
    (model.xClampOperatorModel x).residual (scalarUnitLatent y) =
      model.residualMatrix.mulVec (twoNodeState x y) := by
  funext residualNode
  fin_cases residualNode
  · simp [LinearGaussianOperatorModel.residual, xClampOperatorModel,
      scalarUnitLatent, twoNodeState, Matrix.mulVec, Matrix.vecHead,
      Matrix.vecTail]
    ring
  · simp [LinearGaussianOperatorModel.residual, xClampOperatorModel,
      scalarUnitLatent, twoNodeState, Matrix.mulVec, Matrix.vecHead,
      Matrix.vecTail]
    ring

/-- Exact adapter: the operator theorem's energy is the uniformly clamped
two-node energy, including both residual terms. -/
theorem xClampOperatorModel_energy_eq_clamp
    (model : TwoNodeQuadraticResidualModel) (x y : ℝ) :
    (model.xClampOperatorModel x).energy (scalarUnitLatent y) =
      model.clamp 0 x (twoNodeState 0 y) := by
  have hstate : Function.update (twoNodeState 0 y) 0 x = twoNodeState x y := by
    funext node
    fin_cases node <;> simp [twoNodeState, Function.update]
  unfold LinearGaussianOperatorModel.energy clamp energy
  rw [model.xClampOperatorModel_residual, hstate]
  rfl

/-- Operator-level affine residual model obtained by the same mechanical
intervention on `X`: retain only the residual owned by `Y`. -/
noncomputable def xInterveneOperatorModel
    (model : TwoNodeQuadraticResidualModel) (x : ℝ) :
    LinearGaussianOperatorModel Unit Unit where
  residualMatrix := fun _ _ => model.residualMatrix 1 1
  residualPrecision := Matrix.diagonal fun _ =>
    (2 * model.residualVariance 1)⁻¹
  residualOffset := fun _ => model.residualMatrix 1 0 * x
  residualMatrix_injective := by
    intro u v huv
    funext coordinate
    cases coordinate
    have hy := congrFun huv ()
    simpa [Matrix.mulVec, model.ySelfCoefficient] using hy
  residualPrecision_posDef := by
    apply Matrix.PosDef.diagonal
    intro node
    exact inv_pos.mpr (mul_pos (by norm_num) (model.residualVariance_pos 1))

/-- Exact adapter: deleting `X`'s residual in the uniform operation gives the
single-residual operator model. -/
theorem xInterveneOperatorModel_energy_eq_intervene
    (model : TwoNodeQuadraticResidualModel) (x y : ℝ) :
    (model.xInterveneOperatorModel x).energy (scalarUnitLatent y) =
      model.intervene 0 x (twoNodeState 0 y) := by
  simp [LinearGaussianOperatorModel.energy,
    LinearGaussianOperatorModel.residual, xInterveneOperatorModel,
    intervene, residualContribution, scalarUnitLatent, twoNodeState,
    Matrix.mulVec, dotProduct, Function.update, model.ySelfCoefficient]
  ring

/-- Equilibrium of the full clamped energy, represented through the reusable
operator-level Gaussian theorem. -/
def IsXClampEquilibrium
    (model : TwoNodeQuadraticResidualModel) (x y : ℝ) : Prop :=
  (model.xClampOperatorModel x).Equilibrium (scalarUnitLatent y)

/-- Equilibrium after the uniform intervention deletes `X`'s residual. -/
def IsXInterventionalEquilibrium
    (model : TwoNodeQuadraticResidualModel) (x y : ℝ) : Prop :=
  (model.xInterveneOperatorModel x).Equilibrium (scalarUnitLatent y)

end TwoNodeQuadraticResidualModel

theorem forward_xClampOperatorModel_posteriorMean
    (covariance : PositiveBivariateCovariance) (x : ℝ) :
    ((forwardNodeResidualModel covariance).xClampOperatorModel x).posteriorMean () =
      covariance.forwardCoefficient * x := by
  have hsolve :=
    LinearGaussianOperatorModel.precision_mul_posteriorMean
      ((forwardNodeResidualModel covariance).xClampOperatorModel x)
  have hcoordinate := congrFun hsolve ()
  simp [LinearGaussianOperatorModel.posteriorPrecision,
    LinearGaussianOperatorModel.naturalParameter,
    TwoNodeQuadraticResidualModel.xClampOperatorModel,
    TwoNodeQuadraticResidualModel.residualPrecision,
    forwardNodeResidualModel, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at hcoordinate
  simpa [TwoNodeQuadraticResidualModel.xClampOperatorModel,
    TwoNodeQuadraticResidualModel.residualPrecision,
    forwardNodeResidualModel] using
    hcoordinate.resolve_right (ne_of_gt covariance.forwardResidualVariance_pos)

theorem reverse_xClampOperatorModel_posteriorMean
    (covariance : PositiveBivariateCovariance) (x : ℝ) :
    ((reverseNodeResidualModel covariance).xClampOperatorModel x).posteriorMean () =
      covariance.forwardCoefficient * x := by
  have hsolve :=
    LinearGaussianOperatorModel.precision_mul_posteriorMean
      ((reverseNodeResidualModel covariance).xClampOperatorModel x)
  have hcoordinate := congrFun hsolve ()
  simp [LinearGaussianOperatorModel.posteriorPrecision,
    LinearGaussianOperatorModel.naturalParameter,
    TwoNodeQuadraticResidualModel.xClampOperatorModel,
    TwoNodeQuadraticResidualModel.residualPrecision,
    reverseNodeResidualModel, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at hcoordinate
  let q : ℝ :=
    covariance.reverseCoefficient *
        (covariance.reverseResidualVariance⁻¹ * 2⁻¹) *
        covariance.reverseCoefficient +
      covariance.varY⁻¹ * 2⁻¹
  have hresidualWeight :
      0 < covariance.reverseResidualVariance⁻¹ * 2⁻¹ :=
    mul_pos (inv_pos.mpr covariance.reverseResidualVariance_pos) (by norm_num)
  have hrootWeight : 0 < covariance.varY⁻¹ * 2⁻¹ :=
    mul_pos (inv_pos.mpr covariance.varY_pos) (by norm_num)
  have hfirst :
      0 ≤ covariance.reverseCoefficient *
          (covariance.reverseResidualVariance⁻¹ * 2⁻¹) *
          covariance.reverseCoefficient := by
    nlinarith [mul_nonneg (le_of_lt hresidualWeight)
      (sq_nonneg covariance.reverseCoefficient)]
  have hqpos : 0 < q := by
    dsimp [q]
    linarith
  have hcandidate :
      q * (covariance.forwardCoefficient * x) =
        covariance.reverseCoefficient *
          (covariance.reverseResidualVariance⁻¹ * 2⁻¹) * x := by
    dsimp [q]
    unfold forwardCoefficient reverseCoefficient reverseResidualVariance determinant
    have hdetReverse :
        covariance.varY * covariance.varX - covariance.covXY ^ 2 ≠ 0 := by
      intro hzero
      apply covariance.determinant_ne_zero
      unfold determinant
      nlinarith
    field_simp [covariance.varX_ne_zero, covariance.varY_ne_zero,
      covariance.determinant_ne_zero, hdetReverse]
    ring
  have hcoordinate' :
      q * ((reverseNodeResidualModel covariance).xClampOperatorModel x).posteriorMean () =
        covariance.reverseCoefficient *
          (covariance.reverseResidualVariance⁻¹ * 2⁻¹) * x := by
    simpa [q, TwoNodeQuadraticResidualModel.xClampOperatorModel,
      TwoNodeQuadraticResidualModel.residualPrecision,
      reverseNodeResidualModel] using hcoordinate
  nlinarith [hcoordinate', hcandidate]

/-- The covariance-only conditional expectation of `Y` given `X=x`. -/
noncomputable def conditionalMeanYGivenX
    (covariance : PositiveBivariateCovariance) (x : ℝ) : ℝ :=
  covariance.forwardCoefficient * x

/-- In the forward DAG, ordinary PC clamping is exactly conditioning.  The
equilibrium characterization is inherited from the operator-level Gaussian
theorem rather than re-proved by completing a square. -/
theorem forward_isXClampEquilibrium_iff_conditioning
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    (forwardNodeResidualModel covariance).IsXClampEquilibrium x y ↔
      y = covariance.conditionalMeanYGivenX x := by
  unfold TwoNodeQuadraticResidualModel.IsXClampEquilibrium
  rw [LinearGaussianOperatorModel.equilibrium_iff_eq_posteriorMean,
    scalarUnitLatent_eq_iff,
    covariance.forward_xClampOperatorModel_posteriorMean]
  rfl

/-- In the reverse DAG, retaining every residual term gives the same
conditional expectation.  Clamp therefore does not expose edge direction. -/
theorem reverse_isXClampEquilibrium_iff_conditioning
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    (reverseNodeResidualModel covariance).IsXClampEquilibrium x y ↔
      y = covariance.conditionalMeanYGivenX x := by
  unfold TwoNodeQuadraticResidualModel.IsXClampEquilibrium
  rw [LinearGaussianOperatorModel.equilibrium_iff_eq_posteriorMean,
    scalarUnitLatent_eq_iff,
    covariance.reverse_xClampOperatorModel_posteriorMean]
  rfl

/-- I1 crown: the same covariance-only value is the unique clamped equilibrium
of both genuinely different orientations. -/
theorem clamp_is_conditioning_and_direction_blind
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    ((forwardNodeResidualModel covariance).IsXClampEquilibrium x y ↔
        y = covariance.conditionalMeanYGivenX x) ∧
      ((reverseNodeResidualModel covariance).IsXClampEquilibrium x y ↔
        y = covariance.conditionalMeanYGivenX x) :=
  ⟨covariance.forward_isXClampEquilibrium_iff_conditioning x y,
    covariance.reverse_isXClampEquilibrium_iff_conditioning x y⟩

/-! ## I2: severing changes the equilibrium -/

theorem forward_xInterveneOperatorModel_posteriorMean
    (covariance : PositiveBivariateCovariance) (x : ℝ) :
    ((forwardNodeResidualModel covariance).xInterveneOperatorModel x).posteriorMean () =
      covariance.forwardCoefficient * x := by
  have hsolve :=
    LinearGaussianOperatorModel.precision_mul_posteriorMean
      ((forwardNodeResidualModel covariance).xInterveneOperatorModel x)
  have hcoordinate := congrFun hsolve ()
  simp [LinearGaussianOperatorModel.posteriorPrecision,
    LinearGaussianOperatorModel.naturalParameter,
    TwoNodeQuadraticResidualModel.xInterveneOperatorModel,
    forwardNodeResidualModel, Matrix.mul_apply, Matrix.mulVec,
    dotProduct] at hcoordinate
  simpa [TwoNodeQuadraticResidualModel.xInterveneOperatorModel,
    forwardNodeResidualModel] using
    hcoordinate.resolve_right (ne_of_gt covariance.forwardResidualVariance_pos)

theorem reverse_xInterveneOperatorModel_posteriorMean
    (covariance : PositiveBivariateCovariance) (x : ℝ) :
    ((reverseNodeResidualModel covariance).xInterveneOperatorModel x).posteriorMean () =
      0 := by
  have hsolve :=
    LinearGaussianOperatorModel.precision_mul_posteriorMean
      ((reverseNodeResidualModel covariance).xInterveneOperatorModel x)
  have hcoordinate := congrFun hsolve ()
  simp [LinearGaussianOperatorModel.posteriorPrecision,
    LinearGaussianOperatorModel.naturalParameter,
    TwoNodeQuadraticResidualModel.xInterveneOperatorModel,
    reverseNodeResidualModel, Matrix.mul_apply, Matrix.mulVec,
    dotProduct] at hcoordinate
  simpa [TwoNodeQuadraticResidualModel.xInterveneOperatorModel,
    reverseNodeResidualModel] using
    hcoordinate.resolve_left covariance.varY_ne_zero

/-- The forward `do(X=x)` equilibrium: `X` was already a root, so severing
its own root residual leaves the child mechanism unchanged. -/
theorem forward_isXInterventionalEquilibrium_iff
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    (forwardNodeResidualModel covariance).IsXInterventionalEquilibrium x y ↔
      y = covariance.forwardCoefficient * x := by
  unfold TwoNodeQuadraticResidualModel.IsXInterventionalEquilibrium
  rw [LinearGaussianOperatorModel.equilibrium_iff_eq_posteriorMean,
    scalarUnitLatent_eq_iff,
    covariance.forward_xInterveneOperatorModel_posteriorMean]

/-- The reverse `do(X=x)` equilibrium: deleting `X`'s child residual severs
the edge from `Y`, so `Y` returns to its zero marginal mean. -/
theorem reverse_isXInterventionalEquilibrium_iff
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    (reverseNodeResidualModel covariance).IsXInterventionalEquilibrium x y ↔
      y = 0 := by
  unfold TwoNodeQuadraticResidualModel.IsXInterventionalEquilibrium
  rw [LinearGaussianOperatorModel.equilibrium_iff_eq_posteriorMean,
    scalarUnitLatent_eq_iff,
    covariance.reverse_xInterveneOperatorModel_posteriorMean]

/-- Exact equilibrium-value separation boundary for one intervention. -/
theorem forwardInterventionalEquilibrium_ne_reverse_iff
    (covariance : PositiveBivariateCovariance) (x : ℝ) :
    covariance.forwardCoefficient * x ≠ 0 ↔
      covariance.covXY ≠ 0 ∧ x ≠ 0 := by
  simp [forwardCoefficient, covariance.varX_ne_zero]

/-- Predicate-level I2 crown: the unique interventional equilibria differ
exactly for a nonzero intervention on a correlated covariance. -/
theorem interventionalEquilibria_separate_iff
    (covariance : PositiveBivariateCovariance) (x : ℝ) :
    (∃ forwardY reverseY : ℝ,
        (forwardNodeResidualModel covariance).IsXInterventionalEquilibrium x forwardY ∧
        (reverseNodeResidualModel covariance).IsXInterventionalEquilibrium x reverseY ∧
        forwardY ≠ reverseY) ↔
      covariance.covXY ≠ 0 ∧ x ≠ 0 := by
  constructor
  · rintro ⟨forwardY, reverseY, hforward, hreverse, hne⟩
    rw [covariance.forward_isXInterventionalEquilibrium_iff] at hforward
    rw [covariance.reverse_isXInterventionalEquilibrium_iff] at hreverse
    subst forwardY
    subst reverseY
    exact (covariance.forwardInterventionalEquilibrium_ne_reverse_iff x).mp hne
  · intro hseparate
    refine ⟨covariance.forwardCoefficient * x, 0, ?_, ?_, ?_⟩
    · exact (covariance.forward_isXInterventionalEquilibrium_iff x _).mpr rfl
    · exact (covariance.reverse_isXInterventionalEquilibrium_iff x _).mpr rfl
    · exact (covariance.forwardInterventionalEquilibrium_ne_reverse_iff x).mpr hseparate

/-! ## I3: the intervention certificate -/

/-- `do(X=x)` energy for the forward DAG, obtained by applying the one
uniform intervention operation. -/
noncomputable def forwardInterventionalEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  (forwardNodeResidualModel covariance).intervene 0 x (twoNodeState 0 y)

/-- `do(X=x)` energy for the reverse DAG, using the identical operation. -/
noncomputable def reverseInterventionalEnergy
    (covariance : PositiveBivariateCovariance) (x y : ℝ) : ℝ :=
  (reverseNodeResidualModel covariance).intervene 0 x (twoNodeState 0 y)

theorem forwardInterventionalEnergy_exact
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.forwardInterventionalEnergy x y =
      (1 / (2 * covariance.forwardResidualVariance)) *
        (y - covariance.forwardCoefficient * x) ^ 2 := by
  simp [forwardInterventionalEnergy,
    TwoNodeQuadraticResidualModel.intervene,
    TwoNodeQuadraticResidualModel.residualContribution,
    forwardNodeResidualModel, twoNodeState, Matrix.mulVec,
    Function.update]
  ring

theorem reverseInterventionalEnergy_exact
    (covariance : PositiveBivariateCovariance) (x y : ℝ) :
    covariance.reverseInterventionalEnergy x y =
      (1 / (2 * covariance.varY)) * y ^ 2 := by
  simp [reverseInterventionalEnergy,
    TwoNodeQuadraticResidualModel.intervene,
    TwoNodeQuadraticResidualModel.residualContribution,
    reverseNodeResidualModel, twoNodeState, Matrix.mulVec,
    Function.update]
  ring

/-- Separation by at least one interventional clamp and downstream state. -/
def SeparatesDirectionsByInterventionalEnergy
    (covariance : PositiveBivariateCovariance) : Prop :=
  ∃ x y : ℝ,
    covariance.forwardInterventionalEnergy x y ≠
      covariance.reverseInterventionalEnergy x y

theorem separatesDirectionsByInterventionalEnergy_of_correlated
    (covariance : PositiveBivariateCovariance)
    (hcorrelated : covariance.covXY ≠ 0) :
    covariance.SeparatesDirectionsByInterventionalEnergy := by
  refine ⟨1, 0, ?_⟩
  rw [covariance.forwardInterventionalEnergy_exact,
    covariance.reverseInterventionalEnergy_exact]
  simp only [mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
  apply mul_ne_zero
  · exact one_div_ne_zero (mul_ne_zero (by norm_num)
      (ne_of_gt covariance.forwardResidualVariance_pos))
  · exact pow_ne_zero 2
      (by
        simpa [forwardCoefficient] using
          neg_ne_zero.mpr (div_ne_zero hcorrelated covariance.varX_ne_zero))

theorem not_separatesDirectionsByInterventionalEnergy_of_independent
    (covariance : PositiveBivariateCovariance)
    (hindependent : covariance.covXY = 0) :
    ¬ covariance.SeparatesDirectionsByInterventionalEnergy := by
  rintro ⟨x, y, hne⟩
  apply hne
  rw [covariance.forwardInterventionalEnergy_exact,
    covariance.reverseInterventionalEnergy_exact]
  unfold forwardCoefficient forwardResidualVariance determinant
  rw [hindependent]
  field_simp [covariance.varX_ne_zero, covariance.varY_ne_zero]
  ring

/-- Exact I3 boundary: one `do(X=x)` energy certificate separates the two
orientations if and only if the observational covariance is nonzero. -/
theorem separatesDirectionsByInterventionalEnergy_iff
    (covariance : PositiveBivariateCovariance) :
    covariance.SeparatesDirectionsByInterventionalEnergy ↔
      covariance.covXY ≠ 0 := by
  constructor
  · intro hseparates hzero
    exact covariance.not_separatesDirectionsByInterventionalEnergy_of_independent
      hzero hseparates
  · exact covariance.separatesDirectionsByInterventionalEnergy_of_correlated

/-- I3 crown at the exact covariance C3 cannot distinguish: the residual
operators remain distinct, observational energy is blind on every batch, yet
one uniform intervention separates them. -/
theorem observationally_blind_intervention_certificate
    {Sample : Type*} [Fintype Sample]
    (covariance : PositiveBivariateCovariance)
    (hcorrelated : covariance.covXY ≠ 0) (x y : Sample → ℝ) :
    covariance.forwardResidualMatrix ≠ covariance.reverseResidualMatrix ∧
      (forwardNodeResidualModel covariance).residualMatrix ≠
        (reverseNodeResidualModel covariance).residualMatrix ∧
      (∑ sample, covariance.forwardGaussianPCEnergy (x sample) (y sample)) =
        ∑ sample, covariance.reverseGaussianPCEnergy (x sample) (y sample) ∧
      covariance.SeparatesDirectionsByInterventionalEnergy :=
  ⟨covariance.forwardResidualMatrix_ne_reverseResidualMatrix,
    covariance.forwardNodeResidualMatrix_ne_reverseNodeResidualMatrix hcorrelated,
    covariance.forward_batchEnergy_eq_reverse_batchEnergy x y,
    covariance.separatesDirectionsByInterventionalEnergy_of_correlated hcorrelated⟩

/-- Positive fixture at the exact covariance used for the equal-noise
orientation: both observational energies are `1/2` at `(1,1)`. -/
theorem unitNoiseForwardCovariance_observationalEnergy_fixture :
    unitNoiseForwardCovariance.forwardClampedEnergy 1 1 = 1 / 2 ∧
      unitNoiseForwardCovariance.reverseClampedEnergy 1 1 = 1 / 2 := by
  constructor <;>
    norm_num [forwardClampedEnergy_eq_half_observational,
      reverseClampedEnergy_eq_half_observational,
      forwardGaussianPCEnergy, reverseGaussianPCEnergy,
      forwardCoefficient, reverseCoefficient, forwardResidualVariance,
      reverseResidualVariance, determinant, unitNoiseForwardCovariance]

/-- Positive intervention fixture at the same point: forward energy is zero,
while reverse energy is `1/4`. -/
theorem unitNoiseForwardCovariance_interventionalEnergy_fixture :
    unitNoiseForwardCovariance.forwardInterventionalEnergy 1 1 = 0 ∧
      unitNoiseForwardCovariance.reverseInterventionalEnergy 1 1 = 1 / 4 := by
  constructor
  · rw [unitNoiseForwardCovariance.forwardInterventionalEnergy_exact]
    norm_num [forwardCoefficient, forwardResidualVariance, determinant,
      unitNoiseForwardCovariance]
  · rw [unitNoiseForwardCovariance.reverseInterventionalEnergy_exact]
    norm_num [unitNoiseForwardCovariance]

/-- Combined numerical certificate: observation is exactly tied while the
uniform intervention separates at the very same covariance and state. -/
theorem unitNoiseForwardCovariance_observation_tied_intervention_separates :
    unitNoiseForwardCovariance.forwardClampedEnergy 1 1 =
        unitNoiseForwardCovariance.reverseClampedEnergy 1 1 ∧
      unitNoiseForwardCovariance.forwardInterventionalEnergy 1 1 ≠
        unitNoiseForwardCovariance.reverseInterventionalEnergy 1 1 :=
  ⟨unitNoiseForwardCovariance_observationalEnergy_fixture.1.trans
      unitNoiseForwardCovariance_observationalEnergy_fixture.2.symm,
    by
      rw [unitNoiseForwardCovariance_interventionalEnergy_fixture.1,
        unitNoiseForwardCovariance_interventionalEnergy_fixture.2]
      norm_num⟩

/-- Negative fixture: at independent equal variance, intervention cannot
orient a nonexistent edge; both energies are exactly `y²/2`. -/
theorem independentEqualVarianceCovariance_interventionalEnergy_fixture
    (x y : ℝ) :
    independentEqualVarianceCovariance.forwardInterventionalEnergy x y =
        y ^ 2 / 2 ∧
      independentEqualVarianceCovariance.reverseInterventionalEnergy x y =
        y ^ 2 / 2 := by
  constructor
  · rw [independentEqualVarianceCovariance.forwardInterventionalEnergy_exact]
    norm_num [forwardCoefficient, forwardResidualVariance, determinant,
      independentEqualVarianceCovariance]
    ring
  · rw [independentEqualVarianceCovariance.reverseInterventionalEnergy_exact]
    norm_num [independentEqualVarianceCovariance]
    ring

/-! ## I4: arbitrary data enter quadratic energy through second moments -/

namespace TwoNodeQuadraticResidualModel

/-- State-space quadratic-form matrix `Aᵀ Λ A` induced by a residual model. -/
noncomputable def quadraticFormMatrix
    (model : TwoNodeQuadraticResidualModel) : Matrix (Fin 2) (Fin 2) ℝ :=
  model.residualMatrix.transpose * model.residualPrecision * model.residualMatrix

/-- The residual energy is exactly the corresponding state-space quadratic
form. -/
theorem energy_eq_quadraticForm
    (model : TwoNodeQuadraticResidualModel) (state : Fin 2 → ℝ) :
    model.energy state =
      state ⬝ᵥ model.quadraticFormMatrix.mulVec state := by
  simp [energy, quadraticFormMatrix, residualPrecision, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Unnormalized empirical second-moment matrix of an arbitrary finite batch.
No distribution, Gaussianity, independence, or centering assumption appears. -/
noncomputable def empiricalSecondMomentMatrix
    {Sample : Type*} [Fintype Sample]
    (state : Sample → Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ sample, Matrix.vecMulVec (state sample) (state sample)

theorem energy_eq_trace_quadraticForm_mul_outerProduct
    (model : TwoNodeQuadraticResidualModel) (state : Fin 2 → ℝ) :
    model.energy state =
      Matrix.trace
        (model.quadraticFormMatrix * Matrix.vecMulVec state state) := by
  rw [model.energy_eq_quadraticForm]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec, Fin.sum_univ_two]
  ring

/-- Distribution-free factorization crown: the entire quadratic batch energy
is `tr(Q Σ̂)`.  Consequently changing only the data distribution cannot reveal
higher-order orientation information to this energy; a non-quadratic residual
log-density would be an architectural change. -/
theorem batchEnergy_eq_trace_quadraticForm_mul_empiricalSecondMoment
    {Sample : Type*} [Fintype Sample]
    (model : TwoNodeQuadraticResidualModel)
    (state : Sample → Fin 2 → ℝ) :
    (∑ sample, model.energy (state sample)) =
      Matrix.trace
        (model.quadraticFormMatrix * empiricalSecondMomentMatrix state) := by
  calc
    (∑ sample, model.energy (state sample)) =
        ∑ sample, Matrix.trace
          (model.quadraticFormMatrix *
            Matrix.vecMulVec (state sample) (state sample)) := by
      apply Finset.sum_congr rfl
      intro sample _
      exact model.energy_eq_trace_quadraticForm_mul_outerProduct (state sample)
    _ = Matrix.trace
        (∑ sample, model.quadraticFormMatrix *
          Matrix.vecMulVec (state sample) (state sample)) := by
      rw [Matrix.trace_sum]
    _ = Matrix.trace
        (model.quadraticFormMatrix * empiricalSecondMomentMatrix state) := by
      congr 1
      rw [empiricalSecondMomentMatrix, Matrix.mul_sum]

end TwoNodeQuadraticResidualModel

/-- I4 applied to each fitted orientation: arbitrary batches are summarized
by the same empirical second-moment object before either quadratic form is
scored. -/
theorem both_orientations_batchEnergy_factor_through_secondMoments
    {Sample : Type*} [Fintype Sample]
    (covariance : PositiveBivariateCovariance)
    (state : Sample → Fin 2 → ℝ) :
    (∑ sample, (forwardNodeResidualModel covariance).energy (state sample)) =
        Matrix.trace
          ((forwardNodeResidualModel covariance).quadraticFormMatrix *
            TwoNodeQuadraticResidualModel.empiricalSecondMomentMatrix state) ∧
      (∑ sample, (reverseNodeResidualModel covariance).energy (state sample)) =
        Matrix.trace
          ((reverseNodeResidualModel covariance).quadraticFormMatrix *
            TwoNodeQuadraticResidualModel.empiricalSecondMomentMatrix state) :=
  ⟨TwoNodeQuadraticResidualModel.batchEnergy_eq_trace_quadraticForm_mul_empiricalSecondMoment
        (forwardNodeResidualModel covariance) state,
    TwoNodeQuadraticResidualModel.batchEnergy_eq_trace_quadraticForm_mul_empiricalSecondMoment
        (reverseNodeResidualModel covariance) state⟩

end PositiveBivariateCovariance

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
