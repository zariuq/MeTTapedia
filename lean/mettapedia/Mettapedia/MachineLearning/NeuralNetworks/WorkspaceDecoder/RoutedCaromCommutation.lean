import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom
import Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry.InterferenceGram

/-!
# Routed CAROM: affine switched phases and commutation

This file isolates the exact order-sensitivity boundary for two routed affine
commands.  Linear commutation is necessary but not sufficient for affine
phases: their biases must satisfy a second compatibility equation.  The full
composition discrepancy splits exactly into the matrix commutator acting on
the current state and this bias obstruction.

The degree-two interference energy from `InterferenceGram` therefore detects
the entire obstruction for linear phases, while affine phases retain a
separate, explicit bias term.  No nonlinear or empirical claim is made here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function
open scoped BigOperators Matrix
open Mettapedia.MachineLearning.NeuralNetworks.ForgettingGeometry

namespace RoutedCarom

universe uIndex uExpert

/-! ## Affine phases and simplex routing -/

/-- A finite-dimensional affine command phase. -/
structure AffinePhase (Index : Type uIndex) [Fintype Index] where
  linear : Matrix Index Index ℝ
  bias : Index → ℝ

/-- Action of an affine phase on workspace coordinates. -/
noncomputable def AffinePhase.act
    {Index : Type uIndex} [Fintype Index]
    (phase : AffinePhase Index) (state : Index → ℝ) : Index → ℝ :=
  phase.linear *ᵥ state + phase.bias

/-- Composition in execution order: `inner` acts first, then `outer`. -/
noncomputable def AffinePhase.comp
    {Index : Type uIndex} [Fintype Index]
    (outer inner : AffinePhase Index) : AffinePhase Index where
  linear := outer.linear * inner.linear
  bias := outer.linear *ᵥ inner.bias + outer.bias

@[simp] theorem AffinePhase.act_comp
    {Index : Type uIndex} [Fintype Index]
    (outer inner : AffinePhase Index) (state : Index → ℝ) :
    (outer.comp inner).act state = outer.act (inner.act state) := by
  simp [AffinePhase.comp, AffinePhase.act, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  module

/-- Simplex mixture of affine expert phases, taken componentwise in natural
affine coordinates. -/
noncomputable def mixedAffinePhase
    {Index : Type uIndex} [Fintype Index]
    {Expert : Type uExpert} [Fintype Expert]
    (routing : SimplexWeights Expert) (expert : Expert → AffinePhase Index) :
    AffinePhase Index where
  linear := ∑ item, routing.weight item • (expert item).linear
  bias := ∑ item, routing.weight item • (expert item).bias

/-- Routing an affine expert bank is exactly the weighted mixture of the
expert actions. -/
theorem mixedAffinePhase_act
    {Index : Type uIndex} [Fintype Index]
    {Expert : Type uExpert} [Fintype Expert]
    (routing : SimplexWeights Expert) (expert : Expert → AffinePhase Index)
  (state : Index → ℝ) :
    (mixedAffinePhase routing expert).act state =
      ∑ item, routing.weight item • (expert item).act state := by
  simp [mixedAffinePhase, AffinePhase.act, Matrix.sum_mulVec,
    Matrix.smul_mulVec]
  rw [Finset.sum_add_distrib]

/-! ## Exact two-command boundary -/

/-- The affine bias obstruction left after removing the linear commutator. -/
noncomputable def affineBiasCommutator
    {Index : Type uIndex} [Fintype Index]
    (first second : AffinePhase Index) : Index → ℝ :=
  second.linear *ᵥ first.bias + second.bias -
    (first.linear *ᵥ second.bias + first.bias)

/-- Full condition for two affine phases to commute. -/
def AffinePhasesCommute
    {Index : Type uIndex} [Fintype Index]
    (first second : AffinePhase Index) : Prop :=
  Commute first.linear second.linear ∧
    affineBiasCommutator first second = 0

/-- State-dependent discrepancy between the two command orders. -/
noncomputable def affineCompositionDiscrepancy
    {Index : Type uIndex} [Fintype Index]
    (first second : AffinePhase Index) (state : Index → ℝ) : Index → ℝ :=
  second.act (first.act state) - first.act (second.act state)

/-- Exact discrepancy decomposition: curvature-like noncommutation acts on
the current state, while the affine biases contribute a fixed obstruction. -/
theorem affineCompositionDiscrepancy_exact
    {Index : Type uIndex} [Fintype Index]
    (first second : AffinePhase Index) (state : Index → ℝ) :
    affineCompositionDiscrepancy first second state =
      matrixCommutator first.linear second.linear *ᵥ state +
        affineBiasCommutator first second := by
  simp [affineCompositionDiscrepancy, AffinePhase.act,
    affineBiasCommutator, matrixCommutator, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.sub_mulVec]
  module

/-- The exact discrepancy immediately gives a norm bound with separate
linear-commutator and bias contributions. -/
theorem norm_affineCompositionDiscrepancy_le
    {Index : Type uIndex} [Fintype Index]
    (first second : AffinePhase Index) (state : Index → ℝ) :
    ‖affineCompositionDiscrepancy first second state‖ ≤
      ‖matrixCommutator first.linear second.linear *ᵥ state‖ +
        ‖affineBiasCommutator first second‖ := by
  rw [affineCompositionDiscrepancy_exact]
  exact norm_add_le _ _

/-- T3 crown: two affine command phases are order-independent on every state
if and only if both the linear generators and the affine biases commute. -/
theorem affinePhases_orderIndependent_iff
    {Index : Type uIndex} [Fintype Index]
    (first second : AffinePhase Index) :
    (∀ state, second.act (first.act state) = first.act (second.act state)) ↔
      AffinePhasesCommute first second := by
  constructor
  · intro horder
    have hzeroDiscrepancy :
        affineCompositionDiscrepancy first second (0 : Index → ℝ) = 0 :=
      sub_eq_zero.mpr (horder 0)
    have hbias : affineBiasCommutator first second = 0 := by
      rw [affineCompositionDiscrepancy_exact] at hzeroDiscrepancy
      simpa using hzeroDiscrepancy
    have hcommutator :
        matrixCommutator first.linear second.linear = 0 := by
      apply (Matrix.ext_iff_mulVec).2
      intro state
      have hdiscrepancy :
          affineCompositionDiscrepancy first second state = 0 :=
        sub_eq_zero.mpr (horder state)
      rw [affineCompositionDiscrepancy_exact, hbias, add_zero] at hdiscrepancy
      simpa using hdiscrepancy
    constructor
    · unfold matrixCommutator at hcommutator
      exact (sub_eq_zero.mp hcommutator).symm
    · exact hbias
  · rintro ⟨hlinear, hbias⟩ state
    apply sub_eq_zero.mp
    change affineCompositionDiscrepancy first second state = 0
    rw [affineCompositionDiscrepancy_exact, hbias, add_zero]
    unfold matrixCommutator
    rw [hlinear.eq]
    simp

/-! ## Linear specialization and interference-energy certificate -/

/-- Embed a linear command as an affine phase with zero bias. -/
noncomputable def linearPhase
    {Index : Type uIndex} [Fintype Index]
    (linear : Matrix Index Index ℝ) : AffinePhase Index where
  linear := linear
  bias := 0

@[simp] theorem linearPhase_act
    {Index : Type uIndex} [Fintype Index]
    (linear : Matrix Index Index ℝ) (state : Index → ℝ) :
    (linearPhase linear).act state = linear *ᵥ state := by
  simp [linearPhase, AffinePhase.act]

/-- For linear phases, order-independence is exactly matrix commutation. -/
theorem linearPhases_orderIndependent_iff_commute
    {Index : Type uIndex} [Fintype Index]
    (first second : Matrix Index Index ℝ) :
    (∀ state, (linearPhase second).act ((linearPhase first).act state) =
      (linearPhase first).act ((linearPhase second).act state)) ↔
      Commute first second := by
  rw [affinePhases_orderIndependent_iff]
  simp [AffinePhasesCommute, affineBiasCommutator, linearPhase]

/-- The sealed interference Gram diagonal is a complete order-sensitivity
certificate for two linear routed commands. -/
theorem linearPhases_orderIndependent_iff_interferenceEnergy_zero
    {Index : Type uIndex} [Fintype Index]
    (first second : Matrix Index Index ℝ) :
    (∀ state, (linearPhase second).act ((linearPhase first).act state) =
      (linearPhase first).act ((linearPhase second).act state)) ↔
      pairwiseInterferenceEnergy first second = 0 := by
  rw [linearPhases_orderIndependent_iff_commute]
  exact (pairwiseInterferenceEnergy_eq_zero_iff_commute first second).symm

/-- For symmetric linear command phases, the sealed elementary holonomy proxy
is another exact chart of the same order-independence condition. -/
theorem symmetricLinearPhases_orderIndependent_iff_trivialRotationProxy
    {Index : Type uIndex} [Fintype Index]
    (first second : Matrix Index Index ℝ)
    (hfirst : first.IsSymm) (hsecond : second.IsSymm) :
    (∀ state, (linearPhase second).act ((linearPhase first).act state) =
      (linearPhase first).act ((linearPhase second).act state)) ↔
      TrivialRotationProxy (first * second) := by
  rw [linearPhases_orderIndependent_iff_commute]
  exact (twoSymmetricFactors_trivialRotationProxy_iff_commute
    first second hfirst hsecond).symm

/-! ## Positive and negative fixtures -/

/-- A scalar one-dimensional affine phase, used to expose the bias boundary. -/
noncomputable def scalarAffinePhase (linear bias : ℝ) : AffinePhase (Fin 1) where
  linear := fun _ _ => linear
  bias := fun _ => bias

/-- Positive fixture: the sealed parallel rank-one pair is independent of
command order. -/
theorem parallelRankOne_orderIndependent_positiveExample (x : ℝ) :
    ∀ state,
      (linearPhase (directionRankOneCurvature x 0)).act
          ((linearPhase axisRankOneCurvature).act state) =
        (linearPhase axisRankOneCurvature).act
          ((linearPhase (directionRankOneCurvature x 0)).act state) := by
  apply (linearPhases_orderIndependent_iff_interferenceEnergy_zero _ _).2
  exact parallel_rankOne_interferenceEnergy_zero_positiveExample x

/-- Negative fixture: the unit oblique rank-one pair is order-sensitive. -/
theorem unitOblique_orderSensitive_negativeExample :
    ¬ (∀ state,
      (linearPhase (directionRankOneCurvature 1 1)).act
          ((linearPhase axisRankOneCurvature).act state) =
        (linearPhase axisRankOneCurvature).act
          ((linearPhase (directionRankOneCurvature 1 1)).act state)) := by
  rw [linearPhases_orderIndependent_iff_interferenceEnergy_zero]
  norm_num [unitOblique_interferenceEnergy_positive_negativeExample]

/-- Linear commutation alone does not settle affine command order: these
one-dimensional generators commute, but their biases are incompatible. -/
theorem scalarAffine_biasObstruction_negativeExample :
    Commute (scalarAffinePhase 1 1).linear
        (scalarAffinePhase 2 0).linear ∧
      ¬ AffinePhasesCommute (scalarAffinePhase 1 1)
        (scalarAffinePhase 2 0) := by
  constructor
  · unfold Commute SemiconjBy
    ext i j
    fin_cases i
    fin_cases j
    norm_num [scalarAffinePhase, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro h
    have hbias := h.2
    have hcoordinate := congrFun hbias 0
    norm_num [affineBiasCommutator, scalarAffinePhase, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] at hcoordinate

#print axioms mixedAffinePhase_act
#print axioms affineCompositionDiscrepancy_exact
#print axioms affinePhases_orderIndependent_iff
#print axioms linearPhases_orderIndependent_iff_interferenceEnergy_zero
#print axioms symmetricLinearPhases_orderIndependent_iff_trivialRotationProxy

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
