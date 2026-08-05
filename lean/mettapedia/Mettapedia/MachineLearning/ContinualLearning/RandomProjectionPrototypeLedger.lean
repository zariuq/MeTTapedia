import Mathlib

/-!
# Frozen random-projection prototype ledgers

McDonnell et al.,
*RanPAC: Random Projections and Pre-trained Models for Continual Learning*
(NeurIPS 2023, arXiv:2307.02251), Equations (4), (5), and (10)--(14),
accumulate a frozen projected feature's Gram matrix and class-prototype
matrix additively, then form a ridge-regression head.

This file isolates four exact parts of that mechanism:

* Gram and class-prototype packets compose by addition;
* the resulting ledgers are invariant under every permutation of the same
  projected observations;
* a strictly positive identity ridge makes every accumulated Gram matrix
  positive definite and hence invertible;
* in one output dimension, the displayed closed form is the unique minimizer
  of the regularized squared-error objective whenever its quadratic
  coefficient is positive.

The frozen-map premise is load bearing. A scalar fixture uses different
projectors at two arrival positions and obtains different Gram matrices after
swapping the same raw samples. A second fixture shows that totalized division
at a singular negative-ridge denominator does not produce a minimizer.

The development does not prove the utility of random features, linear
separability, statistical generalization, classifier accuracy, or any
source-reported empirical comparison.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace RandomProjectionPrototypeLedger

noncomputable section

open Matrix
open scoped Matrix

variable {Feature Class : Type*}

/-- One already-projected feature and its class-target vector. The projector
is external to the ledger and must remain fixed for raw-order invariance. -/
structure Observation (Feature Class : Type*) where
  feature : Feature → ℝ
  target : Class → ℝ

/-- One rank-one contribution to Equation (4)'s Gram matrix. -/
def gramPacket (observation : Observation Feature Class) :
    Matrix Feature Feature ℝ :=
  Matrix.vecMulVec observation.feature observation.feature

/-- One rank-one contribution to Equation (4)'s class-prototype matrix. -/
def prototypePacket (observation : Observation Feature Class) :
    Matrix Feature Class ℝ :=
  Matrix.vecMulVec observation.feature observation.target

/-- Exact accumulated Gram statistics. -/
def gramLedger (observations : List (Observation Feature Class)) :
    Matrix Feature Feature ℝ :=
  (observations.map gramPacket).sum

/-- Exact accumulated class-prototype statistics. -/
def prototypeLedger (observations : List (Observation Feature Class)) :
    Matrix Feature Class ℝ :=
  (observations.map prototypePacket).sum

@[simp] theorem gramLedger_nil :
    gramLedger ([] : List (Observation Feature Class)) = 0 := by
  rfl

@[simp] theorem gramLedger_cons
    (observation : Observation Feature Class)
    (observations : List (Observation Feature Class)) :
    gramLedger (observation :: observations) =
      gramPacket observation + gramLedger observations := by
  rfl

@[simp] theorem gramLedger_append
    (first second : List (Observation Feature Class)) :
    gramLedger (first ++ second) =
      gramLedger first + gramLedger second := by
  simp [gramLedger, List.map_append]

@[simp] theorem prototypeLedger_nil :
    prototypeLedger ([] : List (Observation Feature Class)) = 0 := by
  rfl

@[simp] theorem prototypeLedger_cons
    (observation : Observation Feature Class)
    (observations : List (Observation Feature Class)) :
    prototypeLedger (observation :: observations) =
      prototypePacket observation + prototypeLedger observations := by
  rfl

@[simp] theorem prototypeLedger_append
    (first second : List (Observation Feature Class)) :
    prototypeLedger (first ++ second) =
      prototypeLedger first + prototypeLedger second := by
  simp [prototypeLedger, List.map_append]

/-- Equation (4)'s Gram sufficient statistic depends on the multiset of
projected observations, not their arrival order. -/
theorem gramLedger_eq_of_perm
    {first second : List (Observation Feature Class)}
    (permutation : first.Perm second) :
    gramLedger first = gramLedger second := by
  exact (permutation.map gramPacket).sum_eq

/-- Equation (4)'s class-prototype sufficient statistic has the same complete
order invariance. -/
theorem prototypeLedger_eq_of_perm
    {first second : List (Observation Feature Class)}
    (permutation : first.Perm second) :
    prototypeLedger first = prototypeLedger second := by
  exact (permutation.map prototypePacket).sum_eq

/-- Both sufficient statistics are invariant under the same observation
permutation. -/
theorem ledgers_eq_of_perm
    {first second : List (Observation Feature Class)}
    (permutation : first.Perm second) :
    gramLedger first = gramLedger second ∧
      prototypeLedger first = prototypeLedger second :=
  ⟨gramLedger_eq_of_perm permutation,
    prototypeLedger_eq_of_perm permutation⟩

variable [Fintype Feature]

/-- Every finite Gram ledger is positive semidefinite. -/
theorem gramLedger_posSemidef :
  ∀ observations : List (Observation Feature Class),
      (gramLedger observations).PosSemidef
  | [] => by
      simpa using
        (Matrix.PosSemidef.zero :
          (0 : Matrix Feature Feature ℝ).PosSemidef)
  | observation :: observations => by
      have packet_posSemidef :
          (gramPacket observation).PosSemidef := by
        simpa [gramPacket] using
          Matrix.posSemidef_vecMulVec_self_star observation.feature
      simpa using
        packet_posSemidef.add (gramLedger_posSemidef observations)

variable [DecidableEq Feature]

/-- Equation (5)'s regularized Gram matrix. -/
def ridgeGram
    (ridge : ℝ)
    (observations : List (Observation Feature Class)) :
    Matrix Feature Feature ℝ :=
  gramLedger observations +
    ridge • (1 : Matrix Feature Feature ℝ)

/-- A positive ridge makes the accumulated Gram matrix positive definite,
without any full-rank premise on the observed features. -/
theorem ridgeGram_posDef
    (observations : List (Observation Feature Class))
    {ridge : ℝ}
    (ridge_pos : 0 < ridge) :
    (ridgeGram ridge observations).PosDef := by
  have ridge_part :
      (ridge • (1 : Matrix Feature Feature ℝ)).PosDef :=
    PosDef.one.smul ridge_pos
  exact PosDef.posSemidef_add
    (gramLedger_posSemidef observations) ridge_part

/-- The same condition licenses the matrix inverse used by the classifier
head. -/
theorem ridgeGram_isUnit
    (observations : List (Observation Feature Class))
    {ridge : ℝ}
    (ridge_pos : 0 < ridge) :
    IsUnit (ridgeGram ridge observations) :=
  (ridgeGram_posDef observations ridge_pos).isUnit

/-! ## Scalar least-squares recovery -/

/-- Scalar sufficient statistic corresponding to the Gram matrix. -/
def scalarGram (samples : List (ℝ × ℝ)) : ℝ :=
  (samples.map fun sample => sample.1 ^ 2).sum

/-- Scalar sufficient statistic corresponding to the feature-target matrix. -/
def scalarCross (samples : List (ℝ × ℝ)) : ℝ :=
  (samples.map fun sample => sample.1 * sample.2).sum

/-- Target-only constant in the expanded squared-error objective. -/
def scalarTargetEnergy (samples : List (ℝ × ℝ)) : ℝ :=
  (samples.map fun sample => sample.2 ^ 2).sum

/-- One-dimensional form of Equation (14). -/
def scalarRidgeLoss
    (samples : List (ℝ × ℝ))
    (ridge weight : ℝ) : ℝ :=
  (samples.map fun sample =>
    (sample.2 - weight * sample.1) ^ 2).sum +
      ridge * weight ^ 2

/-- One-dimensional form of Equations (11)--(12). -/
def scalarRidgeSolution
    (samples : List (ℝ × ℝ))
    (ridge : ℝ) : ℝ :=
  scalarCross samples / (scalarGram samples + ridge)

/-- Exact sufficient-statistic expansion of the scalar ridge objective. -/
theorem scalarRidgeLoss_eq_quadratic
    (samples : List (ℝ × ℝ))
    (ridge weight : ℝ) :
    scalarRidgeLoss samples ridge weight =
      scalarTargetEnergy samples -
        2 * scalarCross samples * weight +
        (scalarGram samples + ridge) * weight ^ 2 := by
  induction samples with
  | nil =>
      simp [scalarRidgeLoss, scalarTargetEnergy, scalarCross, scalarGram]
  | cons sample samples induction_hypothesis =>
      rcases sample with ⟨feature, target⟩
      unfold scalarRidgeLoss scalarTargetEnergy scalarCross scalarGram at induction_hypothesis ⊢
      simp only [List.map_cons, List.sum_cons] at induction_hypothesis ⊢
      nlinarith

/-- Completing the square recovers the source's scalar closed form. -/
theorem scalarRidgeLoss_sub_solution_eq
    (samples : List (ℝ × ℝ))
    (ridge weight : ℝ)
    (coefficient_ne_zero :
      scalarGram samples + ridge ≠ 0) :
    scalarRidgeLoss samples ridge weight -
        scalarRidgeLoss samples ridge
          (scalarRidgeSolution samples ridge) =
      (scalarGram samples + ridge) *
        (weight - scalarRidgeSolution samples ridge) ^ 2 := by
  rw [scalarRidgeLoss_eq_quadratic,
    scalarRidgeLoss_eq_quadratic]
  unfold scalarRidgeSolution
  field_simp
  ring

/-- A positive quadratic coefficient makes the closed form a global
minimizer. -/
theorem scalarRidgeSolution_minimizes
    (samples : List (ℝ × ℝ))
    (ridge weight : ℝ)
    (coefficient_pos : 0 < scalarGram samples + ridge) :
    scalarRidgeLoss samples ridge
        (scalarRidgeSolution samples ridge) ≤
      scalarRidgeLoss samples ridge weight := by
  have gap := scalarRidgeLoss_sub_solution_eq
    samples ridge weight (ne_of_gt coefficient_pos)
  nlinarith [sq_nonneg
    (weight - scalarRidgeSolution samples ridge)]

/-- Under the same premise the minimizer is unique. -/
theorem scalarRidgeSolution_unique
    (samples : List (ℝ × ℝ))
    (ridge first : ℝ)
    (coefficient_pos : 0 < scalarGram samples + ridge)
    (same_loss :
      scalarRidgeLoss samples ridge first =
        scalarRidgeLoss samples ridge
          (scalarRidgeSolution samples ridge)) :
    first = scalarRidgeSolution samples ridge := by
  have gap := scalarRidgeLoss_sub_solution_eq
    samples ridge first (ne_of_gt coefficient_pos)
  have product_zero :
      (scalarGram samples + ridge) *
        (first - scalarRidgeSolution samples ridge) ^ 2 = 0 := by
    linarith
  have square_zero :
      (first - scalarRidgeSolution samples ridge) ^ 2 = 0 :=
    (mul_eq_zero.mp product_zero).resolve_left
      (ne_of_gt coefficient_pos)
  nlinarith

/-! ## Positive and negative executable boundaries -/

/-- One sample with feature two and target six has unregularized solution
three. Its Gram coefficient is positive, so the minimizer theorem applies. -/
theorem scalar_single_sample_solution :
    scalarRidgeSolution [(2, 6)] 0 = 3 := by
  norm_num [scalarRidgeSolution, scalarCross, scalarGram]

/-- Zero ridge cannot make an empty Gram ledger invertible. -/
theorem zero_ridge_emptyLedger_not_isUnit :
    ¬ IsUnit
      (ridgeGram (Feature := Fin 1) (Class := Fin 1) 0 []) := by
  simp [ridgeGram]

/-- A changing projector destroys raw-order invariance even though the ledger
itself still adds its already-projected packets commutatively. -/
theorem changing_projector_breaks_raw_order_invariance :
    gramLedger
        [⟨fun _ : Fin 1 => 1 * 1, fun _ : Fin 1 => 1⟩,
         ⟨fun _ : Fin 1 => 2 * 2, fun _ : Fin 1 => 1⟩] ≠
      gramLedger
        [⟨fun _ : Fin 1 => 1 * 2, fun _ : Fin 1 => 1⟩,
         ⟨fun _ : Fin 1 => 2 * 1, fun _ : Fin 1 => 1⟩] := by
  intro supposedly_equal
  have entry_equal :=
    congrFun (congrFun supposedly_equal (0 : Fin 1)) (0 : Fin 1)
  norm_num [gramLedger, gramPacket, Matrix.vecMulVec] at entry_equal

/-- If a negative ridge cancels the Gram coefficient, Lean's totalized
division returns zero, but that value is not a minimizer of the resulting
linear objective. -/
theorem singular_negative_ridge_totalizedSolution_not_minimizer :
    scalarRidgeLoss [(2, 6)] (-4) 1 <
      scalarRidgeLoss [(2, 6)] (-4)
        (scalarRidgeSolution [(2, 6)] (-4)) := by
  norm_num [scalarRidgeLoss, scalarRidgeSolution, scalarCross, scalarGram]

#print axioms gramLedger_eq_of_perm
#print axioms prototypeLedger_eq_of_perm
#print axioms gramLedger_posSemidef
#print axioms ridgeGram_posDef
#print axioms ridgeGram_isUnit
#print axioms scalarRidgeLoss_sub_solution_eq
#print axioms scalarRidgeSolution_minimizes
#print axioms scalarRidgeSolution_unique
#print axioms scalar_single_sample_solution
#print axioms zero_ridge_emptyLedger_not_isUnit
#print axioms changing_projector_breaks_raw_order_invariance
#print axioms singular_negative_ridge_totalizedSolution_not_minimizer

end

end RandomProjectionPrototypeLedger

end Mettapedia.MachineLearning.ContinualLearning
