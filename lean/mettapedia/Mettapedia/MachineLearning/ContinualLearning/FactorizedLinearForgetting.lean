import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Parameterization-dependent forgetting in linear models

Mirzadeh, Chaudhry, Yin, Hu, Pascanu, Gorur, and Farajtabar,
*Wide Neural Networks Forget Less Catastrophically* (ICML 2022,
arXiv:2110.11526), Claim C.1, compare a direct linear model with a two-layer
linear factorization.  The two parameterizations describe the same function
class, but gradient descent need not give them the same continual-learning
dynamics.

This file isolates and generalizes the exact algebra used by that claim.
When old and new data matrices have orthogonal row spaces, every direct
gradient packet from the new task preserves the old predictions.  The same
orthogonality preserves the old feature map of a factorized model, but a
change in the output head can still change old predictions.  Forgetting is
then exactly one half of the squared Euclidean length of the head displacement
seen through the old feature map.  Injectivity of that map makes every
nonzero head displacement strictly forgetting.

The source's finite-width/full-rank condition is represented by column
independence of the old feature map, which is equivalent to injectivity of
matrix-vector multiplication.  A counterexample shows that without this
condition a nonzero head displacement can remain invisible.

The theorem is about finite linear-quadratic dynamics.  It does not turn the
paper's empirical monotonic-width observation into a universal theorem for
nonlinear networks.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace FactorizedLinearForgetting

open scoped BigOperators

noncomputable section

variable {OldSample NewSample Feature Hidden : Type*}
  [Fintype OldSample] [Fintype NewSample] [Fintype Feature] [Fintype Hidden]

/-- Prediction of a direct linear model on a finite data matrix. -/
def directPrediction
    (data : Matrix OldSample Feature ℝ)
    (weight : Feature → ℝ) : OldSample → ℝ :=
  data.mulVec weight

/-- The direct weight represented by a two-layer linear factorization. -/
def collapsedWeight
    (featureWeight : Matrix Hidden Feature ℝ)
    (head : Hidden → ℝ) : Feature → ℝ :=
  featureWeight.transpose.mulVec head

/-- Prediction of a two-layer linear factorization. -/
def factorizedPrediction
    (data : Matrix OldSample Feature ℝ)
    (featureWeight : Matrix Hidden Feature ℝ)
    (head : Hidden → ℝ) : OldSample → ℝ :=
  data.mulVec (collapsedWeight featureWeight head)

omit [Fintype OldSample] in
/-- Collapsing a two-layer linear model recovers the corresponding direct
linear prediction exactly. -/
theorem factorizedPrediction_eq_directPrediction
    (data : Matrix OldSample Feature ℝ)
    (featureWeight : Matrix Hidden Feature ℝ)
    (head : Hidden → ℝ) :
    factorizedPrediction data featureWeight head =
      directPrediction data (collapsedWeight featureWeight head) :=
  rfl

/-- Every direct linear weight has a one-hidden-unit factorization. -/
def oneHiddenLift (weight : Feature → ℝ) : Matrix Unit Feature ℝ :=
  fun _ feature => weight feature

/-- Unit output head for `oneHiddenLift`. -/
def unitHead : Unit → ℝ := fun _ => 1

omit [Fintype Feature] in
/-- The one-hidden-unit lift is an exact right inverse of collapse.  Thus the
direct and factorized model classes have the same linear expressivity. -/
@[simp] theorem collapsedWeight_oneHiddenLift
    (weight : Feature → ℝ) :
    collapsedWeight (oneHiddenLift weight) unitHead = weight := by
  funext feature
  simp [collapsedWeight, oneHiddenLift, unitHead, Matrix.mulVec, dotProduct]

/-- Squared Euclidean length divided by two. -/
def halfSquaredL2 {Index : Type*} [Fintype Index]
    (vector : Index → ℝ) : ℝ :=
  (vector ⬝ᵥ vector) / 2

theorem halfSquaredL2_nonneg {Index : Type*} [Fintype Index]
    (vector : Index → ℝ) :
    0 ≤ halfSquaredL2 vector := by
  have dotNonneg : 0 ≤ vector ⬝ᵥ vector := by
    unfold dotProduct
    exact Finset.sum_nonneg fun index _ =>
      mul_self_nonneg (vector index)
  exact div_nonneg dotNonneg (by norm_num)

theorem halfSquaredL2_pos_of_ne_zero
    {Index : Type*} [Fintype Index]
    {vector : Index → ℝ} (nonzero : vector ≠ 0) :
    0 < halfSquaredL2 vector := by
  have dotNonzero : vector ⬝ᵥ vector ≠ 0 :=
    (dotProduct_self_eq_zero.not).2 nonzero
  have dotNonneg : 0 ≤ vector ⬝ᵥ vector := by
    unfold dotProduct
    exact Finset.sum_nonneg fun index _ =>
      mul_self_nonneg (vector index)
  have dotPos : 0 < vector ⬝ᵥ vector :=
    lt_of_le_of_ne dotNonneg (Ne.symm dotNonzero)
  exact div_pos dotPos (by norm_num)

/-- Half-squared training loss of a direct linear model. -/
def directTaskLoss
    (data : Matrix OldSample Feature ℝ)
    (target : OldSample → ℝ)
    (weight : Feature → ℝ) : ℝ :=
  halfSquaredL2 (directPrediction data weight - target)

/-- Half-squared training loss of a factorized linear model. -/
def factorizedTaskLoss
    (data : Matrix OldSample Feature ℝ)
    (target : OldSample → ℝ)
    (featureWeight : Matrix Hidden Feature ℝ)
    (head : Hidden → ℝ) : ℝ :=
  halfSquaredL2
    (factorizedPrediction data featureWeight head - target)

/-- Forgetting is final old-task loss minus initial old-task loss. -/
def directForgetting
    (data : Matrix OldSample Feature ℝ)
    (target : OldSample → ℝ)
    (finalWeight initialWeight : Feature → ℝ) : ℝ :=
  directTaskLoss data target finalWeight -
    directTaskLoss data target initialWeight

/-- Forgetting for a factorized linear parameterization. -/
def factorizedForgetting
    (data : Matrix OldSample Feature ℝ)
    (target : OldSample → ℝ)
    (finalFeature initialFeature : Matrix Hidden Feature ℝ)
    (finalHead initialHead : Hidden → ℝ) : ℝ :=
  factorizedTaskLoss data target finalFeature finalHead -
    factorizedTaskLoss data target initialFeature initialHead

/-- A direct new-task gradient packet.  The residual may change at every
step, so a list of these packets covers an arbitrary finite gradient path. -/
structure DirectPacket (NewSample : Type*) where
  residual : NewSample → ℝ
  rate : ℝ

/-- Feature-space direction generated by a new-task residual. -/
def taskFeatureDirection
    (newData : Matrix NewSample Feature ℝ)
    (residual : NewSample → ℝ) : Feature → ℝ :=
  newData.transpose.mulVec residual

/-- One direct linear gradient packet.  Dataset normalization is absorbed
into `rate`. -/
def directPacketStep
    (newData : Matrix NewSample Feature ℝ)
    (packet : DirectPacket NewSample)
    (weight : Feature → ℝ) : Feature → ℝ :=
  weight - packet.rate •
    taskFeatureDirection newData packet.residual

/-- Run an arbitrary finite sequence of direct gradient packets. -/
def runDirectPackets
    (newData : Matrix NewSample Feature ℝ) :
    List (DirectPacket NewSample) → (Feature → ℝ) → (Feature → ℝ)
  | [], weight => weight
  | packet :: packets, weight =>
      runDirectPackets newData packets
        (directPacketStep newData packet weight)

omit [Fintype OldSample] in
/-- Orthogonal old/new row spaces make every direct new-task gradient packet
invisible on the old data. -/
theorem directPrediction_packetStep_eq
    (oldData : Matrix OldSample Feature ℝ)
    (newData : Matrix NewSample Feature ℝ)
    (orthogonalRows : oldData * newData.transpose = 0)
    (packet : DirectPacket NewSample)
    (weight : Feature → ℝ) :
    directPrediction oldData
        (directPacketStep newData packet weight) =
      directPrediction oldData weight := by
  have directionZero :
      oldData.mulVec
          (taskFeatureDirection newData packet.residual) = 0 := by
    rw [taskFeatureDirection, Matrix.mulVec_mulVec, orthogonalRows]
    simp
  simp [directPrediction, directPacketStep, Matrix.mulVec_sub,
    Matrix.mulVec_smul, directionZero]

omit [Fintype OldSample] in
/-- The preservation law composes through every finite direct gradient path. -/
theorem directPrediction_runDirectPackets_eq
    (oldData : Matrix OldSample Feature ℝ)
    (newData : Matrix NewSample Feature ℝ)
    (orthogonalRows : oldData * newData.transpose = 0)
    (packets : List (DirectPacket NewSample))
    (weight : Feature → ℝ) :
    directPrediction oldData
        (runDirectPackets newData packets weight) =
      directPrediction oldData weight := by
  induction packets generalizing weight with
  | nil => rfl
  | cons packet packets ih =>
      rw [runDirectPackets, ih]
      exact directPrediction_packetStep_eq
        oldData newData orthogonalRows packet weight

/-- Exact source-side direct-model conclusion: if task one was fitted, an
arbitrary finite task-two gradient path has zero task-one forgetting. -/
theorem directForgetting_runDirectPackets_eq_zero
    (oldData : Matrix OldSample Feature ℝ)
    (newData : Matrix NewSample Feature ℝ)
    (target : OldSample → ℝ)
    (orthogonalRows : oldData * newData.transpose = 0)
    (packets : List (DirectPacket NewSample))
    (initialWeight : Feature → ℝ)
    (initialFit :
      directPrediction oldData initialWeight = target) :
    directForgetting oldData target
        (runDirectPackets newData packets initialWeight)
        initialWeight = 0 := by
  unfold directForgetting directTaskLoss
  rw [
    directPrediction_runDirectPackets_eq
      oldData newData orthogonalRows packets initialWeight,
    initialFit]
  simp [halfSquaredL2]

/-- A factorized feature-gradient packet.  The head and residual may both
change between steps. -/
structure FeaturePacket (NewSample Hidden : Type*) where
  head : Hidden → ℝ
  residual : NewSample → ℝ
  rate : ℝ

/-- One factorized feature-weight gradient packet.  It has the rank-one form
used in the source proof. -/
def factorizedFeaturePacketStep
    (newData : Matrix NewSample Feature ℝ)
    (packet : FeaturePacket NewSample Hidden)
    (featureWeight : Matrix Hidden Feature ℝ) :
    Matrix Hidden Feature ℝ :=
  featureWeight -
    packet.rate • Matrix.vecMulVec packet.head
      (taskFeatureDirection newData packet.residual)

/-- Run an arbitrary finite sequence of factorized feature-gradient packets. -/
def runFeaturePackets
    (newData : Matrix NewSample Feature ℝ) :
    List (FeaturePacket NewSample Hidden) →
      Matrix Hidden Feature ℝ → Matrix Hidden Feature ℝ
  | [], featureWeight => featureWeight
  | packet :: packets, featureWeight =>
      runFeaturePackets newData packets
        (factorizedFeaturePacketStep newData packet featureWeight)

omit [Fintype OldSample] [Fintype Hidden] in
/-- A factorized feature packet preserves the old data-to-hidden map under
the same row-space orthogonality condition. -/
theorem oldFeatureMap_packetStep_eq
    (oldData : Matrix OldSample Feature ℝ)
    (newData : Matrix NewSample Feature ℝ)
    (orthogonalRows : oldData * newData.transpose = 0)
    (packet : FeaturePacket NewSample Hidden)
    (featureWeight : Matrix Hidden Feature ℝ) :
    oldData *
        (factorizedFeaturePacketStep
          newData packet featureWeight).transpose =
      oldData * featureWeight.transpose := by
  have directionZero :
      oldData.mulVec
          (taskFeatureDirection newData packet.residual) = 0 := by
    rw [taskFeatureDirection, Matrix.mulVec_mulVec, orthogonalRows]
    simp
  simp only [factorizedFeaturePacketStep, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_vecMulVec,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_vecMulVec,
    directionZero]
  ext oldSample hidden
  simp [Matrix.vecMulVec]

omit [Fintype OldSample] [Fintype Hidden] in
/-- Feature-map preservation composes through an arbitrary finite
factorized-gradient path. -/
theorem oldFeatureMap_runFeaturePackets_eq
    (oldData : Matrix OldSample Feature ℝ)
    (newData : Matrix NewSample Feature ℝ)
    (orthogonalRows : oldData * newData.transpose = 0)
    (packets : List (FeaturePacket NewSample Hidden))
    (initialFeature : Matrix Hidden Feature ℝ) :
    oldData *
        (runFeaturePackets newData packets initialFeature).transpose =
      oldData * initialFeature.transpose := by
  induction packets generalizing initialFeature with
  | nil => rfl
  | cons packet packets ih =>
      rw [runFeaturePackets, ih]
      exact oldFeatureMap_packetStep_eq
        oldData newData orthogonalRows packet initialFeature

omit [Fintype OldSample] in
/-- If the old data-to-hidden map is fixed, the change in old prediction is
exactly that map applied to the head displacement. -/
theorem factorizedPrediction_sub_eq_oldFeatureMap_mulVec_headSub
    (oldData : Matrix OldSample Feature ℝ)
    (finalFeature initialFeature : Matrix Hidden Feature ℝ)
    (finalHead initialHead : Hidden → ℝ)
    (featureMapFixed :
      oldData * finalFeature.transpose =
        oldData * initialFeature.transpose) :
    factorizedPrediction oldData finalFeature finalHead -
        factorizedPrediction oldData initialFeature initialHead =
      (oldData * initialFeature.transpose).mulVec
        (finalHead - initialHead) := by
  simp only [factorizedPrediction, collapsedWeight,
    Matrix.mulVec_mulVec]
  rw [featureMapFixed, ← Matrix.mulVec_sub]

/-- Exact factorized-model forgetting identity from Claim C.1. -/
theorem factorizedForgetting_eq_halfSquared_headDrift
    (oldData : Matrix OldSample Feature ℝ)
    (target : OldSample → ℝ)
    (finalFeature initialFeature : Matrix Hidden Feature ℝ)
    (finalHead initialHead : Hidden → ℝ)
    (featureMapFixed :
      oldData * finalFeature.transpose =
        oldData * initialFeature.transpose)
    (initialFit :
      factorizedPrediction oldData initialFeature initialHead = target) :
    factorizedForgetting oldData target
        finalFeature initialFeature finalHead initialHead =
      halfSquaredL2
        ((oldData * initialFeature.transpose).mulVec
          (finalHead - initialHead)) := by
  have drift := factorizedPrediction_sub_eq_oldFeatureMap_mulVec_headSub
    oldData finalFeature initialFeature finalHead initialHead featureMapFixed
  have finalResidual :
      factorizedPrediction oldData finalFeature finalHead - target =
        (oldData * initialFeature.transpose).mulVec
          (finalHead - initialHead) := by
    rw [← initialFit]
    exact drift
  unfold factorizedForgetting factorizedTaskLoss
  rw [initialFit, finalResidual]
  simp [halfSquaredL2]

/-- Every factorized path satisfying the source orthogonality condition has
the exact head-drift forgetting formula. -/
theorem factorizedForgetting_runFeaturePackets_eq_halfSquared_headDrift
    (oldData : Matrix OldSample Feature ℝ)
    (newData : Matrix NewSample Feature ℝ)
    (target : OldSample → ℝ)
    (orthogonalRows : oldData * newData.transpose = 0)
    (packets : List (FeaturePacket NewSample Hidden))
    (initialFeature : Matrix Hidden Feature ℝ)
    (finalHead initialHead : Hidden → ℝ)
    (initialFit :
      factorizedPrediction oldData initialFeature initialHead = target) :
    factorizedForgetting oldData target
        (runFeaturePackets newData packets initialFeature)
        initialFeature finalHead initialHead =
      halfSquaredL2
        ((oldData * initialFeature.transpose).mulVec
          (finalHead - initialHead)) :=
  factorizedForgetting_eq_halfSquared_headDrift
    oldData target
    (runFeaturePackets newData packets initialFeature)
    initialFeature finalHead initialHead
    (oldFeatureMap_runFeaturePackets_eq
      oldData newData orthogonalRows packets initialFeature)
    initialFit

/-- Full column rank of the old feature map makes every nonzero head
displacement strictly forgetting. -/
theorem factorizedForgetting_pos_of_columnIndependent
    (oldData : Matrix OldSample Feature ℝ)
    (target : OldSample → ℝ)
    (finalFeature initialFeature : Matrix Hidden Feature ℝ)
    (finalHead initialHead : Hidden → ℝ)
    (featureMapFixed :
      oldData * finalFeature.transpose =
        oldData * initialFeature.transpose)
    (initialFit :
      factorizedPrediction oldData initialFeature initialHead = target)
    (fullColumnRank :
      LinearIndependent ℝ (oldData * initialFeature.transpose).col)
    (headChanged : finalHead ≠ initialHead) :
    0 < factorizedForgetting oldData target
      finalFeature initialFeature finalHead initialHead := by
  rw [factorizedForgetting_eq_halfSquared_headDrift
    oldData target finalFeature initialFeature finalHead initialHead
    featureMapFixed initialFit]
  apply halfSquaredL2_pos_of_ne_zero
  have injectiveMap :
      Function.Injective
        (oldData * initialFeature.transpose).mulVec :=
    Matrix.mulVec_injective_iff.mpr fullColumnRank
  intro observedZero
  have headDifferenceZero : finalHead - initialHead = 0 := by
    apply injectiveMap
    simpa using observedZero
  exact headChanged (sub_eq_zero.mp headDifferenceZero)

/-! ## Executable source and boundary fixtures -/

def oldAxisData : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

def newAxisData : Matrix (Fin 1) (Fin 2) ℝ := !![0, 1]

def initialDirectWeight : Fin 2 → ℝ := ![1, 0]

def oldAxisTarget : Fin 1 → ℝ := ![1]

def unitResidual : Fin 1 → ℝ := ![1]

def directUnitPacket : DirectPacket (Fin 1) where
  residual := unitResidual
  rate := 1

theorem old_new_axis_rows_orthogonal :
    oldAxisData * newAxisData.transpose = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [oldAxisData, newAxisData, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem initialDirectWeight_fits_oldAxis :
    directPrediction oldAxisData initialDirectWeight =
      oldAxisTarget := by
  funext i
  fin_cases i
  norm_num [directPrediction, oldAxisData, initialDirectWeight,
    oldAxisTarget, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Positive direct-model fixture: the new-task step is nonzero, but old-task
forgetting is exactly zero. -/
theorem direct_orthogonal_packet_zero_forgetting :
    directPacketStep newAxisData directUnitPacket initialDirectWeight ≠
        initialDirectWeight ∧
      directForgetting oldAxisData oldAxisTarget
        (runDirectPackets newAxisData [directUnitPacket]
          initialDirectWeight)
        initialDirectWeight = 0 := by
  constructor
  · intro equal
    have coordinate := congrFun equal (1 : Fin 2)
    norm_num [directPacketStep, taskFeatureDirection, newAxisData,
      directUnitPacket, unitResidual, initialDirectWeight,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] at coordinate
  · exact directForgetting_runDirectPackets_eq_zero
      oldAxisData newAxisData oldAxisTarget
      old_new_axis_rows_orthogonal [directUnitPacket]
      initialDirectWeight initialDirectWeight_fits_oldAxis

def initialOneHiddenFeature : Matrix Unit (Fin 2) ℝ :=
  oneHiddenLift initialDirectWeight

def doubledUnitHead : Unit → ℝ := fun _ => 2

@[simp] theorem collapsedWeight_initialOneHiddenFeature :
    collapsedWeight initialOneHiddenFeature unitHead =
      initialDirectWeight := by
  simp [initialOneHiddenFeature]

theorem oneHidden_oldFeatureMap_columnIndependent :
    LinearIndependent ℝ
      (oldAxisData * initialOneHiddenFeature.transpose).col := by
  rw [← Matrix.mulVec_injective_iff]
  intro left right equal
  funext hidden
  fin_cases hidden
  have coordinate := congrFun equal (0 : Fin 1)
  norm_num [oldAxisData, initialOneHiddenFeature, oneHiddenLift,
    Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two] at coordinate ⊢
  rcases coordinate with coordinate | impossible
  · exact coordinate
  · change (![1, 0] : Fin 2 → ℝ) 0 = 0 at impossible
    norm_num at impossible

/-- Negative parameterization fixture: the direct and factorized models begin
with the same function, the factorized feature map is unchanged, but changing
its one-dimensional head produces strictly positive old-task forgetting. -/
theorem same_function_class_factorized_head_can_forget :
    collapsedWeight initialOneHiddenFeature unitHead =
        initialDirectWeight ∧
      factorizedPrediction oldAxisData initialOneHiddenFeature unitHead =
        oldAxisTarget ∧
      0 < factorizedForgetting oldAxisData oldAxisTarget
        initialOneHiddenFeature initialOneHiddenFeature
        doubledUnitHead unitHead := by
  constructor
  · exact collapsedWeight_oneHiddenLift initialDirectWeight
  constructor
  · rw [factorizedPrediction_eq_directPrediction,
      collapsedWeight_initialOneHiddenFeature]
    exact initialDirectWeight_fits_oldAxis
  · apply factorizedForgetting_pos_of_columnIndependent
      oldAxisData oldAxisTarget
      initialOneHiddenFeature initialOneHiddenFeature
      doubledUnitHead unitHead
    · rfl
    · rw [factorizedPrediction_eq_directPrediction,
        collapsedWeight_initialOneHiddenFeature]
      exact initialDirectWeight_fits_oldAxis
    · exact oneHidden_oldFeatureMap_columnIndependent
    · intro equal
      have coordinate := congrFun equal ()
      norm_num [doubledUnitHead, unitHead] at coordinate

def noninjectiveOldFeatureMap :
    Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

def initialTwoHead : Fin 2 → ℝ := ![1, 0]

def changedNullHead : Fin 2 → ℝ := ![1, 1]

/-- The full-column-rank premise is essential: a nonzero head displacement in
the kernel of the old feature map causes zero forgetting. -/
theorem noninjective_featureMap_head_change_zero_forgetting :
    changedNullHead ≠ initialTwoHead ∧
      noninjectiveOldFeatureMap.mulVec
          (changedNullHead - initialTwoHead) = 0 := by
  constructor
  · intro equal
    have coordinate := congrFun equal (1 : Fin 2)
    norm_num [changedNullHead, initialTwoHead] at coordinate
  · funext sample
    fin_cases sample
    norm_num [noninjectiveOldFeatureMap, changedNullHead,
      initialTwoHead, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end

end FactorizedLinearForgetting

end Mettapedia.MachineLearning.ContinualLearning
