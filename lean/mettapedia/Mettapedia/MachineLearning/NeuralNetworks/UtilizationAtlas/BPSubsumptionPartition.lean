import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.PCPlasticity
import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate

/-!
# A scoped backpropagation-realization audit for predictive coding

This module asks, for a finite catalog of mechanisms already formalized in the
predictive-coding frontier, whether the mechanism requires a distinct training
rule.  Positive classifications carry explicit backpropagation constructions:
an ordinary update, a curvature metric, a quadratic proximal model, a joint
projection, or a perturbed negative-curvature step.  Local parallel execution
is kept separate because it is an execution-model property rather than an
optimizer identity.

The scope boundaries are part of the result.  A positive curvature
preconditioner cannot move an exact critical point without a perturbation or a
negative-curvature oracle.  Prospective compensation cannot be reproduced
when the compensating readout is frozen.  The trust-region identification is
exact in its declared quadratic model and remains only a Taylor approximation
outside it.  Finally, local backpropagation obeys the same finite-speed
communication lower bound as any other bounded-bandwidth rule, so parallel
local work is not by itself a predictive-coding separation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
open Mettapedia.MachineLearning.ContinualLearning

/-! ## T1: curvature-normalized BP and actual saddle escape -/

/-- A two-coordinate strict-saddle normal form.  The first coordinate has
negative curvature `-negativeCurvature`; the second has unit positive
curvature. -/
noncomputable def strictSaddleNormalEnergy
    (negativeCurvature : ℝ) (state : ℝ × ℝ) : ℝ :=
  (state.2 ^ 2 - negativeCurvature * state.1 ^ 2) / 2

/-- Gradient of `strictSaddleNormalEnergy`. -/
noncomputable def strictSaddleNormalGradient
    (negativeCurvature : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  (-negativeCurvature * state.1, state.2)

/-- A scalar-metric preconditioned gradient step in saddle normal
coordinates. -/
noncomputable def preconditionedSaddleGradientStep
    (preconditioner learningRate negativeCurvature : ℝ)
    (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.1 - learningRate * preconditioner *
      (strictSaddleNormalGradient negativeCurvature state).1,
    state.2 - learningRate * preconditioner *
      (strictSaddleNormalGradient negativeCurvature state).2)

/-- Ordinary preconditioned gradient descent remains at the exact saddle for
every scalar preconditioner and learning rate.  Curvature scaling alone is not
an escape algorithm. -/
theorem preconditionedSaddleGradientStep_origin_fixed
    (preconditioner learningRate negativeCurvature : ℝ) :
    preconditionedSaddleGradientStep preconditioner learningRate
        negativeCurvature (0, 0) = (0, 0) := by
  simp [preconditionedSaddleGradientStep, strictSaddleNormalGradient]

/-- Perturb the negative-curvature coordinate and then take an ordinary BP
gradient step. -/
noncomputable def perturbedBPSaddleStep
    (learningRate negativeCurvature seed : ℝ) : ℝ × ℝ :=
  preconditionedSaddleGradientStep 1 learningRate negativeCurvature (seed, 0)

theorem perturbedBPSaddleStep_exact
    (learningRate negativeCurvature seed : ℝ) :
    perturbedBPSaddleStep learningRate negativeCurvature seed =
      ((1 + learningRate * negativeCurvature) * seed, 0) := by
  simp [perturbedBPSaddleStep, preconditionedSaddleGradientStep,
    strictSaddleNormalGradient]
  ring

/-- A nonzero perturbation followed by BP escapes the strict saddle whenever
the negative curvature is positive and the learning rate is nonnegative. -/
theorem perturbedBPSaddleStep_strictly_escapes
    (learningRate negativeCurvature seed : ℝ)
    (hcurvature : 0 < negativeCurvature)
    (hrate : 0 ≤ learningRate) (hseed : seed ≠ 0) :
    strictSaddleNormalEnergy negativeCurvature
        (perturbedBPSaddleStep learningRate negativeCurvature seed) <
      strictSaddleNormalEnergy negativeCurvature (0, 0) := by
  have hscale : 0 < 1 + learningRate * negativeCurvature := by
    have : 0 ≤ learningRate * negativeCurvature :=
      mul_nonneg hrate (le_of_lt hcurvature)
    linarith
  have hcoordinate :
      (1 + learningRate * negativeCurvature) * seed ≠ 0 :=
    mul_ne_zero (ne_of_gt hscale) hseed
  rw [perturbedBPSaddleStep_exact]
  simp only [strictSaddleNormalEnergy]
  have hsquare := sq_pos_of_ne_zero hcoordinate
  nlinarith

/-- The ordinary BP Hessian normal form has a positive escape magnitude for a
nondegenerate scalar input-target pair. -/
theorem backpropOriginEscapeMagnitude_pos
    (input target : ℝ) (hproduct : input * target ≠ 0) :
    0 < backpropOriginEscapeMagnitude input target := by
  simpa [backpropOriginEscapeMagnitude] using abs_pos.mpr hproduct

/-- A perturbed BP step escapes the BP strict-saddle normal form.  This is the
constructive reverse direction missing from a curvature-magnitude comparison. -/
theorem backpropNormalSaddle_perturbedBP_escapes
    (input target learningRate seed : ℝ)
    (hproduct : input * target ≠ 0)
    (hrate : 0 ≤ learningRate) (hseed : seed ≠ 0) :
    strictSaddleNormalEnergy (backpropOriginEscapeMagnitude input target)
        (perturbedBPSaddleStep learningRate
          (backpropOriginEscapeMagnitude input target) seed) <
      strictSaddleNormalEnergy
        (backpropOriginEscapeMagnitude input target) (0, 0) := by
  exact perturbedBPSaddleStep_strictly_escapes _ _ _
    (backpropOriginEscapeMagnitude_pos input target hproduct) hrate hseed

/-- Explicit perturbation of the actual scalar BP loss.  Choosing
`w₁ = seed` and `w₂ = target * input * seed` moves the product prediction
toward the target.  The exact safe interval is the same scalar `(0,2)`
contraction interval for `input² * seed²`. -/
theorem oneMLPLoss_seededBP_strictly_escapes_origin
    (input target seed : ℝ)
    (hinput : input ≠ 0) (htarget : target ≠ 0) (hseed : seed ≠ 0)
    (hbound : input ^ 2 * seed ^ 2 < 2) :
    oneMLPLoss input target seed (target * input * seed) <
      oneMLPLoss input target 0 0 := by
  have hinputSq : 0 < input ^ 2 := sq_pos_of_ne_zero hinput
  have htargetSq : 0 < target ^ 2 := sq_pos_of_ne_zero htarget
  have hseedSq : 0 < seed ^ 2 := sq_pos_of_ne_zero hseed
  have hscale : 0 < input ^ 2 * seed ^ 2 := mul_pos hinputSq hseedSq
  simp only [oneMLPLoss]
  nlinarith [mul_pos htargetSq hscale,
    mul_pos htargetSq (mul_pos hscale (sub_pos.mpr hbound))]

/-- The local comparison and the constructive escape are separate facts: PC
has larger negative-curvature magnitude in the nondegenerate one-MLP model,
while an explicitly perturbed BP endpoint already leaves the same parameter
origin along a lower-loss direction. -/
theorem pcCurvatureComparison_and_seededBPActualEscape
    (input target seed : ℝ)
    (hinput : input ≠ 0) (htarget : target ≠ 0) (hseed : seed ≠ 0)
    (hbound : input ^ 2 * seed ^ 2 < 2) :
    backpropOriginEscapeMagnitude input target <
        pcOriginEscapeMagnitude input target ∧
      oneMLPLoss input target seed (target * input * seed) <
        oneMLPLoss input target 0 0 := by
  exact ⟨pcOrigin_escapeMagnitude_strictly_larger input target htarget,
    oneMLPLoss_seededBP_strictly_escapes_origin input target seed
      hinput htarget hseed hbound⟩

/-- Positive fixture: the unit seed reaches zero BP loss from the unit
one-MLP origin. -/
theorem unitOneMLP_seededBP_escape_positiveFixture :
    oneMLPLoss 1 1 1 1 < oneMLPLoss 1 1 0 0 := by
  norm_num [oneMLPLoss]

/-- Negative fixture: a seed outside the `(0,2)` contraction interval
overshoots and increases the actual BP loss. -/
theorem unitOneMLP_largeSeed_increasesLoss_negativeFixture :
    oneMLPLoss 1 1 2 2 > oneMLPLoss 1 1 0 0 := by
  norm_num [oneMLPLoss]

/-- Identity curvature-normalized PC and curvature-normalized BP construct the
same endpoint, and that shared endpoint reaches the scalar quadratic optimum
in one step. -/
theorem curvatureNormalizedPC_constructiveBPEmulation
    (sourceActivation downstreamGain target weight : ℝ)
    (heffective : downstreamGain * sourceActivation ≠ 0) :
    chainLinkPreconditionedPCUpdate 1 sourceActivation downstreamGain
          target weight =
        chainLinkNormalizedBPUpdate sourceActivation downstreamGain target weight ∧
      chainLinkHalfSquaredLoss sourceActivation downstreamGain target
          (chainLinkNormalizedBPUpdate sourceActivation downstreamGain
            target weight) = 0 := by
  have heq := (identityPreconditionedPC_bpEquivalentLicense
    sourceActivation downstreamGain target weight).updatesEqual
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact chainLink_identityPreconditioner_reaches_zeroLoss
    sourceActivation downstreamGain target weight heffective

/-! ## T2a: the quadratic trust correction as a proximal BP model -/

/-- Scalar quadratic proximal model with positive metric `fisher`, linearized
gradient `gradient`, and proposed displacement. -/
noncomputable def quadraticProximalBPModel
    (fisher gradient displacement : ℝ) : ℝ :=
  gradient * displacement + (1 / 2 : ℝ) * fisher * displacement ^ 2

/-- Completing the square exposes the exact gap from the proximal minimizer. -/
theorem quadraticProximalBPModel_gap_exact
    (fisher gradient displacement : ℝ) (hfisher : fisher ≠ 0) :
    quadraticProximalBPModel fisher gradient displacement -
        quadraticProximalBPModel fisher gradient
          (quadraticStateShift fisher gradient) =
      (1 / 2 : ℝ) * fisher *
        (displacement - quadraticStateShift fisher gradient) ^ 2 := by
  simp [quadraticProximalBPModel, quadraticStateShift]
  field_simp [hfisher]
  ring

/-- For a positive metric, the PC state shift is the global minimizer of the
same quadratic proximal model available to BP. -/
theorem quadraticStateShift_minimizes_proximalBPModel
    (fisher gradient displacement : ℝ) (hfisher : 0 < fisher) :
    quadraticProximalBPModel fisher gradient
        (quadraticStateShift fisher gradient) ≤
      quadraticProximalBPModel fisher gradient displacement := by
  have hgap := quadraticProximalBPModel_gap_exact fisher gradient displacement
    (ne_of_gt hfisher)
  have hnonneg :
      0 ≤ (1 / 2 : ℝ) * fisher *
        (displacement - quadraticStateShift fisher gradient) ^ 2 := by
    positivity
  linarith

/-- The positive-metric proximal optimum is unique. -/
theorem quadraticStateShift_unique_proximalBPMinimizer
    (fisher gradient displacement : ℝ) (hfisher : 0 < fisher)
    (hminimal :
      quadraticProximalBPModel fisher gradient displacement ≤
        quadraticProximalBPModel fisher gradient
          (quadraticStateShift fisher gradient)) :
    displacement = quadraticStateShift fisher gradient := by
  have hgap := quadraticProximalBPModel_gap_exact fisher gradient displacement
    (ne_of_gt hfisher)
  have hreverse := quadraticStateShift_minimizes_proximalBPModel
    fisher gradient displacement hfisher
  have hzero :
      (1 / 2 : ℝ) * fisher *
        (displacement - quadraticStateShift fisher gradient) ^ 2 = 0 := by
    linarith
  have hcoef : (1 / 2 : ℝ) * fisher ≠ 0 := by positivity
  have hsquare :
      (displacement - quadraticStateShift fisher gradient) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hcoef
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

/-- BP written with the explicit inverse-Fisher proximal correction. -/
noncomputable def proximalBPWeightGradient
    (backpropGradient stateJacobian fisher stateLossGradient : ℝ) : ℝ :=
  backpropGradient + stateJacobian * (stateLossGradient / fisher)

/-- Inside the local quadratic model, the linearized PC weight gradient is
exactly the proximal BP gradient. -/
theorem linearizedPCWeightGradient_constructiveProximalBPEmulation
    (backpropGradient stateJacobian fisher stateLossGradient : ℝ) :
    linearizedPCWeightGradient backpropGradient stateJacobian
        (quadraticStateShift fisher stateLossGradient) =
      proximalBPWeightGradient backpropGradient stateJacobian fisher
        stateLossGradient := by
  exact linearizedPCWeightGradient_eq_inverseFisherCorrection
    backpropGradient stateJacobian fisher stateLossGradient

/-! ## T2b: prospective compensation as BP plus projection -/

/-- Joint hidden/readout endpoint for the scalar prospective-interference
problem. -/
structure JointReadoutRepair where
  hidden : ℝ
  preservedReadout : ℝ

/-- Ordinary BP repairs the hidden activity; a projection then adjusts the old
readout to preserve its previous output. -/
noncomputable def projectedBPRepair
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ) :
    JointReadoutRepair where
  hidden := bpRepairedHidden errorReadout input errorTarget
  preservedReadout := prospectiveCorrectReadout oldHidden oldCorrectReadout
    (bpRepairedHidden errorReadout input errorTarget)

/-- Feasibility means simultaneously fitting the new target and preserving
the old output. -/
def JointReadoutRepair.Feasible
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (repair : JointReadoutRepair) : Prop :=
  sharedHiddenOutput errorReadout repair.hidden input = errorTarget ∧
    sharedHiddenOutput repair.preservedReadout repair.hidden input =
      sharedHiddenOutput oldCorrectReadout oldHidden input

/-- A BP-compatible joint objective: fit the new output while penalizing any
change to the old output. -/
noncomputable def jointPreservationLoss
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (repair : JointReadoutRepair) : ℝ :=
  halfSquaredOutputError errorTarget
      (sharedHiddenOutput errorReadout repair.hidden input) +
    halfSquaredOutputError
      (sharedHiddenOutput oldCorrectReadout oldHidden input)
      (sharedHiddenOutput repair.preservedReadout repair.hidden input)

theorem jointPreservationLoss_nonnegative
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (repair : JointReadoutRepair) :
    0 ≤ jointPreservationLoss input oldHidden oldCorrectReadout
      errorReadout errorTarget repair := by
  simp [jointPreservationLoss, halfSquaredOutputError]
  positivity

/-- BP plus projection is a feasible joint repair under the same nondegenerate
conditions as the prospective construction. -/
theorem projectedBPRepair_feasible
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0) :
    JointReadoutRepair.Feasible input oldHidden oldCorrectReadout
      errorReadout errorTarget
      (projectedBPRepair input oldHidden oldCorrectReadout errorReadout
        errorTarget) := by
  exact prospectiveRepair_fixes_and_preserves
    input oldHidden oldCorrectReadout errorReadout errorTarget hpath hnew

/-- The projected BP repair attains zero joint preservation loss and is
therefore a global minimizer of the explicit BP-compatible objective. -/
theorem projectedBPRepair_globalMinimizer_jointPreservationLoss
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0)
    (repair : JointReadoutRepair) :
    jointPreservationLoss input oldHidden oldCorrectReadout errorReadout
        errorTarget
        (projectedBPRepair input oldHidden oldCorrectReadout errorReadout
          errorTarget) = 0 ∧
      jointPreservationLoss input oldHidden oldCorrectReadout errorReadout
          errorTarget
          (projectedBPRepair input oldHidden oldCorrectReadout errorReadout
            errorTarget) ≤
        jointPreservationLoss input oldHidden oldCorrectReadout errorReadout
          errorTarget repair := by
  have hfeasible := projectedBPRepair_feasible input oldHidden oldCorrectReadout
    errorReadout errorTarget hpath hnew
  have hzero :
      jointPreservationLoss input oldHidden oldCorrectReadout errorReadout
          errorTarget
          (projectedBPRepair input oldHidden oldCorrectReadout errorReadout
            errorTarget) = 0 := by
    simp [jointPreservationLoss, halfSquaredOutputError, hfeasible.1,
      hfeasible.2]
  exact ⟨hzero, by
    rw [hzero]
    exact jointPreservationLoss_nonnegative input oldHidden oldCorrectReadout
      errorReadout errorTarget repair⟩

/-- The projected BP endpoint is the unique simultaneous exact repair. -/
theorem projectedBPRepair_unique
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0)
    (repair : JointReadoutRepair)
    (hrepair : JointReadoutRepair.Feasible input oldHidden oldCorrectReadout
      errorReadout errorTarget repair) :
    repair = projectedBPRepair input oldHidden oldCorrectReadout errorReadout
      errorTarget := by
  let newHidden := bpRepairedHidden errorReadout input errorTarget
  have htarget := bpRepairedHidden_fixes_errorOutput
    errorReadout input errorTarget hpath
  have hhiddenProduct :
      (errorReadout * input) * repair.hidden =
        (errorReadout * input) * newHidden := by
    calc
      (errorReadout * input) * repair.hidden =
          sharedHiddenOutput errorReadout repair.hidden input := by
            simp [sharedHiddenOutput]
            ring
      _ = errorTarget := hrepair.1
      _ = sharedHiddenOutput errorReadout newHidden input := htarget.symm
      _ = (errorReadout * input) * newHidden := by
            simp [sharedHiddenOutput]
            ring
  have hhidden : repair.hidden = newHidden := by
    exact mul_left_cancel₀ hpath hhiddenProduct
  have hinput : input ≠ 0 := right_ne_zero_of_mul hpath
  have hreadoutCoefficient : newHidden * input ≠ 0 := mul_ne_zero hnew hinput
  have hpreserved := prospectiveCorrectReadout_preserves_output
    input oldHidden oldCorrectReadout newHidden hnew
  have hreadoutProduct :
      (newHidden * input) * repair.preservedReadout =
        (newHidden * input) *
          prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden := by
    calc
      (newHidden * input) * repair.preservedReadout =
          sharedHiddenOutput repair.preservedReadout repair.hidden input := by
            rw [hhidden]
            simp [sharedHiddenOutput]
            ring
      _ = sharedHiddenOutput oldCorrectReadout oldHidden input := hrepair.2
      _ = sharedHiddenOutput
          (prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden)
          newHidden input := hpreserved.symm
      _ = (newHidden * input) *
          prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden := by
            simp [sharedHiddenOutput]
            ring
  have hreadout :
      repair.preservedReadout =
        prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden :=
    mul_left_cancel₀ hreadoutCoefficient hreadoutProduct
  cases repair with
  | mk hidden readout =>
      change hidden = newHidden at hhidden
      change readout =
        prospectiveCorrectReadout oldHidden oldCorrectReadout newHidden at hreadout
      subst hidden
      subst readout
      rfl

/-- The projection is minimum-change among feasible exact repairs.  In this
nondegenerate scalar problem the feasible set is a singleton. -/
theorem projectedBPRepair_minimumReadoutChange
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (hpath : errorReadout * input ≠ 0)
    (hnew : bpRepairedHidden errorReadout input errorTarget ≠ 0)
    (repair : JointReadoutRepair)
    (hrepair : JointReadoutRepair.Feasible input oldHidden oldCorrectReadout
      errorReadout errorTarget repair) :
    ((projectedBPRepair input oldHidden oldCorrectReadout errorReadout
        errorTarget).preservedReadout - oldCorrectReadout) ^ 2 ≤
      (repair.preservedReadout - oldCorrectReadout) ^ 2 := by
  rw [projectedBPRepair_unique input oldHidden oldCorrectReadout errorReadout
    errorTarget hpath hnew repair hrepair]

/-- Negative boundary: if BP repairs only the shared hidden activity while the
old readout is frozen, it cannot preserve the old output when the live old path
and hidden displacement are both nonzero. -/
theorem frozenReadout_cannot_emulate_prospectiveRepair
    (input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ)
    (holdPath : oldCorrectReadout * input ≠ 0)
    (hmove : bpRepairedHidden errorReadout input errorTarget ≠ oldHidden) :
    ¬ JointReadoutRepair.Feasible input oldHidden oldCorrectReadout
      errorReadout errorTarget
      { hidden := bpRepairedHidden errorReadout input errorTarget
        preservedReadout := oldCorrectReadout } := by
  intro hfeasible
  have hchanged := (bp_hiddenRepair_changes_correctOutput_iff
    oldCorrectReadout input oldHidden
      (bpRepairedHidden errorReadout input errorTarget)).2 ⟨holdPath, hmove⟩
  exact hchanged hfeasible.2

/-- A zero repaired hidden state cannot preserve a nonzero old output by any
finite readout choice. -/
theorem zeroHidden_nonzeroOldOutput_no_projection
    (input oldHidden oldCorrectReadout : ℝ)
    (hold : sharedHiddenOutput oldCorrectReadout oldHidden input ≠ 0) :
    ∀ readout : ℝ,
      sharedHiddenOutput readout 0 input ≠
        sharedHiddenOutput oldCorrectReadout oldHidden input := by
  intro readout heq
  have hzero : sharedHiddenOutput readout 0 input = 0 := by
    simp [sharedHiddenOutput]
  rw [hzero] at heq
  exact hold heq.symm

/-! ## T2c: online retention as constrained BP -/

/-- BP+ is the minimum-change scalar update satisfying the linearized replay
constraint, provided the proposed task update has already been clipped to the
adapter trust region.  This is the online-learning extension of the proximal
BP partition. -/
theorem bpPlus_onlineRetention_minimumChange
    (metric retentionGradient proposed radius : ℝ)
    (hmetric : 0 ≤ metric)
    (hradius : 0 ≤ radius)
    (hproposed : |proposed| ≤ radius) :
    ScalarMinimumChangeCertificate metric retentionGradient proposed radius
      (bpPlusScalarUpdate retentionGradient proposed) := by
  exact scalarRetentionProjection_certificate metric retentionGradient
    proposed radius hmetric hradius hproposed

/-! ## T3: local communication and the execution-model residue -/

/-- Boundary signal indexed from the loss/output end of a chain. -/
def boundaryBackpropSignal (distance : ℕ) (signal : Bool) :
    ChainState Bool distance :=
  fun node => if node.val = 0 then signal else false

theorem boundaryBackpropSignal_agree_away_from_zero
    (distance : ℕ) (first second : Bool) :
    ∀ node, node.val ≠ 0 →
      boundaryBackpropSignal distance first node =
        boundaryBackpropSignal distance second node := by
  intro node hnode
  simp [boundaryBackpropSignal, hnode]

/-- The parameter node `distance` edges from the output/loss boundary. -/
def deepestBackpropNode (distance : ℕ) : Fin (distance + 1) :=
  ⟨distance, by omega⟩

/-- Proof-bearing exact local implementation of one binary reverse-mode
dependency.  This is deliberately algorithm-independent: any implementation
advertised as local BP must supply its update bandwidth and correctness on the
two distinguishable boundary signals. -/
structure ExactLocalBackpropSignal
    (distance bandwidth rounds : ℕ) where
  step : ChainState Bool distance → ChainState Bool distance
  hasBandwidth : HasChainBandwidth step bandwidth
  falseCorrect :
    (Nat.iterate step rounds (boundaryBackpropSignal distance false))
        (deepestBackpropNode distance) = false
  trueCorrect :
    (Nat.iterate step rounds (boundaryBackpropSignal distance true))
        (deepestBackpropNode distance) = true

/-- Actual communication lower bound for exact local BP: the loss signal's
dependency wavefront must reach the parameter node. -/
theorem exactLocalBackpropSignal_requires_reach
    {distance bandwidth rounds : ℕ}
    (implementation : ExactLocalBackpropSignal distance bandwidth rounds) :
    distance ≤ rounds * bandwidth := by
  by_contra hreach
  have hearly : rounds * bandwidth < distance := Nat.lt_of_not_ge hreach
  have hequal := hasChainBandwidth_iterate_eq_of_agree_away_from_zero
    implementation.step implementation.hasBandwidth
    (boundaryBackpropSignal distance false)
    (boundaryBackpropSignal distance true)
    (boundaryBackpropSignal_agree_away_from_zero distance false true)
    (deepestBackpropNode distance) hearly
  rw [implementation.falseCorrect, implementation.trueCorrect] at hequal
  exact Bool.false_ne_true hequal

/-- Unit-radius copying transports a signal from node zero to node `sweeps`
after exactly `sweeps` synchronized rounds. -/
theorem forwardUnitCopyStep_reaches_sweepIndex
    {Value : Type*} (distance sweeps : ℕ) (hsweeps : sweeps ≤ distance)
    (state : ChainState Value distance) :
    (Nat.iterate (forwardRadiusCopyStep (Value := Value) distance 1) sweeps state)
        (⟨sweeps, Nat.lt_succ_of_le hsweeps⟩ : Fin (distance + 1)) = state 0 := by
  induction sweeps with
  | zero => simp
  | succ sweeps ih =>
      rw [Function.iterate_succ_apply']
      simp only [forwardRadiusCopyStep]
      split
      · simpa using ih (Nat.le_of_succ_le hsweeps)
      · omega

/-- The communication lower bound is tight for a unit-bandwidth local copy
implementation. -/
def unitBandwidthExactLocalBackpropSignal
    (distance : ℕ) : ExactLocalBackpropSignal distance 1 distance where
  step := forwardRadiusCopyStep distance 1
  hasBandwidth := forwardRadiusCopyStep_hasBandwidth distance 1
  falseCorrect := by
    simpa [boundaryBackpropSignal, deepestBackpropNode] using
      forwardUnitCopyStep_reaches_sweepIndex distance distance le_rfl
        (boundaryBackpropSignal distance false)
  trueCorrect := by
    simpa [boundaryBackpropSignal, deepestBackpropNode] using
      forwardUnitCopyStep_reaches_sweepIndex distance distance le_rfl
        (boundaryBackpropSignal distance true)

theorem unitBandwidthLocalBackprop_lowerBound_tight (distance : ℕ) :
    Nonempty (ExactLocalBackpropSignal distance 1 distance) ∧
      ∀ rounds : ℕ, ExactLocalBackpropSignal distance 1 rounds →
        distance ≤ rounds := by
  refine ⟨⟨unitBandwidthExactLocalBackpropSignal distance⟩, ?_⟩
  intro rounds implementation
  simpa using exactLocalBackpropSignal_requires_reach implementation

/-- Like exact unit-bandwidth PC settling, exact unit-bandwidth local BP cannot
beat the layerwise dependency depth in synchronized rounds. -/
theorem exactUnitBandwidthLocalBP_no_strictDigitalLatencyAdvantage
    {distance rounds : ℕ}
    (implementation : ExactLocalBackpropSignal distance 1 rounds) :
    ¬ (synchronizedLocalCost rounds (distance + 1)).parallelLatency <
        layerwiseDigitalLatency distance := by
  have hreach := exactLocalBackpropSignal_requires_reach implementation
  simp [synchronizedLocalCost, layerwiseDigitalLatency] at hreach ⊢
  omega

/-- Parallel local execution has a strict latency/work gap when at least two
nodes are active for at least one round. -/
theorem synchronizedLocalCost_parallel_strictly_below_serial
    (rounds activeNodes : ℕ) (hrounds : 0 < rounds)
    (hnodes : 1 < activeNodes) :
    (synchronizedLocalCost rounds activeNodes).parallelLatency <
      (synchronizedLocalCost rounds activeNodes).serialWork := by
  simpa [synchronizedLocalCost] using
    Nat.mul_lt_mul_of_pos_left hnodes hrounds

/-! ## T4: the finite, proof-bearing partition -/

/-- The named mechanisms audited here.  This is a finite catalog, not a claim
about every past or future predictive-coding proposal. -/
inductive NamedPCBenefit where
  | unitErrorCoordinatePlasticity
  | scalarCurvatureNormalization
  | localQuadraticTrustCorrection
  | prospectiveCompensation
  | strictSaddleCurvature
  | synchronizedLocalParallelism
  deriving DecidableEq, Repr, Fintype

theorem namedPCBenefit_catalog_cardinality : Fintype.card NamedPCBenefit = 6 := by
  decide

/-- Constructive BP evidence attached to each training-rule mechanism. -/
def ConstructiveBPRealization : NamedPCBenefit → Prop
  | .unitErrorCoordinatePlasticity =>
      ∀ predictionJacobian lossGradient : ℝ,
        pcLocalParameterUpdate predictionJacobian
            (epcOneStepError 1 lossGradient) =
          predictionJacobian * lossGradient
  | .scalarCurvatureNormalization =>
      ∀ sourceActivation downstreamGain target weight : ℝ,
        downstreamGain * sourceActivation ≠ 0 →
          chainLinkPreconditionedPCUpdate 1 sourceActivation downstreamGain
                target weight =
              chainLinkNormalizedBPUpdate sourceActivation downstreamGain
                target weight ∧
            chainLinkHalfSquaredLoss sourceActivation downstreamGain target
                (chainLinkNormalizedBPUpdate sourceActivation downstreamGain
                  target weight) = 0
  | .localQuadraticTrustCorrection =>
      (∀ fisher gradient displacement : ℝ, 0 < fisher →
        quadraticProximalBPModel fisher gradient
            (quadraticStateShift fisher gradient) ≤
          quadraticProximalBPModel fisher gradient displacement) ∧
      (∀ backpropGradient stateJacobian fisher stateLossGradient : ℝ,
        linearizedPCWeightGradient backpropGradient stateJacobian
            (quadraticStateShift fisher stateLossGradient) =
          proximalBPWeightGradient backpropGradient stateJacobian fisher
            stateLossGradient)
  | .prospectiveCompensation =>
      ∀ input oldHidden oldCorrectReadout errorReadout errorTarget : ℝ,
        errorReadout * input ≠ 0 →
        bpRepairedHidden errorReadout input errorTarget ≠ 0 →
          JointReadoutRepair.Feasible input oldHidden oldCorrectReadout
              errorReadout errorTarget
              (projectedBPRepair input oldHidden oldCorrectReadout errorReadout
                errorTarget) ∧
            ∀ repair, JointReadoutRepair.Feasible input oldHidden
                oldCorrectReadout errorReadout errorTarget repair →
              repair = projectedBPRepair input oldHidden oldCorrectReadout
                errorReadout errorTarget
  | .strictSaddleCurvature =>
      (∀ preconditioner learningRate negativeCurvature : ℝ,
        preconditionedSaddleGradientStep preconditioner learningRate
            negativeCurvature (0, 0) = (0, 0)) ∧
      (∀ input target learningRate seed : ℝ,
        input * target ≠ 0 → 0 ≤ learningRate → seed ≠ 0 →
          strictSaddleNormalEnergy (backpropOriginEscapeMagnitude input target)
              (perturbedBPSaddleStep learningRate
                (backpropOriginEscapeMagnitude input target) seed) <
            strictSaddleNormalEnergy
              (backpropOriginEscapeMagnitude input target) (0, 0)) ∧
      (∀ input target seed : ℝ,
        input ≠ 0 → target ≠ 0 → seed ≠ 0 → input ^ 2 * seed ^ 2 < 2 →
          backpropOriginEscapeMagnitude input target <
              pcOriginEscapeMagnitude input target ∧
            oneMLPLoss input target seed (target * input * seed) <
              oneMLPLoss input target 0 0)
  | .synchronizedLocalParallelism => False

/-- The remaining named item is an execution-model property.  Its evidence is
the serial/parallel gap together with the fact that exact local BP itself obeys
the bounded-bandwidth round lower bound. -/
def ExecutionModelResidue : NamedPCBenefit → Prop
  | .synchronizedLocalParallelism =>
      (∀ rounds activeNodes : ℕ, 0 < rounds → 1 < activeNodes →
        (synchronizedLocalCost rounds activeNodes).parallelLatency <
          (synchronizedLocalCost rounds activeNodes).serialWork) ∧
      (∀ {distance bandwidth rounds : ℕ},
        ExactLocalBackpropSignal distance bandwidth rounds →
          distance ≤ rounds * bandwidth)
  | _ => False

/-- Every training-rule item in the named catalog has a constructive BP
realization; the only other item is explicitly an execution-model property. -/
theorem namedPCBenefit_constructive_partition
    (benefit : NamedPCBenefit) :
    ConstructiveBPRealization benefit ∨ ExecutionModelResidue benefit := by
  cases benefit with
  | unitErrorCoordinatePlasticity =>
      left
      exact epcOneStepParameterUpdate_unitRate_eq_backprop
  | scalarCurvatureNormalization =>
      left
      intro sourceActivation downstreamGain target weight heffective
      exact curvatureNormalizedPC_constructiveBPEmulation
        sourceActivation downstreamGain target weight heffective
  | localQuadraticTrustCorrection =>
      left
      exact ⟨quadraticStateShift_minimizes_proximalBPModel,
        linearizedPCWeightGradient_constructiveProximalBPEmulation⟩
  | prospectiveCompensation =>
      left
      intro input oldHidden oldCorrectReadout errorReadout errorTarget hpath hnew
      exact ⟨projectedBPRepair_feasible input oldHidden oldCorrectReadout
          errorReadout errorTarget hpath hnew,
        fun repair hrepair => projectedBPRepair_unique input oldHidden
          oldCorrectReadout errorReadout errorTarget hpath hnew repair hrepair⟩
  | strictSaddleCurvature =>
      left
      exact ⟨preconditionedSaddleGradientStep_origin_fixed,
        backpropNormalSaddle_perturbedBP_escapes,
        pcCurvatureComparison_and_seededBPActualEscape⟩
  | synchronizedLocalParallelism =>
      right
      exact ⟨synchronizedLocalCost_parallel_strictly_below_serial,
        fun implementation => exactLocalBackpropSignal_requires_reach implementation⟩

theorem constructiveBPRealization_iff_not_executionOnly
    (benefit : NamedPCBenefit) :
    ConstructiveBPRealization benefit ↔
      benefit ≠ .synchronizedLocalParallelism := by
  constructor
  · intro hrealization heq
    subst benefit
    exact hrealization
  · intro hnotExecution
    cases benefit with
    | unitErrorCoordinatePlasticity =>
        exact epcOneStepParameterUpdate_unitRate_eq_backprop
    | scalarCurvatureNormalization =>
        intro sourceActivation downstreamGain target weight heffective
        exact curvatureNormalizedPC_constructiveBPEmulation
          sourceActivation downstreamGain target weight heffective
    | localQuadraticTrustCorrection =>
        exact ⟨quadraticStateShift_minimizes_proximalBPModel,
          linearizedPCWeightGradient_constructiveProximalBPEmulation⟩
    | prospectiveCompensation =>
        intro input oldHidden oldCorrectReadout errorReadout errorTarget hpath hnew
        exact ⟨projectedBPRepair_feasible input oldHidden oldCorrectReadout
            errorReadout errorTarget hpath hnew,
          fun repair hrepair => projectedBPRepair_unique input oldHidden
            oldCorrectReadout errorReadout errorTarget hpath hnew repair hrepair⟩
    | strictSaddleCurvature =>
        exact ⟨preconditionedSaddleGradientStep_origin_fixed,
          backpropNormalSaddle_perturbedBP_escapes,
          pcCurvatureComparison_and_seededBPActualEscape⟩
    | synchronizedLocalParallelism =>
        exact (hnotExecution rfl).elim

theorem executionModelResidue_iff
    (benefit : NamedPCBenefit) :
    ExecutionModelResidue benefit ↔
      benefit = .synchronizedLocalParallelism := by
  constructor
  · intro hresidue
    cases benefit with
    | unitErrorCoordinatePlasticity => exact hresidue.elim
    | scalarCurvatureNormalization => exact hresidue.elim
    | localQuadraticTrustCorrection => exact hresidue.elim
    | prospectiveCompensation => exact hresidue.elim
    | strictSaddleCurvature => exact hresidue.elim
    | synchronizedLocalParallelism => rfl
  · intro heq
    subst benefit
    exact ⟨synchronizedLocalCost_parallel_strictly_below_serial,
      fun implementation => exactLocalBackpropSignal_requires_reach implementation⟩

/-- The audit crown packages the constructive partition, its sharp saddle
boundary, the frozen-readout counterexample, the Taylor boundary, and the
local-BP communication lower bound.  Its completeness is exactly the finite
`NamedPCBenefit` catalog above. -/
structure BPSubsumptionPartitionLicense : Prop where
  namedPartition : ∀ benefit : NamedPCBenefit,
    ConstructiveBPRealization benefit ∨ ExecutionModelResidue benefit
  trainingRuleCharacterization : ∀ benefit : NamedPCBenefit,
    ConstructiveBPRealization benefit ↔
      benefit ≠ .synchronizedLocalParallelism
  executionCharacterization : ∀ benefit : NamedPCBenefit,
    ExecutionModelResidue benefit ↔
      benefit = .synchronizedLocalParallelism
  preconditionerAloneStuck : ∀ preconditioner learningRate negativeCurvature : ℝ,
    preconditionedSaddleGradientStep preconditioner learningRate
      negativeCurvature (0, 0) = (0, 0)
  frozenReadoutBoundary : ∀ input oldHidden oldCorrectReadout errorReadout
      errorTarget : ℝ,
    oldCorrectReadout * input ≠ 0 →
    bpRepairedHidden errorReadout input errorTarget ≠ oldHidden →
      ¬ JointReadoutRepair.Feasible input oldHidden oldCorrectReadout
        errorReadout errorTarget
        { hidden := bpRepairedHidden errorReadout input errorTarget
          preservedReadout := oldCorrectReadout }
  onlineRetentionProjection : ∀ metric retentionGradient proposed radius : ℝ,
    0 ≤ metric → 0 ≤ radius → |proposed| ≤ radius →
      ScalarMinimumChangeCertificate metric retentionGradient proposed radius
        (bpPlusScalarUpdate retentionGradient proposed)
  generalOnlineRetentionProjection :
    ∀ {Adapter Task : Type*} [NormedAddCommGroup Adapter]
      [InnerProductSpace ℝ Adapter]
      (metric : AdapterMetric Adapter)
      (retentionGradients : Task → Adapter)
      (radius : ℝ) (proposed chosen : Adapter),
      MetricProjectionCertificate metric retentionGradients radius proposed chosen ↔
        IsMetricProjectionMinimum metric retentionGradients radius proposed chosen
  trustRegionBoundary :
    equationSevenTaylorBoundary.status ≠ .exactQuadraticIdentity
  localBPLowerBound : ∀ {distance bandwidth rounds : ℕ},
    ExactLocalBackpropSignal distance bandwidth rounds →
      distance ≤ rounds * bandwidth
  localBPNoUnitLatencyAdvantage : ∀ {distance rounds : ℕ},
    ExactLocalBackpropSignal distance 1 rounds →
      ¬ (synchronizedLocalCost rounds (distance + 1)).parallelLatency <
        layerwiseDigitalLatency distance
  pcNoUnitLatencyAdvantage : ∀ distance sweeps : ℕ,
    ∀ step : PCState (distance + 1) → PCState (distance + 1),
      HasChainBandwidth step 1 →
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0) →
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0) →
      ¬ (synchronizedLocalCost sweeps (distance + 2)).parallelLatency <
        layerwiseDigitalLatency distance
  parallelExecutionGap : ∀ rounds activeNodes : ℕ,
    0 < rounds → 1 < activeNodes →
      (synchronizedLocalCost rounds activeNodes).parallelLatency <
        (synchronizedLocalCost rounds activeNodes).serialWork

theorem bp_subsumption_partition_crown : BPSubsumptionPartitionLicense where
  namedPartition := namedPCBenefit_constructive_partition
  trainingRuleCharacterization := constructiveBPRealization_iff_not_executionOnly
  executionCharacterization := executionModelResidue_iff
  preconditionerAloneStuck := preconditionedSaddleGradientStep_origin_fixed
  frozenReadoutBoundary := frozenReadout_cannot_emulate_prospectiveRepair
  onlineRetentionProjection := bpPlus_onlineRetention_minimumChange
  generalOnlineRetentionProjection := metricProjectionCertificate_iff_minimum
  trustRegionBoundary := equationSevenTaylorBoundary_not_exact
  localBPLowerBound := exactLocalBackpropSignal_requires_reach
  localBPNoUnitLatencyAdvantage :=
    exactUnitBandwidthLocalBP_no_strictDigitalLatencyAdvantage
  pcNoUnitLatencyAdvantage :=
    exactUnitBandwidthPC_no_strictDigitalLatencyAdvantage
  parallelExecutionGap := synchronizedLocalCost_parallel_strictly_below_serial

#print axioms perturbedBPSaddleStep_strictly_escapes
#print axioms pcCurvatureComparison_and_seededBPActualEscape
#print axioms curvatureNormalizedPC_constructiveBPEmulation
#print axioms quadraticStateShift_unique_proximalBPMinimizer
#print axioms projectedBPRepair_unique
#print axioms projectedBPRepair_globalMinimizer_jointPreservationLoss
#print axioms frozenReadout_cannot_emulate_prospectiveRepair
#print axioms bpPlus_onlineRetention_minimumChange
#print axioms exactLocalBackpropSignal_requires_reach
#print axioms unitBandwidthLocalBackprop_lowerBound_tight
#print axioms namedPCBenefit_catalog_cardinality
#print axioms namedPCBenefit_constructive_partition
#print axioms bp_subsumption_partition_crown

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
