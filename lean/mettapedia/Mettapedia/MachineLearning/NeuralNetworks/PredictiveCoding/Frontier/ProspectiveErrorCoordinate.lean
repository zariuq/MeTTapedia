import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.CoordinateRescue
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.ProspectiveInterference
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.HybridRefinement

/-!
# Prospective error-coordinate predictive coding

This file joins two previously separate parts of the predictive-coding
frontier.  Error-coordinate PC supplies explicit hidden prediction errors;
prospective configuration supplies an output state that is inferred before
plasticity.  The model below is the exact scalar linearization of a depth-
indexed adapter around a frozen forward pass.  `pathGain i` is the fixed
Jacobian coefficient from hidden error site `i` to the pre-readout hidden
state, and `readout` is the final linear map.

The joint energy contains one task term, one output-consistency term, and one
precision-weighted term per hidden error.  The task therefore acts directly
only on the prospective output state.  Hidden sites receive its effect through
the output-consistency path.

The scope is finite-dimensional linear/quadratic real arithmetic.  The file
does not claim that the nonlinear trained network follows these exact
dynamics.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier

/-! ## One depth-indexed joint model -/

/-- A frozen scalar linearization with `depth` hidden error sites and one
explicit prospective output state. -/
structure ProspectiveEPCModel (depth : ℕ) where
  target : ℝ
  baseHidden : ℝ
  readout : ℝ
  taskPrecision : ℝ
  outputPrecision : ℝ
  hiddenPrecision : Fin depth → ℝ
  pathGain : Fin depth → ℝ

/-- Hidden errors paired with the explicit prospective output state. -/
abbrev ProspectiveEPCState (depth : ℕ) := (Fin depth → ℝ) × ℝ

/-- The zero hidden-error configuration. -/
def zeroHiddenErrors (depth : ℕ) : Fin depth → ℝ := fun _ => 0

/-- Pre-readout hidden prediction reconstructed from the linearized error
coordinates. -/
noncomputable def prospectiveEPCHiddenPrediction {depth : ℕ}
    (model : ProspectiveEPCModel depth) (error : Fin depth → ℝ) : ℝ :=
  model.baseHidden + ∑ i, model.pathGain i * error i

/-- Output predicted by the frozen linearized adapter. -/
noncomputable def prospectiveEPCPredictedOutput {depth : ℕ}
    (model : ProspectiveEPCModel depth) (error : Fin depth → ℝ) : ℝ :=
  model.readout * prospectiveEPCHiddenPrediction model error

/-- The single joint energy: task loss at the prospective output, consistency
with the frozen readout, and precision-weighted hidden prediction errors. -/
noncomputable def prospectiveEPCJointEnergy {depth : ℕ}
    (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) : ℝ :=
  (1 / 2 : ℝ) * model.taskPrecision * (state.2 - model.target) ^ 2 +
    (1 / 2 : ℝ) * model.outputPrecision *
      (state.2 - prospectiveEPCPredictedOutput model state.1) ^ 2 +
    (1 / 2 : ℝ) * ∑ i, model.hiddenPrecision i * (state.1 i) ^ 2

/-- Output-only prospective objective at the frozen zero-error prediction. -/
noncomputable def prospectiveEPCOutputObjective {depth : ℕ}
    (model : ProspectiveEPCModel depth) (output : ℝ) : ℝ :=
  (1 / 2 : ℝ) * model.taskPrecision * (output - model.target) ^ 2 +
    (1 / 2 : ℝ) * model.outputPrecision *
      (output - model.readout * model.baseHidden) ^ 2

/-- Deep error-coordinate objective obtained by hard-constraining the
prospective output to the frozen readout prediction. -/
noncomputable def deepEPCConstrainedObjective {depth : ℕ}
    (model : ProspectiveEPCModel depth) (error : Fin depth → ℝ) : ℝ :=
  (1 / 2 : ℝ) * model.taskPrecision *
      (prospectiveEPCPredictedOutput model error - model.target) ^ 2 +
    (1 / 2 : ℝ) * ∑ i, model.hiddenPrecision i * (error i) ^ 2

/-! ## T1: the two objective restrictions -/

/-- Clamping every hidden error to zero reduces the joint energy exactly to
the output-only prospective objective. -/
theorem prospectiveEPCJointEnergy_zeroErrors_eq_outputObjective
    {depth : ℕ} (model : ProspectiveEPCModel depth) (output : ℝ) :
    prospectiveEPCJointEnergy model (zeroHiddenErrors depth, output) =
      prospectiveEPCOutputObjective model output := by
  simp [prospectiveEPCJointEnergy, prospectiveEPCOutputObjective,
    prospectiveEPCPredictedOutput, prospectiveEPCHiddenPrediction,
    zeroHiddenErrors]

/-- Hard-constraining the prospective output to the frozen readout prediction
reduces the joint energy exactly to the deep error-coordinate objective. -/
theorem prospectiveEPCJointEnergy_hardOutputConstraint_eq_deepObjective
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (error : Fin depth → ℝ) :
    prospectiveEPCJointEnergy model
        (error, prospectiveEPCPredictedOutput model error) =
      deepEPCConstrainedObjective model error := by
  simp [prospectiveEPCJointEnergy, deepEPCConstrainedObjective]

/-! ## Exact coordinate forces -/

/-- Negative derivative of the output-consistency term with respect to its
predicted output.  This is the force visible to hidden error sites. -/
noncomputable def prospectiveEPCOutputMismatchForce {depth : ℕ}
    (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) : ℝ :=
  model.outputPrecision *
    (state.2 - prospectiveEPCPredictedOutput model state.1)

/-- Negative derivative of the joint energy with respect to hidden error
coordinate `i`. -/
noncomputable def prospectiveEPCHiddenForce {depth : ℕ}
    (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (i : Fin depth) : ℝ :=
  model.readout * model.pathGain i *
      prospectiveEPCOutputMismatchForce model state -
    model.hiddenPrecision i * state.1 i

/-- Negative derivative of the joint energy with respect to the prospective
output state. -/
noncomputable def prospectiveEPCOutputForce {depth : ℕ}
    (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) : ℝ :=
  model.taskPrecision * (model.target - state.2) +
    model.outputPrecision *
      (prospectiveEPCPredictedOutput model state.1 - state.2)

/-! ## The force formulas are exact energy coefficients -/

/-- Shift one hidden error coordinate while leaving all others fixed. -/
def shiftProspectiveEPCHiddenError {depth : ℕ}
    (error : Fin depth → ℝ) (i : Fin depth) (increment : ℝ) :
    Fin depth → ℝ :=
  fun j => if j = i then error j + increment else error j

theorem prospectiveEPCHiddenPrediction_shift_exact
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (error : Fin depth → ℝ) (i : Fin depth) (increment : ℝ) :
    prospectiveEPCHiddenPrediction model
        (shiftProspectiveEPCHiddenError error i increment) =
    prospectiveEPCHiddenPrediction model error +
        model.pathGain i * increment := by
  classical
  unfold prospectiveEPCHiddenPrediction
  have hsum :
    ∑ j, model.pathGain j *
        shiftProspectiveEPCHiddenError error i increment j =
        ∑ j, (model.pathGain j * error j +
          if j = i then model.pathGain j * increment else 0) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hji : j = i
      · subst j
        simp [shiftProspectiveEPCHiddenError]
        ring
      · simp [shiftProspectiveEPCHiddenError, hji]
  calc
    model.baseHidden + ∑ j, model.pathGain j *
        shiftProspectiveEPCHiddenError error i increment j =
      model.baseHidden + ∑ j, (model.pathGain j * error j +
        if j = i then model.pathGain j * increment else 0) := by rw [hsum]
    _ = model.baseHidden +
        ((∑ j, model.pathGain j * error j) +
          ∑ j, if j = i then model.pathGain j * increment else 0) := by
      rw [Finset.sum_add_distrib]
    _ = model.baseHidden + ((∑ j, model.pathGain j * error j) +
        model.pathGain i * increment) := by
      simp
    _ = model.baseHidden + (∑ j, model.pathGain j * error j) +
        model.pathGain i * increment := by ring

theorem prospectiveEPCHiddenPenalty_shift_exact
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (error : Fin depth → ℝ) (i : Fin depth) (increment : ℝ) :
    (∑ j, model.hiddenPrecision j *
        (shiftProspectiveEPCHiddenError error i increment j) ^ 2) =
      (∑ j, model.hiddenPrecision j * (error j) ^ 2) +
        2 * model.hiddenPrecision i * error i * increment +
        model.hiddenPrecision i * increment ^ 2 := by
  classical
  calc
    ∑ j, model.hiddenPrecision j *
        (shiftProspectiveEPCHiddenError error i increment j) ^ 2 =
        ∑ j, (model.hiddenPrecision j * (error j) ^ 2 +
          if j = i then
            2 * model.hiddenPrecision j * error j * increment +
              model.hiddenPrecision j * increment ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hji : j = i
      · subst j
        simp [shiftProspectiveEPCHiddenError]
        ring
      · simp [shiftProspectiveEPCHiddenError, hji]
    _ = (∑ j, model.hiddenPrecision j * (error j) ^ 2) +
        ∑ j, if j = i then
          2 * model.hiddenPrecision j * error j * increment +
            model.hiddenPrecision j * increment ^ 2
        else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j, model.hiddenPrecision j * (error j) ^ 2) +
        2 * model.hiddenPrecision i * error i * increment +
        model.hiddenPrecision i * increment ^ 2 := by
      simp
      ring

/-- Exact output-coordinate energy increment.  Its linear coefficient is the
negative output force, so the force definition is tied to the joint energy. -/
theorem prospectiveEPCJointEnergy_outputIncrement_exact
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (increment : ℝ) :
    prospectiveEPCJointEnergy model (state.1, state.2 + increment) -
        prospectiveEPCJointEnergy model state =
      -increment * prospectiveEPCOutputForce model state +
        (1 / 2 : ℝ) *
          (model.taskPrecision + model.outputPrecision) * increment ^ 2 := by
  unfold prospectiveEPCJointEnergy prospectiveEPCOutputForce
  ring

/-- Exact hidden-coordinate energy increment.  The quadratic coefficient is
the local precision plus the readout/path curvature. -/
theorem prospectiveEPCJointEnergy_hiddenIncrement_exact
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (i : Fin depth) (increment : ℝ) :
    prospectiveEPCJointEnergy model
        (shiftProspectiveEPCHiddenError state.1 i increment, state.2) -
        prospectiveEPCJointEnergy model state =
      -increment * prospectiveEPCHiddenForce model state i +
        (1 / 2 : ℝ) *
          (model.outputPrecision *
              (model.readout * model.pathGain i) ^ 2 +
            model.hiddenPrecision i) * increment ^ 2 := by
  rw [prospectiveEPCJointEnergy, prospectiveEPCJointEnergy]
  rw [prospectiveEPCPredictedOutput, prospectiveEPCPredictedOutput,
    prospectiveEPCHiddenPrediction_shift_exact]
  rw [prospectiveEPCHiddenPenalty_shift_exact]
  unfold prospectiveEPCHiddenForce prospectiveEPCOutputMismatchForce
  unfold prospectiveEPCPredictedOutput
  ring

/-! ## T2: zero-readout ignition -/

/-- With a zero final readout and zero hidden errors, every hidden force is
exactly zero, irrespective of the prospective output. -/
theorem zeroReadout_zeroErrors_hiddenForce_eq_zero
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (hreadout : model.readout = 0) (output : ℝ) (i : Fin depth) :
    prospectiveEPCHiddenForce model
        (zeroHiddenErrors depth, output) i = 0 := by
  simp [prospectiveEPCHiddenForce, zeroHiddenErrors, hreadout]

/-- At zero readout, zero hidden errors, and zero prospective output, the
remaining output force is exactly the task precision times the target. -/
theorem zeroReadout_zeroErrors_outputForce_eq_task
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (hreadout : model.readout = 0) :
    prospectiveEPCOutputForce model (zeroHiddenErrors depth, 0) =
      model.taskPrecision * model.target := by
  simp [prospectiveEPCOutputForce, prospectiveEPCPredictedOutput,
    hreadout]

/-- Exact nonzero condition for output ignition at the zero-readout
boundary. -/
theorem zeroReadout_outputForce_ne_zero_iff
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (hreadout : model.readout = 0) :
    prospectiveEPCOutputForce model (zeroHiddenErrors depth, 0) ≠ 0 ↔
      model.taskPrecision ≠ 0 ∧ model.target ≠ 0 := by
  rw [zeroReadout_zeroErrors_outputForce_eq_task model hreadout]
  exact mul_ne_zero_iff

/-- Concrete ignition fixture: all hidden forces vanish while the output
force is one. -/
noncomputable def prospectiveEPCIgnitionFixture : ProspectiveEPCModel 3 where
  target := 1
  baseHidden := 2
  readout := 0
  taskPrecision := 1
  outputPrecision := 1
  hiddenPrecision := fun _ => 1
  pathGain := fun _ => 1

theorem prospectiveEPC_zeroReadout_ignition_positiveFixture :
    (∀ i, prospectiveEPCHiddenForce prospectiveEPCIgnitionFixture
      (zeroHiddenErrors 3, 0) i = 0) ∧
    prospectiveEPCOutputForce prospectiveEPCIgnitionFixture
      (zeroHiddenErrors 3, 0) = 1 := by
  constructor
  · intro i
    exact zeroReadout_zeroErrors_hiddenForce_eq_zero
      prospectiveEPCIgnitionFixture rfl 0 i
  · norm_num [prospectiveEPCOutputForce, prospectiveEPCPredictedOutput,
      prospectiveEPCHiddenPrediction, prospectiveEPCIgnitionFixture,
      zeroHiddenErrors]

/-- Unit depth-one fixture used for post-ignition, accepted-step, overshoot,
and update-summing tests. -/
noncomputable def prospectiveEPCUnitFixture : ProspectiveEPCModel 1 where
  target := 1
  baseHidden := 0
  readout := 1
  taskPrecision := 1
  outputPrecision := 1
  hiddenPrecision := fun _ => 1
  pathGain := fun _ => 1

/-! ## T4: the post-ignition path condition -/

/-- At an arbitrary error state, the hidden site is active exactly when its
readout-delivered mismatch drive differs from its precision-restoring force. -/
theorem hiddenForce_ne_zero_iff_drive_ne_restoring
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (i : Fin depth) :
    prospectiveEPCHiddenForce model state i ≠ 0 ↔
      model.readout * model.pathGain i *
          prospectiveEPCOutputMismatchForce model state ≠
        model.hiddenPrecision i * state.1 i := by
  exact sub_ne_zero

/-- At zero hidden errors, hidden force is exactly the live-path multiplier
times the output-mismatch force. -/
theorem hiddenForce_zeroErrors_eq_path_mul_outputMismatchForce
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (output : ℝ) (i : Fin depth) :
    prospectiveEPCHiddenForce model (zeroHiddenErrors depth, output) i =
      (model.readout * model.pathGain i) *
        prospectiveEPCOutputMismatchForce model
          (zeroHiddenErrors depth, output) := by
  simp [prospectiveEPCHiddenForce, zeroHiddenErrors]

/-- Nonzero output mismatch reaches hidden site `i` exactly when both the
readout/path coefficient and the mismatch force are nonzero. -/
theorem hiddenForce_zeroErrors_ne_zero_iff
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (output : ℝ) (i : Fin depth) :
    prospectiveEPCHiddenForce model (zeroHiddenErrors depth, output) i ≠ 0 ↔
      model.readout * model.pathGain i ≠ 0 ∧
        prospectiveEPCOutputMismatchForce model
          (zeroHiddenErrors depth, output) ≠ 0 := by
  rw [hiddenForce_zeroErrors_eq_path_mul_outputMismatchForce]
  exact mul_ne_zero_iff

/-- Fully expanded post-ignition characterization. -/
theorem hiddenForce_zeroErrors_ne_zero_iff_livePath
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (output : ℝ) (i : Fin depth) :
    prospectiveEPCHiddenForce model (zeroHiddenErrors depth, output) i ≠ 0 ↔
      model.readout ≠ 0 ∧ model.pathGain i ≠ 0 ∧
        model.outputPrecision ≠ 0 ∧
          output ≠ model.readout * model.baseHidden := by
  rw [hiddenForce_zeroErrors_ne_zero_iff]
  constructor
  · rintro ⟨hpath, hmismatch⟩
    obtain ⟨hreadout, hgain⟩ := mul_ne_zero_iff.mp hpath
    have hmismatch' :
        model.outputPrecision *
            (output - model.readout * model.baseHidden) ≠ 0 := by
      simpa [prospectiveEPCOutputMismatchForce,
        prospectiveEPCPredictedOutput, prospectiveEPCHiddenPrediction,
        zeroHiddenErrors] using hmismatch
    obtain ⟨hprecision, houtput⟩ := mul_ne_zero_iff.mp hmismatch'
    exact ⟨hreadout, hgain, hprecision, sub_ne_zero.mp houtput⟩
  · rintro ⟨hreadout, hgain, hprecision, houtput⟩
    refine ⟨mul_ne_zero hreadout hgain, ?_⟩
    have hmismatch :
        model.outputPrecision *
            (output - model.readout * model.baseHidden) ≠ 0 :=
      mul_ne_zero hprecision (sub_ne_zero.mpr houtput)
    simpa [prospectiveEPCOutputMismatchForce,
      prospectiveEPCPredictedOutput, prospectiveEPCHiddenPrediction,
      zeroHiddenErrors] using hmismatch

/-- A dead downstream path blocks hidden ignition even after the readout is
nonzero. -/
theorem zeroPathGain_blocks_hiddenForce
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (output : ℝ) (i : Fin depth) (hpath : model.pathGain i = 0) :
    prospectiveEPCHiddenForce model (zeroHiddenErrors depth, output) i = 0 := by
  simp [prospectiveEPCHiddenForce, zeroHiddenErrors, hpath]

/-- A live post-ignition readout/path with nonzero mismatch activates the
hidden coordinate. -/
theorem prospectiveEPC_livePath_hiddenIgnition_positiveFixture :
    prospectiveEPCOutputForce prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, 1) = -1 ∧
      prospectiveEPCHiddenForce prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, 1) 0 = 1 := by
  norm_num [prospectiveEPCOutputForce, prospectiveEPCHiddenForce,
    prospectiveEPCOutputMismatchForce, prospectiveEPCPredictedOutput,
    prospectiveEPCHiddenPrediction, prospectiveEPCUnitFixture,
    zeroHiddenErrors]

/-- Negative boundary: even with a live readout and path, nonzero total output
force does not by itself activate a hidden site when output mismatch is zero.
The task force acts on the explicit output first. -/
theorem prospectiveEPC_totalOutputForce_alone_not_hiddenForce :
    prospectiveEPCOutputForce prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, 0) = 1 ∧
      prospectiveEPCHiddenForce prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, 0) 0 = 0 := by
  norm_num [prospectiveEPCOutputForce, prospectiveEPCHiddenForce,
    prospectiveEPCOutputMismatchForce, prospectiveEPCPredictedOutput,
    prospectiveEPCHiddenPrediction, prospectiveEPCUnitFixture,
    zeroHiddenErrors]

/-! ## T3: a fail-closed joint refinement -/

/-- Simultaneous force step on every hidden error and the prospective output. -/
noncomputable def prospectiveEPCJointProposal {depth : ℕ}
    (model : ProspectiveEPCModel depth) (step : ℝ)
    (state : ProspectiveEPCState depth) : ProspectiveEPCState depth :=
  (fun i => state.1 i + step * prospectiveEPCHiddenForce model state i,
    state.2 + step * prospectiveEPCOutputForce model state)

/-- The exact fail-closed acceptance rule used by monotone settling: accept a
joint proposal only when it does not increase the declared joint energy. -/
noncomputable def prospectiveEPCSafeJointRefine {depth : ℕ}
    (model : ProspectiveEPCModel depth) (step : ℝ)
    (state : ProspectiveEPCState depth) : ProspectiveEPCState depth := by
  classical
  exact if prospectiveEPCJointEnergy model
      (prospectiveEPCJointProposal model step state) ≤
      prospectiveEPCJointEnergy model state then
    prospectiveEPCJointProposal model step state
  else state

/-- Every accepted-or-rejected joint refinement is energy non-increasing. -/
theorem prospectiveEPCSafeJointRefine_energy_nonincreasing
    {depth : ℕ} (model : ProspectiveEPCModel depth) (step : ℝ)
    (state : ProspectiveEPCState depth) :
    prospectiveEPCJointEnergy model
        (prospectiveEPCSafeJointRefine model step state) ≤
      prospectiveEPCJointEnergy model state := by
  classical
  unfold prospectiveEPCSafeJointRefine
  split_ifs with h
  · exact h
  · exact le_rfl

theorem prospectiveEPCUnitFixture_zeroErrors_energy (output : ℝ) :
    prospectiveEPCJointEnergy prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, output) =
      (1 / 2 : ℝ) * (output - 1) ^ 2 +
        (1 / 2 : ℝ) * output ^ 2 := by
  simp [prospectiveEPCJointEnergy, prospectiveEPCPredictedOutput,
    prospectiveEPCHiddenPrediction, prospectiveEPCUnitFixture,
    zeroHiddenErrors]

theorem prospectiveEPCUnitFixture_proposal_exact (step : ℝ) :
    prospectiveEPCJointProposal prospectiveEPCUnitFixture step
        (zeroHiddenErrors 1, 0) =
      (zeroHiddenErrors 1, step) := by
  apply Prod.ext
  · funext i
    simp [prospectiveEPCJointProposal, prospectiveEPCHiddenForce,
      prospectiveEPCOutputMismatchForce, prospectiveEPCPredictedOutput,
      prospectiveEPCHiddenPrediction, prospectiveEPCUnitFixture,
      zeroHiddenErrors]
  · simp [prospectiveEPCJointProposal, prospectiveEPCOutputForce,
      prospectiveEPCPredictedOutput, prospectiveEPCHiddenPrediction,
      prospectiveEPCUnitFixture, zeroHiddenErrors]

/-- A quarter force step is accepted and strictly lowers the joint energy. -/
theorem prospectiveEPC_quarterStep_positiveFixture :
    prospectiveEPCSafeJointRefine prospectiveEPCUnitFixture (1 / 4)
        (zeroHiddenErrors 1, 0) =
      (zeroHiddenErrors 1, 1 / 4) ∧
    prospectiveEPCJointEnergy prospectiveEPCUnitFixture
        (prospectiveEPCSafeJointRefine prospectiveEPCUnitFixture (1 / 4)
          (zeroHiddenErrors 1, 0)) <
      prospectiveEPCJointEnergy prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, 0) := by
  have hproposal := prospectiveEPCUnitFixture_proposal_exact (1 / 4)
  have haccept :
      prospectiveEPCJointEnergy prospectiveEPCUnitFixture
          (prospectiveEPCJointProposal prospectiveEPCUnitFixture (1 / 4)
            (zeroHiddenErrors 1, 0)) ≤
        prospectiveEPCJointEnergy prospectiveEPCUnitFixture
          (zeroHiddenErrors 1, 0) := by
    rw [hproposal, prospectiveEPCUnitFixture_zeroErrors_energy,
      prospectiveEPCUnitFixture_zeroErrors_energy]
    norm_num
  have hrefine :
      prospectiveEPCSafeJointRefine prospectiveEPCUnitFixture (1 / 4)
          (zeroHiddenErrors 1, 0) =
        prospectiveEPCJointProposal prospectiveEPCUnitFixture (1 / 4)
          (zeroHiddenErrors 1, 0) := by
    rw [prospectiveEPCSafeJointRefine, if_pos haccept]
  rw [hrefine, hproposal]
  refine ⟨rfl, ?_⟩
  rw [prospectiveEPCUnitFixture_zeroErrors_energy,
    prospectiveEPCUnitFixture_zeroErrors_energy]
  norm_num

/-- A step of size two overshoots; the fail-closed rule rejects it and keeps
the seed exactly. -/
theorem prospectiveEPC_overshoot_rejected_negativeFixture :
    prospectiveEPCSafeJointRefine prospectiveEPCUnitFixture 2
        (zeroHiddenErrors 1, 0) =
      (zeroHiddenErrors 1, 0) ∧
    prospectiveEPCJointEnergy prospectiveEPCUnitFixture
        (prospectiveEPCSafeJointRefine prospectiveEPCUnitFixture 2
          (zeroHiddenErrors 1, 0)) =
      prospectiveEPCJointEnergy prospectiveEPCUnitFixture
        (zeroHiddenErrors 1, 0) := by
  have hproposal := prospectiveEPCUnitFixture_proposal_exact 2
  have hrejected :
      ¬ prospectiveEPCJointEnergy prospectiveEPCUnitFixture
          (prospectiveEPCJointProposal prospectiveEPCUnitFixture 2
            (zeroHiddenErrors 1, 0)) ≤
        prospectiveEPCJointEnergy prospectiveEPCUnitFixture
          (zeroHiddenErrors 1, 0) := by
    rw [hproposal, prospectiveEPCUnitFixture_zeroErrors_energy,
      prospectiveEPCUnitFixture_zeroErrors_energy]
    norm_num
  have hrefine :
      prospectiveEPCSafeJointRefine prospectiveEPCUnitFixture 2
          (zeroHiddenErrors 1, 0) = (zeroHiddenErrors 1, 0) := by
    rw [prospectiveEPCSafeJointRefine, if_neg hrejected]
  rw [hrefine]
  exact ⟨rfl, rfl⟩

/-! ## T5: independently safe updates need not be safe when summed -/

/-- Replace the frozen readout by one candidate trainable parameter. -/
def prospectiveEPCWithReadout {depth : ℕ}
    (model : ProspectiveEPCModel depth) (readout : ℝ) :
    ProspectiveEPCModel depth :=
  { model with readout := readout }

@[simp] theorem prospectiveEPCHiddenPrediction_withReadout
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (readout : ℝ) (error : Fin depth → ℝ) :
    prospectiveEPCHiddenPrediction
        (prospectiveEPCWithReadout model readout) error =
      prospectiveEPCHiddenPrediction model error := by
  rfl

/-- The same joint energy, now viewed as a function of the readout parameter
after prospective state inference. -/
noncomputable def prospectiveEPCReadoutParameterEnergy {depth : ℕ}
    (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (readout : ℝ) : ℝ :=
  prospectiveEPCJointEnergy (prospectiveEPCWithReadout model readout) state

/-- Local negative gradient for the readout parameter.  Prospective output
fitting and ePC's final local plasticity both compute this same endpoint
signal, so adding them as if independent double-counts it. -/
noncomputable def prospectiveEPCReadoutParameterForce {depth : ℕ}
    (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (readout : ℝ) : ℝ :=
  model.outputPrecision * prospectiveEPCHiddenPrediction model state.1 *
    (state.2 - readout * prospectiveEPCHiddenPrediction model state.1)

/-- Exact readout-parameter energy increment, certifying the local parameter
force rather than merely assigning it that name. -/
theorem prospectiveEPCReadoutParameterEnergy_increment_exact
    {depth : ℕ} (model : ProspectiveEPCModel depth)
    (state : ProspectiveEPCState depth) (readout increment : ℝ) :
    prospectiveEPCReadoutParameterEnergy model state (readout + increment) -
        prospectiveEPCReadoutParameterEnergy model state readout =
      -increment *
          prospectiveEPCReadoutParameterForce model state readout +
        (1 / 2 : ℝ) * model.outputPrecision *
          (prospectiveEPCHiddenPrediction model state.1) ^ 2 * increment ^ 2 := by
  simp [prospectiveEPCReadoutParameterEnergy, prospectiveEPCWithReadout,
    prospectiveEPCJointEnergy, prospectiveEPCPredictedOutput,
    prospectiveEPCReadoutParameterForce, prospectiveEPCHiddenPrediction]
  ring

/-- Parameter-level fixture with a unit inferred hidden state and unit
prospective output. -/
noncomputable def prospectiveEPCParameterFixture : ProspectiveEPCModel 1 where
  target := 1
  baseHidden := 1
  readout := 0
  taskPrecision := 1
  outputPrecision := 1
  hiddenPrecision := fun _ => 1
  pathGain := fun _ => 1

theorem prospectiveEPCParameterFixture_energy (readout : ℝ) :
    prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture
        (zeroHiddenErrors 1, 1) readout =
      (1 / 2 : ℝ) * (1 - readout) ^ 2 := by
  simp [prospectiveEPCReadoutParameterEnergy, prospectiveEPCWithReadout,
    prospectiveEPCJointEnergy, prospectiveEPCPredictedOutput,
    prospectiveEPCHiddenPrediction, prospectiveEPCParameterFixture,
    zeroHiddenErrors]

/-- The prospective and ePC local readout updates are each safe at rate
`3/2`; adding both displacements produces effective rate three and strictly
increases the very joint energy each update separately decreases. -/
theorem summedProspectiveAndEPCUpdates_can_increase_jointEnergy :
    let state : ProspectiveEPCState 1 := (zeroHiddenErrors 1, 1)
    let seedReadout : ℝ := 0
    let localForce := prospectiveEPCReadoutParameterForce
      prospectiveEPCParameterFixture state seedReadout
    let prospectiveDelta := (3 / 2 : ℝ) * localForce
    let errorCoordinateDelta := (3 / 2 : ℝ) * localForce
    prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture state
        (seedReadout + prospectiveDelta) <
      prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture state
        seedReadout ∧
    prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture state
        (seedReadout + errorCoordinateDelta) <
      prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture state
        seedReadout ∧
    prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture state
        (seedReadout + prospectiveDelta + errorCoordinateDelta) >
      prospectiveEPCReadoutParameterEnergy prospectiveEPCParameterFixture state
        seedReadout := by
  dsimp
  simp only [prospectiveEPCParameterFixture_energy]
  simp [prospectiveEPCReadoutParameterForce,
    prospectiveEPCHiddenPrediction, prospectiveEPCParameterFixture,
    zeroHiddenErrors]
  norm_num

#print axioms prospectiveEPCJointEnergy_zeroErrors_eq_outputObjective
#print axioms prospectiveEPCJointEnergy_hardOutputConstraint_eq_deepObjective
#print axioms prospectiveEPCJointEnergy_outputIncrement_exact
#print axioms prospectiveEPCJointEnergy_hiddenIncrement_exact
#print axioms prospectiveEPCReadoutParameterEnergy_increment_exact
#print axioms prospectiveEPC_zeroReadout_ignition_positiveFixture
#print axioms prospectiveEPCSafeJointRefine_energy_nonincreasing
#print axioms hiddenForce_zeroErrors_ne_zero_iff_livePath
#print axioms summedProspectiveAndEPCUpdates_can_increase_jointEnergy

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier
