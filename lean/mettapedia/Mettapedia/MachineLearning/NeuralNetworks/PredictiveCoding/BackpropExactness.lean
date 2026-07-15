import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.LinearGaussianChain

/-!
# Predictive-coding backprop exactness

This file extends the scalar linear-Gaussian predictive-coding theory with the
exact free-equilibrium error-signal recursion. The exact object is the
precision-weighted residual force; ordinary gradient equality with forward
backprop is not claimed at free equilibrium.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## L1: equilibrium error-force recursion -/

/-- Precision-weighted residual force, the scalar Gaussian backprop-error analog. -/
noncomputable def pcResidualForce {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) (i : Fin depth) : ℝ :=
  (links i).precision * pcResidual links z i

/-- The gain partial for the existing `pcEnergy = ∑ λ r²` convention. -/
noncomputable def pcGainPartial {depth : ℕ} (links : Fin depth → PCLink)
    (z : PCState depth) (i : Fin depth) : ℝ :=
  -2 * pcResidualForce links z i * z i.castSucc

/-- L1 crown: at a clamped equilibrium, precision-weighted residual forces obey
exactly the scalar backprop one-step recursion. -/
theorem equilibriumError_satisfies_backpropRecursion {depth : ℕ}
    (links : Fin depth → PCLink) (x y : ℝ) (z : PCState depth)
    (i : Fin depth) (hi : i.val + 1 < depth)
    (heq : pcEquilibrium links x y z) :
    pcResidualForce links z i =
      (links ⟨i.val + 1, hi⟩).gain * pcResidualForce links z ⟨i.val + 1, hi⟩ := by
  have hnorm : pcNormalEquations links z :=
    (pcEquilibrium_iff_normalEquations links x y z).mp heq |>.2
  have h := hnorm (⟨i.val + 1, by omega⟩ : Fin (depth + 1))
  unfold pcLocalNormalEquationAt at h
  have hlast : ¬ (i.val + 1 = depth) := by omega
  simp [hlast, pcResidualForce] at h ⊢
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Raw residuals satisfy the same recursion when adjacent precisions are equal. -/
theorem equilibriumRawResidual_satisfies_backpropRecursion_of_equalPrecision {depth : ℕ}
    (links : Fin depth → PCLink) (x y : ℝ) (z : PCState depth)
    (i : Fin depth) (hi : i.val + 1 < depth)
    (hprecision : (links i).precision = (links ⟨i.val + 1, hi⟩).precision)
    (heq : pcEquilibrium links x y z) :
    pcResidual links z i =
      (links ⟨i.val + 1, hi⟩).gain * pcResidual links z ⟨i.val + 1, hi⟩ := by
  have hforce := equilibriumError_satisfies_backpropRecursion links x y z i hi heq
  unfold pcResidualForce at hforce
  rw [hprecision] at hforce
  have hpos : 0 < (links ⟨i.val + 1, hi⟩).precision :=
    (links ⟨i.val + 1, hi⟩).precision_pos
  nlinarith

noncomputable def unitDepth2Links : Fin 2 → PCLink :=
  fun _ => { gain := 1, precision := 1, precision_pos := by norm_num }

noncomputable def depth2EquilibriumState : PCState 2 :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then (3 / 2 : ℝ) else 2

noncomputable def depth2ForwardState : PCState 2 :=
  fun _ => 1

theorem depth2EquilibriumState_is_equilibrium :
    pcEquilibrium unitDepth2Links 1 2 depth2EquilibriumState := by
  rw [pcEquilibrium_iff_normalEquations]
  constructor
  · constructor <;> norm_num [clampedStateSet, depth2EquilibriumState]
  · intro i
    fin_cases i <;> simp [pcLocalNormalEquationAt, unitDepth2Links, depth2EquilibriumState,
      pcResidual]
    norm_num

theorem equilibriumError_depth2_positive_example :
    pcResidualForce unitDepth2Links depth2EquilibriumState 0 =
      (unitDepth2Links 1).gain * pcResidualForce unitDepth2Links depth2EquilibriumState 1 := by
  exact equilibriumError_satisfies_backpropRecursion unitDepth2Links 1 2
    depth2EquilibriumState 0 (by norm_num) depth2EquilibriumState_is_equilibrium

theorem equilibriumRawResidual_depth2_equalPrecision_example :
    pcResidual unitDepth2Links depth2EquilibriumState 0 =
      (unitDepth2Links 1).gain * pcResidual unitDepth2Links depth2EquilibriumState 1 := by
  exact equilibriumRawResidual_satisfies_backpropRecursion_of_equalPrecision unitDepth2Links 1 2
    depth2EquilibriumState 0 (by norm_num) (by norm_num [unitDepth2Links])
    depth2EquilibriumState_is_equilibrium

theorem equilibrium_state_ne_forward_state_example :
    depth2EquilibriumState 1 ≠ depth2ForwardState 1 := by
  norm_num [depth2EquilibriumState, depth2ForwardState]

/-- Closed-form squared-error backprop partial for one scalar gain. -/
noncomputable def scalarSquaredErrorBackpropPartial
    (outputResidual downstreamGain sourceActivation : ℝ) : ℝ :=
  -2 * outputResidual * downstreamGain * sourceActivation

/-- Honesty crown: with `pcEnergy = ∑ λ r²`, the free-equilibrium PC partial
uses the relaxed source latent and differs from the forward-pass backprop
partial on this linear fixture. -/
theorem equilibriumGradient_ne_backpropGradient_example :
    pcGainPartial unitDepth2Links depth2EquilibriumState 0 ≠
      scalarSquaredErrorBackpropPartial 1 1 1 := by
  norm_num [pcGainPartial, pcResidualForce, pcResidual, unitDepth2Links,
    depth2EquilibriumState, scalarSquaredErrorBackpropPartial]

/-! ## L2: tied gain recursion -/

/-- A scalar chain whose links share one gain but keep per-position precisions. -/
structure TiedPCChain (depth : ℕ) where
  gain : ℝ
  precision : Fin depth → ℝ
  precision_pos : ∀ i, 0 < precision i

/-- Untie a shared-gain chain into the existing `PCLink` interface. -/
noncomputable def TiedPCChain.links {depth : ℕ} (chain : TiedPCChain depth) :
    Fin depth → PCLink :=
  fun i =>
    { gain := chain.gain
      precision := chain.precision i
      precision_pos := chain.precision_pos i }

/-- L2 crown: weight tying preserves the equilibrium error recursion. -/
theorem tiedEquilibriumError_satisfies_bpttRecursion {depth : ℕ}
    (chain : TiedPCChain depth) (x y : ℝ) (z : PCState depth)
    (i : Fin depth) (hi : i.val + 1 < depth)
    (heq : pcEquilibrium chain.links x y z) :
    pcResidualForce chain.links z i =
      chain.gain * pcResidualForce chain.links z ⟨i.val + 1, hi⟩ := by
  simpa [TiedPCChain.links] using
    equilibriumError_satisfies_backpropRecursion chain.links x y z i hi heq

/-- Shared-weight sum structure matching BPTT's shape.  This is not the exact
BPTT gradient at free equilibrium; exact gradient identity needs a separate
schedule where the source latent equals the forward activation. -/
noncomputable def tiedEquilibriumCreditSignal {depth : ℕ}
    (chain : TiedPCChain depth) (z : PCState depth) : ℝ :=
  ∑ i : Fin depth, pcResidualForce chain.links z i * z i.castSucc

noncomputable def tiedDepth3UnitChain : TiedPCChain 3 where
  gain := 1
  precision := fun _ => 1
  precision_pos := by
    intro _i
    norm_num

noncomputable def tiedDepth3EquilibriumState : PCState 3 :=
  fun i => (i.val : ℝ) + 1

theorem tiedDepth3EquilibriumState_is_equilibrium :
    pcEquilibrium tiedDepth3UnitChain.links 1 4 tiedDepth3EquilibriumState := by
  rw [pcEquilibrium_iff_normalEquations]
  constructor
  · constructor <;> norm_num [clampedStateSet, tiedDepth3EquilibriumState]
  · intro i
    fin_cases i <;> norm_num [pcLocalNormalEquationAt, TiedPCChain.links, tiedDepth3UnitChain,
      tiedDepth3EquilibriumState, pcResidual]

theorem tiedEquilibriumError_depth3_first_step_positive_example :
    pcResidualForce tiedDepth3UnitChain.links tiedDepth3EquilibriumState 0 =
      tiedDepth3UnitChain.gain *
        pcResidualForce tiedDepth3UnitChain.links tiedDepth3EquilibriumState 1 := by
  exact tiedEquilibriumError_satisfies_bpttRecursion tiedDepth3UnitChain 1 4
    tiedDepth3EquilibriumState 0 (by norm_num) tiedDepth3EquilibriumState_is_equilibrium

theorem tiedEquilibriumError_depth3_second_step_positive_example :
    pcResidualForce tiedDepth3UnitChain.links tiedDepth3EquilibriumState 1 =
      tiedDepth3UnitChain.gain *
        pcResidualForce tiedDepth3UnitChain.links tiedDepth3EquilibriumState 2 := by
  exact tiedEquilibriumError_satisfies_bpttRecursion tiedDepth3UnitChain 1 4
    tiedDepth3EquilibriumState 1 (by norm_num) tiedDepth3EquilibriumState_is_equilibrium

theorem tiedEquilibriumCreditSignal_depth3_positive_example :
    tiedEquilibriumCreditSignal tiedDepth3UnitChain tiedDepth3EquilibriumState = 6 := by
  unfold tiedEquilibriumCreditSignal
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [pcResidualForce, pcResidual, TiedPCChain.links, tiedDepth3UnitChain,
    tiedDepth3EquilibriumState]
  norm_num

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
