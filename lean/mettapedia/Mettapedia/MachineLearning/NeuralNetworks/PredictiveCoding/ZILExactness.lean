import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.SharedLatentDAG

/-!
# Scheduled Z-IL exactness on scalar chains

This file formalizes the schedule-dependent exactness boundary of Song et al.
(2020).  Chain indices are distances from the output: link `0` predicts the
clamped output from node `1`, and link `i` predicts node `i` from node `i + 1`.
The trace starts at the forward pass, clamps node `0` to the target, and applies
synchronous latent-gradient steps with integration step exactly one.

The core induction proves two separate facts.  A source node is still at its
forward activation when its link is updated at time `t = i`, and the residual
first reaching that link is exactly the corresponding backpropagated error.
Consequently the scheduled local gain gradient equals the ordinary backprop
gain gradient.  No equality is claimed at free equilibrium or for an
unlevelled residual graph.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Unit-step inference trace -/

/-- Output-first chain residual: prediction minus current node value. -/
noncomputable def zilChainResidual (links : ℕ → PCLink)
    (z : ℕ → ℝ) (i : ℕ) : ℝ :=
  (links i).gain * z (i + 1) - z i

/-- One synchronous Z-IL inference step.  Node `0` is the clamped target and
node `depth` is the clamped input.  The coefficient one is Song's integration
condition C3. -/
noncomputable def zilChainStep (depth : ℕ) (links : ℕ → PCLink)
    (z : ℕ → ℝ) : ℕ → ℝ :=
  fun n =>
    if n = 0 then z n
    else if depth ≤ n then z n
    else
      z n + zilChainResidual links z n -
        (links (n - 1)).gain * zilChainResidual links z (n - 1)

/-- Inference-time trace initialized at the forward state, except for the
clamped target at output node `0`. -/
noncomputable def zilChainTrace (depth : ℕ) (links : ℕ → PCLink)
    (forward : ℕ → ℝ) (target : ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then target else forward n
  | t + 1, n => zilChainStep depth links (zilChainTrace depth links forward target t) n

/-- The supplied initial state is a genuine forward pass through every link. -/
def zilForwardConsistent (depth : ℕ) (links : ℕ → PCLink)
    (forward : ℕ → ℝ) : Prop :=
  ∀ i, i < depth → (links i).gain * forward (i + 1) = forward i

/-- Before the error frontier reaches a node, synchronous unit-step inference
leaves that node at its forward activation. -/
theorem zilChainTrace_eq_forward_before_arrival
    (depth : ℕ) (links : ℕ → PCLink) (forward : ℕ → ℝ) (target : ℝ)
    (hforward : zilForwardConsistent depth links forward) :
    ∀ t n, t < n → n ≤ depth →
      zilChainTrace depth links forward target t n = forward n := by
  intro t
  induction t with
  | zero =>
      intro n htn _hdepth
      simp [zilChainTrace, Nat.ne_of_gt htn]
  | succ t ih =>
      intro n htn hdepth
      rw [zilChainTrace]
      unfold zilChainStep
      have hn0 : n ≠ 0 := by omega
      simp only [hn0, ↓reduceIte]
      by_cases hnd : depth ≤ n
      · simp [hnd]
        exact ih n (by omega) hdepth
      · simp only [hnd, ↓reduceIte]
        have hnlt : n < depth := by omega
        have hzn : zilChainTrace depth links forward target t n = forward n :=
          ih n (by omega) hdepth
        have hzsucc :
            zilChainTrace depth links forward target t (n + 1) = forward (n + 1) :=
          ih (n + 1) (by omega) (by omega)
        have hnprev : t < n - 1 := by omega
        have hzprev :
            zilChainTrace depth links forward target t (n - 1) = forward (n - 1) :=
          ih (n - 1) hnprev (by omega)
        have hprevSucc : n - 1 + 1 = n := by omega
        have hown : zilChainResidual links
            (zilChainTrace depth links forward target t) n = 0 := by
          unfold zilChainResidual
          rw [hzn, hzsucc, hforward n hnlt]
          ring
        have hforwardPrev := hforward (n - 1) (by omega)
        rw [hprevSucc] at hforwardPrev
        have hprev : zilChainResidual links
            (zilChainTrace depth links forward target t) (n - 1) = 0 := by
          unfold zilChainResidual
          rw [hzprev, hprevSucc, hzn, hforwardPrev]
          ring
        rw [hzn, hown, hprev]
        ring

/-- At the first arrival time, one inference step transports exactly the prior
frontier residual through the intervening gain. -/
theorem zilChainResidual_first_arrival_succ
    (depth : ℕ) (links : ℕ → PCLink) (forward : ℕ → ℝ) (target : ℝ)
    (hforward : zilForwardConsistent depth links forward)
    (k : ℕ) (hk : k + 1 < depth) :
    zilChainResidual links (zilChainTrace depth links forward target (k + 1)) (k + 1) =
      (links k).gain *
        zilChainResidual links (zilChainTrace depth links forward target k) k := by
  have hsource :
      zilChainTrace depth links forward target (k + 1) (k + 2) =
        forward (k + 2) :=
    zilChainTrace_eq_forward_before_arrival depth links forward target hforward
      (k + 1) (k + 2) (by omega) (by omega)
  have hnodeBefore :
      zilChainTrace depth links forward target k (k + 1) = forward (k + 1) :=
    zilChainTrace_eq_forward_before_arrival depth links forward target hforward
      k (k + 1) (by omega) (by omega)
  have hsourceBefore :
      zilChainTrace depth links forward target k (k + 2) = forward (k + 2) :=
    zilChainTrace_eq_forward_before_arrival depth links forward target hforward
      k (k + 2) (by omega) (by omega)
  have hownzero :
      zilChainResidual links (zilChainTrace depth links forward target k) (k + 1) = 0 := by
    unfold zilChainResidual
    rw [hnodeBefore, hsourceBefore, hforward (k + 1) hk]
    ring
  have hnodeStep :
      zilChainTrace depth links forward target (k + 1) (k + 1) =
        zilChainTrace depth links forward target k (k + 1) +
          zilChainResidual links (zilChainTrace depth links forward target k) (k + 1) -
          (links k).gain *
            zilChainResidual links (zilChainTrace depth links forward target k) k := by
    rw [zilChainTrace]
    simp [zilChainStep, show ¬depth ≤ k + 1 by omega]
  unfold zilChainResidual
  rw [hsource, hnodeStep, hnodeBefore, hownzero, hforward (k + 1) hk]
  unfold zilChainResidual
  rw [hnodeBefore]
  ring

/-! ## Exact scheduled gain gradient -/

/-- Output residual produced by the forward pass against the clamped target. -/
noncomputable def zilOutputResidual (links : ℕ → PCLink)
    (forward : ℕ → ℝ) (target : ℝ) : ℝ :=
  (links 0).gain * forward 1 - target

/-- Ordinary scalar backprop error, recursively transported away from the
output through the chain gains. -/
noncomputable def scalarChainBackpropError (links : ℕ → PCLink)
    (outputResidual : ℝ) : ℕ → ℝ
  | 0 => outputResidual
  | k + 1 => (links k).gain * scalarChainBackpropError links outputResidual k

/-- At Song's scheduled time `t = i`, the local prediction error is exactly
the ordinary backprop error at link `i`. -/
theorem zilChainResidual_at_schedule_eq_backpropError
    (depth : ℕ) (links : ℕ → PCLink) (forward : ℕ → ℝ) (target : ℝ)
    (hforward : zilForwardConsistent depth links forward) :
    ∀ i, i < depth →
      zilChainResidual links (zilChainTrace depth links forward target i) i =
        scalarChainBackpropError links (zilOutputResidual links forward target) i := by
  intro i hi
  induction i with
  | zero =>
      simp [zilChainResidual, zilChainTrace, scalarChainBackpropError, zilOutputResidual]
  | succ i ih =>
      rw [zilChainResidual_first_arrival_succ depth links forward target hforward i hi]
      rw [ih (by omega)]
      rfl

/-- The local gain gradient read by Z-IL at the layer-dependent update time. -/
noncomputable def zilScheduledGainGradient
    (depth : ℕ) (links : ℕ → PCLink) (forward : ℕ → ℝ)
    (target : ℝ) (i : ℕ) : ℝ :=
  zilChainResidual links (zilChainTrace depth links forward target i) i *
    zilChainTrace depth links forward target i (i + 1)

/-- The ordinary backprop gradient of the half-squared output loss with
respect to one scalar gain. -/
noncomputable def scalarChainBackpropGainGradient
    (links : ℕ → PCLink) (forward : ℕ → ℝ)
    (outputResidual : ℝ) (i : ℕ) : ℝ :=
  scalarChainBackpropError links outputResidual i * forward (i + 1)

/-- Under forward initialization and unit-step inference, updating
link `i` at time `t = i` gives exactly its ordinary backprop gain gradient.
Both the scheduled error and the still-forward source activation are used. -/
theorem zilScheduledGainGradient_eq_backpropGradient
    (depth : ℕ) (links : ℕ → PCLink) (forward : ℕ → ℝ) (target : ℝ)
    (hforward : zilForwardConsistent depth links forward)
    (i : ℕ) (hi : i < depth) :
    zilScheduledGainGradient depth links forward target i =
      scalarChainBackpropGainGradient links forward
        (zilOutputResidual links forward target) i := by
  unfold zilScheduledGainGradient scalarChainBackpropGainGradient
  rw [zilChainResidual_at_schedule_eq_backpropError depth links forward target hforward i hi]
  rw [zilChainTrace_eq_forward_before_arrival depth links forward target hforward
    i (i + 1) (by omega) (by omega)]

/-! ## Positive and failure fixtures -/

noncomputable def zilUnitLinks : ℕ → PCLink :=
  fun _ => { gain := 1, precision := 1, precision_pos := by norm_num }

noncomputable def zilUnitForward : ℕ → ℝ := fun _ => 1

theorem zilUnitForward_consistent (depth : ℕ) :
    zilForwardConsistent depth zilUnitLinks zilUnitForward := by
  intro i hi
  norm_num [zilUnitLinks, zilUnitForward]

theorem zilDepth3_deepestScheduledGradient_positive_example :
    zilScheduledGainGradient 3 zilUnitLinks zilUnitForward 2 2 =
      scalarChainBackpropGainGradient zilUnitLinks zilUnitForward
        (zilOutputResidual zilUnitLinks zilUnitForward 2) 2 := by
  exact zilScheduledGainGradient_eq_backpropGradient
    3 zilUnitLinks zilUnitForward 2 (zilUnitForward_consistent 3) 2 (by omega)

theorem zilDepth3_deepestBackpropGradient_value :
    scalarChainBackpropGainGradient zilUnitLinks zilUnitForward
      (zilOutputResidual zilUnitLinks zilUnitForward 2) 2 = -1 := by
  norm_num [scalarChainBackpropGainGradient, scalarChainBackpropError,
    zilOutputResidual, zilUnitLinks, zilUnitForward]

/-- Off-schedule boundary: the already-sealed free-equilibrium fixture does
not have the forward source activation required by the Z-IL theorem, and its
gain gradient differs from forward backpropagation. -/
theorem zilOffSchedule_freeEquilibriumGradient_failure :
    pcGainPartial unitDepth2Links depth2EquilibriumState 0 ≠
      scalarSquaredErrorBackpropPartial 1 1 1 :=
  equilibriumGradient_ne_backpropGradient_example

/-! The next fixture records the unequal error-arrival times in Salvatori et
al. (2022), Eq. (10): a parameter contributes to both a one-edge skip path and
a three-edge main path.  The original minimum-distance schedule reads the
parameter when only the skip contribution has arrived. -/

noncomputable def residualSkipBackpropGainGradient
    (outputResidual sourceActivation longPathGain : ℝ) : ℝ :=
  outputResidual * sourceActivation * (1 + longPathGain)

noncomputable def residualSkipNaiveScheduledGainGradient
    (time : ℕ) (outputResidual sourceActivation longPathGain : ℝ) : ℝ :=
  outputResidual * sourceActivation *
    ((if 1 ≤ time then 1 else 0) + if 3 ≤ time then longPathGain else 0)

/-- Residual-graph boundary: at the first-arrival update time, the long-path
contribution is absent, so the naive unlevelled schedule is not exact. -/
theorem residualSkip_naiveFirstArrivalGradient_failure_example :
    residualSkipNaiveScheduledGainGradient 1 1 1 1 ≠
      residualSkipBackpropGainGradient 1 1 1 := by
  norm_num [residualSkipNaiveScheduledGainGradient, residualSkipBackpropGainGradient]

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
