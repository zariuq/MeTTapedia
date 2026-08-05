import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Sequences
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SafeguardedCompositeBlock

/-!
# Safeguarded acceleration as a quasi-Fejer trace

An accelerated fixed-point proposal need not itself be contractive.  The
global convergence argument for stabilized type-I Anderson acceleration
instead combines two kinds of step:

* a fallback step pays a nonnegative decrease in squared distance;
* an accepted accelerated step may increase squared distance, but only by a
  term from a summable error schedule.

This file isolates that argument from the matrix formula used to construct
the accelerated proposal.  A `SafeguardedTrace` records the squared-distance
potential, accepted-step error, and fallback decrease.  Its one-step budget
telescopes at every finite horizon.  Summable accepted error then implies
summable fallback decrease and convergence of the squared-distance
potential.  If accepted residuals also have a summable square budget, the
whole residual converges to zero.

The compact-limit theorem is stated for an arbitrary metric space with a
sequentially compact invariant set.  It strengthens the Euclidean final step:
residual convergence, continuity, and convergence of squared distance to
every fixed point force the full state sequence to converge to a fixed
point.

The source safeguard uses decay `(i + 1)^(-(1 + epsilon))`.  We prove its
summability for positive `epsilon`, and the sharp failure at `epsilon = 0`.
These theorems certify convergence only; they deliberately make no claim
that accepted acceleration improves the baseline rate.

Source correspondence: Zhang, O'Donoghue, and Boyd, *Globally Convergent
Type-I Anderson Acceleration for Non-Smooth Fixed-Point Iterations*,
arXiv:1808.03971, Algorithm 3, equations (16)--(22), and Theorem 6.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SafeguardedAndersonConvergence

open Filter Finset
open scoped NNReal Topology

noncomputable section

/-! ## Abstract finite and infinite budgets -/

/-- A quasi-Fejer trace with an explicit fallback decrease and accepted-step
error.  The step inequality is subtraction-free, so it remains meaningful
for exact nonnegative runtime certificates. -/
structure SafeguardedTrace where
  distanceSq : ℕ → ℝ≥0
  acceptedError : ℕ → ℝ≥0
  fallbackDecrease : ℕ → ℝ≥0
  stepBudget : ∀ step,
    distanceSq (step + 1) + fallbackDecrease step ≤
      distanceSq step + acceptedError step

/-- The one-step safeguard telescopes without any asymptotic assumption. -/
theorem SafeguardedTrace.finite_budget
    (trace : SafeguardedTrace) (horizon : ℕ) :
    trace.distanceSq horizon +
        ∑ step ∈ range horizon, trace.fallbackDecrease step ≤
      trace.distanceSq 0 +
        ∑ step ∈ range horizon, trace.acceptedError step := by
  induction horizon with
  | zero => simp
  | succ horizon inductionHypothesis =>
      rw [sum_range_succ, sum_range_succ]
      calc
        trace.distanceSq (horizon + 1) +
              ((∑ step ∈ range horizon, trace.fallbackDecrease step) +
                trace.fallbackDecrease horizon) =
            (trace.distanceSq (horizon + 1) +
                trace.fallbackDecrease horizon) +
              ∑ step ∈ range horizon, trace.fallbackDecrease step := by
                ac_rfl
        _ ≤ (trace.distanceSq horizon + trace.acceptedError horizon) +
              ∑ step ∈ range horizon, trace.fallbackDecrease step :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (trace.stepBudget horizon)
                  (∑ step ∈ range horizon,
                    trace.fallbackDecrease step)
        _ = (trace.distanceSq horizon +
              ∑ step ∈ range horizon, trace.fallbackDecrease step) +
                trace.acceptedError horizon := by
              ac_rfl
        _ ≤ (trace.distanceSq 0 +
              ∑ step ∈ range horizon, trace.acceptedError step) +
                trace.acceptedError horizon :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right inductionHypothesis
                  (trace.acceptedError horizon)
        _ = trace.distanceSq 0 +
              ((∑ step ∈ range horizon, trace.acceptedError step) +
                trace.acceptedError horizon) := by
              ac_rfl

/-- A summable accepted-error budget bounds every certified distance. -/
theorem SafeguardedTrace.distanceSq_le
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError)
    (horizon : ℕ) :
    trace.distanceSq horizon ≤
      trace.distanceSq 0 + ∑' step, trace.acceptedError step := by
  calc
    trace.distanceSq horizon ≤
        trace.distanceSq horizon +
          ∑ step ∈ range horizon, trace.fallbackDecrease step :=
      le_add_right le_rfl
    _ ≤ trace.distanceSq 0 +
          ∑ step ∈ range horizon, trace.acceptedError step :=
      trace.finite_budget horizon
    _ ≤ trace.distanceSq 0 + ∑' step, trace.acceptedError step :=
      by
        simpa [add_comm] using
          add_le_add_left
            (acceptedSummable.sum_le_tsum (range horizon)
              (fun _ _ => zero_le)) (trace.distanceSq 0)

/-- Summable accelerated-step error forces the total fallback decrease to be
summable as well. -/
theorem SafeguardedTrace.fallbackDecrease_summable
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError) :
    Summable trace.fallbackDecrease := by
  apply NNReal.summable_of_sum_range_le
  intro horizon
  calc
    ∑ step ∈ range horizon, trace.fallbackDecrease step ≤
        trace.distanceSq horizon +
          ∑ step ∈ range horizon, trace.fallbackDecrease step :=
      le_add_left le_rfl
    _ ≤ trace.distanceSq 0 +
          ∑ step ∈ range horizon, trace.acceptedError step :=
      trace.finite_budget horizon
    _ ≤ trace.distanceSq 0 + ∑' step, trace.acceptedError step :=
      by
        simpa [add_comm] using
          add_le_add_left
            (acceptedSummable.sum_le_tsum (range horizon)
              (fun _ _ => zero_le)) (trace.distanceSq 0)

/-- Consequently, the fallback decrease paid at a single step vanishes. -/
theorem SafeguardedTrace.fallbackDecrease_tendsto_zero
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError) :
    Tendsto trace.fallbackDecrease atTop (𝓝 0) :=
  NNReal.tendsto_atTop_zero_of_summable
    (trace.fallbackDecrease_summable acceptedSummable)

/-- Tail of the accepted-error series from a declared step. -/
def acceptedErrorTail (trace : SafeguardedTrace) (step : ℕ) : ℝ≥0 :=
  ∑' offset, trace.acceptedError (offset + step)

/-- Correcting squared distance by the remaining accepted-error budget makes
the sequence genuinely antitone. -/
def correctedDistance (trace : SafeguardedTrace) (step : ℕ) : ℝ≥0 :=
  trace.distanceSq step + acceptedErrorTail trace step

theorem acceptedErrorTail_eq
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError)
    (step : ℕ) :
    acceptedErrorTail trace step =
      trace.acceptedError step + acceptedErrorTail trace (step + 1) := by
  have shiftedSummable :
      Summable (fun offset => trace.acceptedError (offset + step)) :=
    NNReal.summable_nat_add trace.acceptedError acceptedSummable step
  have split :=
    NNReal.sum_add_tsum_nat_add 1 shiftedSummable
  simpa only [acceptedErrorTail, sum_range_one, zero_add, Nat.zero_add,
    Nat.add_zero, Nat.add_assoc, Nat.one_add, Nat.add_comm,
    Nat.add_left_comm] using split

theorem correctedDistance_succ_le
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError)
    (step : ℕ) :
    correctedDistance trace (step + 1) ≤ correctedDistance trace step := by
  have distanceStep :
      trace.distanceSq (step + 1) ≤
        trace.distanceSq step + trace.acceptedError step := by
    calc
      trace.distanceSq (step + 1) ≤
          trace.distanceSq (step + 1) + trace.fallbackDecrease step :=
        le_add_right le_rfl
      _ ≤ trace.distanceSq step + trace.acceptedError step :=
        trace.stepBudget step
  rw [correctedDistance, correctedDistance,
    acceptedErrorTail_eq trace acceptedSummable step]
  calc
    trace.distanceSq (step + 1) +
          acceptedErrorTail trace (step + 1) ≤
        (trace.distanceSq step + trace.acceptedError step) +
          acceptedErrorTail trace (step + 1) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right distanceStep
            (acceptedErrorTail trace (step + 1))
    _ = trace.distanceSq step +
          (trace.acceptedError step +
            acceptedErrorTail trace (step + 1)) := by
      ac_rfl

theorem correctedDistance_antitone
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError) :
    Antitone (correctedDistance trace) :=
  antitone_nat_of_succ_le
    (correctedDistance_succ_le trace acceptedSummable)

/-- This is the quasi-Fejer convergence step: squared distance has a finite
limit whenever the allowed increases are summable. -/
theorem SafeguardedTrace.distanceSq_converges
    (trace : SafeguardedTrace)
    (acceptedSummable : Summable trace.acceptedError) :
    ∃ limit : ℝ≥0, Tendsto trace.distanceSq atTop (𝓝 limit) := by
  let limit := ⨅ step, correctedDistance trace step
  have correctedTendsto :
      Tendsto (correctedDistance trace) atTop (𝓝 limit) :=
    tendsto_atTop_ciInf
      (correctedDistance_antitone trace acceptedSummable) (by simp)
  have tailTendsto :
      Tendsto (acceptedErrorTail trace) atTop (𝓝 0) := by
    change Tendsto
      (fun step => ∑' offset, trace.acceptedError (offset + step))
      atTop (𝓝 0)
    exact NNReal.tendsto_sum_nat_add trace.acceptedError
  refine ⟨limit, ?_⟩
  have differenceTendsto :=
    correctedTendsto.sub tailTendsto
  simpa only [correctedDistance, add_tsub_cancel_right, tsub_zero] using
    differenceTendsto

/-! ## Residual convergence -/

/-- A residual certificate separates the squared residual paid for by
accepted steps from the part paid for by fallback decrease. -/
structure ResidualBudget (trace : SafeguardedTrace) where
  residual : ℕ → ℝ≥0
  acceptedResidualSq : ℕ → ℝ≥0
  fallbackScale : ℝ≥0
  acceptedResidualSq_summable : Summable acceptedResidualSq
  residualSq_le : ∀ step,
    residual step ^ 2 ≤
      acceptedResidualSq step +
        fallbackScale * trace.fallbackDecrease step

theorem ResidualBudget.residualSq_summable
    {trace : SafeguardedTrace}
    (budget : ResidualBudget trace)
    (acceptedErrorSummable : Summable trace.acceptedError) :
    Summable (fun step => budget.residual step ^ 2) := by
  have fallbackSummable :=
    trace.fallbackDecrease_summable acceptedErrorSummable
  have dominatingSummable :
      Summable (fun step =>
        budget.acceptedResidualSq step +
          budget.fallbackScale * trace.fallbackDecrease step) :=
    budget.acceptedResidualSq_summable.add
      (fallbackSummable.mul_left budget.fallbackScale)
  exact NNReal.summable_of_le
    (fun step => budget.residualSq_le step) dominatingSummable

/-- The complete residual vanishes, including both accepted and fallback
steps. -/
theorem ResidualBudget.residual_tendsto_zero
    {trace : SafeguardedTrace}
    (budget : ResidualBudget trace)
    (acceptedErrorSummable : Summable trace.acceptedError) :
    Tendsto budget.residual atTop (𝓝 0) := by
  have squaredTendsto :
      Tendsto (fun step => budget.residual step ^ 2)
        atTop (𝓝 0) :=
    NNReal.tendsto_atTop_zero_of_summable
      (budget.residualSq_summable acceptedErrorSummable)
  have squareRootTendsto :=
    (NNReal.continuous_sqrt.tendsto 0).comp squaredTendsto
  convert squareRootTendsto using 1 <;>
    simp [Function.comp_def]

/-! ## Compact-limit recovery -/

/-- A convergent nonnegative-distance sequence and one convergent subsequence
force the whole sequence to have the same limit. -/
theorem tendsto_of_nndist_converges_of_subsequence
    {State : Type*} [PseudoMetricSpace State] [T2Space State]
    {state : ℕ → State} {target : State}
    (distanceConverges :
      ∃ limit : ℝ≥0,
        Tendsto (fun step => nndist (state step) target)
          atTop (𝓝 limit))
    {subsequence : ℕ → ℕ}
    (subsequenceStrict : StrictMono subsequence)
    (subsequenceTendsto :
      Tendsto (state ∘ subsequence) atTop (𝓝 target)) :
    Tendsto state atTop (𝓝 target) := by
  obtain ⟨limit, distanceTendsto⟩ := distanceConverges
  have subsequenceDistanceFromGlobal :
      Tendsto (fun step => nndist (state (subsequence step)) target)
        atTop (𝓝 limit) := by
    simpa only [Function.comp_apply, Function.comp_def] using
      distanceTendsto.comp subsequenceStrict.tendsto_atTop
  have subsequenceDistance :
      Tendsto (fun step => nndist (state (subsequence step)) target)
        atTop (𝓝 0) := by
    have targetTendsto :
        Tendsto (fun _ : ℕ => target) atTop (𝓝 target) :=
      tendsto_const_nhds
    simpa only [Function.comp_apply, nndist_self] using
      subsequenceTendsto.nndist targetTendsto
  have subsequenceDistanceFromGlobalReal :
      Tendsto
        (fun step =>
          (nndist (state (subsequence step)) target : ℝ))
        atTop (𝓝 (limit : ℝ)) :=
    NNReal.tendsto_coe.mpr subsequenceDistanceFromGlobal
  have subsequenceDistanceReal :
      Tendsto
        (fun step =>
          (nndist (state (subsequence step)) target : ℝ))
        atTop (𝓝 (0 : ℝ)) :=
    NNReal.tendsto_coe.mpr subsequenceDistance
  have limitZero : (limit : ℝ) = 0 :=
    tendsto_nhds_unique
      subsequenceDistanceFromGlobalReal subsequenceDistanceReal
  have limitZeroNN : limit = 0 :=
    NNReal.coe_injective (by simpa using limitZero)
  have distanceZero :
      Tendsto (fun step => nndist (state step) target)
        atTop (𝓝 0) := by
    simpa only [limitZeroNN] using distanceTendsto
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [coe_nndist, NNReal.coe_zero] using
    NNReal.tendsto_coe.mpr distanceZero

/-- Convergence of squared nonnegative distance implies convergence of
distance itself, with the square root of the limiting potential. -/
theorem nndist_converges_of_squaredDistance_converges
    {State : Type*} [PseudoMetricSpace State]
    {state : ℕ → State} {target : State}
    (squaredDistanceConverges :
      ∃ limit : ℝ≥0,
        Tendsto (fun step => nndist (state step) target ^ 2)
          atTop (𝓝 limit)) :
    ∃ limit : ℝ≥0,
      Tendsto (fun step => nndist (state step) target)
        atTop (𝓝 limit) := by
  obtain ⟨limit, squaredTendsto⟩ := squaredDistanceConverges
  refine ⟨NNReal.sqrt limit, ?_⟩
  have squareRootTendsto :=
    (NNReal.continuous_sqrt.tendsto limit).comp squaredTendsto
  convert squareRootTendsto using 1
  simp [Function.comp_def]

/-- Abstract final step of the stabilized-Anderson proof.  Sequential
compactness replaces the source paper's finite-dimensional
Bolzano--Weierstrass argument. -/
theorem converges_to_fixedPoint_of_compact_residual
    {State : Type*} [PseudoMetricSpace State] [T2Space State]
    {state : ℕ → State} {invariant fixedPoints : Set State}
    (invariantCompact : IsSeqCompact invariant)
    (state_mem : ∀ step, state step ∈ invariant)
    {residualAt : State → ℝ≥0}
    (residualContinuous : Continuous residualAt)
    (residualTendsto :
      Tendsto (fun step => residualAt (state step)) atTop (𝓝 0))
    (zeroResidual_fixed :
      ∀ point ∈ invariant, residualAt point = 0 → point ∈ fixedPoints)
    (squaredDistanceConverges :
      ∀ point ∈ fixedPoints,
        ∃ limit : ℝ≥0,
          Tendsto
            (fun step =>
              nndist (state step) point ^ 2)
            atTop (𝓝 limit)) :
    ∃ point ∈ invariant, point ∈ fixedPoints ∧
      Tendsto state atTop (𝓝 point) := by
  obtain ⟨point, pointMem, subsequence, subsequenceStrict,
      subsequenceTendsto⟩ := invariantCompact state_mem
  have residualSubsequenceZero :
      Tendsto (fun step => residualAt (state (subsequence step)))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Function.comp_def] using
      residualTendsto.comp subsequenceStrict.tendsto_atTop
  have residualSubsequencePoint :
      Tendsto (fun step => residualAt (state (subsequence step)))
        atTop (𝓝 (residualAt point)) := by
    simpa only [Function.comp_apply, Function.comp_def] using
      residualContinuous.continuousAt.tendsto.comp subsequenceTendsto
  have residualPointZero : residualAt point = 0 :=
    tendsto_nhds_unique residualSubsequencePoint residualSubsequenceZero
  have pointFixed :=
    zeroResidual_fixed point pointMem residualPointZero
  refine ⟨point, pointMem, pointFixed, ?_⟩
  exact tendsto_of_nndist_converges_of_subsequence
    (nndist_converges_of_squaredDistance_converges
      (squaredDistanceConverges point pointFixed))
    subsequenceStrict subsequenceTendsto

/-! ## End-to-end safeguarded convergence -/

/-- A family of quasi-Fejer certificates, one for the squared distance to
each fixed point.  This is the quantifier needed by the final convergence
argument: convergence of distance to one preselected fixed point would not
identify an arbitrary cluster point. -/
structure FixedPointTraceFamily
    {State : Type*} [PseudoMetricSpace State]
    (state : ℕ → State) (fixedPoints : Set State) where
  traceAt : State → SafeguardedTrace
  distanceSq_eq : ∀ point ∈ fixedPoints, ∀ step,
    (traceAt point).distanceSq step =
      nndist (state step) point ^ 2
  acceptedError_summable : ∀ point ∈ fixedPoints,
    Summable (traceAt point).acceptedError

/-- A residual budget together with its semantic binding to the state
sequence.  Keeping this equality explicit prevents a numerically convenient
surrogate residual from silently standing in for the fixed-point residual. -/
structure ResidualTraceBinding
    {State : Type*} (state : ℕ → State)
    (residualAt : State → ℝ≥0) where
  trace : SafeguardedTrace
  budget : ResidualBudget trace
  acceptedError_summable : Summable trace.acceptedError
  residual_eq : ∀ step,
    budget.residual step = residualAt (state step)

theorem ResidualTraceBinding.semanticResidual_tendsto_zero
    {State : Type*} {state : ℕ → State}
    {residualAt : State → ℝ≥0}
    (binding : ResidualTraceBinding state residualAt) :
    Tendsto (fun step => residualAt (state step))
      atTop (𝓝 0) := by
  have semanticResidual_eq :
      (fun step => residualAt (state step)) =
        binding.budget.residual := by
    funext step
    exact (binding.residual_eq step).symm
  rw [semanticResidual_eq]
  exact binding.budget.residual_tendsto_zero
    binding.acceptedError_summable

/-- End-to-end recovery theorem for a safeguarded accelerated iteration.
Summable accepted-step errors give quasi-Fejer convergence to every fixed
point, the residual budget makes the semantic residual vanish, and
sequential compactness supplies a cluster point.  The entire state sequence
then converges to a fixed point. -/
theorem converges_to_fixedPoint_of_safeguarded_family
    {State : Type*} [PseudoMetricSpace State] [T2Space State]
    {state : ℕ → State} {invariant fixedPoints : Set State}
    (invariantCompact : IsSeqCompact invariant)
    (state_mem : ∀ step, state step ∈ invariant)
    {residualAt : State → ℝ≥0}
    (residualContinuous : Continuous residualAt)
    (zeroResidual_fixed :
      ∀ point ∈ invariant, residualAt point = 0 → point ∈ fixedPoints)
    (family : FixedPointTraceFamily state fixedPoints)
    (residualBinding : ResidualTraceBinding state residualAt) :
    ∃ point ∈ invariant, point ∈ fixedPoints ∧
      Tendsto state atTop (𝓝 point) := by
  apply converges_to_fixedPoint_of_compact_residual
    invariantCompact state_mem residualContinuous
    residualBinding.semanticResidual_tendsto_zero
    zeroResidual_fixed
  intro point pointFixed
  have semanticDistanceSq_eq :
      (fun step => nndist (state step) point ^ 2) =
        (family.traceAt point).distanceSq := by
    funext step
    exact (family.distanceSq_eq point pointFixed step).symm
  rw [semanticDistanceSq_eq]
  exact (family.traceAt point).distanceSq_converges
    (family.acceptedError_summable point pointFixed)

/-! ## The polynomial safeguard used by stabilized AA-I -/

/-- Nonnegative version of the source paper's accepted-step decay schedule. -/
def polynomialSafeguard
    (scale : ℝ≥0) (exponent : ℝ) (step : ℕ) : ℝ≥0 :=
  ⟨(scale : ℝ) / |(step : ℝ) + 1| ^ exponent, by positivity⟩

/-- The accepted-step movement budget is summable precisely in the regime
used by the source safeguard. -/
theorem polynomialSafeguard_summable
    (scale : ℝ≥0) {exponent : ℝ} (exponent_gt_one : 1 < exponent) :
    Summable (polynomialSafeguard scale exponent) := by
  rw [← NNReal.summable_coe]
  change Summable
    (fun step : ℕ =>
      (scale : ℝ) / |(step : ℝ) + 1| ^ exponent)
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    (((Real.summable_one_div_nat_add_rpow 1 exponent).2
      exponent_gt_one).mul_left (scale : ℝ))

/-- Squaring the distance inequality produces one linear and one quadratic
decay term, matching equation (19) of the source proof. -/
def andersonDistanceError
    (linearScale quadraticScale : ℝ≥0)
    (epsilon : ℝ) (step : ℕ) : ℝ≥0 :=
  polynomialSafeguard linearScale (1 + epsilon) step +
    polynomialSafeguard quadraticScale (2 + 2 * epsilon) step

theorem andersonDistanceError_summable
    (linearScale quadraticScale : ℝ≥0)
    {epsilon : ℝ} (epsilon_pos : 0 < epsilon) :
    Summable
      (andersonDistanceError linearScale quadraticScale epsilon) := by
  exact
    (polynomialSafeguard_summable linearScale
      (exponent := 1 + epsilon) (by linarith)).add
      (polynomialSafeguard_summable quadraticScale
        (exponent := 2 + 2 * epsilon) (by linarith))

/-- Sharp negative boundary: replacing the source exponent `1 + epsilon`
by `1` loses summability. -/
theorem harmonicSafeguard_not_summable :
    ¬ Summable (polynomialSafeguard 1 1) := by
  rw [← NNReal.summable_coe]
  change ¬ Summable
    (fun step : ℕ => (1 : ℝ) / |(step : ℝ) + 1| ^ (1 : ℝ))
  rw [Real.summable_one_div_nat_add_rpow]
  norm_num

/-! ## Executable positive and negative fixtures -/

/-- A nontrivial exact trace: every fallback step halves squared distance
and spends the other half as certified decrease. -/
def halfContractionTrace : SafeguardedTrace where
  distanceSq step := (1 / 2 : ℝ≥0) ^ step
  acceptedError _ := 0
  fallbackDecrease step := (1 / 2 : ℝ≥0) ^ (step + 1)
  stepBudget := by
    intro step
    rw [pow_succ]
    norm_num
    ring_nf
    exact le_rfl

theorem halfContractionTrace_finite_budget (horizon : ℕ) :
    halfContractionTrace.distanceSq horizon +
        ∑ step ∈ range horizon,
          halfContractionTrace.fallbackDecrease step ≤ 1 :=
  by
    simpa [halfContractionTrace] using
      halfContractionTrace.finite_budget horizon

/-- Without summable accepted error, the one-step inequality alone permits
unbounded linear drift. -/
def unitDriftTrace : SafeguardedTrace where
  distanceSq step := step
  acceptedError _ := 1
  fallbackDecrease _ := 0
  stepBudget := by
    intro step
    norm_num

theorem unitDriftTrace_distanceSq (step : ℕ) :
    unitDriftTrace.distanceSq step = step := rfl

theorem unitDriftTrace_error_not_summable :
    ¬ Summable unitDriftTrace.acceptedError := by
  intro summableError
  have tendsZero :
      Tendsto (fun _ : ℕ => (1 : ℝ≥0)) atTop (𝓝 0) := by
    apply NNReal.tendsto_atTop_zero_of_summable
    simpa [unitDriftTrace] using summableError
  have tendsZeroReal :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    NNReal.tendsto_coe.mpr tendsZero
  have tendsOneReal :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have oneEqZero : (1 : ℝ) = 0 :=
    tendsto_nhds_unique tendsOneReal tendsZeroReal
  norm_num at oneEqZero

#print axioms SafeguardedTrace.finite_budget
#print axioms SafeguardedTrace.fallbackDecrease_summable
#print axioms SafeguardedTrace.distanceSq_converges
#print axioms ResidualBudget.residual_tendsto_zero
#print axioms tendsto_of_nndist_converges_of_subsequence
#print axioms nndist_converges_of_squaredDistance_converges
#print axioms converges_to_fixedPoint_of_compact_residual
#print axioms ResidualTraceBinding.semanticResidual_tendsto_zero
#print axioms converges_to_fixedPoint_of_safeguarded_family
#print axioms polynomialSafeguard_summable
#print axioms andersonDistanceError_summable
#print axioms harmonicSafeguard_not_summable
#print axioms halfContractionTrace_finite_budget
#print axioms unitDriftTrace_error_not_summable

end

end SafeguardedAndersonConvergence

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
