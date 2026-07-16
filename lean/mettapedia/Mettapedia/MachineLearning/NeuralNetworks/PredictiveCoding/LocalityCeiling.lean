import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.MuPCDepthCredit

/-!
# Locality ceilings for predictive-coding settling

This file separates finite-speed information propagation from linearity.
A bandwidth-`w` update may be nonlinear and may couple every coordinate in
the radius-`w` ball, but one application cannot inspect anything outside
that ball.  Iteration therefore expands dependence by at most `w` chain
edges per sweep.

The lower bound is non-vacuous: a unit-gain, unit-precision PC chain has a
conditional posterior whose penultimate coordinate genuinely changes with
the input boundary.  The posterior identification is obtained through the
operator-level Bayesian crown.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

/-! ## Arbitrary nonlinear bandwidth-`w` maps -/

/-- States on the `depth + 1` vertices of a finite chain. -/
abbrev ChainState (Value : Type*) (depth : ℕ) := Fin (depth + 1) → Value

/-- Graph distance between two vertices of the finite chain. -/
def chainDistance {depth : ℕ} (i j : Fin (depth + 1)) : ℕ :=
  (i.val - j.val) + (j.val - i.val)

@[simp] theorem chainDistance_self {depth : ℕ} (i : Fin (depth + 1)) :
    chainDistance i i = 0 := by
  simp [chainDistance]

theorem chainDistance_comm {depth : ℕ} (i j : Fin (depth + 1)) :
    chainDistance i j = chainDistance j i := by
  simp [chainDistance, add_comm]

theorem chainDistance_triangle {depth : ℕ}
    (i j k : Fin (depth + 1)) :
    chainDistance i k ≤ chainDistance i j + chainDistance j k := by
  simp only [chainDistance]
  omega

/-- Two states agree on the closed chain ball around `center`. -/
def AgreeOnChainBall {Value : Type*} {depth : ℕ}
    (x y : ChainState Value depth) (center : Fin (depth + 1))
    (radius : ℕ) : Prop :=
  ∀ node, chainDistance center node ≤ radius → x node = y node

/-- A possibly nonlinear update has bandwidth `w` when its output at a
coordinate depends only on the radius-`w` input ball. -/
def HasChainBandwidth {Value : Type*} {depth : ℕ}
    (step : ChainState Value depth → ChainState Value depth)
    (w : ℕ) : Prop :=
  ∀ x y center, AgreeOnChainBall x y center w →
    step x center = step y center

/-- One new local sweep adds at most one radius-`w` shell to the dependency
ball.  No algebraic property of `step` is used. -/
theorem hasChainBandwidth_iterate_agreement {Value : Type*} {depth w : ℕ}
    (step : ChainState Value depth → ChainState Value depth)
    (hbandwidth : HasChainBandwidth step w) :
    ∀ sweeps x y center,
      AgreeOnChainBall x y center (sweeps * w) →
        (Nat.iterate step sweeps x) center =
          (Nat.iterate step sweeps y) center := by
  intro sweeps
  induction sweeps with
  | zero =>
      intro x y center hagree
      exact hagree center (by simp)
  | succ sweeps ih =>
      intro x y center hagree
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply hbandwidth
      intro neighbor hneighbor
      apply ih
      intro node hnode
      apply hagree
      have htriangle := chainDistance_triangle center neighbor node
      rw [Nat.succ_mul]
      omega

/-- If two initial states differ only at vertex zero, then a coordinate
farther than `sweeps * w` from zero is still input-independent. -/
theorem hasChainBandwidth_iterate_eq_of_agree_away_from_zero
    {Value : Type*} {depth w sweeps : ℕ}
    (step : ChainState Value depth → ChainState Value depth)
    (hbandwidth : HasChainBandwidth step w)
    (x y : ChainState Value depth)
    (haway : ∀ node, node.val ≠ 0 → x node = y node)
    (center : Fin (depth + 1))
    (hearly : sweeps * w < center.val) :
    (Nat.iterate step sweeps x) center =
      (Nat.iterate step sweeps y) center := by
  apply hasChainBandwidth_iterate_agreement step hbandwidth
  intro node hnode
  apply haway
  intro hzero
  have hdistance : chainDistance center node = center.val := by
    simp [chainDistance, hzero]
  rw [hdistance] at hnode
  omega

/-- General exact-settling lower bound.  If two desired terminal states
differ at `center`, while their initial states differ only at the input
boundary, exact settling requires the wavefront to reach `center`. -/
theorem hasChainBandwidth_exact_settling_requires_reach
    {Value : Type*} {depth w sweeps : ℕ}
    (step : ChainState Value depth → ChainState Value depth)
    (hbandwidth : HasChainBandwidth step w)
    (initial₀ initial₁ target₀ target₁ : ChainState Value depth)
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node)
    (center : Fin (depth + 1))
    (htarget : target₀ center ≠ target₁ center)
    (hsettle₀ : Nat.iterate step sweeps initial₀ = target₀)
    (hsettle₁ : Nat.iterate step sweeps initial₁ = target₁) :
    center.val ≤ sweeps * w := by
  by_contra hreach
  have hearly : sweeps * w < center.val := Nat.lt_of_not_ge hreach
  have hequal :=
    hasChainBandwidth_iterate_eq_of_agree_away_from_zero
      step hbandwidth initial₀ initial₁ haway center hearly
  rw [hsettle₀, hsettle₁] at hequal
  exact htarget hequal

/-! ## A boundary-dependent posterior from the Bayesian crown -/

theorem unitPrecisionPositive (depth : ℕ) :
    ∀ node, node < depth → 0 < (1 : ℝ) := by
  intros
  norm_num

/-- Unit-gain, unit-precision links used by the nondegeneracy witness. -/
noncomputable def localityUnitLinks (depth : ℕ) : Fin depth → PCLink :=
  precisionWeightedUnitLinks depth (fun _ => 1) (unitPrecisionPositive depth)

/-- The explicit endpoint-conditioned equilibrium of the unit chain. -/
noncomputable def localityUnitEquilibrium (depth : ℕ) (input : ℝ) :
    PCState depth :=
  precisionWeightedEquilibriumState depth (fun _ => 1) input 0

/-- The explicit unit-chain equilibrium is the conditional Gaussian
posterior mean supplied by the operator-level Bayesian theorem.  This bridge
adds the concrete unit-chain identification used below. -/
theorem localityUnitEquilibrium_eq_conditionalPosteriorMean
    (distance : ℕ) (input : ℝ) :
    localityUnitEquilibrium (distance + 1) input =
      pcStateOfInterior distance input 0
        (∫ u, u ∂pcConditionalPosterior
          (localityUnitLinks (distance + 1)) input 0) := by
  apply (pcEquilibrium_iff_eq_conditionalPosteriorMean
    (localityUnitLinks (distance + 1)) input 0
    (localityUnitEquilibrium (distance + 1) input)).mp
  exact precisionWeightedEquilibriumState_is_equilibrium
    (distance + 1) (by omega) (fun _ => 1) input 0
    (unitPrecisionPositive (distance + 1))

/-- Vertex `distance` in a chain with `distance + 1` edges: one vertex
before the zero-valued output clamp. -/
def localityObservedNode (distance : ℕ) : Fin (distance + 1 + 1) :=
  ⟨distance, by omega⟩

/-- Nondegeneracy: the conditional posterior at a vertex `distance` edges
from the input changes when the input clamp changes from zero to one. -/
theorem unitChain_conditionalPosteriorMean_depends_on_input
    (distance : ℕ) :
    (pcStateOfInterior distance 0 0
        (∫ u, u ∂pcConditionalPosterior
          (localityUnitLinks (distance + 1)) 0 0))
          (localityObservedNode distance) ≠
      (pcStateOfInterior distance 1 0
        (∫ u, u ∂pcConditionalPosterior
          (localityUnitLinks (distance + 1)) 1 0))
          (localityObservedNode distance) := by
  rw [← localityUnitEquilibrium_eq_conditionalPosteriorMean distance 0,
    ← localityUnitEquilibrium_eq_conditionalPosteriorMean distance 1]
  simp only [localityUnitEquilibrium, precisionWeightedEquilibriumState,
    localityObservedNode]
  rw [precisionResistancePrefix_const, precisionResistancePrefix_const]
  have hden : ((distance + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  norm_num
  field_simp [hden]
  norm_num

/-! ## The nonlinear locality ceiling -/

/-- Initial state with only the input clamp populated. -/
noncomputable def boundaryOnlyInitialState
    (depth : ℕ) (input : ℝ) : PCState depth :=
  fun node => if node.val = 0 then input else 0

theorem boundaryOnlyInitialState_agree_away_from_zero
    (depth : ℕ) (input₀ input₁ : ℝ) :
    ∀ node, node.val ≠ 0 →
      boundaryOnlyInitialState depth input₀ node =
        boundaryOnlyInitialState depth input₁ node := by
  intro node hnode
  simp [boundaryOnlyInitialState, hnode]

/-- L1 crown: every bandwidth-`w` rule that exactly settles both boundary
conditions of the genuine unit-chain PC posterior needs enough sweeps for
its dependency wavefront to traverse the requested distance.  The rule may
be nonlinear and otherwise arbitrary. -/
theorem bandwidth_rule_exact_unitChainPosterior_requires_reach
    (distance w sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step w)
    (hsettle₀ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettle₁ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0)) :
    distance ≤ sweeps * w := by
  exact hasChainBandwidth_exact_settling_requires_reach
    step hbandwidth
    (boundaryOnlyInitialState (distance + 1) 0)
    (boundaryOnlyInitialState (distance + 1) 1)
    (pcStateOfInterior distance 0 0
      (∫ u, u ∂pcConditionalPosterior
        (localityUnitLinks (distance + 1)) 0 0))
    (pcStateOfInterior distance 1 0
      (∫ u, u ∂pcConditionalPosterior
        (localityUnitLinks (distance + 1)) 1 0))
    (boundaryOnlyInitialState_agree_away_from_zero
      (distance + 1) 0 1)
    (localityObservedNode distance)
    (unitChain_conditionalPosteriorMean_depends_on_input distance)
    hsettle₀ hsettle₁

/-- Division form of the L1 ceiling: exact inference takes at least
`distance / w` sweeps. -/
theorem bandwidth_rule_exact_unitChainPosterior_sweep_lower_bound
    (distance w sweeps : ℕ)
    (step : PCState (distance + 1) → PCState (distance + 1))
    (hbandwidth : HasChainBandwidth step w)
    (hsettle₀ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 0) =
        pcStateOfInterior distance 0 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 0 0))
    (hsettle₁ :
      Nat.iterate step sweeps
          (boundaryOnlyInitialState (distance + 1) 1) =
        pcStateOfInterior distance 1 0
          (∫ u, u ∂pcConditionalPosterior
            (localityUnitLinks (distance + 1)) 1 0)) :
    distance / w ≤ sweeps := by
  apply Nat.div_le_of_le_mul
  simpa [mul_comm] using
    bandwidth_rule_exact_unitChainPosterior_requires_reach
      distance w sweeps step hbandwidth hsettle₀ hsettle₁

/-! ## Tight positive and negative fixtures -/

/-- A concrete radius-`w` forward-copy rule.  Vertex `i` reads `i-w`
when that predecessor exists and otherwise retains its value. -/
def forwardRadiusCopyStep {Value : Type*}
    (depth w : ℕ) (state : ChainState Value depth) :
    ChainState Value depth :=
  fun node =>
    if h : w ≤ node.val then
      state ⟨node.val - w, by omega⟩
    else state node

theorem forwardRadiusCopyStep_hasBandwidth {Value : Type*}
    (depth w : ℕ) :
    HasChainBandwidth (forwardRadiusCopyStep (Value := Value) depth w) w := by
  intro x y center hagree
  unfold forwardRadiusCopyStep
  split
  · apply hagree
    simp [chainDistance]
    omega
  · apply hagree
    simp

/-- Positive fixture: a bandwidth-two rule reaches vertex four in exactly
two sweeps. -/
theorem bandwidthTwo_reaches_nodeFour_in_two_sweeps
    {Value : Type*} (state : ChainState Value 4) :
    (Nat.iterate (forwardRadiusCopyStep (Value := Value) 4 2) 2 state)
        (⟨4, by omega⟩ : Fin 5) =
      state 0 := by
  simp [Function.iterate_succ_apply', forwardRadiusCopyStep]

/-- Negative fixture: after two sweeps, every bandwidth-one rule is still
unable to distinguish an input-only change at vertex three. -/
theorem bandwidthOne_nodeThree_inputIndependent_after_two_sweeps
    {Value : Type*}
    (step : ChainState Value 3 → ChainState Value 3)
    (hbandwidth : HasChainBandwidth step 1)
    (initial₀ initial₁ : ChainState Value 3)
    (haway : ∀ node, node.val ≠ 0 → initial₀ node = initial₁ node) :
    (Nat.iterate step 2 initial₀) (⟨3, by omega⟩ : Fin 4) =
      (Nat.iterate step 2 initial₁) (⟨3, by omega⟩ : Fin 4) := by
  apply hasChainBandwidth_iterate_eq_of_agree_away_from_zero
    step hbandwidth initial₀ initial₁ haway
  norm_num

#print axioms bandwidth_rule_exact_unitChainPosterior_requires_reach

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
