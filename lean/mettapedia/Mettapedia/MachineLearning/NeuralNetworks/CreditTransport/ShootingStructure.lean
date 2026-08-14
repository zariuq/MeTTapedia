import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MultiSiteErrorCoordinatePC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.NondimensionalSettlingSchedule
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SettledCreditSpectralGeometry
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.DAGScheduleExactness
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.RecurrentGradientHorizon
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.RankedDAGTensorSubstitution
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.ZILExactness
import Mathlib.Tactic

/-!
# Shooting structure and scheduled predictive credit

Introducing an independent state at every recurrent time step exposes the
multiple-shooting structure hidden by a condensed recurrent sensitivity.  Two
different boundaries must not be conflated.  The AC implementation's ranked
state and reduced-error forms are an invertible coordinate change of one
unchanged energy; `rankedDAG_criticalDifferential_iff` already proves that this
change preserves and reflects criticality.  By contrast, replacing a hard
matching relation by a soft lifted energy and then eliminating its internal
states is a genuine model transformation.  It agrees with the condensed model
on exactly matched trajectories, but its finite optimization geometry---and,
when its Schur metric depends on learned parameters, its stationary set---can
differ.

This file isolates four boundaries needed by the AC predictive-coding
experiment.

* A condensed terminal sensitivity contains an ordered product of local
  Jacobians.  The lifted matching energy contains only one-step residuals.
* Local lifting does not by itself give a depth-independent condition-number
  bound: the unanchored matching energy has a nonzero zero-energy direction.
* A simultaneous local schedule transports nonzero credit at most one edge
  per causal phase.  An ordered output-to-input sweep recovers the chain
  reverse derivative, but consumes one sequential phase per traversed edge.
* Increasing sweep completeness does not make cosine-to-backprop monotone
  without a geometric hypothesis.  Signed contributions can first decrease
  and later restore alignment.  Orthogonal nonnegative energy capture gives
  a valid monotone special case.

The conditioning statements deliberately avoid replacing singular-value
spread by operator norm.  A two-mode fixture has the same maximum gain in an
isotropic and an anisotropic system, while the normal-equation condition
proxies are respectively `1` and `10000`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ShootingStructure

open scoped BigOperators
open NondimensionalSettlingSchedule
open SettledCreditSpectralGeometry

noncomputable section

/-! ## Ordered products and finite-speed transport -/

/-- Ordered scalar Jacobian product along the first `depth` links of a chain.
Link zero is adjacent to the output. -/
def prefixJacobianProduct (gain : ℕ → ℝ) (depth : ℕ) : ℝ :=
  ∏ i ∈ Finset.range depth, gain i

@[simp] theorem prefixJacobianProduct_zero (gain : ℕ → ℝ) :
    prefixJacobianProduct gain 0 = 1 := by
  simp [prefixJacobianProduct]

theorem prefixJacobianProduct_succ (gain : ℕ → ℝ) (depth : ℕ) :
    prefixJacobianProduct gain (depth + 1) =
      gain depth * prefixJacobianProduct gain depth := by
  simp [prefixJacobianProduct, Finset.prod_range_succ, mul_comm]

/-- Reverse-mode chain credit at a declared depth. -/
def backpropChainCredit (gain : ℕ → ℝ) (outputCredit : ℝ)
    (depth : ℕ) : ℝ :=
  prefixJacobianProduct gain depth * outputCredit

/-- One output-to-input ordered sweep.  The recursive call is the freshly
available credit at the child, so this definition exposes its sequential
dependency. -/
def orderedSweepCredit (gain : ℕ → ℝ) (outputCredit : ℝ) : ℕ → ℝ
  | 0 => outputCredit
  | depth + 1 => gain depth * orderedSweepCredit gain outputCredit depth

/-- An ordered output-to-input sweep computes the ordinary reverse-mode chain
credit exactly. -/
theorem orderedSweepCredit_eq_backpropChainCredit
    (gain : ℕ → ℝ) (outputCredit : ℝ) (depth : ℕ) :
    orderedSweepCredit gain outputCredit depth =
      backpropChainCredit gain outputCredit depth := by
  induction depth with
  | zero => simp [orderedSweepCredit, backpropChainCredit]
  | succ depth ih =>
      simp only [orderedSweepCredit, backpropChainCredit,
        prefixJacobianProduct_succ, ih]
      ring

/-- Parallel local propagation from an output clamp.  Each phase reads the
previous phase, so information crosses at most one chain edge per phase. -/
def synchronousCredit (gain : ℕ → ℝ) (outputCredit : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => outputCredit
  | 0, _depth + 1 => 0
  | _time + 1, 0 => outputCredit
  | time + 1, depth + 1 => gain depth * synchronousCredit gain outputCredit time depth

/-- A simultaneous nearest-neighbour update cannot transport credit beyond
its causal frontier. -/
theorem synchronousCredit_eq_zero_of_time_lt_depth
    (gain : ℕ → ℝ) (outputCredit : ℝ) {time depth : ℕ}
    (before : time < depth) :
    synchronousCredit gain outputCredit time depth = 0 := by
  induction time generalizing depth with
  | zero =>
      cases depth with
      | zero => omega
      | succ depth => simp [synchronousCredit]
  | succ time ih =>
      cases depth with
      | zero => omega
      | succ depth =>
          have earlier : time < depth := by omega
          simp [synchronousCredit, ih earlier]

/-- The first arrival at depth `d` is the exact ordered Jacobian product. -/
theorem synchronousCredit_diagonal_eq_backprop
    (gain : ℕ → ℝ) (outputCredit : ℝ) (depth : ℕ) :
    synchronousCredit gain outputCredit depth depth =
      backpropChainCredit gain outputCredit depth := by
  induction depth with
  | zero => simp [synchronousCredit, backpropChainCredit]
  | succ depth ih =>
      simp only [synchronousCredit, ih, backpropChainCredit,
        prefixJacobianProduct_succ]
      ring

/-- If the exact reverse credit is nonzero, fewer than `depth` causal phases
cannot reproduce it. -/
theorem exact_nonzero_credit_requires_depth_phases
    (gain : ℕ → ℝ) (outputCredit : ℝ) {time depth : ℕ}
    (nonzero : backpropChainCredit gain outputCredit depth ≠ 0)
    (exact : synchronousCredit gain outputCredit time depth =
      backpropChainCredit gain outputCredit depth) :
    depth ≤ time := by
  by_contra notEnough
  have before : time < depth := Nat.lt_of_not_ge notEnough
  have zero := synchronousCredit_eq_zero_of_time_lt_depth
    gain outputCredit before
  rw [exact] at zero
  exact nonzero zero

/-- One "ordered sweep" has full-depth transport because it contains exactly
one sequential dependency phase for every traversed edge. -/
def orderedSweepSequentialSpan (depth : ℕ) : ℕ := depth

@[simp] theorem orderedSweepSequentialSpan_eq_depth (depth : ℕ) :
    orderedSweepSequentialSpan depth = depth := rfl

/-! ## Single shooting, lifting, and the conditioning boundary -/

/-- Condensed endpoint sensitivity of a scalar recurrent chain. -/
def singleShootingSensitivity (gain : ℕ → ℝ) (depth : ℕ) : ℝ :=
  prefixJacobianProduct gain depth

/-- Terminal least-squares curvature in the scalar condensed coordinate. -/
def singleShootingTerminalCurvature (gain : ℕ → ℝ)
    (depth : ℕ) : ℝ :=
  singleShootingSensitivity gain depth ^ 2

theorem singleShootingSensitivity_constant (jacobian : ℝ) (depth : ℕ) :
    singleShootingSensitivity (fun _ => jacobian) depth = jacobian ^ depth := by
  simp [singleShootingSensitivity, prefixJacobianProduct]

theorem singleShootingTerminalCurvature_constant
    (jacobian : ℝ) (depth : ℕ) :
    singleShootingTerminalCurvature (fun _ => jacobian) depth =
      (jacobian ^ depth) ^ 2 := by
  rw [singleShootingTerminalCurvature,
    singleShootingSensitivity_constant]

/-- Multiple-shooting matching energy with one independent state at every
chain node.  Each summand contains only one local Jacobian. -/
def liftedMatchingEnergy (gain state : ℕ → ℝ) (depth : ℕ) : ℝ :=
  ∑ i ∈ Finset.range depth,
    (state (i + 1) - gain i * state i) ^ 2 / 2

/-- The local defect represented by one lifted matching row. -/
def liftedResidual (gain state : ℕ → ℝ) (index : ℕ) : ℝ :=
  state (index + 1) - gain index * state index

/-- A lifted matching row is a genuinely local stencil: changing every state
except its two incident nodes cannot change that row. -/
theorem liftedResidual_eq_of_incident_eq
    {gain left right : ℕ → ℝ} {index : ℕ}
    (atSource : left index = right index)
    (atTarget : left (index + 1) = right (index + 1)) :
    liftedResidual gain left index = liftedResidual gain right index := by
  simp [liftedResidual, atSource, atTarget]

/-- The lifted matching energy is the sum of squares of those one-edge
stencils; no ordered Jacobian product occurs in an individual row. -/
theorem liftedMatchingEnergy_eq_sum_residual_sq
    (gain state : ℕ → ℝ) (depth : ℕ) :
    liftedMatchingEnergy gain state depth =
      ∑ i ∈ Finset.range depth, liftedResidual gain state i ^ 2 / 2 := by
  rfl

/-- The trajectory generated by the condensed forward recurrence. -/
def liftedTrajectory (gain : ℕ → ℝ) (initial : ℝ) (depth : ℕ) : ℝ :=
  prefixJacobianProduct gain depth * initial

theorem liftedTrajectory_step
    (gain : ℕ → ℝ) (initial : ℝ) (depth : ℕ) :
    liftedTrajectory gain initial (depth + 1) =
      gain depth * liftedTrajectory gain initial depth := by
  simp [liftedTrajectory, prefixJacobianProduct_succ, mul_assoc]

/-- Every exactly matched trajectory has zero lifted defect energy. -/
theorem liftedMatchingEnergy_trajectory_eq_zero
    (gain : ℕ → ℝ) (initial : ℝ) (depth : ℕ) :
    liftedMatchingEnergy gain (liftedTrajectory gain initial) depth = 0 := by
  unfold liftedMatchingEnergy
  apply Finset.sum_eq_zero
  intro i _inRange
  rw [liftedTrajectory_step]
  ring

/-- Local one-step curvature bounds alone cannot give a global coercivity or
condition-number theorem: the unanchored matching energy has a nonzero
zero-energy direction. -/
theorem liftedMatchingEnergy_has_nonzero_zero_direction
    (gain : ℕ → ℝ) (depth : ℕ) :
    liftedMatchingEnergy gain (liftedTrajectory gain 1) depth = 0 ∧
      liftedTrajectory gain 1 ≠ 0 := by
  constructor
  · exact liftedMatchingEnergy_trajectory_eq_zero gain 1 depth
  · intro zeroFunction
    have atZero := congrFun zeroFunction 0
    norm_num [liftedTrajectory, prefixJacobianProduct] at atZero

/-- Terminal task energy of the condensed single-shooting presentation. -/
def coarseTerminalEnergy (gain : ℕ → ℝ) (depth : ℕ)
    (initial target : ℝ) : ℝ :=
  (target - prefixJacobianProduct gain depth * initial) ^ 2 / 2

/-- The gradient of a condensed terminal mismatch with respect to its initial
state explicitly contains the full ordered sensitivity product twice: once as
transport and once inside the endpoint mismatch. -/
theorem coarseTerminalEnergy_hasDerivAt_initial
    (gain : ℕ → ℝ) (depth : ℕ) (initial target : ℝ) :
    HasDerivAt (fun value => coarseTerminalEnergy gain depth value target)
      (prefixJacobianProduct gain depth *
        (prefixJacobianProduct gain depth * initial - target)) initial := by
  unfold coarseTerminalEnergy
  let product := prefixJacobianProduct gain depth
  have derivative :=
    (((hasDerivAt_const initial target).sub
      ((hasDerivAt_id initial).const_mul product)).pow 2).div_const 2
  exact derivative.congr_deriv (by simp [product]; ring)

/-- Lifted matching plus terminal task energy. -/
def liftedChainEnergy (gain state : ℕ → ℝ) (depth : ℕ)
    (target : ℝ) : ℝ :=
  liftedMatchingEnergy gain state depth + (target - state depth) ^ 2 / 2

/-- Coarse and lifted presentations agree on the exact matching manifold.
Off that manifold they are different optimization problems. -/
theorem liftedChainEnergy_trajectory_eq_coarse
    (gain : ℕ → ℝ) (initial target : ℝ) (depth : ℕ) :
    liftedChainEnergy gain (liftedTrajectory gain initial) depth target =
      coarseTerminalEnergy gain depth initial target := by
  rw [liftedChainEnergy, liftedMatchingEnergy_trajectory_eq_zero]
  simp [coarseTerminalEnergy, liftedTrajectory]

/-! ### Exact two-segment condensation -/

/-- Two local matching residuals with fixed endpoints and a free midpoint. -/
def twoSegmentFineEnergy
    (firstGain secondGain initial target midpoint : ℝ) : ℝ :=
  (midpoint - firstGain * initial) ^ 2 / 2 +
    (target - secondGain * midpoint) ^ 2 / 2

/-- Midpoint selected by exact elimination of the fine quadratic. -/
def twoSegmentOptimalMidpoint
    (firstGain secondGain initial target : ℝ) : ℝ :=
  (firstGain * initial + secondGain * target) / (1 + secondGain ^ 2)

/-- Schur-condensed fine energy.  It is a scaled terminal mismatch, not the
naive single-shooting terminal energy. -/
def twoSegmentCondensedEnergy
    (firstGain secondGain initial target : ℝ) : ℝ :=
  (target - secondGain * firstGain * initial) ^ 2 /
    (2 * (1 + secondGain ^ 2))

/-- Completing the square exposes the exact condensation factor. -/
theorem twoSegmentFineEnergy_eq_condensed_add_square
    (firstGain secondGain initial target midpoint : ℝ) :
    twoSegmentFineEnergy firstGain secondGain initial target midpoint =
      twoSegmentCondensedEnergy firstGain secondGain initial target +
        (1 + secondGain ^ 2) / 2 *
          (midpoint -
            twoSegmentOptimalMidpoint firstGain secondGain initial target) ^ 2 := by
  have denominator : 1 + secondGain ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg secondGain]
  unfold twoSegmentFineEnergy twoSegmentCondensedEnergy
    twoSegmentOptimalMidpoint
  field_simp [denominator]
  ring

theorem twoSegmentFineEnergy_at_optimum
    (firstGain secondGain initial target : ℝ) :
    twoSegmentFineEnergy firstGain secondGain initial target
        (twoSegmentOptimalMidpoint firstGain secondGain initial target) =
      twoSegmentCondensedEnergy firstGain secondGain initial target := by
  rw [twoSegmentFineEnergy_eq_condensed_add_square]
  ring

/-- Forward equality is recovered when the midpoint constraint is imposed
exactly. -/
theorem twoSegmentFineEnergy_on_forward_midpoint
    (firstGain secondGain initial target : ℝ) :
    twoSegmentFineEnergy firstGain secondGain initial target
        (firstGain * initial) =
      (target - secondGain * firstGain * initial) ^ 2 / 2 := by
  simp [twoSegmentFineEnergy]
  ring

/-- The midpoint derivative of the two-segment lifted problem contains only
the adjacent gain.  This is the scalar local-Hessian stencil behind multiple
shooting. -/
theorem twoSegmentFineEnergy_hasDerivAt_midpoint
    (firstGain secondGain initial target midpoint : ℝ) :
    HasDerivAt
      (twoSegmentFineEnergy firstGain secondGain initial target)
      ((1 + secondGain ^ 2) * midpoint -
        (firstGain * initial + secondGain * target)) midpoint := by
  unfold twoSegmentFineEnergy
  have derivative :=
    ((((hasDerivAt_id midpoint).sub_const (firstGain * initial)).pow 2).div_const 2).add
      ((((hasDerivAt_const midpoint target).sub
        ((hasDerivAt_id midpoint).const_mul secondGain)).pow 2).div_const 2)
  exact derivative.congr_deriv (by simp; ring)

/-- The absolute midpoint force is bounded entirely by adjacent quantities.
This is the frozen-checkpoint conformance bound for a two-segment local row;
it contains no horizon product. -/
theorem abs_twoSegment_midpointGradient_le_local
    (firstGain secondGain initial target midpoint : ℝ) :
    |(1 + secondGain ^ 2) * midpoint -
        (firstGain * initial + secondGain * target)| ≤
      (1 + |secondGain| ^ 2) * |midpoint| +
        |firstGain| * |initial| + |secondGain| * |target| := by
  calc
    |(1 + secondGain ^ 2) * midpoint -
        (firstGain * initial + secondGain * target)|
        ≤ |(1 + secondGain ^ 2) * midpoint| +
          |firstGain * initial + secondGain * target| := abs_sub _ _
    _ ≤ |(1 + secondGain ^ 2) * midpoint| +
          (|firstGain * initial| + |secondGain * target|) := by
          gcongr
          exact abs_add_le _ _
    _ = (1 + |secondGain| ^ 2) * |midpoint| +
          |firstGain| * |initial| + |secondGain| * |target| := by
          rw [abs_mul, abs_mul, abs_mul]
          have nonnegative : 0 ≤ 1 + secondGain ^ 2 := by positivity
          rw [abs_of_nonneg nonnegative]
          rw [sq_abs]
          ring

/-- Exact elimination is stationary at the declared optimal midpoint. -/
theorem twoSegmentFineEnergy_optimalMidpoint_derivative_zero
    (firstGain secondGain initial target : ℝ) :
    HasDerivAt
      (twoSegmentFineEnergy firstGain secondGain initial target) 0
      (twoSegmentOptimalMidpoint firstGain secondGain initial target) := by
  have denominator : 1 + secondGain ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg secondGain]
  convert twoSegmentFineEnergy_hasDerivAt_midpoint firstGain secondGain initial target
    (twoSegmentOptimalMidpoint firstGain secondGain initial target) using 1
  · unfold twoSegmentOptimalMidpoint
    field_simp [denominator]
    ring

/-- Concrete negative boundary: exact elimination of a lifted midpoint gives
energy `1/4`, whereas the naive coarse terminal penalty gives `1/2`. -/
theorem condensed_fine_energy_ne_naive_coarse_energy :
    twoSegmentCondensedEnergy 1 1 0 1 ≠
      (1 - 1 * 1 * 0) ^ 2 / 2 := by
  norm_num [twoSegmentCondensedEnergy]

/-! Parameter-dependent condensation can also change stationary sets.  The
extra denominator below depends on the downstream gain, so it cannot be
dropped as a harmless positive constant while that gain is being learned. -/

def naiveLearnedGainEnergy (gain : ℝ) : ℝ :=
  (1 - gain) ^ 2 / 2

def condensedLearnedGainEnergy (gain : ℝ) : ℝ :=
  (1 - gain) ^ 2 / (2 * (1 + gain ^ 2))

theorem naiveLearnedGainEnergy_hasDerivAt (gain : ℝ) :
    HasDerivAt naiveLearnedGainEnergy (gain - 1) gain := by
  unfold naiveLearnedGainEnergy
  have derivative :=
    (((hasDerivAt_const gain 1).sub (hasDerivAt_id gain)).pow 2).div_const 2
  exact derivative.congr_deriv (by simp; ring)

theorem condensedLearnedGainEnergy_hasDerivAt (gain : ℝ) :
    HasDerivAt condensedLearnedGainEnergy
      ((gain ^ 2 - 1) / (1 + gain ^ 2) ^ 2) gain := by
  have denominator : 2 * (1 + gain ^ 2) ≠ 0 := by
    nlinarith [sq_nonneg gain]
  unfold condensedLearnedGainEnergy
  have numerator :=
    ((hasDerivAt_const gain 1).sub (hasDerivAt_id gain)).pow 2
  have denominatorDerivative :=
    ((hasDerivAt_const gain 1).add ((hasDerivAt_id gain).pow 2)).const_mul 2
  apply (numerator.div denominatorDerivative denominator).congr_deriv
  simp
  have innerDenominator : 1 + gain ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg gain]
  field_simp [innerDenominator]
  ring

/-- At gain `-1`, the Schur-condensed lifted energy is stationary while the
naive coarse terminal energy is not.  Forward equality on the matching
manifold therefore does not imply equality of learned-parameter stationary
sets. -/
theorem condensation_can_change_parameter_stationarity :
    HasDerivAt condensedLearnedGainEnergy 0 (-1) ∧
      ¬ HasDerivAt naiveLearnedGainEnergy 0 (-1) := by
  constructor
  · convert condensedLearnedGainEnergy_hasDerivAt (-1) using 1
    norm_num
  · intro zeroDerivative
    have actualDerivative := naiveLearnedGainEnergy_hasDerivAt (-1)
    have impossible := actualDerivative.unique zeroDerivative
    norm_num at impossible

/-! ### Norm is not condition number -/

/-- Maximum modal gain, used only as a scalar operator-norm proxy for a
two-dimensional diagonal map. -/
def twoModeNormProxy (first second : ℝ) : ℝ :=
  max |first| |second|

/-- Condition proxy of the associated positive diagonal normal matrix.  The
fixtures below keep both modal gains nonzero. -/
def twoModeNormalCondition (first second : ℝ) : ℝ :=
  max (first ^ 2) (second ^ 2) / min (first ^ 2) (second ^ 2)

/-- Equal maximum Jacobian-product norm does not identify conditioning.
Uniform expansion has condition one; anisotropic expansion with the same
maximum gain has condition ten thousand. -/
theorem equal_product_norm_different_condition :
    twoModeNormProxy 100 100 = twoModeNormProxy 100 1 ∧
      twoModeNormalCondition 100 100 = 1 ∧
      twoModeNormalCondition 100 1 = 10000 := by
  norm_num [twoModeNormProxy, twoModeNormalCondition, abs_of_nonneg]

/-- Maximum gain after repeatedly applying a two-mode diagonal recurrence. -/
def twoModeProductNormProxy (first second : ℝ) (depth : ℕ) : ℝ :=
  twoModeNormProxy (first ^ depth) (second ^ depth)

/-- Normal-equation condition proxy after `depth` recurrent steps. -/
def twoModeProductNormalCondition (first second : ℝ) (depth : ℕ) : ℝ :=
  twoModeNormalCondition (first ^ depth) (second ^ depth)

/-- Repetition makes the distinction between growth and conditioning sharper:
both fixtures have product norm `256` at depth eight, but the isotropic chain
has condition proxy one while the anisotropic chain has proxy `65536`. -/
theorem equal_depth_product_norm_different_condition :
    twoModeProductNormProxy 2 2 8 = twoModeProductNormProxy 2 1 8 ∧
      twoModeProductNormalCondition 2 2 8 = 1 ∧
      twoModeProductNormalCondition 2 1 8 = 65536 := by
  norm_num [twoModeProductNormProxy, twoModeProductNormalCondition,
    twoModeNormProxy, twoModeNormalCondition]

/-! ## Sweep-completeness geometry -/

abbrev Credit2 := Fin 2 → ℝ

/-- BP reference for the cancellation fixture. -/
def cancellationBPCredit : Credit2 := ![1, 0]

/-- Successive sweep prefixes.  The middle prefix contains a transverse
contribution that is cancelled by the final local contribution. -/
def cancellationSweepCredit : Fin 3 → Credit2 :=
  ![![1, 0], ![1, 1], ![1, 0]]

/-- Squared coordinate cosine, avoiding square roots while preserving angle
ordering for nonzero vectors. -/
def squaredCoordinateCosine {index : Type*} [Fintype index]
    (left right : index → ℝ) : ℝ :=
  coordinateInner left right ^ 2 /
    (coordinateNormSq left * coordinateNormSq right)

theorem cancellationSweep_squaredCosine_values :
    squaredCoordinateCosine (cancellationSweepCredit 0) cancellationBPCredit = 1 ∧
      squaredCoordinateCosine (cancellationSweepCredit 1) cancellationBPCredit =
        1 / 2 ∧
      squaredCoordinateCosine (cancellationSweepCredit 2) cancellationBPCredit = 1 := by
  norm_num [squaredCoordinateCosine, cancellationSweepCredit,
    cancellationBPCredit, coordinateInner, coordinateNormSq,
    Fin.sum_univ_succ]

/-- More completed local contributions can temporarily reduce alignment with
the final BP credit.  Therefore unconditional cosine monotonicity along a
sweep-completeness dial is false. -/
theorem sweep_completeness_cosine_not_monotone :
    ¬ Monotone (fun level : Fin 3 =>
      squaredCoordinateCosine
        (cancellationSweepCredit level) cancellationBPCredit) := by
  intro monotone
  have decrease := monotone (show (0 : Fin 3) ≤ 1 by decide)
  obtain ⟨first, middle, _last⟩ := cancellationSweep_squaredCosine_values
  change squaredCoordinateCosine (cancellationSweepCredit 0) cancellationBPCredit ≤
    squaredCoordinateCosine (cancellationSweepCredit 1) cancellationBPCredit at decrease
  rw [first, middle] at decrease
  norm_num at decrease

/-- Under pairwise orthogonality, squared cosine is the fraction of BP-credit
energy already captured. -/
def orthogonalCapturedFraction (captured remaining : ℝ) : ℝ :=
  captured / (captured + remaining)

/-- Capturing an additional nonnegative orthogonal component monotonically
improves squared alignment when the total credit energy is positive.  This is
one useful sufficient hypothesis replacing unconditional cosine monotonicity.
-/
theorem orthogonalCapturedFraction_mono
    {captured added remaining : ℝ}
    (captured_pos : 0 < captured) (added_nonneg : 0 ≤ added)
    (remaining_nonneg : 0 ≤ remaining) :
    orthogonalCapturedFraction captured (added + remaining) ≤
      orthogonalCapturedFraction (captured + added) remaining := by
  have denominator_pos : 0 < captured + added + remaining := by
    positivity
  rw [orthogonalCapturedFraction, orthogonalCapturedFraction]
  rw [show captured + (added + remaining) = captured + added + remaining by ring]
  exact (div_le_div_iff_of_pos_right denominator_pos).2 (by linarith)

/-! ## Per-block nondimensional schedules -/

/-- Choose a scalar residual schedule by specifying its desired signed
one-step contraction factor. -/
def scheduleForResidualFactor
    (precision factor : ℝ) (sweeps : ℕ) : ScalarResidualSchedule where
  rate := (1 - factor) / precision
  precision := precision
  sweeps := sweeps

theorem scheduleForResidualFactor_residualFactor
    (precision factor : ℝ) (sweeps : ℕ) (precision_ne : precision ≠ 0) :
    (scheduleForResidualFactor precision factor sweeps).residualFactor = factor := by
  simp [scheduleForResidualFactor, ScalarResidualSchedule.residualFactor, precision_ne]

theorem scheduleForResidualFactor_finiteResponse
    (precision factor : ℝ) (sweeps : ℕ) (precision_ne : precision ≠ 0) :
    (scheduleForResidualFactor precision factor sweeps).finiteResponse =
      1 - factor ^ sweeps := by
  change 1 -
      (scheduleForResidualFactor precision factor sweeps).residualFactor ^ sweeps =
    1 - factor ^ sweeps
  rw [scheduleForResidualFactor_residualFactor precision factor sweeps precision_ne]

/-- The scalar rate that gives residual factor one half at AC's terminal
precision `125` is `1/250 = 0.004`, not `0.05`.  This remains only a scalar
candidate until the task and recurrent curvature are certified. -/
theorem ac_terminal_half_factor_candidate :
    (scheduleForResidualFactor 125 (1 / 2) 8).rate = 1 / 250 ∧
      (scheduleForResidualFactor 125 (1 / 2) 8).residualFactor = 1 / 2 ∧
      (scheduleForResidualFactor 125 (1 / 2) 8).finiteResponse = 255 / 256 := by
  norm_num [scheduleForResidualFactor, ScalarResidualSchedule.residualFactor,
    ScalarResidualSchedule.finiteResponse]

/-- A per-stage scalar candidate that equalizes the residual-only one-step
factor at one half while retaining each registered sweep count. -/
def acStageHalfFactorSchedule (stage : ACStage) : ScalarResidualSchedule :=
  scheduleForResidualFactor stage.schedule.precision (1 / 2)
    stage.schedule.sweeps

/-- Exact candidate rates for all five registered AC stages.  These are not
nonlinear-network licenses: task and recurrent curvature still have to pass
the regional preconditioned certificate. -/
theorem acStage_halfFactor_candidate_rates :
    (acStageHalfFactorSchedule ACStage.ignition).rate = 3 / 20000 ∧
      (acStageHalfFactorSchedule ACStage.twoStep).rate = 1 / 1000 ∧
      (acStageHalfFactorSchedule ACStage.fourStep).rate = 1 / 500 ∧
      (acStageHalfFactorSchedule ACStage.fiveStep).rate = 1 / 400 ∧
      (acStageHalfFactorSchedule ACStage.eightStep).rate = 1 / 250 := by
  norm_num [acStageHalfFactorSchedule, scheduleForResidualFactor,
    ACStage.schedule]

/-- Every half-factor candidate has the requested signed residual factor. -/
theorem acStageHalfFactorSchedule_residualFactor (stage : ACStage) :
    (acStageHalfFactorSchedule stage).residualFactor = 1 / 2 := by
  apply scheduleForResidualFactor_residualFactor
  cases stage <;> norm_num [ACStage.schedule]

#print axioms orderedSweepCredit_eq_backpropChainCredit
#print axioms synchronousCredit_eq_zero_of_time_lt_depth
#print axioms synchronousCredit_diagonal_eq_backprop
#print axioms exact_nonzero_credit_requires_depth_phases
#print axioms coarseTerminalEnergy_hasDerivAt_initial
#print axioms liftedResidual_eq_of_incident_eq
#print axioms liftedMatchingEnergy_has_nonzero_zero_direction
#print axioms liftedChainEnergy_trajectory_eq_coarse
#print axioms twoSegmentFineEnergy_eq_condensed_add_square
#print axioms abs_twoSegment_midpointGradient_le_local
#print axioms condensed_fine_energy_ne_naive_coarse_energy
#print axioms condensation_can_change_parameter_stationarity
#print axioms equal_product_norm_different_condition
#print axioms equal_depth_product_norm_different_condition
#print axioms sweep_completeness_cosine_not_monotone
#print axioms orthogonalCapturedFraction_mono
#print axioms ac_terminal_half_factor_candidate
#print axioms acStage_halfFactor_candidate_rates

end

end ShootingStructure

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
