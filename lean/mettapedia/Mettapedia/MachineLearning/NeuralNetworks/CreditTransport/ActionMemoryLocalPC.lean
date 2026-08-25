import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DirectionalTaskDescent
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.TransportedDirectionAlignment
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteSolverSubstitution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Local predictive coding for the routed action-memory reasoner

This module owns the exact-real semantics used by the two-node active/evidence
reasoner.  The runtime uses the same scalar cross-couplings independently in
each hidden coordinate.  We first prove the scalar block-maximum contraction;
the coordinatewise result follows without a width-dependent constant.

The local-credit section separates three objects that are easy to conflate:
the matched BP task gradient, raw finite-settling PC credit, and the direction
actually transported to the parameters.  Admission controls direction and
scale and then delegates finite task descent to the existing directional
upper-model theorem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace ActionMemoryLocalPC

noncomputable section

open DirectionalTaskDescent
open TransportedDirectionAlignment

/-! ## Exact two-node nonlinear reasoner -/

/-- One hidden coordinate of the runtime's active/evidence state. -/
@[ext] structure TwoNodeState where
  active : ℝ
  evidence : ℝ
deriving DecidableEq

/-- Block-maximum distance used by the runtime contraction calculation. -/
def blockDistance (left right : TwoNodeState) : ℝ :=
  max |left.active - right.active| |left.evidence - right.evidence|

/-- The undamped mutually coupled map, with drives fixed by the routed input. -/
def candidateMap (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (state : TwoNodeState) : TwoNodeState where
  active := Real.tanh (activeDrive + activeCoupling * state.evidence)
  evidence := Real.tanh (evidenceDrive + evidenceCoupling * state.active)

/-- The actual convexly damped runtime iteration. -/
def dampedMap (damping activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (state : TwoNodeState) : TwoNodeState :=
  let candidate := candidateMap activeDrive evidenceDrive activeCoupling
    evidenceCoupling state
  { active := (1 - damping) * state.active + damping * candidate.active
    evidence := (1 - damping) * state.evidence + damping * candidate.evidence }

/-- The exact upper bound reported by the Python runtime. -/
def contractionFactor (damping activeCoupling evidenceCoupling : ℝ) : ℝ :=
  (1 - damping) + damping * max |activeCoupling| |evidenceCoupling|

/-- Runtime initialization before either the feedforward pass or recurrent
refinement. -/
def initialState (activeDrive evidenceDrive : ℝ) : TwoNodeState where
  active := Real.tanh activeDrive
  evidence := Real.tanh evidenceDrive

/-- The capacity-matched feedforward cell.  Its evidence node reads the
initial active prediction, then its active node reads that updated evidence.
There is no edge from the final active state back into evidence. -/
def feedforwardState
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ) :
    TwoNodeState :=
  let initial := initialState activeDrive evidenceDrive
  let evidence :=
    Real.tanh (evidenceDrive + evidenceCoupling * initial.active)
  { active := Real.tanh (activeDrive + activeCoupling * evidence)
    evidence := evidence }

theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hquotient := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  have hfunction : Real.tanh = Real.sinh / Real.cosh := by
    funext value
    simpa only [Pi.div_apply] using Real.tanh_eq_sinh_div_cosh value
  rw [hfunction]
  apply hquotient.congr_deriv
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem abs_tanh_derivative_le_one (x : ℝ) :
    |1 / Real.cosh x ^ 2| ≤ 1 := by
  have hcosh : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hsq : 1 ≤ Real.cosh x ^ 2 := by nlinarith
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / Real.cosh x ^ 2)]
  exact (div_le_one (by positivity)).2 hsq

/-- `tanh` is globally one-Lipschitz; no regional activation bound is hidden
in the reasoner certificate. -/
theorem tanh_sub_le (left right : ℝ) :
    |Real.tanh left - Real.tanh right| ≤ |left - right| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.tanh) (s := Set.univ) (x := right) (y := left) (C := (1 : ℝ))
    (fun value _ => (hasDerivAt_tanh value).differentiableAt)
    (fun value _ => by
      rw [(hasDerivAt_tanh value).deriv, Real.norm_eq_abs]
      exact abs_tanh_derivative_le_one value)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa [Real.norm_eq_abs] using h

theorem candidate_active_difference_le
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (left right : TwoNodeState) :
    |(candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).active -
        (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).active| ≤
      |activeCoupling| * blockDistance left right := by
  calc
    _ ≤ |(activeDrive + activeCoupling * left.evidence) -
          (activeDrive + activeCoupling * right.evidence)| :=
      tanh_sub_le _ _
    _ = |activeCoupling| * |left.evidence - right.evidence| := by
      rw [show (activeDrive + activeCoupling * left.evidence) -
          (activeDrive + activeCoupling * right.evidence) =
          activeCoupling * (left.evidence - right.evidence) by ring, abs_mul]
    _ ≤ |activeCoupling| * blockDistance left right := by
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _)

theorem candidate_evidence_difference_le
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (left right : TwoNodeState) :
    |(candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).evidence -
        (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).evidence| ≤
      |evidenceCoupling| * blockDistance left right := by
  calc
    _ ≤ |(evidenceDrive + evidenceCoupling * left.active) -
          (evidenceDrive + evidenceCoupling * right.active)| :=
      tanh_sub_le _ _
    _ = |evidenceCoupling| * |left.active - right.active| := by
      rw [show (evidenceDrive + evidenceCoupling * left.active) -
          (evidenceDrive + evidenceCoupling * right.active) =
          evidenceCoupling * (left.active - right.active) by ring, abs_mul]
    _ ≤ |evidenceCoupling| * blockDistance left right := by
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _)

/-- The two scalar cross-couplings control the undamped block map, independent
of hidden width. -/
theorem candidateMap_contracts
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (left right : TwoNodeState) :
    blockDistance
        (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left)
        (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right) ≤
      max |activeCoupling| |evidenceCoupling| * blockDistance left right := by
  apply max_le
  · exact (candidate_active_difference_le activeDrive evidenceDrive activeCoupling
      evidenceCoupling left right).trans <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by
        exact (abs_nonneg _).trans (le_max_left _ _))
  · exact (candidate_evidence_difference_le activeDrive evidenceDrive activeCoupling
      evidenceCoupling left right).trans <|
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by
        exact (abs_nonneg _).trans (le_max_left _ _))

/-- Damping gives exactly the runtime factor `(1-d)+d*kappa`. -/
theorem dampedMap_contracts
    {damping : ℝ} (hdamping0 : 0 ≤ damping) (hdamping1 : damping ≤ 1)
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (left right : TwoNodeState) :
    blockDistance
        (dampedMap damping activeDrive evidenceDrive activeCoupling evidenceCoupling left)
        (dampedMap damping activeDrive evidenceDrive activeCoupling evidenceCoupling right) ≤
      contractionFactor damping activeCoupling evidenceCoupling *
        blockDistance left right := by
  let κ := max |activeCoupling| |evidenceCoupling|
  have hκ : 0 ≤ κ := (abs_nonneg _).trans (le_max_left _ _)
  have hcandidate := candidateMap_contracts activeDrive evidenceDrive
    activeCoupling evidenceCoupling left right
  apply max_le
  · calc
      _ = |(1 - damping) * (left.active - right.active) +
          damping *
            ((candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).active -
             (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).active)| := by
        simp only [dampedMap]
        congr 1
        ring
      _ ≤ |1 - damping| * |left.active - right.active| +
          |damping| *
            |(candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).active -
             (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).active| := by
        simpa [abs_mul] using abs_add_le
          ((1 - damping) * (left.active - right.active))
          (damping *
            ((candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).active -
             (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).active))
      _ ≤ (1 - damping) * blockDistance left right +
          damping * (κ * blockDistance left right) := by
        rw [abs_of_nonneg hdamping0, abs_of_nonneg (sub_nonneg.mpr hdamping1)]
        gcongr
        · exact le_max_left _ _
        · exact candidate_active_difference_le activeDrive evidenceDrive
            activeCoupling evidenceCoupling left right |>.trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (by
                exact (abs_nonneg _).trans (le_max_left _ _)))
      _ = contractionFactor damping activeCoupling evidenceCoupling *
          blockDistance left right := by
        simp [contractionFactor, κ]
        ring
  · calc
      _ = |(1 - damping) * (left.evidence - right.evidence) +
          damping *
            ((candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).evidence -
             (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).evidence)| := by
        simp only [dampedMap]
        congr 1
        ring
      _ ≤ |1 - damping| * |left.evidence - right.evidence| +
          |damping| *
            |(candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).evidence -
             (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).evidence| := by
        simpa [abs_mul] using abs_add_le
          ((1 - damping) * (left.evidence - right.evidence))
          (damping *
            ((candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling left).evidence -
             (candidateMap activeDrive evidenceDrive activeCoupling evidenceCoupling right).evidence))
      _ ≤ (1 - damping) * blockDistance left right +
          damping * (κ * blockDistance left right) := by
        rw [abs_of_nonneg hdamping0, abs_of_nonneg (sub_nonneg.mpr hdamping1)]
        gcongr
        · exact le_max_right _ _
        · exact candidate_evidence_difference_le activeDrive evidenceDrive
            activeCoupling evidenceCoupling left right |>.trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by
                exact (abs_nonneg _).trans (le_max_left _ _)))
      _ = contractionFactor damping activeCoupling evidenceCoupling *
          blockDistance left right := by
        simp [contractionFactor, κ]
        ring

/-- The bounded `tanh` parameterization used by Python makes both effective
couplings strictly smaller than the configured limit. -/
theorem boundedCoupling_lt
    {limit raw : ℝ} (hlimit : 0 < limit) :
    |limit * Real.tanh raw| < limit := by
  rw [abs_mul, abs_of_pos hlimit]
  nlinarith [Real.abs_tanh_lt_one raw]

/-- The registered default values imply the reported `0.6` strict factor. -/
theorem registered_default_contraction :
    contractionFactor (1 / 2) (1 / 5) (1 / 5) = 3 / 5 ∧
      contractionFactor (1 / 2) (1 / 5) (1 / 5) < 1 := by
  norm_num [contractionFactor]

/-! ## Existence and uniqueness of the equilibrium -/

/-- Product presentation used only to invoke the Banach fixed-point theorem.
The runtime-facing state remains `TwoNodeState`. -/
def pairDampedMap
    (damping activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (state : ℝ × ℝ) : ℝ × ℝ :=
  let next := dampedMap damping activeDrive evidenceDrive activeCoupling
    evidenceCoupling { active := state.1, evidence := state.2 }
  (next.active, next.evidence)

theorem pairDampedMap_contracting
    {damping : ℝ} (hdamping0 : 0 ≤ damping) (hdamping1 : damping ≤ 1)
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (hfactor0 : 0 ≤ contractionFactor damping activeCoupling evidenceCoupling)
    (hfactor1 : contractionFactor damping activeCoupling evidenceCoupling < 1) :
    ContractingWith
      ⟨contractionFactor damping activeCoupling evidenceCoupling, hfactor0⟩
      (pairDampedMap damping activeDrive evidenceDrive activeCoupling
        evidenceCoupling) := by
  constructor
  · exact_mod_cast hfactor1
  · apply LipschitzWith.of_dist_le_mul
    intro left right
    change dist
        (pairDampedMap damping activeDrive evidenceDrive activeCoupling
          evidenceCoupling left)
        (pairDampedMap damping activeDrive evidenceDrive activeCoupling
          evidenceCoupling right) ≤
      contractionFactor damping activeCoupling evidenceCoupling * dist left right
    simpa [pairDampedMap, Prod.dist_eq, Real.dist_eq, blockDistance] using
      dampedMap_contracts hdamping0 hdamping1 activeDrive evidenceDrive
        activeCoupling evidenceCoupling
        { active := left.1, evidence := left.2 }
        { active := right.1, evidence := right.2 }

/-- Under the declared strict contraction certificate, the exact nonlinear
two-node runtime has one and only one equilibrium. -/
theorem dampedMap_existsUnique_equilibrium
    {damping : ℝ} (hdamping0 : 0 ≤ damping) (hdamping1 : damping ≤ 1)
    (activeDrive evidenceDrive activeCoupling evidenceCoupling : ℝ)
    (hfactor0 : 0 ≤ contractionFactor damping activeCoupling evidenceCoupling)
    (hfactor1 : contractionFactor damping activeCoupling evidenceCoupling < 1) :
    ∃! state : TwoNodeState,
      dampedMap damping activeDrive evidenceDrive activeCoupling evidenceCoupling
        state = state := by
  let factor : NNReal :=
    ⟨contractionFactor damping activeCoupling evidenceCoupling, hfactor0⟩
  let step := pairDampedMap damping activeDrive evidenceDrive activeCoupling
    evidenceCoupling
  have hcontracting : ContractingWith factor step := by
    exact pairDampedMap_contracting hdamping0 hdamping1 activeDrive evidenceDrive
      activeCoupling evidenceCoupling hfactor0 hfactor1
  obtain ⟨target, htarget, _converges, _bound⟩ :=
    hcontracting.exists_fixedPoint (0, 0) (edist_ne_top _ _)
  let state : TwoNodeState := { active := target.1, evidence := target.2 }
  refine ⟨state, ?_, ?_⟩
  · apply TwoNodeState.ext
    · exact congrArg Prod.fst htarget
    · exact congrArg Prod.snd htarget
  · intro other hother
    have hdistance := dampedMap_contracts hdamping0 hdamping1 activeDrive
      evidenceDrive activeCoupling evidenceCoupling other state
    have hstate :
        dampedMap damping activeDrive evidenceDrive activeCoupling
          evidenceCoupling state = state := by
      apply TwoNodeState.ext
      · exact congrArg Prod.fst htarget
      · exact congrArg Prod.snd htarget
    rw [hother, hstate] at hdistance
    have hzero : blockDistance other state = 0 := by
      by_contra hne
      have hpositive : 0 < blockDistance other state := by
        have hnonneg : 0 ≤ blockDistance other state :=
          (abs_nonneg _).trans (le_max_left _ _)
        exact lt_of_le_of_ne hnonneg (Ne.symm hne)
      have hstrict :
          contractionFactor damping activeCoupling evidenceCoupling *
              blockDistance other state < blockDistance other state := by
        simpa using mul_lt_mul_of_pos_right hfactor1 hpositive
      exact (not_lt_of_ge hdistance) hstrict
    apply TwoNodeState.ext
    · have hactive : |other.active - state.active| = 0 := by
        apply le_antisymm
        · exact (le_max_left _ _).trans_eq hzero
        · exact abs_nonneg _
      exact sub_eq_zero.mp (abs_eq_zero.mp hactive)
    · have hevidence : |other.evidence - state.evidence| = 0 := by
        apply le_antisymm
        · exact (le_max_right _ _).trans_eq hzero
        · exact abs_nonneg _
      exact sub_eq_zero.mp (abs_eq_zero.mp hevidence)

/-! ## Finite iteration and readout transport -/

def iterateState
    (step : TwoNodeState → TwoNodeState) : ℕ → TwoNodeState → TwoNodeState
  | 0, state => state
  | time + 1, state => step (iterateState step time state)

/-- The equilibrium cell reuses the mutually coupled damped map from the same
parameter-matched initialization. -/
def equilibriumFiniteState
    (steps : ℕ) (damping activeDrive evidenceDrive activeCoupling
      evidenceCoupling : ℝ) : TwoNodeState :=
  iterateState
    (dampedMap damping activeDrive evidenceDrive activeCoupling
      evidenceCoupling)
    steps (initialState activeDrive evidenceDrive)

theorem feedforwardState_zeroCoupling
    (activeDrive evidenceDrive : ℝ) :
    feedforwardState activeDrive evidenceDrive 0 0 =
      initialState activeDrive evidenceDrive := by
  ext <;> simp [feedforwardState, initialState]

theorem equilibriumFiniteState_zeroCoupling_oneStep
    (activeDrive evidenceDrive : ℝ) :
    equilibriumFiniteState 1 1 activeDrive evidenceDrive 0 0 =
      initialState activeDrive evidenceDrive := by
  ext <;> simp [equilibriumFiniteState, iterateState, dampedMap, candidateMap,
    initialState]

/-- Equal parameter names and values do not make the two dynamics identical:
the feedforward evidence node is frozen after its first parent read, whereas
the recurrent map may update it from the new active state. -/
theorem feedforward_and_equilibrium_maps_can_differ :
    let activeDrive : ℝ := 1 / 2
    let evidenceDrive : ℝ := 1 / 4
    let coupling : ℝ := 1 / 5
    let feedforward := feedforwardState activeDrive evidenceDrive coupling coupling
    candidateMap activeDrive evidenceDrive coupling coupling feedforward ≠
      feedforward := by
  dsimp
  intro equality
  have hevidence := congrArg TwoNodeState.evidence equality
  simp only [candidateMap, feedforwardState, initialState] at hevidence
  have hinjective := Real.tanh_injective hevidence
  have hactiveNe :
      Real.tanh
          (1 / 2 + 1 / 5 *
            Real.tanh (1 / 4 + 1 / 5 * Real.tanh (1 / 2))) ≠
        Real.tanh (1 / 2) := by
    intro hactive
    have harg := Real.tanh_injective hactive
    have hinner :
        Real.tanh (1 / 4 + 1 / 5 * Real.tanh (1 / 2)) ≠ 0 := by
      intro hzero
      have hzeroArg :
          (1 / 4 + 1 / 5 * Real.tanh (1 / 2) : ℝ) = 0 :=
        Real.tanh_injective (by simpa using hzero)
      have htanhLower := Real.neg_one_lt_tanh (1 / 2 : ℝ)
      nlinarith
    apply hinner
    nlinarith
  apply hactiveNe
  nlinarith [hinjective]

theorem iterateState_error_le_pow
    (step : TwoNodeState → TwoNodeState) (target initial : TwoNodeState)
    {factor : ℝ} (hfactor : 0 ≤ factor)
    (hstep : ∀ left right,
      blockDistance (step left) (step right) ≤
        factor * blockDistance left right)
    (hfixed : step target = target) (time : ℕ) :
    blockDistance (iterateState step time initial) target ≤
      factor ^ time * blockDistance initial target := by
  induction time with
  | zero => simp [iterateState]
  | succ time ih =>
      rw [iterateState]
      calc
        blockDistance (step (iterateState step time initial)) target =
            blockDistance (step (iterateState step time initial)) (step target) := by
          rw [hfixed]
        _ ≤
            factor * blockDistance (iterateState step time initial) target :=
          hstep _ _
        _ ≤ factor * (factor ^ time * blockDistance initial target) :=
          mul_le_mul_of_nonneg_left ih hfactor
        _ = factor ^ (time + 1) * blockDistance initial target := by
          rw [pow_succ]
          ring

/-- A scalar linear readout transports the finite state error without adding
an unregistered width factor. -/
theorem linearReadout_error_le
    (weight : ℝ) (left right : TwoNodeState) :
    |weight * left.active - weight * right.active| ≤
      |weight| * blockDistance left right := by
  rw [← mul_sub, abs_mul]
  gcongr
  exact le_max_left _ _

/-- Finite settling plus a scalar readout gives the exact geometric bound
consumed by the local-credit certificate. -/
theorem finiteReadout_error_le_pow
    (step : TwoNodeState → TwoNodeState) (target initial : TwoNodeState)
    {factor : ℝ} (hfactor : 0 ≤ factor)
    (hstep : ∀ left right,
      blockDistance (step left) (step right) ≤
        factor * blockDistance left right)
    (hfixed : step target = target) (weight : ℝ) (time : ℕ) :
    |weight * (iterateState step time initial).active - weight * target.active| ≤
      |weight| * (factor ^ time * blockDistance initial target) := by
  exact (linearReadout_error_le weight _ _).trans <|
    mul_le_mul_of_nonneg_left
      (iterateState_error_le_pow step target initial hfactor hstep hfixed time)
      (abs_nonneg weight)

/-! ## Gate and route boundaries -/

def gatedLegalLogit
    (base residual gate : ℝ) (route legal : Bool) : ℝ :=
  if route && legal then base + gate * residual else base

@[simp] theorem gatedLegalLogit_gate_zero
    (base residual : ℝ) (route legal : Bool) :
    gatedLegalLogit base residual 0 route legal = base := by
  simp [gatedLegalLogit]

@[simp] theorem gatedLegalLogit_no_route
    (base residual gate : ℝ) (legal : Bool) :
    gatedLegalLogit base residual gate false legal = base := by
  simp [gatedLegalLogit]

@[simp] theorem gatedLegalLogit_illegal
    (base residual gate : ℝ) (route : Bool) :
    gatedLegalLogit base residual gate route false = base := by
  simp [gatedLegalLogit]

/-! ## Direction-and-scale admission -/

open scoped InnerProductSpace

structure CreditAdmission (Parameter : Type*)
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] where
  bp : Parameter
  raw : Parameter
  transported : Parameter
  cosineFloor : ℝ
  minimumNormRatio : ℝ
  maximumNormRatio : ℝ
  numericalError : ℝ
  numericalError_nonneg : 0 ≤ numericalError
  bp_nonzero : ‖bp‖ ≠ 0
  raw_nonzero : ‖raw‖ ≠ 0
  transported_nonzero : ‖transported‖ ≠ 0
  raw_cosine_floor :
    cosineFloor * (‖raw‖ * ‖bp‖) ≤ ⟪bp, raw⟫_ℝ
  transported_alignment_pos : 0 < ⟪bp, transported⟫_ℝ
  transported_norm_lower : minimumNormRatio * ‖bp‖ ≤ ‖transported‖
  transported_norm_upper : ‖transported‖ ≤ maximumNormRatio * ‖bp‖

theorem CreditAdmission.raw_inner_pos
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (certificate : CreditAdmission Parameter)
    (hfloor : 0 < certificate.cosineFloor) :
    0 < ⟪certificate.bp, certificate.raw⟫_ℝ := by
  have hnorms : 0 < ‖certificate.raw‖ * ‖certificate.bp‖ :=
    mul_pos (lt_of_le_of_ne (norm_nonneg _) certificate.raw_nonzero.symm)
      (lt_of_le_of_ne (norm_nonneg _) certificate.bp_nonzero.symm)
  exact lt_of_lt_of_le (mul_pos hfloor hnorms) certificate.raw_cosine_floor

/-- The certificate's transported direction plugs directly into the existing
finite-step descent theorem; cosine telemetry alone is not used as the proof. -/
theorem CreditAdmission.strictTaskDescent
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (certificate : CreditAdmission Parameter)
    {loss : Parameter → ℝ} {parameter : Parameter} {curvature step : ℝ}
    (upper : HasDirectionalTaskUpperModelAt loss parameter certificate.bp
      certificate.transported curvature)
    (hstep : 0 < step)
    (htrust : step * curvature / 2 <
      ⟪certificate.bp, certificate.transported⟫_ℝ) :
    loss (parameter - step • certificate.transported) < loss parameter := by
  exact directionalTask_strict_descent upper hstep htrust

/-! ## Positive and negative executable fixtures -/

abbrev FixturePlane := EuclideanSpace ℝ (Fin 2)

noncomputable def fixturePlane (first second : ℝ) : FixturePlane :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![first, second]

private theorem fixturePlane_norm_sq (vector : FixturePlane) :
    ‖vector‖ ^ 2 = vector 0 ^ 2 + vector 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

noncomputable def usefulNonBPAdmission : CreditAdmission FixturePlane where
  bp := fixturePlane 1 0
  raw := fixturePlane 1 1
  transported := fixturePlane 1 1
  cosineFloor := 1 / 2
  minimumNormRatio := 1 / 2
  maximumNormRatio := 2
  numericalError := 0
  numericalError_nonneg := by norm_num
  bp_nonzero := by
    intro h
    have hsquare := congrArg (fun value : ℝ => value ^ 2) h
    rw [fixturePlane_norm_sq] at hsquare
    norm_num [fixturePlane, WithLp.equiv] at hsquare
  raw_nonzero := by
    intro h
    have hsquare := congrArg (fun value : ℝ => value ^ 2) h
    rw [fixturePlane_norm_sq] at hsquare
    norm_num [fixturePlane, WithLp.equiv] at hsquare
  transported_nonzero := by
    intro h
    have hsquare := congrArg (fun value : ℝ => value ^ 2) h
    rw [fixturePlane_norm_sq] at hsquare
    norm_num [fixturePlane, WithLp.equiv] at hsquare
  raw_cosine_floor := by
    have hbp : ‖fixturePlane 1 0‖ ^ 2 = 1 := by
      rw [fixturePlane_norm_sq]
      norm_num [fixturePlane, WithLp.equiv]
    have hraw : ‖fixturePlane 1 1‖ ^ 2 = 2 := by
      rw [fixturePlane_norm_sq]
      norm_num [fixturePlane, WithLp.equiv]
    have hbp_nonneg : 0 ≤ ‖fixturePlane 1 0‖ := norm_nonneg _
    have hraw_nonneg : 0 ≤ ‖fixturePlane 1 1‖ := norm_nonneg _
    have hbp_le : ‖fixturePlane 1 0‖ ≤ 1 := by nlinarith
    have hraw_le : ‖fixturePlane 1 1‖ ≤ 2 := by nlinarith
    rw [show ⟪fixturePlane 1 0, fixturePlane 1 1⟫_ℝ = 1 by
      norm_num [fixturePlane, WithLp.equiv, PiLp.inner_apply,
        Fin.sum_univ_two]]
    nlinarith
  transported_alignment_pos := by
    norm_num [fixturePlane, WithLp.equiv, PiLp.inner_apply,
      Fin.sum_univ_two]
  transported_norm_lower := by
    have hbp : ‖fixturePlane 1 0‖ ^ 2 = 1 := by
      rw [fixturePlane_norm_sq]
      norm_num [fixturePlane, WithLp.equiv]
    have hraw : ‖fixturePlane 1 1‖ ^ 2 = 2 := by
      rw [fixturePlane_norm_sq]
      norm_num [fixturePlane, WithLp.equiv]
    nlinarith [norm_nonneg (fixturePlane 1 0), norm_nonneg (fixturePlane 1 1)]
  transported_norm_upper := by
    have hbp : ‖fixturePlane 1 0‖ ^ 2 = 1 := by
      rw [fixturePlane_norm_sq]
      norm_num [fixturePlane, WithLp.equiv]
    have hraw : ‖fixturePlane 1 1‖ ^ 2 = 2 := by
      rw [fixturePlane_norm_sq]
      norm_num [fixturePlane, WithLp.equiv]
    nlinarith [norm_nonneg (fixturePlane 1 0), norm_nonneg (fixturePlane 1 1)]

theorem usefulNonBPAdmission_is_not_bp :
    usefulNonBPAdmission.raw ≠ usefulNonBPAdmission.bp := by
  intro h
  have := congrArg (fun vector : FixturePlane => vector 1) h
  norm_num [usefulNonBPAdmission, fixturePlane, WithLp.equiv] at this

/-- Perfect cosine cannot replace the norm-ratio gate. -/
theorem highCosine_wrongScale_fails_norm_floor :
    let bp : FixturePlane := fixturePlane 1 0
    let tiny : FixturePlane := fixturePlane (1 / 1000) 0
    ⟪bp, tiny⟫_ℝ = ‖bp‖ * ‖tiny‖ ∧
      ¬ (1 / 10 : ℝ) * ‖bp‖ ≤ ‖tiny‖ := by
  dsimp
  have hbp : ‖fixturePlane 1 0‖ ^ 2 = 1 := by
    rw [fixturePlane_norm_sq]
    norm_num [fixturePlane, WithLp.equiv]
  have htiny : ‖fixturePlane (1 / 1000) 0‖ ^ 2 = (1 / 1000 : ℝ) ^ 2 := by
    rw [fixturePlane_norm_sq]
    norm_num [fixturePlane, WithLp.equiv]
  have hbpNorm : ‖fixturePlane 1 0‖ = 1 := by
    nlinarith [norm_nonneg (fixturePlane 1 0)]
  have htinyNorm : ‖fixturePlane (1 / 1000) 0‖ = 1 / 1000 := by
    nlinarith [norm_nonneg (fixturePlane (1 / 1000) 0)]
  rw [hbpNorm, htinyNorm]
  constructor
  · norm_num [fixturePlane, WithLp.equiv, PiLp.inner_apply,
      Fin.sum_univ_two]
  · norm_num

/-- Recurrence genuinely changes the finite output in a contractive fixture. -/
theorem recurrence_changes_finite_output :
    let driveA : ℝ := 1 / 2
    let driveE : ℝ := 1 / 4
    let coupling : ℝ := 1 / 5
    let initial : TwoNodeState :=
      { active := Real.tanh driveA, evidence := Real.tanh driveE }
    candidateMap driveA driveE coupling coupling initial ≠ initial := by
  dsimp
  intro h
  have hactive := congrArg TwoNodeState.active h
  simp only [candidateMap] at hactive
  have hstrict := Real.tanh_injective hactive
  have hnonzero : Real.tanh (1 / 4 : ℝ) ≠ 0 := by
    intro hzero
    have : (1 / 4 : ℝ) = 0 := Real.tanh_injective (by simpa using hzero)
    norm_num at this
  apply hnonzero
  nlinarith

#print axioms tanh_sub_le
#print axioms dampedMap_contracts
#print axioms dampedMap_existsUnique_equilibrium
#print axioms boundedCoupling_lt
#print axioms iterateState_error_le_pow
#print axioms finiteReadout_error_le_pow
#print axioms CreditAdmission.strictTaskDescent
#print axioms usefulNonBPAdmission_is_not_bp
#print axioms highCosine_wrongScale_fails_norm_floor
#print axioms recurrence_changes_finite_output

end

end ActionMemoryLocalPC
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
