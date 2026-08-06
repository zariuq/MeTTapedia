import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.Dynamics
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.OperatorStability
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.PreconditionedLearning
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.EntropyTurnover
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.TrainedNonlinearTurnover

/-!
# Linear workspace settling transported from the predictive-coding spine

The contraction and depth-turnover results in this file are linear-model
statements.  They do not claim that a trained nonlinear workspace decoder has
the same spectrum, reaches the same target, or exhibits the same optimum.

Transport accounting:

* `linearWorkspace_geometricRate` and `linearWorkspace_tendsto_equilibrium`
  lift `OperatorStability` through an exact affine-residual identity.
* `finiteDepthMismatch_*` lifts the exact target/away readout laws from
  `EntropyTurnover` and adds the loss-optimum packaging needed by the prereg.
* `PreconditionedLearning` is the residual-operator ancestor imported by
  `OperatorStability`; no second preconditioner theorem is copied here.
* `TrainedNonlinearTurnover` supplies the explicit nonlinear scope boundary;
  none of its trained-model conclusions is generalized to workspace decoders.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Filter Function Set Topology
open scoped ENNReal NNReal
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

universe uState

/-! ## Affine linear settling -/

/-- A linear workspace settling model on a complex Banach state space.  Its
step is the affine map `x ↦ L x + b`; this structure makes no nonlinear or
neural-network training claim. -/
structure LinearWorkspaceModel (State : Type uState)
    [NormedAddCommGroup State] [NormedSpace ℂ State] where
  linearPart : State →L[ℂ] State
  bias : State

namespace LinearWorkspaceModel

variable {State : Type uState} [NormedAddCommGroup State] [NormedSpace ℂ State]
  (model : LinearWorkspaceModel State)

/-- The affine linear workspace step.  All settling theorems about this map
below remain confined to the linear model. -/
noncomputable def step (state : State) : State :=
  model.linearPart state + model.bias

/-- The candidate linear equilibrium obtained by applying the ring inverse of
`I - L` to the bias.  It is certified as an equilibrium only under the explicit
spectral condition below. -/
noncomputable def equilibrium : State :=
  Ring.inverse (1 - model.linearPart) model.bias

/-- Spectral radius below one makes `I - L` a unit.  This is a direct spectrum
bridge for the linear model, not an assertion about nonlinear Jacobians. -/
theorem one_sub_linearPart_isUnit
    [CompleteSpace State] [Nontrivial State]
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    IsUnit (1 - model.linearPart) := by
  have hresolvent : (1 : ℂ) ∈ resolventSet ℂ model.linearPart :=
    spectrum.mem_resolventSet_of_spectralRadius_lt (by simpa using hradius)
  simpa [resolventSet] using hresolvent

/-- Under the explicit spectral condition, the constructed point is an actual
fixed point of the affine linear workspace step. -/
theorem equilibrium_isFixedPt
    [CompleteSpace State] [Nontrivial State]
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    IsFixedPt model.step model.equilibrium := by
  let departure : State →L[ℂ] State := 1 - model.linearPart
  have hunit : IsUnit departure := by
    simpa [departure] using model.one_sub_linearPart_isUnit hradius
  have hcancel : departure * Ring.inverse departure = 1 :=
    Ring.mul_inverse_cancel departure hunit
  have happ := congrArg (fun operator : State →L[ℂ] State => operator model.bias) hcancel
  have hdeparture :
      departure (Ring.inverse departure model.bias) = model.bias := by
    simpa [mul_apply_eq_comp] using happ
  have hdeparture' :
      Ring.inverse departure model.bias -
        model.linearPart (Ring.inverse departure model.bias) = model.bias := by
    simpa [departure] using hdeparture
  change model.linearPart (Ring.inverse (1 - model.linearPart) model.bias) + model.bias =
    Ring.inverse (1 - model.linearPart) model.bias
  change model.linearPart (Ring.inverse departure model.bias) + model.bias =
    Ring.inverse departure model.bias
  calc
    model.linearPart (Ring.inverse departure model.bias) + model.bias =
        model.linearPart (Ring.inverse departure model.bias) +
          (Ring.inverse departure model.bias -
            model.linearPart (Ring.inverse departure model.bias)) :=
      congrArg (fun value =>
        model.linearPart (Ring.inverse departure model.bias) + value) hdeparture'.symm
    _ = Ring.inverse departure model.bias := by abel

/-- One affine step transports residual from equilibrium by exactly `L`.  This
is new workspace algebra; the subsequent rate theorem is the PC-spine lift. -/
theorem step_sub_equilibrium
    [CompleteSpace State] [Nontrivial State]
    (hradius : spectralRadius ℂ model.linearPart < 1) (state : State) :
    model.step state - model.equilibrium =
      model.linearPart (state - model.equilibrium) := by
  have hfixed := model.equilibrium_isFixedPt hradius
  rw [IsFixedPt] at hfixed
  simp only [step] at hfixed ⊢
  rw [map_sub]
  calc
    model.linearPart state + model.bias - model.equilibrium =
        model.linearPart state + model.bias -
          (model.linearPart model.equilibrium + model.bias) :=
      congrArg (fun value => model.linearPart state + model.bias - value) hfixed.symm
    _ = model.linearPart state - model.linearPart model.equilibrium := by abel

/-- At every finite recurrence depth, affine-workspace residual is exactly the
`operatorResidualIterate` already analyzed by the linear PC spine. -/
theorem iterate_step_sub_equilibrium
    [CompleteSpace State] [Nontrivial State]
    (hradius : spectralRadius ℂ model.linearPart < 1)
    (initial : State) (depth : ℕ) :
    (model.step^[depth] initial) - model.equilibrium =
      operatorResidualIterate model.linearPart
        (initial - model.equilibrium) depth := by
  induction depth with
  | zero => simp [operatorResidualIterate]
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      rw [model.step_sub_equilibrium hradius]
      rw [ih, operatorResidualIterate, operatorResidualIterate]
      rw [pow_succ', mul_apply_eq_comp]

/-- Crown, linear scope: spectral radius below one gives a unique affine
workspace equilibrium.  Existence uses the resolvent; uniqueness is transported
from full-spectrum PC residual convergence, including nonnormal operators. -/
theorem spectralCondition_uniqueEquilibrium
    [CompleteSpace State] [Nontrivial State]
    (hradius : spectralRadius ℂ model.linearPart < 1) :
    ∃! equilibrium : State, IsFixedPt model.step equilibrium := by
  refine ⟨model.equilibrium, model.equilibrium_isFixedPt hradius, ?_⟩
  intro other hother
  have hresidual :
      model.linearPart (other - model.equilibrium) =
        other - model.equilibrium := by
    have htransport := model.step_sub_equilibrium hradius other
    rw [hother.eq] at htransport
    exact htransport.symm
  have htendsto := operatorEigenmode_tendsto_zero_of_spectralRadius_lt_one
    model.linearPart (other - model.equilibrium) 1 (by simpa using hresidual) hradius
  have hconstant :
      Tendsto (fun _depth : ℕ => other - model.equilibrium)
        atTop (𝓝 (0 : State)) := by
    simpa using htendsto
  have hzero : other - model.equilibrium = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  exact sub_eq_zero.mp hzero

/-- Crown, linear scope: every rate `q` strictly above the spectral radius and
below one gives the PC spine's global geometric envelope for affine workspace
residuals, with the finite nonnormal transient absorbed into `C`. -/
theorem linearWorkspace_geometricRate
    [CompleteSpace State] [Nontrivial State]
    (initial : State) (q : ℝ≥0∞)
    (hradius_q : spectralRadius ℂ model.linearPart < q) (hq_one : q < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ depth : ℕ,
      ‖model.step^[depth] initial - model.equilibrium‖ ≤
        C * q.toReal ^ depth * ‖initial - model.equilibrium‖ := by
  have hradius : spectralRadius ℂ model.linearPart < 1 := hradius_q.trans hq_one
  obtain ⟨C, hC, hbound⟩ :=
    operatorResidualIterate_norm_geometricEnvelope
      model.linearPart (initial - model.equilibrium) q hradius_q hq_one
  refine ⟨C, hC, fun depth => ?_⟩
  rw [model.iterate_step_sub_equilibrium hradius]
  exact hbound depth

/-- Crown, linear scope: the affine workspace iteration converges to its unique
equilibrium whenever the linear part has spectral radius below one. -/
theorem linearWorkspace_tendsto_equilibrium
    [CompleteSpace State] [Nontrivial State]
    (initial : State) (hradius : spectralRadius ℂ model.linearPart < 1) :
    Tendsto (fun depth : ℕ => model.step^[depth] initial)
      atTop (𝓝 model.equilibrium) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hresidual := operatorResidualIterate_tendsto_zero_of_spectralRadius_lt_one
    model.linearPart (initial - model.equilibrium) hradius
  simpa only [model.iterate_step_sub_equilibrium hradius, norm_zero] using hresidual.norm

end LinearWorkspaceModel

/-! ## Finite-depth training/equilibrium mismatch -/

/-- Linear finite-depth evaluation loss: the exact PC shift-chain readout is
trained against a target at recurrence depth `trainingDepth`.  This is not a
loss theorem for nonlinear workspace decoders. -/
noncomputable def finiteDepthMismatchLoss
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ) : ℝ :=
  (arbitraryDepthTurnoverProbability trainingDepth target evaluationDepth - target) ^ 2

/-- Linear scope: at the registered training depth, the interior target is hit
exactly and the mismatch loss is zero. -/
theorem finiteDepthMismatchLoss_at_trainingDepth
    (trainingDepth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1) :
    finiteDepthMismatchLoss trainingDepth target trainingDepth = 0 := by
  rw [finiteDepthMismatchLoss,
    arbitraryDepthTurnoverProbability_at_target trainingDepth target htarget]
  ring

/-- Linear scope: at every other recurrence depth, the shift-chain readout is
uniform, so the mismatch loss is exactly `(1/2 - target)^2`. -/
theorem finiteDepthMismatchLoss_away_from_trainingDepth
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ)
    (hne : evaluationDepth ≠ trainingDepth) :
    finiteDepthMismatchLoss trainingDepth target evaluationDepth =
      (1 / 2 - target) ^ 2 := by
  rw [finiteDepthMismatchLoss,
    arbitraryDepthTurnoverProbability_away_from_target
      trainingDepth target evaluationDepth hne]

/-- Linear scope: a nonuniform target makes every off-depth mismatch loss
strictly positive.  The uniform target is the explicit negative boundary. -/
theorem finiteDepthMismatchLoss_pos_away
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ)
    (htarget : target ≠ 1 / 2) (hne : evaluationDepth ≠ trainingDepth) :
    0 < finiteDepthMismatchLoss trainingDepth target evaluationDepth := by
  rw [finiteDepthMismatchLoss_away_from_trainingDepth _ _ _ hne]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr htarget.symm)

/-- Prediction (a), derived in the linear model: the finite registered depth
`T* = trainingDepth` is the unique global minimizer of mismatch loss. -/
theorem finiteDepthMismatch_uniqueOptimum
    (trainingDepth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hnonuniform : target ≠ 1 / 2) :
    (∀ evaluationDepth,
      finiteDepthMismatchLoss trainingDepth target trainingDepth ≤
        finiteDepthMismatchLoss trainingDepth target evaluationDepth) ∧
    (∀ evaluationDepth,
      finiteDepthMismatchLoss trainingDepth target evaluationDepth =
        finiteDepthMismatchLoss trainingDepth target trainingDepth ↔
      evaluationDepth = trainingDepth) := by
  constructor
  · intro evaluationDepth
    rw [finiteDepthMismatchLoss_at_trainingDepth _ _ htarget]
    exact sq_nonneg _
  · intro evaluationDepth
    constructor
    · intro heq
      by_contra hne
      have hpos := finiteDepthMismatchLoss_pos_away
        trainingDepth target evaluationDepth hnonuniform hne
      rw [finiteDepthMismatchLoss_at_trainingDepth _ _ htarget] at heq
      linarith
    · rintro rfl
      rfl

/-- Prediction (a), derived in the linear model: every depth beyond `T*` is
strictly worse than the fitted finite depth. -/
theorem finiteDepthMismatch_overSettling_strictlyWorse
    (trainingDepth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hnonuniform : target ≠ 1 / 2) (evaluationDepth : ℕ)
    (hover : trainingDepth < evaluationDepth) :
    finiteDepthMismatchLoss trainingDepth target trainingDepth <
      finiteDepthMismatchLoss trainingDepth target evaluationDepth := by
  rw [finiteDepthMismatchLoss_at_trainingDepth _ _ htarget]
  exact finiteDepthMismatchLoss_pos_away trainingDepth target evaluationDepth
    hnonuniform (by omega)

/-- Linear scope: after the target impulse has passed the readout, the complete
finite-support shift-chain state is the zero equilibrium. -/
theorem finiteDepthTurnoverState_eq_equilibrium
    (trainingDepth : ℕ) (target : ℝ) (evaluationDepth : ℕ)
    (hover : trainingDepth < evaluationDepth) :
    arbitraryDepthTurnoverState trainingDepth target evaluationDepth = 0 := by
  funext index
  rw [arbitraryDepthTurnoverState, linearTurnoverShift_iterate_apply]
  simp [arbitraryDepthTurnoverInitialState]
  omega

/-- Linear scope: zero is an equilibrium of the PC shift operator. -/
theorem linearTurnover_zero_isFixedPt :
    IsFixedPt linearTurnoverShift (0 : LinearTurnoverChainState) := by
  rfl

/-- Crown for prereg prediction (a), linear scope only: finite-depth fitting is
exact, equilibrium evaluation is uniform and mismatched, and every over-settled
depth is strictly worse. -/
theorem finiteDepthMismatch_equilibrium
    (trainingDepth : ℕ) (target : ℝ) (htarget : target ∈ Ioo (0 : ℝ) 1)
    (hnonuniform : target ≠ 1 / 2) :
    finiteDepthMismatchLoss trainingDepth target trainingDepth = 0 ∧
      (∀ evaluationDepth, trainingDepth < evaluationDepth →
        arbitraryDepthTurnoverState trainingDepth target evaluationDepth = 0) ∧
      (∀ evaluationDepth, trainingDepth < evaluationDepth →
        finiteDepthMismatchLoss trainingDepth target trainingDepth <
          finiteDepthMismatchLoss trainingDepth target evaluationDepth) := by
  exact ⟨finiteDepthMismatchLoss_at_trainingDepth trainingDepth target htarget,
    fun evaluationDepth hover =>
      finiteDepthTurnoverState_eq_equilibrium trainingDepth target evaluationDepth hover,
    fun evaluationDepth hover =>
      finiteDepthMismatch_overSettling_strictlyWorse
        trainingDepth target htarget hnonuniform evaluationDepth hover⟩

/-! ## Machine-checked transport accounting -/

/-- The four sealed PC-spine sources required for provenance accounting.  The
ledger does not broaden any linear conclusion. -/
inductive PCSpineSource where
  | operatorStability
  | preconditionedLearning
  | entropyTurnover
  | trainedNonlinearTurnover
  deriving DecidableEq, Repr

/-- A direct theorem lift is separated from new workspace algebra and from an
explicit scope-boundary citation. -/
inductive TransportKind where
  | directLift
  | newWorkspaceContent
  | scopeBoundary
  deriving DecidableEq, Repr

/-- One auditable provenance entry for the linear settling crown. -/
structure TransportEntry where
  result : String
  source : Option PCSpineSource
  kind : TransportKind
  deriving DecidableEq, Repr

/-- Exhaustive accounting for the exported T2 crown results.  Zero direct
lifts from the preconditioner and nonlinear files are intentional and prevent
duplicate settling theory or nonlinear overclaiming. -/
def linearSettlingTransportLedger : List TransportEntry :=
  [ { result := "affine equilibrium existence", source := none,
      kind := .newWorkspaceContent },
    { result := "affine residual identity", source := none,
      kind := .newWorkspaceContent },
    { result := "unique equilibrium", source := some .operatorStability,
      kind := .directLift },
    { result := "geometric residual rate", source := some .operatorStability,
      kind := .directLift },
    { result := "finite-depth exact fit", source := some .entropyTurnover,
      kind := .directLift },
    { result := "off-depth uniform readout", source := some .entropyTurnover,
      kind := .directLift },
    { result := "finite unique optimum", source := none,
      kind := .newWorkspaceContent },
    { result := "over-settling strict loss", source := none,
      kind := .newWorkspaceContent },
    { result := "preconditioner ancestor only", source := some .preconditionedLearning,
      kind := .scopeBoundary },
    { result := "nonlinear trained model not lifted",
      source := some .trainedNonlinearTurnover, kind := .scopeBoundary } ]

/-- The T2 ledger contains four direct PC lifts, four new workspace results,
and two explicit scope boundaries. -/
theorem linearSettlingTransportLedger_counts :
    (linearSettlingTransportLedger.filter (fun entry =>
      entry.kind == .directLift)).length = 4 ∧
    (linearSettlingTransportLedger.filter (fun entry =>
      entry.kind == .newWorkspaceContent)).length = 4 ∧
    (linearSettlingTransportLedger.filter (fun entry =>
      entry.kind == .scopeBoundary)).length = 2 := by
  decide

/-! ## Positive and negative depth fixtures -/

/-- Positive linear fixture: depth four is the unique optimum for target `3/4`.
This is not a nonlinear workspace-decoder result. -/
theorem depthFour_threeQuarter_uniqueOptimum :
    (∀ evaluationDepth,
      finiteDepthMismatchLoss 4 (3 / 4) 4 ≤
        finiteDepthMismatchLoss 4 (3 / 4) evaluationDepth) ∧
    (∀ evaluationDepth,
      finiteDepthMismatchLoss 4 (3 / 4) evaluationDepth =
        finiteDepthMismatchLoss 4 (3 / 4) 4 ↔ evaluationDepth = 4) := by
  exact finiteDepthMismatch_uniqueOptimum 4 (3 / 4) (by norm_num) (by norm_num)

/-- Negative linear boundary: for the uniform target, every recurrence depth
has zero mismatch loss, so no unique finite optimum can be derived. -/
theorem uniformTarget_no_uniqueDepth_negativeExample
    (trainingDepth evaluationDepth : ℕ) :
    finiteDepthMismatchLoss trainingDepth (1 / 2) evaluationDepth = 0 := by
  by_cases heq : evaluationDepth = trainingDepth
  · subst evaluationDepth
    exact finiteDepthMismatchLoss_at_trainingDepth _ _ (by norm_num)
  · rw [finiteDepthMismatchLoss_away_from_trainingDepth _ _ _ heq]
    norm_num

#print axioms LinearWorkspaceModel.spectralCondition_uniqueEquilibrium
#print axioms LinearWorkspaceModel.linearWorkspace_geometricRate
#print axioms LinearWorkspaceModel.linearWorkspace_tendsto_equilibrium
#print axioms finiteDepthMismatch_uniqueOptimum
#print axioms finiteDepthMismatch_overSettling_strictlyWorse
#print axioms finiteDepthMismatch_equilibrium
#print axioms linearSettlingTransportLedger_counts
#print axioms depthFour_threeQuarter_uniqueOptimum
#print axioms uniformTarget_no_uniqueDepth_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
