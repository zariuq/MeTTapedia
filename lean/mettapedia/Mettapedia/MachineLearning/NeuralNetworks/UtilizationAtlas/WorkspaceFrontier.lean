import Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas.PCPlasticity
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromInheritance

/-!
# Typed, selective, and routed workspace frontier

The new core is a necessary-and-sufficient two-hole quadratic boundary.
Independent per-slot settling is valid exactly when the cross-slot Hessian
block is zero.  With nonzero coupling, the joint solution contains the usual
Schur-style correction and independent per-slot optima leave explicit cross
residuals.

The file also adds a strict routing-usefulness fixture: context-dependent
routing attains zero two-context risk, while every constant expert mixture has
strictly positive risk.  Its negative boundary has identical contexts, where a
constant expert is already optimal.  Existing theorems supply selective-gain
separation, exact affine composition obstructions, arbitrary-switching
instability, common-Lyapunov stability, and checker-owned safety inheritance.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas

open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCarom
open Mettapedia.GSLT.LanguageDef.AtomicRefinement

/-! ## Cross-slot Hessian boundary -/

/-- Gradient in the first slot of a two-hole quadratic with diagonal
curvatures `firstCurvature`, `secondCurvature` and cross block `coupling`. -/
noncomputable def twoSlotGradientFirst
    (firstCurvature coupling firstForce : ℝ)
    (firstState secondState : ℝ) : ℝ :=
  firstCurvature * firstState + coupling * secondState - firstForce

/-- Gradient in the second slot of the same two-hole quadratic. -/
noncomputable def twoSlotGradientSecond
    (secondCurvature coupling secondForce : ℝ)
    (firstState secondState : ℝ) : ℝ :=
  secondCurvature * secondState + coupling * firstState - secondForce

/-- The Hessian of the declared two-slot quadratic. -/
noncomputable def twoSlotHessian
    (firstCurvature secondCurvature coupling : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![firstCurvature, coupling; coupling, secondCurvature]

/-- Off-diagonal Hessian block from the first slot to the second. -/
noncomputable def crossSlotHessianBlock
    (firstCurvature secondCurvature coupling : ℝ) : ℝ :=
  twoSlotHessian firstCurvature secondCurvature coupling 0 1

theorem crossSlotHessianBlock_eq_coupling
    (firstCurvature secondCurvature coupling : ℝ) :
    crossSlotHessianBlock firstCurvature secondCurvature coupling = coupling := by
  rfl

/-- Each slot can compute its gradient without inspecting the other slot. -/
def SlotwiseIndependentSettling
    (firstCurvature secondCurvature coupling firstForce secondForce : ℝ) : Prop :=
  (∀ firstState secondState otherSecondState,
    twoSlotGradientFirst firstCurvature coupling firstForce
        firstState secondState =
      twoSlotGradientFirst firstCurvature coupling firstForce
        firstState otherSecondState) ∧
  (∀ firstState otherFirstState secondState,
    twoSlotGradientSecond secondCurvature coupling secondForce
        firstState secondState =
      twoSlotGradientSecond secondCurvature coupling secondForce
        otherFirstState secondState)

/-- T5 new iff crown: independent two-hole settling is valid exactly when the
cross-slot Hessian block vanishes. -/
theorem slotwiseIndependentSettling_iff_crossSlotHessianBlock_zero
    (firstCurvature secondCurvature coupling firstForce secondForce : ℝ) :
    SlotwiseIndependentSettling firstCurvature secondCurvature coupling
        firstForce secondForce ↔
      crossSlotHessianBlock firstCurvature secondCurvature coupling = 0 := by
  rw [crossSlotHessianBlock_eq_coupling]
  constructor
  · intro hindependent
    have hfirst := hindependent.1 0 0 1
    simp [twoSlotGradientFirst] at hfirst
    linarith
  · intro hzero
    subst coupling
    constructor <;> intros <;>
      simp [twoSlotGradientFirst, twoSlotGradientSecond]

/-- Determinant of the two-slot Hessian. -/
noncomputable def twoSlotHessianDeterminant
    (firstCurvature secondCurvature coupling : ℝ) : ℝ :=
  firstCurvature * secondCurvature - coupling ^ 2

/-- Joint stationary point, including the cross-slot correction. -/
noncomputable def coupledTwoSlotCorrection
    (firstCurvature secondCurvature coupling firstForce secondForce : ℝ) :
    ℝ × ℝ :=
  ((secondCurvature * firstForce - coupling * secondForce) /
      twoSlotHessianDeterminant firstCurvature secondCurvature coupling,
    (firstCurvature * secondForce - coupling * firstForce) /
      twoSlotHessianDeterminant firstCurvature secondCurvature coupling)

/-- The coupled correction exactly zeros both slot gradients whenever the
joint Hessian is invertible. -/
theorem coupledTwoSlotCorrection_stationary
    (firstCurvature secondCurvature coupling firstForce secondForce : ℝ)
    (hinvertible :
      twoSlotHessianDeterminant firstCurvature secondCurvature coupling ≠ 0) :
    twoSlotGradientFirst firstCurvature coupling firstForce
        (coupledTwoSlotCorrection firstCurvature secondCurvature coupling
          firstForce secondForce).1
        (coupledTwoSlotCorrection firstCurvature secondCurvature coupling
          firstForce secondForce).2 = 0 ∧
      twoSlotGradientSecond secondCurvature coupling secondForce
        (coupledTwoSlotCorrection firstCurvature secondCurvature coupling
          firstForce secondForce).1
        (coupledTwoSlotCorrection firstCurvature secondCurvature coupling
          firstForce secondForce).2 = 0 := by
  have hdet :
      firstCurvature * secondCurvature - coupling ^ 2 ≠ 0 := by
    simpa [twoSlotHessianDeterminant] using hinvertible
  have hdetComm :
      secondCurvature * firstCurvature - coupling ^ 2 ≠ 0 := by
    simpa [mul_comm] using hdet
  constructor
  · dsimp [coupledTwoSlotCorrection]
    unfold twoSlotGradientFirst twoSlotHessianDeterminant
    field_simp [hdet]
    ring
  · dsimp [coupledTwoSlotCorrection]
    unfold twoSlotGradientSecond twoSlotHessianDeterminant
    field_simp [hdet, hdetComm]
    ring

/-- Independent diagonal optima leave exactly the declared cross residuals;
this is the correction omitted when cross-slot Hessian blocks are ignored. -/
theorem independentSlotOptima_crossResidual_exact
    (firstCurvature secondCurvature coupling firstForce secondForce : ℝ)
    (hfirst : firstCurvature ≠ 0) (hsecond : secondCurvature ≠ 0) :
    twoSlotGradientFirst firstCurvature coupling firstForce
        (firstForce / firstCurvature) (secondForce / secondCurvature) =
      coupling * secondForce / secondCurvature ∧
    twoSlotGradientSecond secondCurvature coupling secondForce
        (firstForce / firstCurvature) (secondForce / secondCurvature) =
      coupling * firstForce / firstCurvature := by
  constructor
  · unfold twoSlotGradientFirst
    field_simp [hfirst, hsecond]
    ring
  · unfold twoSlotGradientSecond
    field_simp [hfirst, hsecond]
    ring

/-- Concrete coupled negative fixture: diagonal slot solutions `(1,1)` leave
unit residuals, whereas the joint correction is `(2/3,2/3)`. -/
theorem coupledSlots_independentSettling_negativeFixture :
    twoSlotGradientFirst 2 1 2 1 1 = 1 ∧
      twoSlotGradientSecond 2 1 2 1 1 = 1 ∧
      coupledTwoSlotCorrection 2 2 1 2 2 = (2 / 3, 2 / 3) := by
  norm_num [twoSlotGradientFirst, twoSlotGradientSecond,
    coupledTwoSlotCorrection, twoSlotHessianDeterminant]

/-! ## Strict usefulness of context-dependent routing -/

/-- Two expert proposals at the outer endpoints. -/
noncomputable def routedExpertProposal (expert : Fin 2) : ℝ :=
  if expert = 0 then -1 else 1

/-- A constant mixture uses the same expert weight in both contexts. -/
noncomputable def constantExpertMixtureOutput (firstWeight : ℝ) : ℝ :=
  firstWeight * routedExpertProposal 0 +
    (1 - firstWeight) * routedExpertProposal 1

/-- Context targets disagree, making routing observationally useful. -/
def routedContextTarget : Bool → ℝ
  | false => -1
  | true => 1

/-- Total squared risk over the two contexts. -/
noncomputable def twoContextRoutingRisk (prediction : Bool → ℝ) : ℝ :=
  (prediction false - routedContextTarget false) ^ 2 +
    (prediction true - routedContextTarget true) ^ 2

/-- Context-dependent hard routing selects the matching expert. -/
noncomputable def selectiveRoutedPrediction (context : Bool) : ℝ :=
  if context then routedExpertProposal 1 else routedExpertProposal 0

theorem selectiveRouting_zeroRisk :
    twoContextRoutingRisk selectiveRoutedPrediction = 0 := by
  norm_num [twoContextRoutingRisk, selectiveRoutedPrediction,
    routedContextTarget, routedExpertProposal]

/-- Exact constant-mixture penalty. -/
theorem constantExpertMixtureRisk_exact (firstWeight : ℝ) :
    twoContextRoutingRisk (fun _ => constantExpertMixtureOutput firstWeight) =
      2 + 2 * (1 - 2 * firstWeight) ^ 2 := by
  norm_num [twoContextRoutingRisk, constantExpertMixtureOutput,
    routedContextTarget, routedExpertProposal]
  ring

/-- Routing-usefulness crown: the selective router strictly beats every
constant mixture on the two-context task. -/
theorem selectiveRouting_strictlyOutperforms_everyConstantMixture
    (firstWeight : ℝ) :
    twoContextRoutingRisk selectiveRoutedPrediction <
      twoContextRoutingRisk (fun _ => constantExpertMixtureOutput firstWeight) := by
  rw [selectiveRouting_zeroRisk, constantExpertMixtureRisk_exact]
  nlinarith [sq_nonneg (1 - 2 * firstWeight)]

/-- Negative boundary: when both contexts request expert one, constant expert
one and selective routing have the same zero risk. -/
theorem identicalContexts_noStrictRoutingAdvantage :
    ((constantExpertMixtureOutput 0 - 1) ^ 2 +
        (constantExpertMixtureOutput 0 - 1) ^ 2) =
      ((routedExpertProposal 1 - 1) ^ 2 +
        (routedExpertProposal 1 - 1) ^ 2) := by
  norm_num [constantExpertMixtureOutput, routedExpertProposal]

/-! ## Existing exact routed boundaries, re-exported as licenses -/

/-- Selective gating is strictly useful under unequal positive noise. -/
theorem selectiveWorkspaceGain_license
    (priorVariance firstNoise secondNoise gate : ℝ)
    (hprior : 0 < priorVariance)
    (hfirst : 0 < firstNoise) (hsecond : 0 < secondNoise)
    (hnoise : firstNoise ≠ secondNoise) :
    twoRegimeSelectiveRisk priorVariance firstNoise secondNoise <
      twoRegimeConstantGateRisk priorVariance firstNoise secondNoise gate :=
  everyConstantGate_strictlySuboptimal priorVariance firstNoise secondNoise
    gate hprior hfirst hsecond hnoise

/-- Exact composition license: affine phases commute on every state iff both
the matrix commutator and affine bias obstruction vanish. -/
theorem routedComposition_license
    {Index : Type*} [Fintype Index]
    (first second : AffinePhase Index) :
    (∀ state, second.act (first.act state) = first.act (second.act state)) ↔
      AffinePhasesCommute first second :=
  affinePhases_orderIndependent_iff first second

/-- Common-Lyapunov switched-stability license for every finite route
schedule. -/
theorem routedCommonLyapunov_license
    {Command : Type*} {Index : Type*} [Fintype Index]
    {transition : Command → Matrix Index Index ℝ}
    (certificate : CommonQuadraticLyapunov transition)
    (schedule : List Command) (initial : Index → ℝ) :
    quadraticEnergy certificate.metric
        (runLinearSchedule transition schedule initial) ≤
      certificate.rate ^ schedule.length *
        quadraticEnergy certificate.metric initial :=
  certificate.runLinearSchedule_energy_le schedule initial

/-- Routed checker safety is inherited for arbitrary routes, temperatures,
schedules, contents, and recurrence depths. -/
theorem routedWorkspaceSafetyInheritance_license
    {root : AtomicRoot} {Route Temperature Slot Content : Type*}
    (decoder : RoutedLegalActionDecoder root Slot Content Route Temperature)
    (laws : AtomicRootLaws root)
    {budget : Nat} {trace : List (RefineAction root.Hole root.Head)}
    {program : root.Program} :
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program ↔
      root.asRefinementInterface.Accepts budget trace program) ∧
    (root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget trace program →
      root.wellFormed program) ∧
    (root.budgetOK budget → root.wellFormed program →
      root.programCost program ≤ budget →
      root.asRefinementInterface.RankedAccepts
        decoder.toLegalActionWorkspaceDecoder.ranking budget
        (root.encode program) program) :=
  decoder.inheritance laws

/-! ## T5 crown -/

/-- Workspace-frontier license for the canonical negative and positive
fixtures, combined with the generic cross-slot and routing theorems above. -/
structure WorkspaceFrontierLicense : Prop where
  independentIff : ∀ firstCurvature secondCurvature coupling firstForce secondForce,
    SlotwiseIndependentSettling firstCurvature secondCurvature coupling
        firstForce secondForce ↔
      crossSlotHessianBlock firstCurvature secondCurvature coupling = 0
  routedStrictUsefulness : ∀ firstWeight : ℝ,
    twoContextRoutingRisk selectiveRoutedPrediction <
      twoContextRoutingRisk (fun _ => constantExpertMixtureOutput firstWeight)
  routedNegativeBoundary :
    ((constantExpertMixtureOutput 0 - 1) ^ 2 +
        (constantExpertMixtureOutput 0 - 1) ^ 2) =
      ((routedExpertProposal 1 - 1) ^ 2 +
        (routedExpertProposal 1 - 1) ^ 2)
  switchingNegative : ∀ bound : ℝ,
    ∃ cycles : ℕ, bound < divergentAlternatingState cycles 1
  commonLyapunovPositive : ∀ schedule : List Unit, ∀ initial : Fin 1 → ℝ,
    quadraticEnergy halfScalarCommonLyapunov.metric
        (runLinearSchedule halfScalarTransition schedule initial) ≤
      (1 / 4 : ℝ) ^ schedule.length *
        quadraticEnergy halfScalarCommonLyapunov.metric initial

theorem workspace_frontier : WorkspaceFrontierLicense where
  independentIff :=
    slotwiseIndependentSettling_iff_crossSlotHessianBlock_zero
  routedStrictUsefulness :=
    selectiveRouting_strictlyOutperforms_everyConstantMixture
  routedNegativeBoundary := identicalContexts_noStrictRoutingAdvantage
  switchingNegative := individuallyStable_switchingDiverges
  commonLyapunovPositive := halfScalar_allSchedules_positiveExample

#print axioms slotwiseIndependentSettling_iff_crossSlotHessianBlock_zero
#print axioms coupledTwoSlotCorrection_stationary
#print axioms independentSlotOptima_crossResidual_exact
#print axioms selectiveRouting_strictlyOutperforms_everyConstantMixture
#print axioms routedComposition_license
#print axioms routedCommonLyapunov_license
#print axioms routedWorkspaceSafetyInheritance_license
#print axioms workspace_frontier

end Mettapedia.MachineLearning.NeuralNetworks.UtilizationAtlas
