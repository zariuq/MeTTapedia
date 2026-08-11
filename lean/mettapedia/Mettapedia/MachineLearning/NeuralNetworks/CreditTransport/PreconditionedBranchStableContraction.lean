import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.RegionalLinearizationCertificate
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.FiniteTrajectoryAcceleration

/-!
# Preconditioned and branch-stable regional contraction

The Unified predictive-coding implementation does not step along the raw
Euclidean gradient.  It divides error-coordinate gradients by registered row
masses and then applies a monotone backtracking policy.  A source-facing
contraction certificate must therefore concern the preconditioned field and
must prove that the accepted-rate branch is stable throughout the admitted
neighborhood.

This file supplies those two missing interfaces.  A uniform Jacobian enclosure
for a linearly preconditioned field yields the existing audited-center local
contraction certificate.  Separately, an executable finite backtracking search
is proved equal to its initial fixed-rate proposal whenever that proposal is
accepted; a local contraction transfers across this regional equality.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PreconditionedBranchStableContraction

open scoped InnerProductSpace
open LocalAmortizedInitialization
open RegionalErrorCoordinateContraction
open RegionalLinearizationCertificate
open Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

noncomputable section

variable {State : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-! ## Linear preconditioning -/

/-- The field actually used by a fixed linear preconditioner.  In the source
application the map is diagonal inverse row mass on active coordinates. -/
def preconditionedField
    (preconditioner : State →L[ℝ] State)
    (gradient : State → State) (state : State) : State :=
  preconditioner (gradient state)

/-- One fixed-rate step on the preconditioned field. -/
def preconditionedStep
    (preconditioner : State →L[ℝ] State) (rate : ℝ)
    (gradient : State → State) (state : State) : State :=
  state - rate • preconditionedField preconditioner gradient state

theorem preconditionedStep_eq_regionalGradientStep
    (preconditioner : State →L[ℝ] State) (rate : ℝ)
    (gradient : State → State) :
    preconditionedStep preconditioner rate gradient =
      regionalGradientStep rate (preconditionedField preconditioner gradient) := by
  rfl

/-- Differentiating a fixed linear preconditioner composes it with the raw
field Jacobian. -/
theorem preconditionedField_hasFDerivAt
    (preconditioner : State →L[ℝ] State)
    {gradient : State → State} {state : State}
    (hgradient : DifferentiableAt ℝ gradient state) :
    HasFDerivAt (preconditionedField preconditioner gradient)
      (preconditioner.comp (fderiv ℝ gradient state)) state := by
  exact preconditioner.hasFDerivAt.comp state hgradient.hasFDerivAt

/-- Source-shaped enclosure data.  The raw Jacobian variation is multiplied
by the preconditioner operator norm, while strong monotonicity is required of
the preconditioned central Jacobian itself. -/
structure PreconditionedJacobianEnclosure
    (preconditioner : State →L[ℝ] State)
    (gradient : State → State) (center : State) (radius : ℝ) where
  linearModulus : ℝ
  rawJacobianVariation : ℝ
  radius_nonneg : 0 ≤ radius
  linearModulus_nonneg : 0 ≤ linearModulus
  rawJacobianVariation_nonneg : 0 ≤ rawJacobianVariation
  scaledVariation_lt_linearModulus :
    ‖preconditioner‖ * rawJacobianVariation < linearModulus
  linearModulus_le_norm :
    linearModulus ≤ ‖preconditioner.comp (fderiv ℝ gradient center)‖
  gradient_differentiable_on_ball : ∀ state,
    InClosedBall center radius state → DifferentiableAt ℝ gradient state
  preconditionedLinear_strongMonotone : ∀ displacement,
    linearModulus * ‖displacement‖ ^ 2 ≤
      ⟪preconditioner (fderiv ℝ gradient center displacement), displacement⟫_ℝ
  rawJacobian_deviation_on_ball : ∀ state,
    InClosedBall center radius state →
    ‖fderiv ℝ gradient state - fderiv ℝ gradient center‖ ≤
      rawJacobianVariation

/-- The source-shaped data induce the generic audited-center enclosure for the
preconditioned field. -/
noncomputable def PreconditionedJacobianEnclosure.toAuditedCenterEnclosure
    {preconditioner : State →L[ℝ] State}
    {gradient : State → State} {center : State} {radius : ℝ}
    (enclosure : PreconditionedJacobianEnclosure
      preconditioner gradient center radius) :
    AuditedCenterJacobianEnclosure
      (preconditionedField preconditioner gradient) center radius
      (preconditioner.comp (fderiv ℝ gradient center)) where
  linearModulus := enclosure.linearModulus
  jacobianVariation := ‖preconditioner‖ * enclosure.rawJacobianVariation
  radius_nonneg := enclosure.radius_nonneg
  linearModulus_nonneg := enclosure.linearModulus_nonneg
  jacobianVariation_nonneg :=
    mul_nonneg (norm_nonneg _) enclosure.rawJacobianVariation_nonneg
  jacobianVariation_lt_linearModulus :=
    enclosure.scaledVariation_lt_linearModulus
  linearModulus_le_norm := enclosure.linearModulus_le_norm
  gradient_differentiable_on_ball := by
    intro state hstate
    exact (preconditionedField_hasFDerivAt preconditioner
      (enclosure.gradient_differentiable_on_ball state hstate)).differentiableAt
  linear_eq_centerJacobian := by
    have hcenter : InClosedBall center radius center := by
      simp [InClosedBall, enclosure.radius_nonneg]
    rw [(preconditionedField_hasFDerivAt preconditioner
      (enclosure.gradient_differentiable_on_ball center hcenter)).fderiv]
  linear_strongMonotone := by
    intro displacement
    simpa using enclosure.preconditionedLinear_strongMonotone displacement
  jacobian_deviation_on_ball := by
    intro state hstate
    have hcenter : InClosedBall center radius center := by
      simp [InClosedBall, enclosure.radius_nonneg]
    rw [(preconditionedField_hasFDerivAt preconditioner
      (enclosure.gradient_differentiable_on_ball state hstate)).fderiv]
    have hcomposition :
        preconditioner.comp (fderiv ℝ gradient state) -
            preconditioner.comp (fderiv ℝ gradient center) =
          preconditioner.comp
            (fderiv ℝ gradient state - fderiv ℝ gradient center) := by
      ext displacement
      simp
    rw [hcomposition]
    calc
      ‖preconditioner.comp
          (fderiv ℝ gradient state - fderiv ℝ gradient center)‖ ≤
          ‖preconditioner‖ *
            ‖fderiv ℝ gradient state - fderiv ℝ gradient center‖ :=
        preconditioner.opNorm_comp_le _
      _ ≤ ‖preconditioner‖ * enclosure.rawJacobianVariation :=
        mul_le_mul_of_nonneg_left
          (enclosure.rawJacobian_deviation_on_ball state hstate)
          (norm_nonneg _)

/-- A preconditioned Jacobian enclosure, stable rate, and audited center
displacement give the exact local contraction consumed by finite-trajectory
acceleration. -/
noncomputable def PreconditionedJacobianEnclosure.toLocalContractionCertificate
    {preconditioner : State →L[ℝ] State}
    {gradient : State → State} {center : State} {radius rate : ℝ}
    (enclosure : PreconditionedJacobianEnclosure
      preconditioner gradient center radius)
    (hrate : 0 < rate)
    (hstable :
      rate *
          (‖preconditioner.comp (fderiv ℝ gradient center)‖ +
            ‖preconditioner‖ * enclosure.rawJacobianVariation) ^ 2 <
        2 *
          (enclosure.linearModulus -
            ‖preconditioner‖ * enclosure.rawJacobianVariation))
    (hadmission :
      ‖preconditionedStep preconditioner rate gradient center - center‖ ≤
        (1 - hilbertSettlingContraction
          (enclosure.linearModulus -
            ‖preconditioner‖ * enclosure.rawJacobianVariation)
          (‖preconditioner.comp (fderiv ℝ gradient center)‖ +
            ‖preconditioner‖ * enclosure.rawJacobianVariation)
          rate) * radius) :
    LocalContractionCertificate
      (preconditionedStep preconditioner rate gradient) center radius := by
  simpa [preconditionedStep_eq_regionalGradientStep] using
    enclosure.toAuditedCenterEnclosure.toLocalContractionCertificate
      hrate hstable hadmission

/-! ## Executable finite backtracking and branch stability -/

/-- Search the initial rate and then at most `retries` successively shrunken
rates, returning the first accepted candidate. -/
def firstAcceptedCandidate?
    (updateAt : ℝ → State → State)
    (accept : State → State → Bool)
    (initialRate shrink : ℝ) : ℕ → State → Option State
  | 0, state =>
      let candidate := updateAt initialRate state
      if accept state candidate then some candidate else none
  | retries + 1, state =>
      let candidate := updateAt initialRate state
      if accept state candidate then
        some candidate
      else
        firstAcceptedCandidate? updateAt accept
          (initialRate * shrink) shrink retries state

/-- Totalized branch used only to state a local solver map.  Outside the
certified region an exhausted search returns the input unchanged; the source
implementation may instead fail closed. -/
def backtrackingOrIdentity
    (updateAt : ℝ → State → State)
    (accept : State → State → Bool)
    (initialRate shrink : ℝ) (retries : ℕ) (state : State) : State :=
  (firstAcceptedCandidate? updateAt accept initialRate shrink retries state).getD state

/-- Exact-real counterpart of the source implementation's monotone-energy
test.  Finiteness is automatic for real-valued energies; a realized floating
point checker must additionally reject non-finite values. -/
def monotoneEnergyAccept
    (energy : State → ℝ) (tolerance : ℝ)
    (state candidate : State) : Bool :=
  decide (energy candidate ≤ energy state + tolerance)

omit [NormedAddCommGroup State] [InnerProductSpace ℝ State] in
theorem monotoneEnergyAccept_eq_true_iff
    (energy : State → ℝ) (tolerance : ℝ)
    (state candidate : State) :
    monotoneEnergyAccept energy tolerance state candidate = true ↔
      energy candidate ≤ energy state + tolerance := by
  simp [monotoneEnergyAccept]

omit [NormedAddCommGroup State] [InnerProductSpace ℝ State] in
/-- Acceptance of the initial proposal makes the entire finite backtracking
search definitionally choose that proposal, independently of retry budget. -/
theorem firstAcceptedCandidate_eq_initial_of_accept
    (updateAt : ℝ → State → State)
    (accept : State → State → Bool)
    (initialRate shrink : ℝ) (retries : ℕ) (state : State)
    (haccept : accept state (updateAt initialRate state) = true) :
    firstAcceptedCandidate? updateAt accept initialRate shrink retries state =
      some (updateAt initialRate state) := by
  cases retries <;> simp [firstAcceptedCandidate?, haccept]

omit [NormedAddCommGroup State] [InnerProductSpace ℝ State] in
theorem backtrackingOrIdentity_eq_initial_of_accept
    (updateAt : ℝ → State → State)
    (accept : State → State → Bool)
    (initialRate shrink : ℝ) (retries : ℕ) (state : State)
    (haccept : accept state (updateAt initialRate state) = true) :
    backtrackingOrIdentity updateAt accept initialRate shrink retries state =
      updateAt initialRate state := by
  simp [backtrackingOrIdentity,
    firstAcceptedCandidate_eq_initial_of_accept updateAt accept initialRate
      shrink retries state haccept]

/-- If the initial proposal is accepted everywhere in the invariant ball,
the backtracking implementation inherits the fixed-rate local contraction
certificate exactly. -/
def branchStableLocalContractionCertificate
    {updateAt : ℝ → State → State}
    {accept : State → State → Bool}
    {initialRate shrink : ℝ} {retries : ℕ}
    {center : State} {radius : ℝ}
    (fixedCertificate :
      LocalContractionCertificate (updateAt initialRate) center radius)
    (initialAccepted : ∀ state,
      InClosedBall center radius state →
        accept state (updateAt initialRate state) = true) :
    LocalContractionCertificate
      (backtrackingOrIdentity updateAt accept initialRate shrink retries)
      center radius where
  factor := fixedCertificate.factor
  factor_nonneg := fixedCertificate.factor_nonneg
  factor_lt_one := fixedCertificate.factor_lt_one
  radius_nonneg := fixedCertificate.radius_nonneg
  maps_ball := by
    intro state hstate
    rw [backtrackingOrIdentity_eq_initial_of_accept updateAt accept
      initialRate shrink retries state (initialAccepted state hstate)]
    exact fixedCertificate.maps_ball state hstate
  contracts_on_ball := by
    intro left right hleft hright
    rw [backtrackingOrIdentity_eq_initial_of_accept updateAt accept
      initialRate shrink retries left (initialAccepted left hleft)]
    rw [backtrackingOrIdentity_eq_initial_of_accept updateAt accept
      initialRate shrink retries right (initialAccepted right hright)]
    exact fixedCertificate.contracts_on_ball left right hleft hright

/-- End-to-end source-shaped regional certificate: a row-mass
preconditioned Jacobian enclosure licenses the fixed proposal, and a uniform
monotone-energy check proves that finite backtracking executes that proposal
throughout the admitted ball. -/
noncomputable def
    PreconditionedJacobianEnclosure.toMonotoneBacktrackingCertificate
    {preconditioner : State →L[ℝ] State}
    {gradient : State → State} {energy : State → ℝ}
    {center : State} {radius rate tolerance shrink : ℝ} {retries : ℕ}
    (enclosure : PreconditionedJacobianEnclosure
      preconditioner gradient center radius)
    (hrate : 0 < rate)
    (hstable :
      rate *
          (‖preconditioner.comp (fderiv ℝ gradient center)‖ +
            ‖preconditioner‖ * enclosure.rawJacobianVariation) ^ 2 <
        2 *
          (enclosure.linearModulus -
            ‖preconditioner‖ * enclosure.rawJacobianVariation))
    (hadmission :
      ‖preconditionedStep preconditioner rate gradient center - center‖ ≤
        (1 - hilbertSettlingContraction
          (enclosure.linearModulus -
            ‖preconditioner‖ * enclosure.rawJacobianVariation)
          (‖preconditioner.comp (fderiv ℝ gradient center)‖ +
            ‖preconditioner‖ * enclosure.rawJacobianVariation)
          rate) * radius)
    (hinitialMonotone : ∀ state,
      InClosedBall center radius state →
        energy (preconditionedStep preconditioner rate gradient state) ≤
          energy state + tolerance) :
    LocalContractionCertificate
      (backtrackingOrIdentity
        (fun proposedRate =>
          preconditionedStep preconditioner proposedRate gradient)
        (monotoneEnergyAccept energy tolerance) rate shrink retries)
      center radius :=
  branchStableLocalContractionCertificate
    (enclosure.toLocalContractionCertificate hrate hstable hadmission)
    (by
      intro state hstate
      exact (monotoneEnergyAccept_eq_true_iff energy tolerance state
        (preconditionedStep preconditioner rate gradient state)).2
          (hinitialMonotone state hstate))

/-! ## Positive and negative executable boundaries -/

def scalarGradientStep (rate state : ℝ) : ℝ := state - rate * state

def acceptEveryProposal (_state _candidate : ℝ) : Bool := true

def scalarSquareEnergy (state : ℝ) : ℝ := state ^ 2

theorem scalarHalf_monotoneEnergyAccept (state : ℝ) :
    monotoneEnergyAccept scalarSquareEnergy 0 state
      (scalarGradientStep (1 / 2) state) = true := by
  rw [monotoneEnergyAccept_eq_true_iff]
  simp only [scalarSquareEnergy, scalarGradientStep, add_zero]
  nlinarith [sq_nonneg state]

def scalarHalfLocalCertificate :
    LocalContractionCertificate (scalarGradientStep (1 / 2)) 0 1 where
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  radius_nonneg := by norm_num
  maps_ball := by
    intro state hstate
    simp only [InClosedBall, sub_zero, Real.norm_eq_abs] at hstate ⊢
    dsimp [scalarGradientStep]
    rw [show state - (1 / 2 : ℝ) * state = state / 2 by ring, abs_div]
    norm_num
    linarith
  contracts_on_ball := by
    intro left right _ _
    simp only [scalarGradientStep]
    rw [show (left - (1 / 2 : ℝ) * left) -
        (right - (1 / 2 : ℝ) * right) = (left - right) / 2 by ring]
    norm_num [Real.norm_eq_abs, abs_div, div_eq_mul_inv]
    rw [mul_comm]

def scalarHalfBacktrackingCertificate :
    LocalContractionCertificate
      (backtrackingOrIdentity scalarGradientStep acceptEveryProposal
        (1 / 2) (1 / 2) 12) 0 1 :=
  branchStableLocalContractionCertificate scalarHalfLocalCertificate
    (by simp [acceptEveryProposal])

def scalarHalfMonotoneBacktrackingCertificate :
    LocalContractionCertificate
      (backtrackingOrIdentity scalarGradientStep
        (monotoneEnergyAccept scalarSquareEnergy 0)
        (1 / 2) (1 / 2) 12) 0 1 :=
  branchStableLocalContractionCertificate scalarHalfLocalCertificate
    (by
      intro state _
      exact scalarHalf_monotoneEnergyAccept state)

theorem scalarHalf_backtracking_one :
    backtrackingOrIdentity scalarGradientStep acceptEveryProposal
      (1 / 2) (1 / 2) 12 1 = 1 / 2 := by
  norm_num [backtrackingOrIdentity, firstAcceptedCandidate?,
    scalarGradientStep, acceptEveryProposal]

def acceptAtLeastThreeQuarters (_state candidate : ℝ) : Bool :=
  decide ((3 / 4 : ℝ) ≤ candidate)

/-- Without initial-branch acceptance, backtracking can select a genuinely
different finite map: the half-step is rejected and the quarter-rate proposal
returns `3/4`. -/
theorem rejectedInitial_branch_differs_from_fixedStep :
    backtrackingOrIdentity scalarGradientStep acceptAtLeastThreeQuarters
        (1 / 2) (1 / 2) 1 1 = 3 / 4 ∧
      scalarGradientStep (1 / 2) 1 = 1 / 2 := by
  norm_num [backtrackingOrIdentity, firstAcceptedCandidate?,
    scalarGradientStep, acceptAtLeastThreeQuarters]

/-- The actual monotone-energy rule also changes the map when an unstable
initial rate is rejected: rate `3` maps `1` to `-2` and raises the square
energy, while one half-rate retry maps `1` to `-1/2` and is accepted. -/
theorem monotoneBacktracking_rejects_unstable_initial :
    backtrackingOrIdentity scalarGradientStep
        (monotoneEnergyAccept scalarSquareEnergy 0) 3 (1 / 2) 1 1 =
        -(1 / 2) ∧
      scalarGradientStep 3 1 = -2 := by
  norm_num [backtrackingOrIdentity, firstAcceptedCandidate?,
    monotoneEnergyAccept, scalarSquareEnergy, scalarGradientStep]

end


#print axioms preconditionedField_hasFDerivAt
#print axioms PreconditionedJacobianEnclosure.toAuditedCenterEnclosure
#print axioms PreconditionedJacobianEnclosure.toLocalContractionCertificate
#print axioms firstAcceptedCandidate_eq_initial_of_accept
#print axioms branchStableLocalContractionCertificate
#print axioms PreconditionedJacobianEnclosure.toMonotoneBacktrackingCertificate
#print axioms scalarHalf_backtracking_one
#print axioms rejectedInitial_branch_differs_from_fixedStep
#print axioms monotoneBacktracking_rejects_unstable_initial

end PreconditionedBranchStableContraction

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
