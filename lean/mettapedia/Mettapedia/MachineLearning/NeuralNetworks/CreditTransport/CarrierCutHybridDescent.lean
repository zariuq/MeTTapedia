import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CarrierOutputPC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation

/-!
# Hybrid task descent across a carrier cut

A detached carrier-local objective depends only on parameters upstream of the
declared carrier cut.  Its derivative therefore vanishes on every pure head
perturbation.  A full-model update must combine prospective upstream credit
with an explicit supervised head gradient.

This file puts that update in the genuine Euclidean product of the upstream
and head parameter spaces.  It proves its exact first-order margin, derives
finite task descent from an upstream credit-error certificate, and provides an
observable residual certificate only under an explicit contraction premise.
The final examples record the four failure boundaries: a detached objective
cannot move a downstream-only head, energy decrease is not contraction, a
large credit-error ball may contain an anti-aligned direction, and positive
first-order alignment does not license an oversized parameter step.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CarrierCutHybridDescent

open scoped InnerProductSpace
open AmortizedInitialization
open LocalAmortizedInitialization
open AmortizedCreditReadout
open CarrierOutputPC
open DirectionalTaskDescent
open WorkNormalizedTruncation

noncomputable section

variable {Upstream Head Carrier State : Type*}
  [NormedAddCommGroup Upstream] [InnerProductSpace ℝ Upstream]
  [NormedAddCommGroup Head] [InnerProductSpace ℝ Head]

/-- The Euclidean product of the upstream and downstream parameter blocks. -/
abbrev ProductParameter (Upstream Head : Type*)
    [NormedAddCommGroup Upstream] [InnerProductSpace ℝ Upstream]
    [NormedAddCommGroup Head] [InnerProductSpace ℝ Head] :=
  WithLp 2 (Upstream × Head)

/-- Exact task gradient on the two plastic parameter blocks. -/
def productTaskGradient (upstreamGradient : Upstream) (headGradient : Head) :
    ProductParameter Upstream Head :=
  WithLp.toLp 2 (upstreamGradient, headGradient)

/-- Prospective credit upstream of the cut, paired with exact supervised
credit for parameters which occur only after the cut. -/
def hybridDirection (upstreamCredit : Upstream) (headGradient : Head) :
    ProductParameter Upstream Head :=
  WithLp.toLp 2 (upstreamCredit, headGradient)

/-- Carrier-local credit without a supervised downstream component. -/
def carrierLocalOnlyDirection (upstreamCredit : Upstream) :
    ProductParameter Upstream Head :=
  WithLp.toLp 2 (upstreamCredit, 0)

/-! ## Detached carrier objectives have no downstream derivative -/

variable [NormedAddCommGroup Carrier]

/-- Quadratic local prediction error at a fixed, detached carrier target. -/
def detachedCarrierObjective
    (prediction : Upstream → Carrier) (settled : Carrier)
    (precision : ℝ) (upstream : Upstream) : ℝ :=
  precision * ‖prediction upstream - settled‖ ^ 2 / 2

/-- The head-coordinate slice of the detached objective at fixed upstream
parameters.  Its value is independent of the downstream-only block. -/
def detachedCarrierObjectiveHeadSlice
    (prediction : Upstream → Carrier) (settled : Carrier)
    (precision : ℝ) (upstream : Upstream) (_head : Head) : ℝ :=
  detachedCarrierObjective prediction settled precision upstream

omit [NormedAddCommGroup Upstream] [InnerProductSpace ℝ Upstream] in
/-- The head-coordinate Fréchet derivative of a detached carrier objective with
respect to any downstream-only head block is identically zero. -/
theorem hasFDerivAt_detachedCarrierObjectiveHeadSlice_zero
    (prediction : Upstream → Carrier) (settled : Carrier)
    (precision : ℝ) (upstream : Upstream) (head : Head) :
    HasFDerivAt
      (detachedCarrierObjectiveHeadSlice prediction settled precision upstream)
      (0 : Head →L[ℝ] ℝ) head := by
  change HasFDerivAt
    (fun _ : Head =>
      detachedCarrierObjective prediction settled precision upstream)
    (0 : Head →L[ℝ] ℝ) head
  exact hasFDerivAt_const (𝕜 := ℝ)
    (detachedCarrierObjective prediction settled precision upstream) head

omit [NormedAddCommGroup Upstream] [InnerProductSpace ℝ Upstream] in
/-- Consequently the head-coordinate derivative is the zero continuous linear
map, not merely zero on a selected perturbation. -/
theorem fderiv_detachedCarrierObjectiveHeadSlice_eq_zero
    (prediction : Upstream → Carrier) (settled : Carrier)
    (precision : ℝ) (upstream : Upstream) (head : Head) :
    fderiv ℝ
        (detachedCarrierObjectiveHeadSlice prediction settled precision upstream)
        head = 0 :=
  (hasFDerivAt_detachedCarrierObjectiveHeadSlice_zero prediction settled
    precision upstream head).fderiv

/-! ## Ignition and possible departure in the complete product -/

variable [InnerProductSpace ℝ Carrier]

/-- Product update whose upstream component is carrier-local prospective
credit and whose head component is the exact supervised task gradient. -/
def prospectiveHybridDirection
    (pullback : Carrier →ₗ[ℝ] Upstream)
    (prediction settled : Carrier) (precision : ℝ)
    (headGradient : Head) : ProductParameter Upstream Head :=
  hybridDirection
    (carrierLocalCredit pullback prediction settled precision) headGradient

/-- Matched full task gradient at the feed-forward carrier prediction. -/
def carrierBPProductGradient
    (pullback : Carrier →ₗ[ℝ] Upstream)
    (taskGradient : Carrier → Carrier) (prediction : Carrier)
    (headGradient : Head) : ProductParameter Upstream Head :=
  productTaskGradient
    (carrierBPCredit pullback taskGradient prediction) headGradient

/-- Unit rate-times-precision recovers the complete BP product direction at
the first accepted prospective step. -/
theorem firstStep_prospectiveHybridDirection_eq_BP
    (pullback : Carrier →ₗ[ℝ] Upstream)
    (prediction : Carrier) (precision rate : ℝ)
    (taskGradient : Carrier → Carrier) (headGradient : Head)
    (hscale : precision * rate = 1) :
    prospectiveHybridDirection pullback prediction
        (ProspectiveResidualSemantics.prospectiveGradientStep
          prediction precision rate taskGradient prediction)
        precision headGradient =
      carrierBPProductGradient pullback taskGradient prediction
        headGradient := by
  apply WithLp.ofLp_injective 2
  simp only [prospectiveHybridDirection, carrierBPProductGradient,
    hybridDirection, productTaskGradient, WithLp.ofLp_toLp]
  exact Prod.ext
    (firstStep_carrierLocalCredit_eq_BP pullback prediction precision rate
      taskGradient hscale)
    rfl

/-- A constant task-gradient field witnesses that later settling need not
depart from the BP ignition direction. -/
theorem constantField_firstStep_hybrid_eq_BP
    (pullback : Carrier →ₗ[ℝ] Upstream)
    (prediction gradient : Carrier) (precision rate : ℝ)
    (headGradient : Head) (hscale : precision * rate = 1) :
    prospectiveHybridDirection pullback prediction
        (ProspectiveResidualSemantics.prospectiveGradientStep prediction
          precision rate (fun _ => gradient) prediction)
        precision headGradient =
      carrierBPProductGradient pullback (fun _ => gradient) prediction
        headGradient := by
  exact firstStep_prospectiveHybridDirection_eq_BP pullback prediction
    precision rate (fun _ => gradient) headGradient hscale

/-! ## Exact product-space alignment -/

/-- The hybrid first-order margin is the upstream margin plus the squared norm
of the exact supervised head gradient. -/
theorem productTaskGradient_inner_hybridDirection
    (upstreamGradient upstreamCredit : Upstream) (headGradient : Head) :
    ⟪productTaskGradient upstreamGradient headGradient,
        hybridDirection upstreamCredit headGradient⟫_ℝ =
      ⟪upstreamGradient, upstreamCredit⟫_ℝ + ‖headGradient‖ ^ 2 := by
  simp [productTaskGradient, hybridDirection, WithLp.prod_inner_apply,
    ]

/-- An upstream norm-error certificate lifts additively to the complete
hybrid direction. -/
theorem hybridAlignment_lower_of_upstream_error
    (upstreamGradient upstreamCredit : Upstream) (headGradient : Head)
    (error : ℝ)
    (herror : ‖upstreamCredit - upstreamGradient‖ ≤ error) :
    ‖upstreamGradient‖ * (‖upstreamGradient‖ - error) +
        ‖headGradient‖ ^ 2 ≤
      ⟪productTaskGradient upstreamGradient headGradient,
        hybridDirection upstreamCredit headGradient⟫_ℝ := by
  rw [productTaskGradient_inner_hybridDirection]
  simpa [add_comm] using add_le_add_right
    (approximateDirection_inner_lower upstreamGradient upstreamCredit error
      herror)
    (‖headGradient‖ ^ 2)

/-- Error strictly below the true upstream-gradient norm gives positive
complete-product alignment. -/
theorem hybrid_positiveAlignment_of_upstream_error_lt_norm
    (upstreamGradient upstreamCredit : Upstream) (headGradient : Head)
    (error : ℝ)
    (herror : ‖upstreamCredit - upstreamGradient‖ ≤ error)
    (hrelative : error < ‖upstreamGradient‖) :
    0 < ⟪productTaskGradient upstreamGradient headGradient,
      hybridDirection upstreamCredit headGradient⟫_ℝ := by
  have herrorNonneg : 0 ≤ error :=
    le_trans (norm_nonneg (upstreamCredit - upstreamGradient)) herror
  have hgradientPositive : 0 < ‖upstreamGradient‖ :=
    lt_of_le_of_lt herrorNonneg hrelative
  have hmargin :
      0 < ‖upstreamGradient‖ * (‖upstreamGradient‖ - error) :=
    mul_pos hgradientPositive (sub_pos.mpr hrelative)
  have hlower := hybridAlignment_lower_of_upstream_error
    upstreamGradient upstreamCredit headGradient error herror
  nlinarith [sq_nonneg ‖headGradient‖]

/-! ## Finite task descent -/

/-- The exact additive margin gives a finite-step task-descent certificate for
the hybrid update. -/
theorem hybrid_strictTaskDescent_of_upstream_error
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head}
    {upstreamGradient upstreamCredit : Upstream} {headGradient : Head}
    {error curvature step : ℝ}
    (certificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient headGradient)
      (hybridDirection upstreamCredit headGradient) curvature)
    (herror : ‖upstreamCredit - upstreamGradient‖ ≤ error)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 <
        ‖upstreamGradient‖ * (‖upstreamGradient‖ - error) +
          ‖headGradient‖ ^ 2) :
    loss (parameter - step • hybridDirection upstreamCredit headGradient) <
      loss parameter := by
  apply directionalTask_strict_descent certificate hstep
  exact lt_of_lt_of_le htrust
    (hybridAlignment_lower_of_upstream_error upstreamGradient upstreamCredit
      headGradient error herror)

/-- With zero upstream task gradient and credit, a nonzero exact head gradient
alone supplies the complete first-order margin. -/
theorem exactHead_strictTaskDescent_of_zeroUpstream
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head} {headGradient : Head}
    {curvature step : ℝ}
    (certificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient (0 : Upstream) headGradient)
      (hybridDirection (0 : Upstream) headGradient) curvature)
    (hstep : 0 < step)
    (htrust : step * curvature / 2 < ‖headGradient‖ ^ 2) :
    loss (parameter - step • hybridDirection (0 : Upstream) headGradient) <
      loss parameter := by
  apply directionalTask_strict_descent certificate hstep
  rw [productTaskGradient_inner_hybridDirection]
  simpa using htrust

/-- With zero head gradient, the product theorem reduces to the upstream
credit theorem. -/
theorem upstreamOnly_strictTaskDescent
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head}
    {upstreamGradient upstreamCredit : Upstream}
    {curvature step : ℝ}
    (certificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient (0 : Head))
      (hybridDirection upstreamCredit (0 : Head)) curvature)
    (hstep : 0 < step)
    (htrust : step * curvature / 2 <
      ⟪upstreamGradient, upstreamCredit⟫_ℝ) :
    loss (parameter - step • hybridDirection upstreamCredit (0 : Head)) <
      loss parameter := by
  apply directionalTask_strict_descent certificate hstep
  rw [productTaskGradient_inner_hybridDirection]
  simpa using htrust

/-! ## Observable residual admission -/

variable [NormedAddCommGroup State]

/-- Complete upstream-credit error budget: local solver residual plus the
separate mismatch between the equilibrium readout and exact task gradient. -/
def residualUpstreamErrorBudget
    {solver : State → State} (certificate : ContractionCertificate solver)
    (target state : State) (readout : State → Upstream)
    (upstreamGradient : Upstream) (sensitivity : ℝ) : ℝ :=
  sensitivity * (‖state - solver state‖ / (1 - certificate.factor)) +
    ‖readout target - upstreamGradient‖

omit [InnerProductSpace ℝ Upstream] in
/-- A contraction certificate and a Lipschitz readout make the upstream
credit-error premise observable up to explicit equilibrium mismatch. -/
theorem upstreamCreditError_le_residualBudget
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (sensitivity : ℝ) (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity) :
    ‖readout state - upstreamGradient‖ ≤
      residualUpstreamErrorBudget certificate target state readout
        upstreamGradient sensitivity := by
  simpa [residualUpstreamErrorBudget] using
    creditError_le_residual_plus_equilibriumMismatch certificate target state
      htarget readout upstreamGradient sensitivity hsensitivity hreadout

/-- Residual-certified hybrid descent.  Global contraction is a load-bearing
premise; monotone energy alone is not substituted for it. -/
theorem residualCertifiedHybrid_strictTaskDescent
    {solver : State → State}
    (solverCertificate : ContractionCertificate solver)
    (target state : State) (htarget : IsFixedPoint solver target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (headGradient : Head) (sensitivity : ℝ)
    (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity)
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head} {curvature step : ℝ}
    (taskCertificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient headGradient)
      (hybridDirection (readout state) headGradient) curvature)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 <
        ‖upstreamGradient‖ *
          (‖upstreamGradient‖ -
            residualUpstreamErrorBudget solverCertificate target state
              readout upstreamGradient sensitivity) +
          ‖headGradient‖ ^ 2) :
    loss (parameter - step • hybridDirection (readout state) headGradient) <
      loss parameter := by
  exact hybrid_strictTaskDescent_of_upstream_error taskCertificate
    (upstreamCreditError_le_residualBudget solverCertificate target state
      htarget readout upstreamGradient sensitivity hsensitivity hreadout)
    hstep htrust

/-- The corresponding error budget for a solver certified only on an explicit
invariant neighborhood. -/
def localResidualUpstreamErrorBudget
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target state : State) (readout : State → Upstream)
    (upstreamGradient : Upstream) (sensitivity : ℝ) : ℝ :=
  sensitivity * (‖state - solver state‖ / (1 - certificate.factor)) +
    ‖readout target - upstreamGradient‖

omit [InnerProductSpace ℝ Upstream] in
/-- Inside the certified invariant neighborhood, the same observable residual
controls upstream-credit error.  Membership of both target and endpoint is
load-bearing. -/
theorem upstreamCreditError_le_localResidualBudget
    {solver : State → State} {center : State} {radius : ℝ}
    (certificate : LocalContractionCertificate solver center radius)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint solver target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (sensitivity : ℝ) (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity) :
    ‖readout state - upstreamGradient‖ ≤
      localResidualUpstreamErrorBudget certificate target state readout
        upstreamGradient sensitivity := by
  have htriangle :
      ‖readout state - upstreamGradient‖ ≤
        ‖readout state - readout target‖ +
          ‖readout target - upstreamGradient‖ := by
    simpa [sub_eq_add_neg, add_assoc] using
      norm_add_le (readout state - readout target)
        (readout target - upstreamGradient)
  have hresidual := local_creditReadout_distance_le_residual_div certificate
    target state htargetMem hstateMem htarget readout sensitivity hsensitivity
    hreadout
  unfold localResidualUpstreamErrorBudget
  exact htriangle.trans (add_le_add_left hresidual _)

/-- Local residual-certified hybrid descent.  This is the fresh-start
admission form: it cannot be used until the endpoint and fixed point are shown
to remain in the same contraction region. -/
theorem localResidualCertifiedHybrid_strictTaskDescent
    {solver : State → State} {center : State} {radius : ℝ}
    (solverCertificate : LocalContractionCertificate solver center radius)
    (target state : State)
    (htargetMem : InClosedBall center radius target)
    (hstateMem : InClosedBall center radius state)
    (htarget : IsFixedPoint solver target)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (headGradient : Head) (sensitivity : ℝ)
    (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout target sensitivity)
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head} {curvature step : ℝ}
    (taskCertificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient headGradient)
      (hybridDirection (readout state) headGradient) curvature)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 <
        ‖upstreamGradient‖ *
          (‖upstreamGradient‖ -
            localResidualUpstreamErrorBudget solverCertificate target state
              readout upstreamGradient sensitivity) +
          ‖headGradient‖ ^ 2) :
    loss (parameter - step • hybridDirection (readout state) headGradient) <
      loss parameter := by
  exact hybrid_strictTaskDescent_of_upstream_error taskCertificate
    (upstreamCreditError_le_localResidualBudget solverCertificate target state
      htargetMem hstateMem htarget readout upstreamGradient sensitivity
      hsensitivity hreadout)
    hstep htrust

/-! ### Final-gradient admission for prospective settling -/

variable [InnerProductSpace ℝ State]

/-- Upstream error budget expressed in the final prospective energy-gradient
norm logged at the accepted endpoint. -/
def finalGradientUpstreamErrorBudget
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (exactResolver : State → State) (readout : State → Upstream)
    (upstreamGradient : Upstream) (sensitivity : ℝ) : ℝ :=
  sensitivity *
      (‖ProspectiveResidualSemantics.prospectiveEnergyGradient prediction
          precision taskGradient state‖ / precision) +
    ‖readout (exactResolver prediction) - upstreamGradient‖

omit [InnerProductSpace ℝ Upstream] in
/-- Positive precision, task-gradient monotonicity, and the exact resolvent
equation turn the logged final energy-gradient norm into a credit-error bound.
Energy decrease by itself supplies none of these premises. -/
theorem upstreamCreditError_le_finalGradientBudget
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (exactResolver : State → State)
    (hprecision : 0 < precision)
    (htask : NonlinearResolvent.MonotoneMap taskGradient)
    (resolventEquation : NonlinearResolvent.IsUnitResolventMapOf
      (ProspectiveResidualSemantics.prospectiveImplicitOperator
        precision taskGradient)
      exactResolver)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (sensitivity : ℝ) (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout
      (exactResolver prediction) sensitivity) :
    ‖readout state - upstreamGradient‖ ≤
      finalGradientUpstreamErrorBudget prediction precision taskGradient state
        exactResolver readout upstreamGradient sensitivity := by
  have hdistance :=
    ProspectiveResidualSemantics.distance_exactProspectiveState_le_finalGradient_div
      prediction precision taskGradient state hprecision htask
      resolventEquation
  have hreadoutDistance :
      ‖readout state - readout (exactResolver prediction)‖ ≤
        sensitivity *
          (‖ProspectiveResidualSemantics.prospectiveEnergyGradient prediction
              precision taskGradient state‖ / precision) := by
    exact (hreadout state).trans
      (mul_le_mul_of_nonneg_left hdistance hsensitivity)
  have htriangle :
      ‖readout state - upstreamGradient‖ ≤
        ‖readout state - readout (exactResolver prediction)‖ +
          ‖readout (exactResolver prediction) - upstreamGradient‖ := by
    simpa [sub_eq_add_neg, add_assoc] using
      norm_add_le (readout state - readout (exactResolver prediction))
        (readout (exactResolver prediction) - upstreamGradient)
  unfold finalGradientUpstreamErrorBudget
  exact htriangle.trans (add_le_add_left hreadoutDistance _)

/-- Logged-final-gradient hybrid descent.  The parameter-step curvature
certificate remains separate from the inference residual certificate. -/
theorem finalGradientCertifiedHybrid_strictTaskDescent
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (state : State)
    (exactResolver : State → State)
    (hprecision : 0 < precision)
    (htask : NonlinearResolvent.MonotoneMap taskGradient)
    (resolventEquation : NonlinearResolvent.IsUnitResolventMapOf
      (ProspectiveResidualSemantics.prospectiveImplicitOperator
        precision taskGradient)
      exactResolver)
    (readout : State → Upstream) (upstreamGradient : Upstream)
    (headGradient : Head) (sensitivity : ℝ)
    (hsensitivity : 0 ≤ sensitivity)
    (hreadout : CreditReadoutLipschitzAt readout
      (exactResolver prediction) sensitivity)
    {loss : ProductParameter Upstream Head → ℝ}
    {parameter : ProductParameter Upstream Head} {curvature step : ℝ}
    (taskCertificate : HasDirectionalTaskUpperModelAt loss parameter
      (productTaskGradient upstreamGradient headGradient)
      (hybridDirection (readout state) headGradient) curvature)
    (hstep : 0 < step)
    (htrust :
      step * curvature / 2 <
        ‖upstreamGradient‖ *
          (‖upstreamGradient‖ -
            finalGradientUpstreamErrorBudget prediction precision taskGradient
              state exactResolver readout upstreamGradient sensitivity) +
          ‖headGradient‖ ^ 2) :
    loss (parameter - step • hybridDirection (readout state) headGradient) <
      loss parameter := by
  exact hybrid_strictTaskDescent_of_upstream_error taskCertificate
    (upstreamCreditError_le_finalGradientBudget prediction precision
      taskGradient state exactResolver hprecision htask resolventEquation
      readout upstreamGradient sensitivity hsensitivity hreadout)
    hstep htrust

/-! ## Positive and negative scalar boundaries -/

abbrev ScalarProduct := ProductParameter ℝ ℝ

def scalarParameter (upstream head : ℝ) : ScalarProduct :=
  WithLp.toLp 2 (upstream, head)

/-- Adding the explicit supervised component changes the downstream block;
carrier-local credit alone leaves it exactly frozen. -/
theorem supervisedHead_moves_while_localOnly_freezes :
    let parameter := scalarParameter 0 3
    let localNext := parameter -
      (1 : ℝ) • carrierLocalOnlyDirection (Head := ℝ) 1
    let hybridNext := parameter - (1 : ℝ) • hybridDirection 1 2
    localNext.snd = 3 ∧ hybridNext.snd = 1 := by
  norm_num [scalarParameter, carrierLocalOnlyDirection, hybridDirection]

/-- Two prospective steps can depart in the upstream coordinate while the
supervised head coordinate remains the same exact task gradient. -/
theorem scalar_secondStep_hybrid_departs_from_BP :
    let first :=
      ProspectiveResidualSemantics.prospectiveGradientStep 2 2 (1 / 2)
        ProspectiveResidualSemantics.identityTaskGradient 2
    let second :=
      ProspectiveResidualSemantics.prospectiveGradientStep 2 2 (1 / 2)
        ProspectiveResidualSemantics.identityTaskGradient first
    prospectiveHybridDirection scalarPullback 2 second 2 (3 : ℝ) ≠
      carrierBPProductGradient scalarPullback
        ProspectiveResidualSemantics.identityTaskGradient 2 (3 : ℝ) := by
  norm_num [prospectiveHybridDirection, carrierBPProductGradient,
    hybridDirection, productTaskGradient, carrierLocalCredit,
    carrierBPCredit, pulledCredit, scalarPullback,
    ProspectiveResidualSemantics.prospectiveGradientStep,
    ProspectiveResidualSemantics.prospectiveEnergyGradient,
    ProspectiveResidualSemantics.identityTaskGradient]

def shiftSolver (state : ℝ) : ℝ := state + 1

def descendingAffineEnergy (state : ℝ) : ℝ := -state

/-- The shift lowers a smooth energy at every point. -/
theorem shiftSolver_strictly_decreases_energy (state : ℝ) :
    descendingAffineEnergy (shiftSolver state) < descendingAffineEnergy state := by
  simp [descendingAffineEnergy, shiftSolver]

/-- Nevertheless the shift preserves pairwise distances and has no global
contraction certificate with factor below one. -/
theorem shiftSolver_has_no_contractionCertificate :
    ¬ Nonempty (ContractionCertificate shiftSolver) := by
  rintro ⟨certificate⟩
  have hcontract := certificate.contracts (0 : ℝ) 1
  norm_num [shiftSolver, Real.norm_eq_abs] at hcontract
  linarith [certificate.factor_lt_one]

/-- An error budget at least as large as the true upstream-gradient norm can
contain an exactly anti-aligned hybrid direction when the head gradient is zero. -/
theorem large_upstream_error_does_not_ensure_hybrid_alignment :
    ‖(-1 : ℝ) - 1‖ ≤ 2 ∧
      (2 : ℝ) ≥ ‖(1 : ℝ)‖ ∧
      ⟪productTaskGradient (1 : ℝ) (0 : ℝ),
        hybridDirection (-1 : ℝ) (0 : ℝ)⟫_ℝ < 0 := by
  norm_num [productTaskGradient, hybridDirection, WithLp.prod_inner_apply,
    Real.norm_eq_abs]

def coupledQuadratic (parameter : ScalarProduct) : ℝ :=
  (parameter.fst + parameter.snd) ^ 2 / 2

/-- The exact product gradient has positive first-order alignment at `(1,1)`,
but a step of size two overshoots the coupled quadratic and increases loss. -/
theorem oversized_hybrid_step_increases_coupledQuadratic :
    let parameter := scalarParameter 1 1
    let gradient := productTaskGradient (2 : ℝ) (2 : ℝ)
    0 < ⟪gradient, gradient⟫_ℝ ∧
      coupledQuadratic (parameter - (2 : ℝ) • gradient) >
        coupledQuadratic parameter := by
  norm_num [scalarParameter, productTaskGradient, coupledQuadratic,
    WithLp.prod_inner_apply]

#print axioms hasFDerivAt_detachedCarrierObjectiveHeadSlice_zero
#print axioms fderiv_detachedCarrierObjectiveHeadSlice_eq_zero
#print axioms firstStep_prospectiveHybridDirection_eq_BP
#print axioms constantField_firstStep_hybrid_eq_BP
#print axioms productTaskGradient_inner_hybridDirection
#print axioms hybridAlignment_lower_of_upstream_error
#print axioms hybrid_positiveAlignment_of_upstream_error_lt_norm
#print axioms hybrid_strictTaskDescent_of_upstream_error
#print axioms exactHead_strictTaskDescent_of_zeroUpstream
#print axioms upstreamOnly_strictTaskDescent
#print axioms upstreamCreditError_le_residualBudget
#print axioms residualCertifiedHybrid_strictTaskDescent
#print axioms upstreamCreditError_le_localResidualBudget
#print axioms localResidualCertifiedHybrid_strictTaskDescent
#print axioms upstreamCreditError_le_finalGradientBudget
#print axioms finalGradientCertifiedHybrid_strictTaskDescent
#print axioms supervisedHead_moves_while_localOnly_freezes
#print axioms scalar_secondStep_hybrid_departs_from_BP
#print axioms shiftSolver_has_no_contractionCertificate
#print axioms large_upstream_error_does_not_ensure_hybrid_alignment
#print axioms oversized_hybrid_step_increases_coupledQuadratic

end

end CarrierCutHybridDescent

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
