import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ErrorCoordinateResidualSemantics

/-!
# Predictive credit at a carrier decision-state interface

A recurrent, workspace, or routed carrier exposes a state cut before a fixed
task readout.  Prospective settling may use that cut as the fast variable and
train every plastic parameter upstream of it from the detached local
prediction error.  For a readout that also attends directly to encoded
memory, the cut must contain both the adapted memory and the carrier decision
states; the product is one admissible `State` below.

This file separates that full carrier-facing credit from an adapter-only
update.  The first accepted inference step recovers the backpropagated credit
at the usual rate-times-precision scale after any declared linear pullback.
Further settling need not remain the same update.  Conversely, an
adapter-only scope has an identically zero carrier coordinate and cannot equal
a full credit whose carrier coordinate is nonzero.  A decision-only cut is
also insufficient when the task has a nonzero direct memory bypass.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CarrierOutputPC

open scoped InnerProductSpace
open ProspectiveResidualSemantics
open ErrorCoordinateResidualSemantics

noncomputable section

variable {State Parameter Carrier Adapter : Type*}
  [NormedAddCommGroup State] [InnerProductSpace ℝ State]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- Pull a decision-state credit back through the declared plastic parameter
partition.  In an executable model this linear map is the reverse derivative
of the carrier decision-state prediction at the current parameter point. -/
def pulledCredit
    (pullback : State →ₗ[ℝ] Parameter) (credit : State) : Parameter :=
  pullback credit

/-- Backpropagated parameter credit at the feed-forward decision state. -/
def carrierBPCredit
    (pullback : State →ₗ[ℝ] Parameter)
    (taskGradient : State → State) (prediction : State) : Parameter :=
  pulledCredit pullback (taskGradient prediction)

/-- Local parameter credit obtained from a detached settled decision state. -/
def carrierLocalCredit
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction settled : State) (precision : ℝ) : Parameter :=
  pulledCredit pullback (precision • (prediction - settled))

/-- The first prospective decision-state step pulls back to the BP credit at
the common `precision * rate` scale for every linearized carrier. -/
theorem firstStep_carrierLocalCredit_eq_scaledBP
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) :
    carrierLocalCredit pullback prediction
        (prospectiveGradientStep
          prediction precision rate taskGradient prediction)
        precision =
      (precision * rate) •
        carrierBPCredit pullback taskGradient prediction := by
  rw [carrierLocalCredit, carrierBPCredit, pulledCredit,
    firstStep_localPredictionCredit_eq_scaledTaskGradient]
  exact pullback.map_smul (precision * rate) (taskGradient prediction)

/-- Unit rate-times-precision is the exact BP ignition point at the carrier
decision-state interface. -/
theorem firstStep_carrierLocalCredit_eq_BP
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State)
    (hscale : precision * rate = 1) :
    carrierLocalCredit pullback prediction
        (prospectiveGradientStep
          prediction precision rate taskGradient prediction)
        precision =
      carrierBPCredit pullback taskGradient prediction := by
  rw [firstStep_carrierLocalCredit_eq_scaledBP, hscale, one_smul]

/-! ## Ignition is not departure -/

/-- For a constant task-gradient field, the exact BP ignition point is already
a fixed point of prospective settling.  Exact first-step agreement therefore
does not imply that later finite settling must depart from BP. -/
theorem constantTaskGradient_firstStep_is_fixed
    (prediction gradient : State) (precision rate : ℝ)
    (hscale : precision * rate = 1) :
    let first :=
      prospectiveGradientStep prediction precision rate
        (fun _ => gradient) prediction
    prospectiveGradientStep prediction precision rate
        (fun _ => gradient) first = first := by
  dsimp only
  let first :=
    prospectiveGradientStep prediction precision rate
      (fun _ => gradient) prediction
  change prospectiveGradientStep prediction precision rate
      (fun _ => gradient) first = first
  have hfirst : first = prediction - rate • gradient := by
    exact prospectiveGradientStep_from_prediction
      prediction precision rate (fun _ => gradient)
  have herror : first - prediction = -(rate • gradient) := by
    rw [hfirst]
    abel
  have hpenalty : precision • (first - prediction) = -gradient := by
    rw [herror, smul_neg, smul_smul, hscale, one_smul]
  have hstationary :
      prospectiveEnergyGradient prediction precision
          (fun _ => gradient) first = 0 := by
    rw [prospectiveEnergyGradient, hpenalty]
    simp
  rw [prospectiveGradientStep, hstationary, smul_zero, sub_zero]

/-- At the constant-field fixed point, every further local-credit read remains
the BP credit.  Departure is consequently a property of the task field and
training trajectory, not an admission condition at update zero. -/
theorem constantTaskGradient_fixedCredit_eq_BP
    (pullback : State →ₗ[ℝ] Parameter)
    (prediction gradient : State) (precision rate : ℝ)
    (hscale : precision * rate = 1) :
    carrierLocalCredit pullback prediction
        (prospectiveGradientStep prediction precision rate
          (fun _ => gradient) prediction)
        precision =
      carrierBPCredit pullback (fun _ => gradient) prediction :=
  firstStep_carrierLocalCredit_eq_BP
    pullback prediction precision rate (fun _ => gradient) hscale

/-! ## State and error coordinates at one carrier cut -/

/-- The task gradient in error coordinates is the state-coordinate task
gradient translated by the carrier's feed-forward prediction. -/
def translatedTaskGradient
    (prediction : State) (taskGradient : State → State) (error : State) :
    State :=
  taskGradient (prediction + error)

/-- At one declared carrier cut, state-coordinate prospective energy and
translated error-coordinate energy are the same vector field.  Consequently
these two descriptions are an exact coordinate change, not two efficacy
mechanisms. -/
theorem prospectiveEnergyGradient_eq_translatedErrorCoordinate
    (prediction : State) (precision : ℝ)
    (taskGradient : State → State) (error : State) :
    prospectiveEnergyGradient prediction precision taskGradient
        (prediction + error) =
      errorCoordinateEnergyGradient precision
        (translatedTaskGradient prediction taskGradient) error := by
  simp [prospectiveEnergyGradient, errorCoordinateEnergyGradient,
    translatedTaskGradient]

/-- The corresponding explicit inference steps commute with translation
between an error and its represented carrier state. -/
theorem prospectiveGradientStep_eq_prediction_add_errorStep
    (prediction : State) (precision rate : ℝ)
    (taskGradient : State → State) (error : State) :
    prospectiveGradientStep prediction precision rate taskGradient
        (prediction + error) =
      prediction +
        (error - rate •
          errorCoordinateEnergyGradient precision
            (translatedTaskGradient prediction taskGradient) error) := by
  simp [prospectiveGradientStep,
    prospectiveEnergyGradient_eq_translatedErrorCoordinate]
  abel

/-! ## Plasticity scope -/

variable [Zero Carrier]

/-- A full carrier-facing credit has independent carrier and adapter
coordinates. -/
def fullScopedCredit
    (carrierCredit : Carrier) (adapterCredit : Adapter) : Carrier × Adapter :=
  (carrierCredit, adapterCredit)

/-- The legacy adapter-only scope leaves the carrier coordinate fixed. -/
def adapterOnlyCredit (adapterCredit : Adapter) : Carrier × Adapter :=
  (0, adapterCredit)

theorem adapterOnlyCredit_fst (adapterCredit : Adapter) :
    (adapterOnlyCredit (Carrier := Carrier) adapterCredit).1 = 0 :=
  rfl

/-- Adapter-only training cannot masquerade as full-carrier training when the
carrier credit is nonzero. -/
theorem adapterOnlyCredit_ne_fullScopedCredit
    (carrierCredit : Carrier) (adapterCredit : Adapter)
    (hcarrier : carrierCredit ≠ 0) :
    adapterOnlyCredit (Carrier := Carrier) adapterCredit ≠
      fullScopedCredit carrierCredit adapterCredit := by
  intro hequal
  have hfirst := congrArg Prod.fst hequal
  exact hcarrier hfirst.symm

/-! ## Exact scalar fixtures -/

def scalarPullback : ℝ →ₗ[ℝ] ℝ :=
  LinearMap.id

theorem scalar_firstStep_recovers_BP :
    carrierLocalCredit scalarPullback 2
        (prospectiveGradientStep 2 2 (1 / 2) identityTaskGradient 2) 2 =
      carrierBPCredit scalarPullback identityTaskGradient 2 := by
  apply firstStep_carrierLocalCredit_eq_BP
  norm_num

/-- A second accepted settle step can leave the BP ignition direction even
though the first step was exactly BP. -/
theorem scalar_secondStep_departs_from_BP :
    let first :=
      prospectiveGradientStep 2 2 (1 / 2) identityTaskGradient 2
    let second :=
      prospectiveGradientStep 2 2 (1 / 2) identityTaskGradient first
    carrierLocalCredit scalarPullback 2 second 2 = 1 ∧
      carrierBPCredit scalarPullback identityTaskGradient 2 = 2 ∧
      carrierLocalCredit scalarPullback 2 second 2 ≠
        carrierBPCredit scalarPullback identityTaskGradient 2 := by
  norm_num [carrierLocalCredit, carrierBPCredit, pulledCredit, scalarPullback,
    prospectiveGradientStep, prospectiveEnergyGradient,
    identityTaskGradient]

theorem adapterOnly_scope_is_strict :
    adapterOnlyCredit (Carrier := ℝ) (2 : ℝ) ≠
      fullScopedCredit (1 : ℝ) (2 : ℝ) := by
  exact adapterOnlyCredit_ne_fullScopedCredit 1 2 one_ne_zero

/-- A carrier decision state alone is not a separating cut when the task
readout has a direct, nonzero adapted-memory path.  The executable TGAD cut
therefore contains both adapted memory and decision state. -/
theorem decisionOnly_cut_misses_memory_bypass :
    let decisionPathCredit : ℝ := 1
    let memoryBypassCredit : ℝ := 1
    decisionPathCredit ≠ decisionPathCredit + memoryBypassCredit := by
  norm_num

/-- Omitting the translation from the task gradient is not an error-coordinate
re-expression of a nonzero carrier prediction. -/
theorem unshiftedErrorCoordinate_not_equivalent :
    prospectiveEnergyGradient 2 1 identityTaskGradient (2 + 1) ≠
      errorCoordinateEnergyGradient 1 identityTaskGradient 1 := by
  norm_num [prospectiveEnergyGradient, errorCoordinateEnergyGradient,
    identityTaskGradient]

#print axioms firstStep_carrierLocalCredit_eq_scaledBP
#print axioms firstStep_carrierLocalCredit_eq_BP
#print axioms constantTaskGradient_firstStep_is_fixed
#print axioms constantTaskGradient_fixedCredit_eq_BP
#print axioms prospectiveEnergyGradient_eq_translatedErrorCoordinate
#print axioms prospectiveGradientStep_eq_prediction_add_errorStep
#print axioms adapterOnlyCredit_ne_fullScopedCredit
#print axioms scalar_firstStep_recovers_BP
#print axioms scalar_secondStep_departs_from_BP
#print axioms adapterOnly_scope_is_strict
#print axioms decisionOnly_cut_misses_memory_bypass
#print axioms unshiftedErrorCoordinate_not_equivalent

end

end CarrierOutputPC

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
