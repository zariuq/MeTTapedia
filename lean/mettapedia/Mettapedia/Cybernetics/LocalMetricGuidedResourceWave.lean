import Mettapedia.Cybernetics.GeometricGoalDirectedResourceWave
import Mettapedia.GSLT.Dynamics.LocalMetricValueGeometry

/-!
# Local-metric guidance under certified resource waves

A value-space distance can guide a certified wave globally.  Statistical and
spacetime-like models additionally use a metric that varies with the current
value and acts on local directions.  This module adds that local layer without
granting it execution authority.

`LocalMetricGuidedWave` contains an already certified geometric wave together
with a local metric field and a value-dependent direction.  Forgetting the
local layer preserves the complete observation/effect/resource certificate.
Conversely, no local tensor can recover a value coordinate hidden by the
execution observer.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.LocalMetricGuidedResourceWave

open Mettapedia.Cybernetics
open Mettapedia.Cybernetics.MultiscaleGoal
open Mettapedia.Cybernetics.GeometricGoalDirectedResourceWave
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.LocalMetricValueGeometry

universe uItem uGuard uCandidateView uState uStateView uAccount uPayload
  uTangent

/-- A certified resource wave with an additional point-dependent metric on
local value directions.  The certificate remains the sole authority to run
the wave; the metric supplies only a typed control signal. -/
structure LocalMetricGuidedWave
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Account : Type uAccount} [AddMonoid Account]
    {Cost Value : Type uPayload}
    (Tangent : Type uTangent)
    [AddCommGroup Tangent] [Module ℝ Tangent]
    (contract : Contract Item Guard CandidateView)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (demand : Item → Account) (source : Account) (batch : List Item)
    (problem : ProblemSpace State) (cost : State → Cost)
    (value : State → Value) where
  geometric : GeometricGoalDirectedWave contract semantics initial
    referenceTarget demand source batch problem cost value
  localMetric : LocalMetricField Value Tangent
  direction : Value → Tangent

namespace LocalMetricGuidedWave

variable {Item : Type uItem} {Guard : Type uGuard}
variable {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Account : Type uAccount} [AddMonoid Account]
variable {Cost Value : Type uPayload}
variable {Tangent : Type uTangent}
  [AddCommGroup Tangent] [Module ℝ Tangent]
variable {contract : Contract Item Guard CandidateView}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {demand : Item → Account} {source : Account} {batch : List Item}
variable {problem : ProblemSpace State} {cost : State → Cost}
variable {value : State → Value}

/-- Erasing local differential guidance changes no execution authority. -/
def toGeometricGoalDirectedWave
    (wave : LocalMetricGuidedWave Tangent contract semantics initial
      referenceTarget demand source batch problem cost value) :
    GeometricGoalDirectedWave contract semantics initial referenceTarget
      demand source batch problem cost value :=
  wave.geometric

/-- Complete-bag activation is inherited from the independently supplied
observation/effect/resource certificate. -/
theorem completeBag_dispatches_bulk
    (wave : LocalMetricGuidedWave Tangent contract semantics initial
      referenceTarget demand source batch problem cost value)
    (complete : contract.demand.completion = .completeBag) :
    (wave.geometric.certified.plan .general).activation = .bulk :=
  wave.geometric.completeBag_dispatches_bulk complete

/-- The observer-visible local quadratic signal agrees with the signal at the
actual target state.  This is a readout theorem, not permission to execute. -/
theorem observed_target_localQuadratic
    (wave : LocalMetricGuidedWave Tangent contract semantics initial
      referenceTarget demand source batch problem cost value) :
    let observedValue := wave.geometric.readout.run .value
      (semantics.observe referenceTarget)
    wave.localMetric.tensor observedValue
        (wave.direction observedValue) (wave.direction observedValue) =
      wave.localMetric.tensor (value referenceTarget)
        (wave.direction (value referenceTarget))
        (wave.direction (value referenceTarget)) := by
  dsimp only
  have observedValue :
      wave.geometric.readout.run .value
          (semantics.observe referenceTarget) =
        value referenceTarget := by
    simpa [GeometricGoalCostControl.goalCostValueFamily] using
      (wave.geometric.readout.agrees .value referenceTarget)
  rw [observedValue]

/-- A hidden value coordinate cannot be reconstructed by adding a local metric
after the fact. -/
theorem no_wave_of_invisible
    (invisible :
      ¬ (GeometricGoalCostControl.goalCostValueFamily problem cost value).SupportsReadout
        semantics.observe) :
    ¬ Nonempty
      (LocalMetricGuidedWave Tangent contract semantics initial
        referenceTarget demand source batch problem cost value) := by
  rintro ⟨wave⟩
  exact GeometricGoalDirectedWave.no_wave_of_invisible invisible
    ⟨wave.geometric⟩

end LocalMetricGuidedWave

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.Cybernetics.GeometricGoalDirectedResourceWave.Canary

/-- The ordinary product form supplies a local Euclidean metric at each
Boolean value. -/
noncomputable def boolLocalMetric : LocalMetricField Bool ℝ where
  tensor _ := LinearMap.mk₂ ℝ
    (fun first second => first * second)
    (by intro first second third; ring)
    (by intro scalar first second; ring)
    (by intro first second third; ring)
    (by intro scalar first second; ring)
  symmetric := by
    intro point first second
    simp only [LinearMap.mk₂_apply]
    ring

def boolDirection : Bool → ℝ
  | false => 0
  | true => 1

noncomputable def exactLocalWave :
    LocalMetricGuidedWave ℝ contract exactSemantics (false, 0, false)
      (true, 1, true) demand 1 [()] problem cost value where
  geometric := exactWave
  localMetric := boolLocalMetric
  direction := boolDirection

/-- Positive control: the certified wave remains bulk and its local quadratic
signal is computed at the observer-visible target value. -/
theorem exact_wave_is_bulk_and_locally_guided :
    (exactLocalWave.geometric.certified.plan .general).activation = .bulk ∧
      exactLocalWave.localMetric.tensor true
        (exactLocalWave.direction true) (exactLocalWave.direction true) = 1 := by
  constructor
  · exact exactLocalWave.completeBag_dispatches_bulk rfl
  · norm_num [exactLocalWave, boolLocalMetric, boolDirection]

/-- Negative control: the same execution and resource certificates at the
coarse observer still cannot authorize a local-metric wave. -/
theorem coarse_certificates_do_not_recover_local_value :
    ¬ Nonempty
      (LocalMetricGuidedWave ℝ contract coarseSemantics (false, 0, false)
        (true, 1, true) demand 1 [()] problem cost value) := by
  apply LocalMetricGuidedWave.no_wave_of_invisible
  exact GeometricGoalCostControl.Canary.coarse_refuses_geometric_control

end Canary

/-! ## Axiom audit -/

#print axioms LocalMetricGuidedWave.completeBag_dispatches_bulk
#print axioms LocalMetricGuidedWave.observed_target_localQuadratic
#print axioms LocalMetricGuidedWave.no_wave_of_invisible
#print axioms Canary.exact_wave_is_bulk_and_locally_guided
#print axioms Canary.coarse_certificates_do_not_recover_local_value

end Mettapedia.Cybernetics.LocalMetricGuidedResourceWave
