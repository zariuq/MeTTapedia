import Mettapedia.GSLT.Dynamics.ObservationPolicyFamilyUniversal
import Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
import Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission

/-!
# Cost² policy-key admission as generic observation-family sufficiency

The Cost² receipt-key theory and the general observation-family theory have
the same information boundary.  This module makes that relationship formal
without changing either layer: every existing policy-key admission supplies
the generic executable readout realization, and the generic least-sufficient
theorem rederives refinement onto the request's policy vector.

Exact replay remains a separate capability.  A collapsed key can realize a
constant policy family while provably failing to replay the retained state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyFamilyObservationBridge

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.Languages.MeTTa.Prime.CostTwoCacheReplayBoundary
open Mettapedia.Languages.MeTTa.Prime.CostTwoObservationKeyOrder
open Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyKeyNIKAdmission

universe uState uKey

/-- Forget the revision and replay request temporarily to expose exactly the
dependent observation family requested from retained semantic state. -/
def observationFamily
    {State : Type uState} (request : PolicyRequest State) :
    PolicyFamily State where
  Policy := request.Policy
  Result := request.Value
  decide := request.observe

/-- A Cost/NIK policy-key admission retains precisely the executable runners
required by the generic observation-family realization. -/
def observationRealization
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    (admission : PolicyKeyAdmission dependencies revision request key) :
    (observationFamily request).ReadoutRealization key where
  run := fun policy => (admission.realize policy).run
  agrees := fun policy state => (admission.realize policy).run_encode state

/-- The Cost/NIK key admission is an ordinary revision-indexed GSLT policy
family admission after forgetting only its independent replay field. -/
def toGenericAdmission
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    (admission : PolicyKeyAdmission dependencies revision request key) :
    PolicyFamilyAdmittedAt dependencies revision (observationFamily request)
      key where
  realization := observationRealization admission

/-- Conversely, on an explicitly policy-only request, the generic GSLT
admission supplies the whole Cost/NIK policy-key admission.  Exact replay is
not manufactured; the contradiction discharges only a request which has
already declared that replay is absent. -/
def ofGenericAdmissionPolicyOnly
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    (generic : PolicyFamilyAdmittedAt dependencies revision
      (observationFamily request) key)
    (policyOnly : ¬ request.requiresExactReplay) :
    PolicyKeyAdmission dependencies revision request key where
  realize := fun policy =>
    { run := generic.realization.run policy
      agrees := by
        funext state
        exact (generic.realization.agrees policy state).symm }
  replay := fun required => False.elim (policyOnly required)

/-- Crossing from a policy-only Cost request into the generic layer and back
does not change any executable keyed policy function. -/
@[simp] theorem policyOnly_roundtrip_run
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    (admission : PolicyKeyAdmission dependencies revision request key)
    (policyOnly : ¬ request.requiresExactReplay)
    (policy : request.Policy) (encoded : Key) :
    (ofGenericAdmissionPolicyOnly (toGenericAdmission admission) policyOnly
      |>.realize policy).run encoded =
      (admission.realize policy).run encoded :=
  rfl

/-- Current activation transports to the generic layer without adding a
second dependency test. -/
def activeToGeneric
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    {admission : PolicyKeyAdmission dependencies revision request key}
    (active : admission.Active currentRevision) :
    (toGenericAdmission admission).Active currentRevision :=
  ⟨active.current⟩

/-- The transported current runner is definitionally the same hot function. -/
@[simp] theorem activeToGeneric_runKey
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    {admission : PolicyKeyAdmission dependencies revision request key}
    (active : admission.Active currentRevision)
    (policy : request.Policy) (encoded : Key) :
    (activeToGeneric active).runKey policy encoded =
      active.runKey policy encoded :=
  rfl

/-- Every admitted Cost/NIK key supports its complete generic observation
family. -/
theorem policyKeyAdmission_supportsObservationFamily
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    (admission : PolicyKeyAdmission dependencies revision request key) :
    (observationFamily request).SupportsReadout key :=
  ⟨observationRealization admission⟩

/-- The generic universal property rederives the Cost-specific information
order: every admitted key refines the dependent vector of requested values. -/
theorem policyKeyAdmission_refinesPolicyVector_fromObservationUniversal
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {State : Type uState} {request : PolicyRequest State}
    {Key : Type uKey} {key : State -> Key}
    (admission : PolicyKeyAdmission dependencies revision request key) :
    KeyRefines key (policyVectorKey request) := by
  have factors :=
    ((observationFamily request).supportsReadout_iff_vectorFactors key).1
      (policyKeyAdmission_supportsObservationFamily admission)
  obtain ⟨forget, recovers⟩ := factors
  refine ⟨forget, funext fun state => ?_⟩
  exact (recovers state).symm

/-! ## Exact replay remains strictly stronger -/

namespace Canary

def dependencies : DependencySystem where
  Revision := Unit
  Dependency := Unit
  Value := Unit
  read := fun _ _ => ()

def constantRequest : PolicyRequest Bool :=
  singlePolicyRequest (fun _ => true) False

def collapsedKey : Bool -> Unit := fun _ => ()

/-- A constant policy genuinely admits the collapsed key. -/
def collapsedAdmission :
    PolicyKeyAdmission dependencies () constantRequest collapsedKey where
  realize := fun _ =>
    { run := fun _ => true
      agrees := by funext state; cases state <;> rfl }
  replay := fun required => False.elim required

/-- Generic family support does not imply exact replay of semantic state. -/
theorem familySupport_does_not_mint_exactReplay :
    (observationFamily constantRequest).SupportsReadout collapsedKey /\
      Not (ExactReplayKey collapsedKey) := by
  constructor
  · exact policyKeyAdmission_supportsObservationFamily collapsedAdmission
  · exact collision_prevents_exactReplayKey
      (key := collapsedKey) (left := false) (right := true)
      (by decide) rfl

end Canary

#print axioms policyKeyAdmission_supportsObservationFamily
#print axioms policyKeyAdmission_refinesPolicyVector_fromObservationUniversal
#print axioms policyOnly_roundtrip_run
#print axioms activeToGeneric_runKey
#print axioms Canary.familySupport_does_not_mint_exactReplay

end Mettapedia.Languages.MeTTa.Prime.CostTwoPolicyFamilyObservationBridge
