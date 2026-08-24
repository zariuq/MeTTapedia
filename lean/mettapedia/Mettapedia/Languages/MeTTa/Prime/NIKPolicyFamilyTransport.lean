import Mettapedia.GSLT.Core.PolicyFamilyTransport
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection

/-!
# Transport of policy-indexed maximal-native selections

A policy catalog over target semantic state pulls back along any state map.
The native realization family, capability order, licensed set, declared policy
support, and exact candidate fibre remain unchanged; only policy decisions and
readouts are precomposed with the state map.  Consequently maximal and
strongest selections transport without rerunning the selector, and their
retained policy functions are the same executable functions.

This construction preserves an already-justified selection.  For a
non-surjective state map it does not claim that the transported catalog lists
every additional policy that might become valid on the smaller image.
Re-recognition may earn such capabilities separately.  Surjective transport
is the reflection boundary established by `PolicyFamilyTransport`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection

universe uIndex uCapability uArtifact uSourceState uTargetState
  uPolicy uResult uKey uRevision uDependency uDependencyValue

namespace PolicyReadoutCatalog

/-- Pull an indexed policy-readout catalog back along a semantic state map.
Every runner and declared support proof is retained unchanged. -/
def pullbackState
    {Index : Type uIndex} [Preorder Index]
    {SourceState : Type uSourceState} {TargetState : Type uTargetState}
    {policies : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
    (mapState : SourceState → TargetState)
    (catalog : PolicyReadoutCatalog.{uIndex, uTargetState, uPolicy, uResult,
      uKey} Index TargetState policies) :
    PolicyReadoutCatalog Index SourceState (policies.pullback mapState) where
  Key := catalog.Key
  readout := fun index => catalog.readout index ∘ mapState
  Supports := catalog.Supports
  runner := catalog.runner
  agrees := fun index policy support state =>
    catalog.agrees index policy support (mapState state)
  supports_mono := catalog.supports_mono

@[simp] theorem pullbackState_readout
    {Index : Type uIndex} [Preorder Index]
    {SourceState : Type uSourceState} {TargetState : Type uTargetState}
    {policies : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
    (mapState : SourceState → TargetState)
    (catalog : PolicyReadoutCatalog.{uIndex, uTargetState, uPolicy, uResult,
      uKey} Index TargetState policies)
    (index : Index) (state : SourceState) :
    (PolicyReadoutCatalog.pullbackState mapState catalog).readout index state =
      catalog.readout index (mapState state) :=
  rfl

@[simp] theorem pullbackState_supports_iff
    {Index : Type uIndex} [Preorder Index]
    {SourceState : Type uSourceState} {TargetState : Type uTargetState}
    {policies : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
    (mapState : SourceState → TargetState)
    (catalog : PolicyReadoutCatalog.{uIndex, uTargetState, uPolicy, uResult,
      uKey} Index TargetState policies)
    (index : Index) (policy : policies.Policy) :
    (PolicyReadoutCatalog.pullbackState mapState catalog).Supports index policy ↔
      catalog.Supports index policy :=
  Iff.rfl

end PolicyReadoutCatalog

namespace PolicyFamilyAdmittedAt

/-- A revision-indexed admitted policy family pulls back along a state map
without changing its retained executable functions or dependency revision. -/
def pullbackState
    {dependencies : DependencySystem}
    {revision : dependencies.Revision}
    {SourceState : Type uSourceState} {TargetState : Type uTargetState}
    {family : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
    {Key : Type uKey} {readout : TargetState → Key}
    (mapState : SourceState → TargetState)
    (admission :
      Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission.PolicyFamilyAdmittedAt
        dependencies revision family readout) :
    Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission.PolicyFamilyAdmittedAt
      dependencies revision (family.pullback mapState) (readout ∘ mapState) where
  realization := admission.realization.pullback mapState

/-- Currentness is reused rather than checked again. -/
def Active.pullbackState
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {SourceState : Type uSourceState} {TargetState : Type uTargetState}
    {family : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
    {Key : Type uKey} {readout : TargetState → Key}
    {admission :
      Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission.PolicyFamilyAdmittedAt
        dependencies revision family readout}
    (active : admission.Active currentRevision)
    (mapState : SourceState → TargetState) :
    (PolicyFamilyAdmittedAt.pullbackState mapState admission).Active
      currentRevision :=
  ⟨active.current⟩

/-- The pulled-back active object exposes exactly the original hot runner. -/
@[simp] theorem Active.pullbackState_runKey
    {dependencies : DependencySystem}
    {revision currentRevision : dependencies.Revision}
    {SourceState : Type uSourceState} {TargetState : Type uTargetState}
    {family : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
    {Key : Type uKey} {readout : TargetState → Key}
    {admission :
      Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission.PolicyFamilyAdmittedAt
        dependencies revision family readout}
    (active : admission.Active currentRevision)
    (mapState : SourceState → TargetState)
    (policy : family.Policy) (encoded : Key) :
    (PolicyFamilyAdmittedAt.Active.pullbackState active mapState).runKey
        policy encoded =
      active.runKey policy encoded :=
  rfl

end PolicyFamilyAdmittedAt

namespace PolicyCapabilityRequest

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {source target : AdmissionObject.{uArtifact}}
variable {base : RecognizedFamily.{uIndex, uCapability, uArtifact} Index source
  target}
variable {SourceState : Type uSourceState} {TargetState : Type uTargetState}
variable {policies : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
variable {catalog :
  PolicyReadoutCatalog.{uIndex, uTargetState, uPolicy, uResult, uKey}
    Index TargetState policies}
variable {nativeRequest : base.CapabilityRequest}

/-- Transport an exact native-plus-policy request without changing its finite
candidate fibre. -/
def pullbackState (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest) :
    PolicyCapabilityRequest
      (PolicyReadoutCatalog.pullbackState mapState catalog) nativeRequest where
  requiredPolicies := request.requiredPolicies
  candidates := request.candidates
  candidates_exact := request.candidates_exact
  candidates_nonempty := request.candidates_nonempty

@[simp] theorem pullbackState_candidates
    (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest) :
    (PolicyCapabilityRequest.pullbackState mapState request).candidates =
      request.candidates :=
  rfl

@[simp] theorem pullbackState_requested_decide
    (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (policy : (PolicyCapabilityRequest.pullbackState mapState request).requestedFamily.Policy)
    (state : SourceState) :
    (PolicyCapabilityRequest.pullbackState mapState request).requestedFamily.decide
        policy state =
      request.requestedFamily.decide policy (mapState state) :=
  rfl

/-- A maximal member of the exact target request remains maximal in the exact
transported request because both licensed fibres and the native order are
identical. -/
def pullbackMaximalSelection
    (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple) :
    (PolicyCapabilityRequest.pullbackState mapState request).toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple :=
  ⟨selection.1, selection.2⟩

/-- A genuinely strongest selection transports for the same reason. -/
def pullbackStrongestSelection
    (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection : request.toCapabilityRequest.StrongestNativeCalculusPrinciple) :
    (PolicyCapabilityRequest.pullbackState mapState request).toCapabilityRequest.StrongestNativeCalculusPrinciple :=
  ⟨selection.1, selection.2⟩

/-- The pulled-back candidate realization uses the same keyed runner as the
target realization. -/
@[simp] theorem pullbackState_candidateRealization_run
    (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (candidate : Index) (member : candidate ∈ request.candidates)
    (policy : (PolicyCapabilityRequest.pullbackState mapState request).requestedFamily.Policy)
    (encoded : catalog.Key candidate) :
    ((PolicyCapabilityRequest.pullbackState mapState request).candidateRealization
      candidate member).run policy encoded =
      (request.candidateRealization candidate member).run policy encoded :=
  rfl

/-- Maximal selection therefore retains exactly the original executable
policy function after state transport. -/
@[simp] theorem pullbackState_maximalRealization_run
    (mapState : SourceState → TargetState)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple)
    (policy : (PolicyCapabilityRequest.pullbackState mapState request).requestedFamily.Policy)
    (encoded : catalog.Key selection.1) :
    ((PolicyCapabilityRequest.pullbackState mapState request).maximalRealization
      (PolicyCapabilityRequest.pullbackMaximalSelection mapState request
        selection)).run
        policy encoded =
      (request.maximalRealization selection).run policy encoded :=
  rfl

end PolicyCapabilityRequest

namespace SelectedPolicyAdmissionAt

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {source target : AdmissionObject}
variable {base : RecognizedFamily.{uIndex, uCapability, 0} Index source target}
variable {SourceState : Type uSourceState} {TargetState : Type uTargetState}
variable {policies : PolicyFamily.{uTargetState, uPolicy, uResult} TargetState}
variable {catalog :
  PolicyReadoutCatalog.{uIndex, uTargetState, uPolicy, uResult, uKey}
    Index TargetState policies}
variable {nativeRequest : base.CapabilityRequest}
variable {request : PolicyCapabilityRequest catalog nativeRequest}
variable {dependencies :
  DependencySystem.{uRevision, uDependency, uDependencyValue}}
variable {revision currentRevision : dependencies.Revision}

/-- Transport the common retained native-operation/policy selection at the
same dependency revision. -/
def pullbackState (mapState : SourceState → TargetState)
    (selected : SelectedPolicyAdmissionAt request dependencies revision) :
    SelectedPolicyAdmissionAt
      (PolicyCapabilityRequest.pullbackState mapState request)
      dependencies revision where
  candidate := selected.candidate
  maximal := selected.maximal

/-- Current activation transports with the same dependency witness. -/
def Active.pullbackState
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision)
    (mapState : SourceState → TargetState) :
    (SelectedPolicyAdmissionAt.pullbackState mapState selected).Active
      currentRevision :=
  ⟨active.current⟩

/-- The transported selected policy runner is definitionally the same hot
function. -/
@[simp] theorem Active.pullbackState_runKey
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision)
    (mapState : SourceState → TargetState)
    (policy : (PolicyCapabilityRequest.pullbackState mapState request).requestedFamily.Policy)
    (encoded : catalog.Key selected.candidate) :
    (SelectedPolicyAdmissionAt.Active.pullbackState active mapState).policyActive.runKey
        policy encoded =
      active.policyActive.runKey policy encoded :=
  rfl

end SelectedPolicyAdmissionAt

/-! ## Concrete positive and negative controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection.Canary

def diagonal : Bool → Bool × Bool := fun state => (state, state)

def pulledCatalog := PolicyReadoutCatalog.pullbackState diagonal catalog

def pulledLeftRequest :=
  PolicyCapabilityRequest.pullbackState diagonal leftRequest

def pulledLeftSelection :=
  PolicyCapabilityRequest.pullbackMaximalSelection diagonal leftRequest
    leftSelection

/-- The exact left-policy selection and its runner survive state transport. -/
theorem pulled_selection_runs_left_policy :
    (pulledLeftRequest.maximalRealization pulledLeftSelection).run
        ⟨Axis.left, rfl⟩ true = true :=
  rfl

/-- Transport does not manufacture the missing joint capability: the declared
catalog still contains no candidate supporting both orthogonal policies. -/
theorem pullback_does_not_mint_joint_support :
    ¬ ∃ candidate : Choice,
      candidate ∈ NoGreatestCanary.neutralRequest.candidates ∧
        ∀ policy : Axis, pulledCatalog.Supports candidate policy := by
  rintro ⟨candidate, member, supportsAll⟩
  exact no_candidate_supports_both_policies
    ⟨candidate, member, fun policy => supportsAll policy⟩

end Canary

#print axioms PolicyReadoutCatalog.pullbackState
#print axioms PolicyFamilyAdmittedAt.Active.pullbackState_runKey
#print axioms PolicyCapabilityRequest.pullbackMaximalSelection
#print axioms PolicyCapabilityRequest.pullbackStrongestSelection
#print axioms PolicyCapabilityRequest.pullbackState_maximalRealization_run
#print axioms SelectedPolicyAdmissionAt.Active.pullbackState_runKey
#print axioms Canary.pulled_selection_runs_left_policy
#print axioms Canary.pullback_does_not_mint_joint_support

end Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport
