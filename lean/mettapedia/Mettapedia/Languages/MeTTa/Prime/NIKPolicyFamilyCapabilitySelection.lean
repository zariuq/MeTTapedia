import Mettapedia.GSLT.Dynamics.ObservationPolicyFamilyUniversal
import Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection

/-!
# Policy-family capabilities in maximal-native NIK selection

Native computational structure and policy-facing observation sufficiency are
independent request axes.  This module combines them without introducing a
new selector:

* an existing recognized native family retains its admitted operations and
  native capability order;
* a displayed catalog records each realization's readout and the policies it
  can execute from that readout;
* an exact policy request augments the existing capability request;
* ordinary maximal, strongest, and profitability-frontier selection then run
  unchanged on the combined exact fibre.

Every selected candidate retains an executable realization of the requested
dependent policy family.  Requiring unsupported policies makes the native
fibre infeasible; it does not mint a runner or silently choose a weaker
request.  Empty policy requirements also do not order incomparable native
calculi.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection

universe uIndex uCapability uArtifact uState uPolicy uResult uKey uCost

/-! ## Proof-relevant policy support displayed over native realizations -/

/-- Readouts and executable policy runners for one recognized index family.
Support is monotone in the existing native-strength order, but readout
representations may vary by index. -/
structure PolicyReadoutCatalog
    (Index : Type uIndex) [Preorder Index]
    (State : Type uState)
    (policies : PolicyFamily.{uState, uPolicy, uResult} State) where
  Key : Index -> Type uKey
  readout : (index : Index) -> State -> Key index
  Supports : Index -> policies.Policy -> Prop
  runner : (index : Index) -> (policy : policies.Policy) ->
    Supports index policy -> Key index -> policies.Result policy
  agrees : forall index policy support state,
    runner index policy support (readout index state) =
      policies.decide policy state
  supports_mono : forall {weaker stronger}, weaker <= stronger ->
    forall policy, Supports weaker policy -> Supports stronger policy

namespace PolicyReadoutCatalog

variable {Index : Type uIndex} [Preorder Index]
variable {State : Type uState}
variable {policies : PolicyFamily.{uState, uPolicy, uResult} State}

/-- The dependent policy family selected by a request subset. -/
def requestedFamily
    (_catalog : PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
      Index State policies)
    (required : Set policies.Policy) : PolicyFamily State :=
  policies.reindex (fun policy : {policy // policy ∈ required} => policy.1)

/-- Pointwise support data assembles into one executable realization of the
complete requested family. -/
def realization
    (catalog : PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
      Index State policies)
    (index : Index) (required : Set policies.Policy)
    (supported : forall policy, policy ∈ required ->
      catalog.Supports index policy) :
    (catalog.requestedFamily required).ReadoutRealization
      (catalog.readout index) where
  run := fun policy =>
    catalog.runner index policy.1 (supported policy.1 policy.2)
  agrees := fun policy state =>
    catalog.agrees index policy.1 (supported policy.1 policy.2) state

/-- Requested policy support therefore implies factorization onto the least
sufficient answer vector. -/
theorem requestedVector_factors
    (catalog : PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
      Index State policies)
    (index : Index) (required : Set policies.Policy)
    (supported : forall policy, policy ∈ required ->
      catalog.Supports index policy) :
    NonFactorization.Factors (catalog.readout index)
      (catalog.requestedFamily required).vector :=
  (catalog.realization index required supported).vectorFactors

end PolicyReadoutCatalog

/-! ## Product with the existing native capability family -/

/-- Augment native capabilities by policy capabilities while retaining the
same admitted operations, recognition, licensing, and strength order.  A
strict native comparison remains strict through the left injection. -/
def policyAugmentedFamily
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject.{uArtifact}}
    (base : RecognizedFamily.{uIndex, uCapability, uArtifact} Index source
      target)
    {State : Type uState}
    {policies : PolicyFamily.{uState, uPolicy, uResult} State}
    (catalog : PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
      Index State policies) :
    RecognizedFamily Index source target where
  package := base.package
  Capability := Sum base.Capability policies.Policy
  supports := fun index capability =>
    match capability with
    | .inl native => base.supports index native
    | .inr policy => catalog.Supports index policy
  supports_mono := by
    intro weaker stronger related capability supported
    cases capability with
    | inl native => exact base.supports_mono related native supported
    | inr policy => exact catalog.supports_mono related policy supported
  strict_support_gain := by
    intro weaker stronger strict
    obtain ⟨capability, strongerSupports, weakerRefuses⟩ :=
      base.strict_support_gain strict
    exact ⟨.inl capability, strongerSupports, weakerRefuses⟩
  recognized := base.recognized
  licensed := base.licensed
  licensed_subset_recognized := base.licensed_subset_recognized
  licensed_nonempty := base.licensed_nonempty

/-- A policy request displayed over one already exact native capability
request.  Candidate membership is exact on both axes. -/
structure PolicyCapabilityRequest
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject.{uArtifact}}
    {base : RecognizedFamily.{uIndex, uCapability, uArtifact} Index source
      target}
    {State : Type uState}
    {policies : PolicyFamily.{uState, uPolicy, uResult} State}
    (catalog : PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
      Index State policies)
    (nativeRequest : base.CapabilityRequest) where
  requiredPolicies : Set policies.Policy
  candidates : Finset Index
  candidates_exact : forall candidate,
    candidate ∈ candidates <->
      candidate ∈ nativeRequest.candidates /\
        forall policy, policy ∈ requiredPolicies ->
          catalog.Supports candidate policy
  candidates_nonempty : candidates.Nonempty

namespace PolicyCapabilityRequest

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {source target : AdmissionObject.{uArtifact}}
variable {base : RecognizedFamily.{uIndex, uCapability, uArtifact} Index source
  target}
variable {State : Type uState}
variable {policies : PolicyFamily.{uState, uPolicy, uResult} State}
variable {catalog :
  PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
    Index State policies}
variable {nativeRequest : base.CapabilityRequest}

/-- Convert the displayed product request into the one existing exact
capability-request interface used by every native selector. -/
def toCapabilityRequest
    (request : PolicyCapabilityRequest catalog nativeRequest) :
    (policyAugmentedFamily base catalog).CapabilityRequest where
  required := fun capability =>
    match capability with
    | .inl native => native ∈ nativeRequest.required
    | .inr policy => policy ∈ request.requiredPolicies
  candidates := request.candidates
  candidates_exact := by
    intro candidate
    constructor
    · intro member
      have requestData := (request.candidates_exact candidate).mp member
      have nativeData :=
        (nativeRequest.candidates_exact candidate).mp requestData.1
      refine ⟨nativeData.1, ?_⟩
      intro capability required
      cases capability with
      | inl native => exact nativeData.2 native required
      | inr policy => exact requestData.2 policy required
    · rintro ⟨licensed, supportsAll⟩
      apply (request.candidates_exact candidate).mpr
      constructor
      · apply (nativeRequest.candidates_exact candidate).mpr
        refine ⟨licensed, ?_⟩
        intro native required
        exact supportsAll (.inl native) required
      · intro policy required
        exact supportsAll (.inr policy) required
  candidates_nonempty := request.candidates_nonempty

/-- The exact dependent policy family requested on this fibre. -/
def requestedFamily (request : PolicyCapabilityRequest catalog nativeRequest) :
    PolicyFamily State :=
  catalog.requestedFamily request.requiredPolicies

/-- Every exact candidate carries an executable realization of the requested
policy family. -/
def candidateRealization
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (candidate : Index) (member : candidate ∈ request.candidates) :
    request.requestedFamily.ReadoutRealization
      (catalog.readout candidate) :=
  catalog.realization candidate request.requiredPolicies
    ((request.candidates_exact candidate).mp member).2

/-- Selection by semantic maximality retains the complete requested policy
realization. -/
def maximalRealization
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple) :
    request.requestedFamily.ReadoutRealization
      (catalog.readout selection.1) :=
  request.candidateRealization selection.1 selection.2.1

/-- A genuinely strongest selection, when the exact fibre is directed, has
the same policy realization. -/
def strongestRealization
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection : request.toCapabilityRequest.StrongestNativeCalculusPrinciple) :
    request.requestedFamily.ReadoutRealization
      (catalog.readout selection.1) :=
  request.candidateRealization selection.1 selection.2.1

/-- Cost selection over the semantic frontier cannot discard policy
sufficiency: its chosen index remains a member of the same exact request. -/
def profitabilityRealization
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (Cost : Type uCost) [LinearOrder Cost]
    (cost : Index -> Cost)
    (selection :
      RecognizedFamily.CapabilityRequest.ProfitabilitySelection
        request.toCapabilityRequest Cost cost) :
    request.requestedFamily.ReadoutRealization
      (catalog.readout selection.chosen) :=
  request.candidateRealization selection.chosen
    selection.chosen_mem_exact_request

/-- Any maximal selection therefore factors onto the canonical requested
answer vector. -/
theorem maximalReadout_refines_requestedVector
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple) :
    NonFactorization.Factors (catalog.readout selection.1)
      request.requestedFamily.vector :=
  (request.maximalRealization selection).vectorFactors

end PolicyCapabilityRequest

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus

abbrev Choice := NoGreatestCanary.Choice

inductive Axis where
  | left
  | right
deriving DecidableEq

def policies : PolicyFamily (Bool × Bool) where
  Policy := Axis
  Result := fun _ => Bool
  decide := fun
    | .left => Prod.fst
    | .right => Prod.snd

def readout : Choice -> (Bool × Bool) -> Bool
  | .left => Prod.fst
  | .right => Prod.snd

def supports : Choice -> Axis -> Prop
  | .left, .left => True
  | .right, .right => True
  | _, _ => False

def runner (choice : Choice) (axis : Axis)
    (_support : supports choice axis) : Bool -> Bool :=
  id

theorem runner_agrees (choice : Choice) (axis : Axis)
    (support : supports choice axis) (state : Bool × Bool) :
    runner choice axis support (readout choice state) =
      policies.decide axis state := by
  cases choice <;> cases axis <;>
    simp [runner, readout, policies, supports] at support ⊢

def catalog : PolicyReadoutCatalog Choice (Bool × Bool) policies where
  Key := fun _ => Bool
  readout := readout
  Supports := supports
  runner := runner
  agrees := runner_agrees
  supports_mono := by
    intro weaker stronger related policy supported
    cases related
    exact supported

/-- Requiring the left policy cuts the incomparable native family down to the
one realization that can execute it. -/
def leftRequest :
    PolicyCapabilityRequest catalog NoGreatestCanary.neutralRequest where
  requiredPolicies := fun policy => policy = Axis.left
  candidates := {NoGreatestCanary.Choice.left}
  candidates_exact := by
    intro candidate
    constructor
    · intro member
      have candidateLeft : candidate = NoGreatestCanary.Choice.left := by
        simpa using member
      subst candidate
      constructor
      · simp [NoGreatestCanary.neutralRequest]
      · intro policy required
        have policyLeft : policy = Axis.left := required
        subst policy
        trivial
    · rintro ⟨_nativeMember, supportsRequired⟩
      cases candidate with
      | left => simp
      | right =>
          have impossible := supportsRequired Axis.left rfl
          simp [catalog, supports] at impossible
  candidates_nonempty := ⟨NoGreatestCanary.Choice.left, by simp⟩

def leftSelection :
    leftRequest.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple :=
  ⟨NoGreatestCanary.Choice.left, by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        PolicyCapabilityRequest.toCapabilityRequest, leftRequest]
    · intro candidate _ related
      exact related.symm⟩

/-- The selected native readout reconstructs the complete requested vector. -/
theorem selected_left_refines_requestedVector :
    NonFactorization.Factors (catalog.readout leftSelection.1)
      leftRequest.requestedFamily.vector :=
  leftRequest.maximalReadout_refines_requestedVector leftSelection

/-- No recognized realization supports both orthogonal policies.  The exact
two-policy fibre is therefore empty and cannot be presented as a feasible
native request. -/
theorem no_candidate_supports_both_policies :
    Not (Exists fun candidate : Choice =>
      candidate ∈ NoGreatestCanary.neutralRequest.candidates /\
        forall policy : Axis, catalog.Supports candidate policy) := by
  rintro ⟨candidate, _member, allPolicies⟩
  cases candidate with
  | left => simpa [catalog, supports] using allPolicies Axis.right
  | right => simpa [catalog, supports] using allPolicies Axis.left

/-- With no policy requirement, both incomparable native realizations remain
eligible.  Observation structure does not invent a strongest calculus. -/
def emptyPolicyRequest :
    PolicyCapabilityRequest catalog NoGreatestCanary.neutralRequest where
  requiredPolicies := ∅
  candidates := {NoGreatestCanary.Choice.left,
    NoGreatestCanary.Choice.right}
  candidates_exact := by
    intro candidate
    cases candidate <;>
      simp [NoGreatestCanary.neutralRequest]
  candidates_nonempty := ⟨NoGreatestCanary.Choice.left, by simp⟩

theorem emptyPolicyRequest_has_no_strongest :
    Not (Exists fun chosen =>
      emptyPolicyRequest.toCapabilityRequest.restrictedFamily.IsGreatestLicensed
        chosen) := by
  rintro ⟨chosen, strongest⟩
  cases chosen with
  | left =>
      have impossible : NoGreatestCanary.Choice.right <=
          NoGreatestCanary.Choice.left :=
        strongest.2 NoGreatestCanary.Choice.right (by
          simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
            PolicyCapabilityRequest.toCapabilityRequest, emptyPolicyRequest])
      cases impossible
  | right =>
      have impossible : NoGreatestCanary.Choice.left <=
          NoGreatestCanary.Choice.right :=
        strongest.2 NoGreatestCanary.Choice.left (by
          simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
            PolicyCapabilityRequest.toCapabilityRequest, emptyPolicyRequest])
      cases impossible

end Canary

#print axioms PolicyReadoutCatalog.requestedVector_factors
#print axioms policyAugmentedFamily
#print axioms PolicyCapabilityRequest.toCapabilityRequest
#print axioms PolicyCapabilityRequest.maximalReadout_refines_requestedVector
#print axioms Canary.selected_left_refines_requestedVector
#print axioms Canary.no_candidate_supports_both_policies
#print axioms Canary.emptyPolicyRequest_has_no_strongest

end Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
