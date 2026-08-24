import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
import Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection

/-!
# Revision-current activation of native selections with policy families

An exact native-plus-policy request selects one semantically maximal admitted
operation and an executable realization of every requested policy.  This file
retains both at the same NIK dependency revision:

* maximal, greatest, and profitability-frontier selection all construct the
  same common retained object;
* one currentness proof activates both the selected semantic operation and its
  policy runners;
* hot execution applies only the retained operation and keyed functions;
* preparation keeps the original semantic state independently of the selected
  readout;
* staleness disables the whole selected display while preserving fallback.

The construction does not turn a maximal candidate into a greatest one and
does not let profitability manufacture semantic or observational capability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection

universe uIndex uCapability uState uPolicy uResult uKey
  uRevision uDependency uDependencyValue uCost

/-- A semantically maximal member of one exact native-plus-policy request,
retained at an exact dependency revision.  `maximal` deliberately does not
claim `greatest`. -/
structure SelectedPolicyAdmissionAt
    {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
    {source target : AdmissionObject}
    {base : RecognizedFamily.{uIndex, uCapability, 0} Index source target}
    {State : Type uState}
    {policies : PolicyFamily.{uState, uPolicy, uResult} State}
    {catalog :
      PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
        Index State policies}
    {nativeRequest : base.CapabilityRequest}
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (dependencies :
      DependencySystem.{uRevision, uDependency, uDependencyValue})
    (revision : dependencies.Revision) where
  candidate : Index
  maximal :
    request.toCapabilityRequest.restrictedFamily.IsMaximalLicensed candidate

namespace SelectedPolicyAdmissionAt

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {source target : AdmissionObject}
variable {base : RecognizedFamily.{uIndex, uCapability, 0} Index source target}
variable {State : Type uState}
variable {policies : PolicyFamily.{uState, uPolicy, uResult} State}
variable {catalog :
  PolicyReadoutCatalog.{uIndex, uState, uPolicy, uResult, uKey}
    Index State policies}
variable {nativeRequest : base.CapabilityRequest}
variable {request : PolicyCapabilityRequest catalog nativeRequest}
variable {dependencies :
  DependencySystem.{uRevision, uDependency, uDependencyValue}}
variable {revision currentRevision : dependencies.Revision}

/-- A selected maximal candidate is a member of the exact product request. -/
theorem member
    (selected : SelectedPolicyAdmissionAt request dependencies revision) :
    selected.candidate ∈ request.candidates :=
  selected.maximal.1

/-- The semantic operation remains the original native-family package. -/
def operation
    (selected : SelectedPolicyAdmissionAt request dependencies revision) :
    source ⟶ target :=
  base.package selected.candidate

/-- Retain the selected operation in the ordinary revision-indexed NIK
admission doctrine. -/
def operationAdmission
    (selected : SelectedPolicyAdmissionAt request dependencies revision) :
    AdmittedAt dependencies revision
      (discreteOperationalObject source) (discreteOperationalObject target)
    where
  refinement := refinementOfAdmission selected.operation

/-- Retain every executable requested-policy runner at the same revision. -/
def policyAdmission
    (selected : SelectedPolicyAdmissionAt request dependencies revision) :
    PolicyFamilyAdmittedAt dependencies revision request.requestedFamily
      (catalog.readout selected.candidate) where
  realization := request.candidateRealization selected.candidate selected.member

/-- Any ordinary maximal selection constructs the common retained object. -/
def ofMaximal
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple)
    (dependencies :
      DependencySystem.{uRevision, uDependency, uDependencyValue})
    (revision : dependencies.Revision) :
    SelectedPolicyAdmissionAt request dependencies revision where
  candidate := selection.1
  maximal := selection.2

/-- A genuinely strongest selection is in particular maximal; the stronger
proof is used without changing the retained operation. -/
def ofStrongest
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection : request.toCapabilityRequest.StrongestNativeCalculusPrinciple)
    (dependencies :
      DependencySystem.{uRevision, uDependency, uDependencyValue})
    (revision : dependencies.Revision) :
    SelectedPolicyAdmissionAt request dependencies revision where
  candidate := selection.1
  maximal :=
    ⟨selection.2.1, fun candidate candidateMember _chosenLe =>
      selection.2.2 candidate candidateMember⟩

/-- Profitability may choose only from the semantic maximal frontier.  Its
result therefore constructs the same retained object and gains no authority. -/
def ofProfitability
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (Cost : Type uCost) [LinearOrder Cost] (cost : Index -> Cost)
    (selection :
      RecognizedFamily.CapabilityRequest.ProfitabilitySelection
        request.toCapabilityRequest Cost cost)
    (dependencies :
      DependencySystem.{uRevision, uDependency, uDependencyValue})
    (revision : dependencies.Revision) :
    SelectedPolicyAdmissionAt request dependencies revision where
  candidate := selection.chosen
  maximal := selection.semanticMaximal

/-- One dependency-current witness activates both retained components. -/
structure Active
    (_selected : SelectedPolicyAdmissionAt request dependencies revision)
    (currentRevision : dependencies.Revision) : Prop where
  current : dependencies.SameDependencies revision currentRevision

def activate
    (selected : SelectedPolicyAdmissionAt request dependencies revision)
    (current : dependencies.SameDependencies revision currentRevision) :
    selected.Active currentRevision :=
  ⟨current⟩

def Active.operationActive
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision) :
    selected.operationAdmission.Active currentRevision :=
  selected.operationAdmission.activate active.current

def Active.policyActive
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision) :
    selected.policyAdmission.Active currentRevision :=
  selected.policyAdmission.activate active.current

/-- Hot semantic execution is exactly the retained selected package. -/
def Active.run
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision) :
    source.Carrier -> target.Carrier :=
  active.operationActive.run

@[simp] theorem Active.run_eq_selectedOperation
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision) (input : source.Carrier) :
    active.run input = selected.operation.run input :=
  rfl

theorem Active.run_preserves
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision)
    (input : source.Carrier) (meaningful : source.Meaning input) :
    target.Meaning (active.run input) :=
  selected.operation.preserves input meaningful

/-- Preparation keeps an ordinary semantic input and the complete policy
state.  Only the latter's selected readout is precomputed. -/
structure Prepared
    (selected : SelectedPolicyAdmissionAt request dependencies revision) where
  input : source.Carrier
  policyState : selected.policyAdmission.PreparedState

def prepare
    (selected : SelectedPolicyAdmissionAt request dependencies revision)
    (input : source.Carrier) (state : State) : selected.Prepared where
  input := input
  policyState := selected.policyAdmission.prepare state

/-- Fallback retains both untransformed components; it does not attempt to
invert the selected readout. -/
def Prepared.fallback
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (prepared : selected.Prepared) : source.Carrier × State :=
  (prepared.input, prepared.policyState.fallback)

/-- Execute the selected operation and one requested policy using only the
two retained hot functions. -/
def Active.runPrepared
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision)
    (prepared : selected.Prepared)
    (policy : request.requestedFamily.Policy) :
    target.Carrier × request.requestedFamily.Result policy :=
  (active.run prepared.input,
    active.policyActive.runPrepared prepared.policyState policy)

@[simp] theorem Active.runPrepared_eq
    {selected : SelectedPolicyAdmissionAt request dependencies revision}
    (active : selected.Active currentRevision)
    (prepared : selected.Prepared)
    (policy : request.requestedFamily.Policy) :
    active.runPrepared prepared policy =
      (selected.operation.run prepared.input,
        request.requestedFamily.decide policy prepared.policyState.state) := by
  apply Prod.ext
  · rfl
  · exact active.policyActive.runPrepared_eq prepared.policyState policy

def StaleAt
    (_selected : SelectedPolicyAdmissionAt request dependencies revision)
    (candidateRevision : dependencies.Revision) : Prop :=
  ¬ dependencies.SameDependencies revision candidateRevision

/-- A relevant dependency change disables the semantic operation and policy
runners together, while their complete raw inputs remain available. -/
theorem stale_prevents_activation_and_preserves_fallback
    (selected : SelectedPolicyAdmissionAt request dependencies revision)
    {candidateRevision : dependencies.Revision}
    (stale : selected.StaleAt candidateRevision)
    (prepared : selected.Prepared) :
    (¬ selected.Active candidateRevision) ∧
      prepared.fallback =
        (prepared.input, prepared.policyState.state) := by
  constructor
  · rintro ⟨current⟩
    exact stale current
  · rfl

end SelectedPolicyAdmissionAt

/-! ## A native operation and policy runner activated together -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection.Canary

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read := fun revision _ => revision

def selected :
    SelectedPolicyAdmissionAt leftRequest dependencies false :=
  SelectedPolicyAdmissionAt.ofMaximal leftRequest leftSelection
    dependencies false

def active : selected.Active false :=
  selected.activate (dependencies.sameDependencies_refl false)

def leftPolicy : leftRequest.requestedFamily.Policy :=
  ⟨Axis.left, rfl⟩

def prepared : selected.Prepared :=
  selected.prepare (1 : Nat) (true, false)

/-- The current bundle executes the native successor and the selected left
observation without replaying either proof. -/
theorem current_run_executes_operation_and_policy :
    active.runPrepared prepared leftPolicy = ((2 : Nat), true) :=
  rfl

theorem current_run_preserves_meaning :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.AdmissionCanary.positiveNaturals
      |>.Meaning (active.run (1 : Nat)) :=
  active.run_preserves (1 : Nat) (by
    change (1 : Nat) ≠ 0
    decide)

theorem changed_revision_is_stale : selected.StaleAt true := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- Staleness refuses the selected fast path but preserves both the ordinary
input and the complete policy state. -/
theorem changed_revision_refuses_selection_and_preserves_fallback :
    (¬ selected.Active true) ∧
      prepared.fallback = ((1 : Nat), (true, false)) :=
  selected.stale_prevents_activation_and_preserves_fallback
    changed_revision_is_stale prepared

end Canary

#print axioms SelectedPolicyAdmissionAt.Active.runPrepared_eq
#print axioms SelectedPolicyAdmissionAt.stale_prevents_activation_and_preserves_fallback
#print axioms Canary.current_run_executes_operation_and_policy
#print axioms Canary.changed_revision_refuses_selection_and_preserves_fallback

end Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
