import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeConversionNeedConsumer
import Mettapedia.TypeTheory.ContextualComputationAlgebra
import Mettapedia.TypeTheory.ContextualComputationAlgebraProducts
import Mettapedia.TypeTheory.ContextualDependentSequencing

/-!
# Request-indexed native conversion computation services

The actual finite native conversion checker supplies a family of reply types
indexed by complete requests. Free contextual computation algebras on these
types form a dependent product. Its projections apply a service to its exact
request, retaining the candidate code and the checker verdict.

Selecting one provider before two applications differs from applying a
pointwise choice of providers twice. Two distinct accepted native proof codes
give correlated versus independent artifact pairs, with different ordered
intent histories. Neither computation products nor their projections identify
these two effect placements. Accepted replies still require independent source
admission and target formation before mathematical use; changed request indices
are checked by the existing packet projection.

This is semantic higher-order service composition, not reified computation
lambda syntax, a new conversion checker, a memoization implementation, or a
claim that candidate rejection refutes conversion. The logical package is the
existing MIL service package and is not selected by an unchecked request tag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeConversionAlgebraService

open Presentation NativeConversionChecking NativeConversionNeedConsumer
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bind_assoc)
open Mettapedia.TypeTheory

variable {State Intent : Type} {n : Nat}

/-- The returner for the actual dependent reply, including its native code. -/
def replyAlgebra (State Intent : Type) (request : Request n) :
    ContextualComputationAlgebraProducts.Computation State Intent :=
  (ContextualComputationAlgebra.free State Intent).obj (Reply request)

/-- A computation function is a dependent product of computation objects. -/
def serviceAlgebra (State Intent : Type) (n : Nat) :
    ContextualComputationAlgebraProducts.Computation State Intent :=
  ContextualComputationAlgebraProducts.product (replyAlgebra State Intent (n := n))

abbrev Service (State Intent : Type) (n : Nat) := (serviceAlgebra State Intent n).A

/-- Application is the product's algebra homomorphism at the exact request. -/
def application (service : Service State Intent n) (request : Request n) :
    Program State (Reply request) Intent :=
  (ContextualComputationAlgebraProducts.projection (replyAlgebra State Intent) request).f service

@[simp] theorem application_eq (service : Service State Intent n) (request : Request n) :
    application service request = service request := rfl

/-- Applying the product action uses actual contextual sequencing in the
chosen reply fibre, not a function-space equality erasing effects. -/
theorem application_action (program : Program State (Service State Intent n) Intent)
    (request : Request n) :
    application ((serviceAlgebra State Intent n).a program) request =
      program.bind (fun service => application service request) := by
  change (replyAlgebra State Intent request).a
    (Program.map (fun service => service request) program) = _
  change Program.bind (Program.map (fun service => service request) program)
    (fun next => next) = _
  unfold Program.map
  rw [bind_assoc]
  rfl

/-- No search is hidden here: invoke the existing checker on a proposed code. -/
def checkedService (candidate : Request n → MILCode n) : Service State Intent n :=
  fun request => .pure (produce candidate request)

@[simp] theorem application_checked (candidate : Request n → MILCode n) (request : Request n) :
    application (checkedService (State := State) (Intent := Intent) candidate) request =
      .pure (produce candidate request) := rfl

theorem checked_application_result (candidate : Request n → MILCode n) (request : Request n)
    (state : State) (branch : BranchTrace)
    (output : WorldResult State (Reply request) Intent)
    (retained : output ∈ runWorldsAt (application (checkedService candidate) request) state branch) :
    output.answer = produce candidate request := by
  simp only [application_checked, runWorldsAt, List.mem_singleton] at retained
  subst output
  rfl

/-- A returned accepted artifact licenses native conversion use only beside
independently supplied source admission and target formation. -/
theorem checked_application_admits (candidate : Request n → MILCode n) (request : Request n)
    (state : State) (branch : BranchTrace)
    (output : WorldResult State (Reply request) Intent)
    (retained : output ∈ runWorldsAt (application (checkedService candidate) request) state branch)
    (accepted : output.answer.accepted = true)
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    output.answer.candidate = candidate request ∧
      FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.right := by
  constructor
  · rw [checked_application_result candidate request state branch output retained]
    rfl
  · exact output.answer.admit accepted source targetFormed isUniverse

/-! ## A selected provider versus a pointwise effectful function -/

abbrev Provider (n : Nat) := (request : Request n) → Reply request

/-- Invocation records its own intent; selecting the provider remains separate. -/
def providedService (provider : Provider n) : Service Unit Nat n :=
  fun request => .intent 20 (.pure (provider request))

/-- A computation returning a genuine request-dependent provider function. -/
def selectedProviders (first second : Request n → MILCode n) :
    Program Unit (Provider n) Nat :=
  .intent 10 (.choose (.pure (produce first)) (.pure (produce second)))

/-- Lift the selected provider to an application-effectful service without
executing any of its request components during this mapping. -/
def selectedServices (first second : Request n → MILCode n) :
    Program Unit (Service Unit Nat n) Nat :=
  Program.map providedService (selectedProviders first second)

/-- The same selection interpreted pointwise as a computation function.
Each application executes its selected component, including the choice. -/
def pointwiseService (first second : Request n → MILCode n) : Service Unit Nat n :=
  (serviceAlgebra Unit Nat n).a (selectedServices first second)

theorem pointwise_application (first second : Request n → MILCode n) (request : Request n) :
    application (pointwiseService first second) request =
      (selectedServices first second).bind (fun service => application service request) :=
  application_action _ request

theorem pointwise_application_from_providers
    (first second : Request n → MILCode n) (request : Request n) :
    application (pointwiseService first second) request =
      (selectedProviders first second).bind
        (fun provider => application (providedService provider) request) := by
  rw [pointwise_application]
  unfold selectedServices Program.map
  rw [bind_assoc]
  rfl

/-- Both reply types retain their own requests, even when those requests differ. -/
def applyTwo (service : Service State Intent n) (left right : Request n) :
    Program State (Reply left × Reply right) Intent :=
  (application service left).bind fun first =>
    Program.map (fun second => (first, second)) (application service right)

def providerSelectedOnce (first second : Request n → MILCode n) (left right : Request n) :
    Program Unit (Reply left × Reply right) Nat :=
  (selectedServices first second).bind fun service => applyTwo service left right

def providerSelectedPerCall (first second : Request n → MILCode n) (left right : Request n) :
    Program Unit (Reply left × Reply right) Nat :=
  applyTwo (pointwiseService first second) left right

/-! ## Actual accepted native artifacts and stale requests -/

namespace Examples

open StructuralConversionCode
open IntrinsicMILHypothesis
open NativeConversionChecking.Examples
open NativeConversionNeedConsumer.Examples

def leftRequest : Request 0 := sameEndpointRequest
def rightRequest : Request 0 := { sameEndpointRequest with revision := 1 }

def reflexiveCode : MILCode 0 := .refl (.head secondHead)
def headCode : MILCode 0 := .single (.head secondHead secondHead)

def reflexiveCandidate (_ : Request 0) : MILCode 0 := reflexiveCode
def headCandidate (_ : Request 0) : MILCode 0 := headCode

theorem actual_codes_are_distinct : reflexiveCode ≠ headCode := by
  intro impossible
  cases impossible

/-- Both real codes check at both requests; the revisions are distinct data. -/
theorem actual_codes_accepted_at_both_requests :
    (produce reflexiveCandidate leftRequest).accepted = true ∧
      (produce headCandidate leftRequest).accepted = true ∧
      (produce reflexiveCandidate rightRequest).accepted = true ∧
      (produce headCandidate rightRequest).accepted = true := by decide

def once : Program Unit (Reply leftRequest × Reply rightRequest) Nat :=
  providerSelectedOnce reflexiveCandidate headCandidate leftRequest rightRequest

def perCall : Program Unit (Reply leftRequest × Reply rightRequest) Nat :=
  providerSelectedPerCall reflexiveCandidate headCandidate leftRequest rightRequest

def observeArtifacts (result : WorldResult Unit (Reply leftRequest × Reply rightRequest) Nat) :
    (MILCode 0 × MILCode 0) × List Nat :=
  ((result.answer.1.candidate, result.answer.2.candidate), result.intents)

theorem selected_once_correlates_actual_artifacts :
    (runWorlds once ()).map observeArtifacts =
      [((reflexiveCode, reflexiveCode), [10, 20, 20]),
       ((headCode, headCode), [10, 20, 20])] := rfl

theorem selected_per_call_keeps_four_actual_artifact_pairs :
    (runWorlds perCall ()).map observeArtifacts =
      [((reflexiveCode, reflexiveCode), [10, 20, 10, 20]),
       ((reflexiveCode, headCode), [10, 20, 10, 20]),
       ((headCode, reflexiveCode), [10, 20, 10, 20]),
       ((headCode, headCode), [10, 20, 10, 20])] := rfl

theorem every_selected_artifact_checks :
    ((runWorlds once ()).map (fun result =>
      (result.answer.1.accepted, result.answer.2.accepted))) = [(true, true), (true, true)] ∧
    ((runWorlds perCall ()).map (fun result =>
      (result.answer.1.accepted, result.answer.2.accepted))) =
        [(true, true), (true, true), (true, true), (true, true)] := by decide

/-- Effect placement changes real artifact occurrences despite every verdict
being acceptance. This is not an assumed identification of function types. -/
theorem provider_effect_placement_is_observable : runWorlds once () ≠ runWorlds perCall () := by
  intro equal
  have counts := congrArg List.length equal
  change 2 = 4 at counts
  cases counts

/-- Hiding proof-code identity and occurrence counts can conceal the change. -/
theorem same_acceptance_support (leftAccepted rightAccepted : Bool) :
    (leftAccepted, rightAccepted) ∈ (runWorlds once ()).map
        (fun result => (result.answer.1.accepted, result.answer.2.accepted)) ↔
      (leftAccepted, rightAccepted) ∈ (runWorlds perCall ()).map
        (fun result => (result.answer.1.accepted, result.answer.2.accepted)) := by
  rw [every_selected_artifact_checks.1, every_selected_artifact_checks.2]
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]

theorem request_revision_is_not_erased :
    Mettapedia.Languages.MeTTa.PrimeNeedDependentService.project?
      (family 0) rightRequest ⟨leftRequest, produce reflexiveCandidate leftRequest⟩ = none :=
  Mettapedia.Languages.MeTTa.PrimeNeedDependentService.project?_mismatched (family 0)
    (by intro same; have impossible := congrArg Request.revision same; cases impossible) _

def changedTarget : Request 0 := { leftRequest with right := .head .legacyGround }

theorem request_endpoint_is_not_erased :
    Mettapedia.Languages.MeTTa.PrimeNeedDependentService.project?
      (family 0) changedTarget ⟨leftRequest, produce reflexiveCandidate leftRequest⟩ = none :=
  Mettapedia.Languages.MeTTa.PrimeNeedDependentService.project?_mismatched (family 0)
    (by intro same; have impossible := congrArg Request.right same; cases impossible) _

/-- The actual service result admits native identity conversion beside
independently proved source admission and target formation. -/
theorem native_identity_application_and_admission (revision : Nat) :
    application (checkedService (State := Unit) (Intent := Nat)
      (fun _ : Request 8 => primitiveIdentityTypeCode)) (identityRequest revision) =
        .pure (identityProducer (identityRequest revision)) ∧
      FormationSensitive.Judgment IntrinsicMILHypothesis.rules contextSPMPCSourceTargetSymbol
        (.refl primitiveIotaLeft) (identityRequest revision).right := by
  constructor
  · rfl
  · let output : WorldResult Unit (Reply (identityRequest revision)) Nat :=
      { branch := [], answer := identityProducer (identityRequest revision),
        state := (), intents := [] }
    have retained : output ∈ runWorldsAt
        (application (checkedService (fun _ : Request 8 => primitiveIdentityTypeCode))
          (identityRequest revision)) () [] := by
      exact List.mem_singleton.mpr rfl
    have source := FormationSensitiveMILElimination.primitiveIota_judgments.1
    have target := checked_mil_step_preserves source primitive_step_checked
    obtain ⟨sortHead, isUniverse, typeFormed⟩ := source.regularity
      (FormationSensitive.towerUniverseRegularity.includeSignature rawSignature)
    exact (checked_application_admits (fun _ : Request 8 => primitiveIdentityTypeCode)
      (identityRequest revision) () [] output retained (identity_reply_accepted revision)
      ⟨source.context, .reflIntro source.typing⟩
      (.idForm typeFormed.typing isUniverse target.typing target.typing) isUniverse).2

end Examples

#print axioms application_action
#print axioms checked_application_result
#print axioms checked_application_admits
#print axioms pointwise_application
#print axioms pointwise_application_from_providers
#print axioms Examples.actual_codes_are_distinct
#print axioms Examples.actual_codes_accepted_at_both_requests
#print axioms Examples.selected_once_correlates_actual_artifacts
#print axioms Examples.selected_per_call_keeps_four_actual_artifact_pairs
#print axioms Examples.every_selected_artifact_checks
#print axioms Examples.provider_effect_placement_is_observable
#print axioms Examples.same_acceptance_support
#print axioms Examples.request_revision_is_not_erased
#print axioms Examples.request_endpoint_is_not_erased
#print axioms Examples.native_identity_application_and_admission

end NativeConversionAlgebraService
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
