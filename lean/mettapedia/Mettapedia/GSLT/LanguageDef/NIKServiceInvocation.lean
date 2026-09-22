import Mettapedia.GSLT.LanguageDef.NIKServiceFamily

/-!
# Invoking the four native inference service faces

Requests retain the selected service and its actual face-specific input.
Decisions receive claims, native proof kernels receive claims and guest proof
objects, native operations receive raw source values, and external boundaries
receive claims and external certificates. The executable invocation never
converts one face into another or searches for missing evidence.

Source admission for an operation is a separate judgment, not an assumed
decision procedure on source meaning. Invocation can execute a raw operation
input; its result is semantically admitted only when that source premise is
available. The shared continuation theorem applies an existing admitted
operation to a successful result, retaining this precondition.

This is a typed invocation boundary. It neither parses external bytes nor
claims compilation/hosting adequacy or a step-for-step backend realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKServiceInvocation

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIK

universe uArtifact uEvidence

variable {target : AdmissionObject.{uArtifact}}

/-- Each constructor carries only the input of its actual service face.
Proof objects have the guest's syntax; they need not yet judge the claim. -/
inductive Request : Service.{uArtifact, uEvidence} target →
    Type (max (uArtifact + 1) (uEvidence + 1)) where
  | directDecision {kernel : Checker.DecisionKernel target.Carrier target.Meaning}
      (claim : target.Carrier) : Request (.directDecision kernel)
  | nativeProof {guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier}
      {kernel : NativeProofKernel guest}
      {exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim)}
      (claim : target.Carrier) (proof : guest.ProofObject) :
      Request (.nativeProof guest kernel exactMeaning)
  | nativeOperation {source : AdmissionObject.{uArtifact}}
      {operation : source ⟶ target} (input : source.Carrier) :
      Request (.nativeOperation source operation)
  | certificateBoundary {Certificate : Type uEvidence}
      {checker : Checker target.Carrier Certificate}
      {authority : checker.Authority target.Meaning}
      (claim : target.Carrier) (certificate : Certificate) :
      Request (.certificateBoundary Certificate checker authority)

/-- The original request indexes every response, retaining its claim and
submitted proof/certificate. Rejection of evidence is not a negative decision. -/
inductive Response : {service : Service.{uArtifact, uEvidence} target} →
    Request service → Type (max (uArtifact + 1) (uEvidence + 1)) where
  | decided {kernel claim} (verdict : Bool) :
      Response (Request.directDecision (kernel := kernel) claim)
  | proofChecked {guest kernel exactMeaning claim proof} (accepted : Bool) :
      Response (Request.nativeProof (guest := guest) (kernel := kernel)
        (exactMeaning := exactMeaning) claim proof)
  | produced {source operation input} (value : target.Carrier) :
      Response (Request.nativeOperation (source := source) (operation := operation) input)
  | boundaryChecked {Certificate checker authority claim certificate} (accepted : Bool) :
      Response (Request.certificateBoundary (Certificate := Certificate)
        (checker := checker) (authority := authority) claim certificate)

/-- Only native operation execution needs a separately admitted source.
The other constructors introduce no extra source precondition. -/
inductive InputAdmission : {service : Service.{uArtifact, uEvidence} target} →
    Request service → Prop where
  | directDecision {kernel claim} :
      InputAdmission (Request.directDecision (kernel := kernel) claim)
  | nativeProof {guest kernel exactMeaning claim proof} :
      InputAdmission (Request.nativeProof (guest := guest) (kernel := kernel)
        (exactMeaning := exactMeaning) claim proof)
  | nativeOperation {source operation input} (meaningful : source.Meaning input) :
      InputAdmission (Request.nativeOperation (source := source) (operation := operation) input)
  | certificateBoundary {Certificate checker authority claim certificate} :
      InputAdmission (Request.certificateBoundary (Certificate := Certificate)
        (checker := checker) (authority := authority) claim certificate)

/-- Execute the supplied kernel/checker or the actual admitted arrow's raw
function. No semantic source judgment is decided by this function. -/
def invoke {service : Service.{uArtifact, uEvidence} target}
    (request : Request service) : Response request := by
  cases request with
  | @directDecision kernel claim => exact .decided (kernel.decide claim)
  | @nativeProof guest kernel exactMeaning claim proof =>
      exact .proofChecked (kernel.decide claim proof)
  | @nativeOperation source operation input => exact .produced (operation.run input)
  | @certificateBoundary Certificate checker authority claim certificate =>
      exact .boundaryChecked (checker.check claim certificate)

/-- The value usable by a success-only continuation. For the three checking
faces this is exactly the submitted claim, never a substituted target. -/
def Response.acceptedValue {service : Service.{uArtifact, uEvidence} target}
    {request : Request service} (response : Response request) : Option target.Carrier := by
  cases response with
  | @decided kernel claim verdict => exact if verdict then some claim else none
  | @proofChecked guest kernel exactMeaning claim proof accepted =>
      exact if accepted then some claim else none
  | @produced source operation input value => exact some value
  | @boundaryChecked Certificate checker authority claim certificate accepted =>
      exact if accepted then some claim else none

theorem direct_decision_true_iff
    (kernel : Checker.DecisionKernel target.Carrier target.Meaning)
    (claim : target.Carrier) :
    invoke (Request.directDecision (kernel := kernel) claim) = .decided true ↔
      target.Meaning claim := by
  simpa [invoke] using kernel.correct claim

/-- Unlike evidence rejection, a negative direct decision refutes meaning. -/
theorem direct_decision_false_iff
    (kernel : Checker.DecisionKernel target.Carrier target.Meaning)
    (claim : target.Carrier) :
    invoke (Request.directDecision (kernel := kernel) claim) = .decided false ↔
      ¬ target.Meaning claim := by
  rw [← kernel.correct]
  cases verdict : kernel.decide claim <;> simp [invoke, verdict]

theorem native_proof_checked_iff
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) (proof : guest.ProofObject) :
    invoke (Request.nativeProof (kernel := kernel) (exactMeaning := exactMeaning) claim proof) =
        .proofChecked true ↔ guest.Judges proof claim := by
  simpa [invoke] using kernel.correct claim proof

/-- The failed native object does not judge this claim. The theorem does
not say that the guest's entire proof fibre is empty. -/
theorem native_proof_rejected_iff
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) (proof : guest.ProofObject) :
    invoke (Request.nativeProof (kernel := kernel) (exactMeaning := exactMeaning) claim proof) =
        .proofChecked false ↔ ¬ guest.Judges proof claim := by
  rw [← kernel.correct]
  cases verdict : kernel.decide claim proof <;> simp [invoke, verdict]

theorem boundary_checked_iff
    {Certificate : Type uEvidence} (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) (certificate : Certificate) :
    invoke (Request.certificateBoundary (checker := checker) (authority := authority)
      claim certificate) = .boundaryChecked true ↔ checker.check claim certificate = true := by
  simp [invoke]

theorem boundary_rejected_iff
    {Certificate : Type uEvidence} (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) (certificate : Certificate) :
    invoke (Request.certificateBoundary (checker := checker) (authority := authority)
      claim certificate) = .boundaryChecked false ↔ checker.check claim certificate = false := by
  simp [invoke]

/-- Acceptance retains the submitted native claim as well as checking its
submitted proof. No other target claim can be returned by this crossing. -/
theorem native_proof_value_iff
    (guest : NativeProofSystem.{uArtifact, uEvidence} target.Carrier)
    (kernel : NativeProofKernel guest)
    (exactMeaning : ∀ claim, target.Meaning claim ↔ Nonempty (guest.ProofFibre claim))
    (claim : target.Carrier) (proof : guest.ProofObject) (value : target.Carrier) :
    (invoke (Request.nativeProof (kernel := kernel) (exactMeaning := exactMeaning)
      claim proof)).acceptedValue = some value ↔
      kernel.decide claim proof = true ∧ value = claim := by
  cases verdict : kernel.decide claim proof <;>
    simp [invoke, Response.acceptedValue, verdict, eq_comm]

/-- The corresponding target binding for a genuinely external certificate. -/
theorem boundary_value_iff
    {Certificate : Type uEvidence} (checker : Checker target.Carrier Certificate)
    (authority : checker.Authority target.Meaning)
    (claim : target.Carrier) (certificate : Certificate) (value : target.Carrier) :
    (invoke (Request.certificateBoundary (checker := checker) (authority := authority)
      claim certificate)).acceptedValue = some value ↔
      checker.check claim certificate = true ∧ value = claim := by
  cases verdict : checker.check claim certificate <;>
    simp [invoke, Response.acceptedValue, verdict, eq_comm]

theorem native_operation_produces
    {source : AdmissionObject.{uArtifact}} (operation : source ⟶ target)
    (input : source.Carrier) :
    invoke (Request.nativeOperation (operation := operation) input) =
      .produced (operation.run input) := rfl

theorem native_operation_input_admission_iff
    {source : AdmissionObject.{uArtifact}} (operation : source ⟶ target)
    (input : source.Carrier) :
    InputAdmission (Request.nativeOperation (operation := operation) input) ↔
      source.Meaning input := by
  constructor
  · intro admitted
    cases admitted with
    | nativeOperation meaningful => exact meaningful
  · exact InputAdmission.nativeOperation

/-- Every successful actual invocation supplies target meaning, using the
operation face's real source premise and the other faces' existing kernels. -/
theorem accepted_meaning {service : Service.{uArtifact, uEvidence} target}
    (request : Request service) (admitted : InputAdmission request)
    {value : target.Carrier} (accepted : (invoke request).acceptedValue = some value) :
    target.Meaning value := by
  cases request with
  | @directDecision kernel claim =>
      simp only [invoke, Response.acceptedValue] at accepted
      split at accepted
      · obtain rfl := Option.some.inj accepted
        exact (kernel.correct claim).mp ‹kernel.decide claim = true›
      · cases accepted
  | @nativeProof guest kernel exactMeaning claim proof =>
      simp only [invoke, Response.acceptedValue] at accepted
      split at accepted
      · obtain rfl := Option.some.inj accepted
        exact (exactMeaning claim).mpr
          ⟨⟨proof, (kernel.correct claim proof).mp ‹kernel.decide claim proof = true›⟩⟩
      · cases accepted
  | @nativeOperation source operation input =>
      cases admitted with
      | nativeOperation meaningful =>
          obtain rfl := Option.some.inj accepted
          exact operation.preserves input meaningful
  | @certificateBoundary Certificate checker authority claim certificate =>
      simp only [invoke, Response.acceptedValue] at accepted
      split at accepted
      · obtain rfl := Option.some.inj accepted
        exact authority.sound claim certificate ‹checker.check claim certificate = true›
      · cases accepted

/-- Execute an already admitted continuation on the actual returned value.
The original indexed response is not rewritten or recoded as a certificate. -/
def continueWith {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) {service : Service.{uArtifact, uEvidence} target}
    {request : Request service} (response : Response request) : Option later.Carrier :=
  response.acceptedValue.map operation.run

theorem continuation_preserves {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) {service : Service.{uArtifact, uEvidence} target}
    (request : Request service) (admitted : InputAdmission request)
    {output : later.Carrier} (returned : continueWith operation (invoke request) = some output) :
    later.Meaning output := by
  obtain ⟨value, accepted, rfl⟩ := Option.map_eq_some_iff.mp returned
  exact operation.preserves value (accepted_meaning request admitted accepted)

/-- Rejected replies do not silently run a success continuation. -/
theorem no_continuation_of_no_value {later : AdmissionObject.{uArtifact}}
    (operation : target ⟶ later) {service : Service.{uArtifact, uEvidence} target}
    {request : Request service} (response : Response request)
    (rejected : response.acceptedValue = none) : continueWith operation response = none := by
  simp [continueWith, rejected]

/-! ## Four actual inputs, one nonidentity continuation, and failed evidence -/

namespace PositiveNaturalControl

open AdmissionCanary

/-- The native guest's positive-number introduction proof syntax. -/
inductive Proof where
  | successor (predecessor : Nat)

def guest : NativeProofSystem.{0, 0} Nat where
  ProofObject := Proof
  Judges proof claim := match proof with
    | .successor predecessor => claim = predecessor + 1

/-- This kernel checks the submitted introduction and its claimed result;
it does not synthesize a proof from the claim. -/
def kernel : NativeProofKernel guest where
  decide claim proof := match proof with
    | .successor predecessor => decide (claim = predecessor + 1)
  correct claim proof := by cases proof; simp [guest]

theorem guest_exact (claim : Nat) :
    positiveNaturals.Meaning claim ↔ Nonempty (guest.ProofFibre claim) := by
  constructor
  · intro meaningful
    obtain ⟨predecessor, equal⟩ := Nat.exists_eq_succ_of_ne_zero meaningful
    exact ⟨⟨.successor predecessor, equal⟩⟩
  · rintro ⟨⟨proof, judged⟩⟩
    cases proof with
    | successor predecessor =>
        change claim = predecessor + 1 at judged
        change claim ≠ 0
        omega

def proofService : Service.{0, 0} positiveNaturals :=
  .nativeProof guest kernel guest_exact

/-- A different, external evidence language: finite Boolean words witness
a positive number by their length. Their symbols remain boundary evidence. -/
def wordChecker : Checker Nat (List Bool) where
  check claim certificate := decide (claim = certificate.length + 1)

theorem wordAuthority : wordChecker.Authority positiveNaturals.Meaning where
  sound claim certificate accepted := by
    have equal : claim = certificate.length + 1 := by simpa [wordChecker] using accepted
    change claim ≠ 0
    omega
  complete claim meaningful := by
    obtain ⟨predecessor, equal⟩ := Nat.exists_eq_succ_of_ne_zero meaningful
    exact ⟨List.replicate predecessor false, by simp [wordChecker, equal]⟩

def boundaryService : Service.{0, 0} positiveNaturals :=
  .certificateBoundary (List Bool) wordChecker wordAuthority

def decisionRequest : Request (NIK.Canary.direct : Service.{0, 0} positiveNaturals) :=
  .directDecision (2 : Nat)

def proofRequest : Request proofService := .nativeProof (2 : Nat) (Proof.successor 1)

def operationRequest : Request (NIK.Canary.native : Service.{0, 0} positiveNaturals) :=
  .nativeOperation (1 : Nat)

def boundaryRequest : Request boundaryService := .certificateBoundary (2 : Nat) [false]

/-- Every face really executes its own input and returns the common value
two. The native operation starts from one, not from a submitted target claim. -/
theorem four_invocations :
    invoke decisionRequest = .decided true ∧
      invoke proofRequest = .proofChecked true ∧
      invoke operationRequest = .produced (2 : Nat) ∧
      invoke boundaryRequest = .boundaryChecked true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The existing nonidentity admitted successor continues all four actual
crossings. Semantic admission is obtained through the common theorem. -/
theorem four_continuations :
    continueWith successor (invoke decisionRequest) = some (3 : Nat) ∧
      continueWith successor (invoke proofRequest) = some (3 : Nat) ∧
      continueWith successor (invoke operationRequest) = some (3 : Nat) ∧
      continueWith successor (invoke boundaryRequest) = some (3 : Nat) ∧
      positiveNaturals.Meaning (3 : Nat) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact continuation_preserves successor operationRequest
    (.nativeOperation (Nat.succ_ne_zero 0)) rfl

/-- The claim is meaningful and has an accepted native proof, yet a
different submitted proof is rejected and cannot run the continuation. -/
theorem bad_native_proof_does_not_refute :
    positiveNaturals.Meaning (2 : Nat) ∧
      invoke proofRequest = .proofChecked true ∧
      invoke (Request.nativeProof (target := positiveNaturals)
        (kernel := kernel) (exactMeaning := guest_exact)
        (2 : Nat) (Proof.successor 0)) = .proofChecked false ∧
      continueWith successor
        (invoke (Request.nativeProof (target := positiveNaturals)
          (kernel := kernel) (exactMeaning := guest_exact)
          (2 : Nat) (Proof.successor 0))) = none := by
  exact ⟨Nat.succ_ne_zero 1, rfl, rfl, rfl⟩

/-- Rejection of an external certificate likewise does not negate its
claim, even though accepted certificates are semantically authoritative. -/
theorem bad_certificate_does_not_refute :
    positiveNaturals.Meaning (2 : Nat) ∧
      invoke boundaryRequest = .boundaryChecked true ∧
      invoke (Request.certificateBoundary (target := positiveNaturals)
        (checker := wordChecker) (authority := wordAuthority) (2 : Nat) []) = .boundaryChecked false ∧
      continueWith successor
        (invoke (Request.certificateBoundary (target := positiveNaturals)
          (checker := wordChecker) (authority := wordAuthority) (2 : Nat) [])) = none := by
  exact ⟨Nat.succ_ne_zero 1, rfl, rfl, rfl⟩

/-- Changing only the submitted claim rejects both of these previously
accepted evidence objects; the changed claim is still a meaningful number. -/
theorem altered_claim_rejected :
    positiveNaturals.Meaning (3 : Nat) ∧
      invoke (Request.nativeProof (target := positiveNaturals)
        (kernel := kernel) (exactMeaning := guest_exact)
        (3 : Nat) (Proof.successor 1)) = .proofChecked false ∧
      invoke (Request.certificateBoundary (target := positiveNaturals)
        (checker := wordChecker) (authority := wordAuthority) (3 : Nat) [false]) =
        .boundaryChecked false := by
  exact ⟨Nat.succ_ne_zero 2, rfl, rfl⟩

/-- Zero is a genuinely false direct decision, a different outcome from
rejected evidence for the meaningful claims above. -/
theorem false_decision_refutes :
    invoke (Request.directDecision.{0, 0} (target := positiveNaturals)
      (kernel := NIK.Canary.nonzeroDecision) (0 : Nat)) =
        .decided false ∧ ¬ positiveNaturals.Meaning (0 : Nat) := by
  exact ⟨rfl, (direct_decision_false_iff.{0, 0} (target := positiveNaturals)
    NIK.Canary.nonzeroDecision (0 : Nat)).mp rfl⟩

/-- The admitted range of successor is a proper subset of target meaning:
one is meaningful but no meaningful source input produces it. -/
theorem native_admitted_range_is_proper :
    positiveNaturals.Meaning (1 : Nat) ∧
      ¬ ∃ request : Request (NIK.Canary.native : Service.{0, 0} positiveNaturals),
        InputAdmission request ∧ (invoke request).acceptedValue = some (1 : Nat) := by
  refine ⟨Nat.succ_ne_zero 0, ?_⟩
  rintro ⟨request, admitted, returned⟩
  cases request with
  | nativeOperation input =>
      cases admitted with
      | nativeOperation meaningful =>
          have equal : Nat.succ input = (1 : Nat) := Option.some.inj returned
          exact meaningful (Nat.succ.inj equal)

/-- A nonidentity operation whose source premise really matters for raw
execution: doubling a non-admitted zero returns non-admitted zero. -/
def doubling : positiveNaturals ⟶ positiveNaturals where
  run (value : Nat) := value + value
  preserves value meaningful := by
    intro zero
    exact meaningful (Nat.add_eq_zero_iff.mp zero).1

theorem raw_operation_is_not_source_admission :
    invoke (Request.nativeOperation (operation := doubling) (0 : Nat)) = .produced (0 : Nat) ∧
      ¬ InputAdmission (Request.nativeOperation (operation := doubling) (0 : Nat)) ∧
      ¬ positiveNaturals.Meaning (0 : Nat) := by
  refine ⟨rfl, ?_, fun meaningful => meaningful rfl⟩
  intro admitted
  exact ((native_operation_input_admission_iff doubling (0 : Nat)).mp admitted) rfl

end PositiveNaturalControl

#print axioms direct_decision_true_iff
#print axioms direct_decision_false_iff
#print axioms native_proof_checked_iff
#print axioms native_proof_rejected_iff
#print axioms boundary_checked_iff
#print axioms boundary_rejected_iff
#print axioms native_proof_value_iff
#print axioms boundary_value_iff
#print axioms native_operation_input_admission_iff
#print axioms accepted_meaning
#print axioms continuation_preserves
#print axioms no_continuation_of_no_value
#print axioms PositiveNaturalControl.guest_exact
#print axioms PositiveNaturalControl.wordAuthority
#print axioms PositiveNaturalControl.four_invocations
#print axioms PositiveNaturalControl.four_continuations
#print axioms PositiveNaturalControl.bad_native_proof_does_not_refute
#print axioms PositiveNaturalControl.bad_certificate_does_not_refute
#print axioms PositiveNaturalControl.altered_claim_rejected
#print axioms PositiveNaturalControl.false_decision_refutes
#print axioms PositiveNaturalControl.native_admitted_range_is_proper
#print axioms PositiveNaturalControl.raw_operation_is_not_source_admission

end Mettapedia.GSLT.LanguageDef.NIKServiceInvocation
