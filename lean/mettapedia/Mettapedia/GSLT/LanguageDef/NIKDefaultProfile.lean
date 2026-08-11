import Mettapedia.GSLT.Core.ClosureCriteria
import Mettapedia.GSLT.LanguageDef.NIKGSLT

/-!
# The open, statusful default NIK profile

The Boolean checker is the trusted semantic core of one authority, but it is
not an adequate public protocol for untrusted requests.  Before a checker can
return `true` or `false`, a request must parse and resolve to an installed,
typed authority.  This module separates those stages and exposes four logical
outcomes:

* `malformed`: the request did not parse;
* `unsupported`: it parsed, but no declared authority resolved it;
* `rejected`: a resolved authority replayed the evidence and returned false;
* `accepted`: a resolved authority replayed the evidence and returned true.

Operational expiration is a separate result layer.  In particular, an
expired native run is neither rejection nor unsupported evidence.

The concrete request grammar, authority identifiers, registry representation,
and internal scheduler are deliberately parameters.  The stable object is
the status algebra and its exact refinement laws, not a prematurely fixed ABI.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ClosureCriteria
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKGSLT

universe uKind uClaim uCertificate uRequest uParsed uMachine uResidual uFault

/-! ## Typed submissions and public outcomes -/

/-- A request whose claim and certificate are already known to belong to the
same authority fibre.  This dependent pair makes cross-authority coercion
unrepresentable after successful resolution. -/
abbrev TypedSubmission {Kind : Type uKind} (family : AuthorityFamily Kind) :=
  Sigma fun kind => family.Claim kind × family.Certificate kind

namespace TypedSubmission

variable {Kind : Type uKind} {family : AuthorityFamily Kind}

/-- Forget the certificate while retaining the selected authority tag. -/
def claim (submission : TypedSubmission family) : family.PackedClaim :=
  ⟨submission.1, submission.2.1⟩

@[simp] theorem claim_mk (kind : Kind) (payload : family.Claim kind)
    (certificate : family.Certificate kind) :
    TypedSubmission.claim ⟨kind, payload, certificate⟩ = ⟨kind, payload⟩ :=
  rfl

end TypedSubmission

/-- The logical result of one fully completed NIK request.  The certificate
may be retained by an execution receipt; the public logical result needs only
the typed claim. -/
inductive SubmissionOutcome (Claim : Type uClaim) where
  | malformed
  | unsupported
  | rejected (claim : Claim)
  | accepted (claim : Claim)
deriving Repr

namespace SubmissionOutcome

variable {Claim : Type uClaim}

theorem malformed_ne_unsupported :
    (malformed : SubmissionOutcome Claim) ≠ unsupported := by
  intro equal
  cases equal

theorem malformed_ne_rejected (claim : Claim) :
    (malformed : SubmissionOutcome Claim) ≠ rejected claim := by
  intro equal
  cases equal

theorem unsupported_ne_rejected (claim : Claim) :
    (unsupported : SubmissionOutcome Claim) ≠ rejected claim := by
  intro equal
  cases equal

theorem rejected_ne_accepted (rejectedClaim acceptedClaim : Claim) :
    (rejected rejectedClaim : SubmissionOutcome Claim) ≠
      accepted acceptedClaim := by
  intro equal
  cases equal

end SubmissionOutcome

/-! ## Open request resolution -/

/-- A two-stage, fail-closed request boundary.

Parsing answers only whether the request has valid syntax.  Resolution then
consults the open, versioned authority environment and either produces a
typed submission or reports that the parsed request is unsupported.  A
canonical encoder is included so certificate completeness survives transport
to the request carrier. -/
structure Frontend {Kind : Type uKind} (family : AuthorityFamily Kind)
    (Request : Type uRequest) where
  Parsed : Type uParsed
  parse : Request → Option Parsed
  resolve : Parsed → Option (TypedSubmission family)
  encode : TypedSubmission family → Request
  resolve_encode : ∀ submission, ∃ parsed,
    parse (encode submission) = some parsed ∧
      resolve parsed = some submission

namespace Frontend

variable {Kind : Type uKind} {family : AuthorityFamily Kind}
    {Request : Type uRequest}

/-- The canonical no-serialization frontend.  It is useful as the semantic
reference underneath every concrete parser, codec, or registry. -/
def typed (family : AuthorityFamily Kind) :
    Frontend family (TypedSubmission family) where
  Parsed := TypedSubmission family
  parse := some
  resolve := some
  encode := id
  resolve_encode := by
    intro submission
    exact ⟨submission, rfl, rfl⟩

/-- Build a fail-closed public frontend from any faithful partial request
codec.  Failed decoding is `malformed`; successful decoding is already a
typed submission and therefore needs no authority guess or cross-tag cast. -/
def ofRequestCodec (family : AuthorityFamily Kind) {Request : Type uRequest}
    (codec : Checker.PartialCodec (TypedSubmission family) Request) :
    Frontend family Request where
  Parsed := TypedSubmission family
  parse := codec.decode
  resolve := some
  encode := codec.encode
  resolve_encode := by
    intro submission
    exact ⟨submission, codec.decode_encode submission, rfl⟩

@[simp] theorem ofRequestCodec_parse
    (family : AuthorityFamily Kind) {Request : Type uRequest}
    (codec : Checker.PartialCodec (TypedSubmission family) Request)
    (request : Request) :
    (ofRequestCodec family codec).parse request = codec.decode request :=
  rfl

/-- Execute the public logical protocol.  This is a total reference function,
not a requirement that a native implementation execute atomically. -/
def run (frontend : Frontend family Request) (request : Request) :
    SubmissionOutcome family.PackedClaim :=
  match frontend.parse request with
  | none => .malformed
  | some parsed =>
      match frontend.resolve parsed with
      | none => .unsupported
      | some submission =>
          match (family.checker submission.1).check
              submission.2.1 submission.2.2 with
          | false => .rejected submission.claim
          | true => .accepted submission.claim

@[simp] theorem run_of_parse_none (frontend : Frontend family Request)
    {request : Request} (malformed : frontend.parse request = none) :
    frontend.run request = .malformed := by
  simp [run, malformed]

/-- A request rejected by the decoder has the logical status `malformed`,
not `unsupported` and not a false guest judgment. -/
theorem ofRequestCodec_decode_none
    (family : AuthorityFamily Kind)
    (codec : Checker.PartialCodec (TypedSubmission family) Request)
    {request : Request} (invalid : codec.decode request = none) :
    (ofRequestCodec family codec).run request = .malformed := by
  exact Frontend.run_of_parse_none _ invalid

@[simp] theorem run_of_resolve_none (frontend : Frontend family Request)
    {request : Request} {parsed : frontend.Parsed}
    (parsedRequest : frontend.parse request = some parsed)
    (unsupported : frontend.resolve parsed = none) :
    frontend.run request = .unsupported := by
  simp [run, parsedRequest, unsupported]

@[simp] theorem run_of_check_false (frontend : Frontend family Request)
    {request : Request} {parsed : frontend.Parsed}
    {submission : TypedSubmission family}
    (parsedRequest : frontend.parse request = some parsed)
    (resolved : frontend.resolve parsed = some submission)
    (rejected : (family.checker submission.1).check
      submission.2.1 submission.2.2 = false) :
    frontend.run request = .rejected submission.claim := by
  simp [run, parsedRequest, resolved, rejected]

@[simp] theorem run_of_check_true (frontend : Frontend family Request)
    {request : Request} {parsed : frontend.Parsed}
    {submission : TypedSubmission family}
    (parsedRequest : frontend.parse request = some parsed)
    (resolved : frontend.resolve parsed = some submission)
    (accepted : (family.checker submission.1).check
      submission.2.1 submission.2.2 = true) :
    frontend.run request = .accepted submission.claim := by
  simp [run, parsedRequest, resolved, accepted]

/-- Canonical encoding cannot produce `malformed` or `unsupported`; it reaches
the exact Boolean verdict of the selected authority. -/
theorem run_encode (frontend : Frontend family Request)
    (submission : TypedSubmission family) :
    frontend.run (frontend.encode submission) =
      match (family.checker submission.1).check
          submission.2.1 submission.2.2 with
      | false => .rejected submission.claim
      | true => .accepted submission.claim := by
  obtain ⟨parsed, parsedRequest, resolved⟩ :=
    frontend.resolve_encode submission
  simp [run, parsedRequest, resolved]

/-- Public acceptance establishes the exact certificate scope of the resolved
authority.  Neither parsing nor successful registry lookup contributes this
semantic fact. -/
theorem accepted_implies_certified (frontend : Frontend family Request)
    {request : Request} {claim : family.PackedClaim}
    (accepted : frontend.run request = .accepted claim) :
    family.packedCertified claim := by
  unfold run at accepted
  cases parsedRequest : frontend.parse request with
  | none => simp [parsedRequest] at accepted
  | some parsed =>
      cases resolved : frontend.resolve parsed with
      | none => simp [parsedRequest, resolved] at accepted
      | some submission =>
          cases checked : (family.checker submission.1).check
              submission.2.1 submission.2.2 with
          | false => simp [parsedRequest, resolved, checked] at accepted
          | true =>
              have sameClaim : submission.claim = claim := by
                simpa [parsedRequest, resolved, checked] using accepted
              rw [← sameClaim]
              exact (family.projection submission.1).authority.sound
                submission.2.1 submission.2.2 checked

/-- The semantic projection remains explicit: acceptance first establishes
the authority's exact certificate scope, which then projects to guest meaning. -/
theorem accepted_implies_meaning (frontend : Frontend family Request)
    {request : Request} {claim : family.PackedClaim}
    (accepted : frontend.run request = .accepted claim) :
    family.packedMeaning claim :=
  family.packedCertified_implies_meaning claim
    (frontend.accepted_implies_certified accepted)

/-- Certificate completeness survives the canonical request encoding. -/
theorem certified_has_accepted_request (frontend : Frontend family Request)
    (claim : family.PackedClaim) (certified : family.packedCertified claim) :
    ∃ certificate : family.Certificate claim.1,
      frontend.run
        (frontend.encode ⟨claim.1, claim.2, certificate⟩) =
          .accepted claim := by
  rcases claim with ⟨kind, claim⟩
  obtain ⟨certificate, accepted⟩ :=
    (family.projection kind).authority.complete claim certified
  refine ⟨certificate, ?_⟩
  simpa [TypedSubmission.claim, accepted] using
    frontend.run_encode
      (⟨kind, claim, certificate⟩ : TypedSubmission family)

/-- The strongest completeness statement justified by an authority family:
membership in the declared certified scope is exactly existence of a
canonically encoded request that completes with acceptance. -/
theorem certified_iff_exists_accepted_request
    (frontend : Frontend family Request) (claim : family.PackedClaim) :
    family.packedCertified claim ↔
      ∃ certificate : family.Certificate claim.1,
        frontend.run
          (frontend.encode ⟨claim.1, claim.2, certificate⟩) =
            .accepted claim := by
  constructor
  · exact frontend.certified_has_accepted_request claim
  · rintro ⟨certificate, accepted⟩
    exact frontend.accepted_implies_certified accepted

end Frontend

/-! ## The statusful reference GSLT -/

namespace Atomic

variable {Kind : Type uKind} {family : AuthorityFamily Kind}
    {Request : Type uRequest}

/-- Public configurations of the statusful request protocol. -/
inductive State (Request : Type uRequest) (Claim : Type uClaim) where
  | submitted (request : Request)
  | completed (outcome : SubmissionOutcome Claim)

/-- One reference transition computes exactly one completed logical outcome. -/
def Step (frontend : Frontend family Request) :
    State Request family.PackedClaim → State Request family.PackedClaim → Prop
  | .submitted request, .completed outcome => outcome = frontend.run request
  | _, _ => False

/-- The atomic reference presentation of the default NIK profile. -/
def theory (frontend : Frontend family Request) : GSLT where
  Term := State Request family.PackedClaim
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step frontend
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

@[simp] theorem submitted_step_completed_iff
    (frontend : Frontend family Request) (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) :
    (theory frontend).Step (.submitted request) (.completed outcome) ↔
      frontend.run request = outcome := by
  simp [theory, GSLT.Step, Step, eq_comm]

theorem completed_noStep (frontend : Frontend family Request)
    (outcome : SubmissionOutcome family.PackedClaim) (target) :
    ¬ (theory frontend).Step (.completed outcome) target := by
  cases target <;> simp [theory, GSLT.Step, Step]

/-- Completed-outcome reachability is exactly equality with the total
reference function. -/
theorem submitted_multiStep_completed_iff
    (frontend : Frontend family Request) (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) :
    (theory frontend).MultiStep (.submitted request) (.completed outcome) ↔
      frontend.run request = outcome := by
  constructor
  · intro path
    rcases NIKGSLT.Atomic.multiStep_refl_or_step path with
      reflexive | ⟨middle, first, rest⟩
    · cases reflexive
    · cases middle with
      | submitted middleWire =>
          simp [theory, GSLT.Step, Step] at first
      | completed middleOutcome =>
          have middleIsRun : middleOutcome = frontend.run request := by
            simpa [theory, GSLT.Step, Step] using first
          subst middleOutcome
          have terminal := NIKGSLT.Atomic.multiStep_eq_of_noStep
            (completed_noStep frontend (frontend.run request)) rest
          injection terminal.symm
  · intro computed
    exact GSLT.MultiStep.step
      ((submitted_step_completed_iff frontend request outcome).2 computed)
      (@GSLT.MultiStep.refl (theory frontend) (State.completed outcome))

end Atomic

/-! ## Arbitrary staged/native refinements -/

namespace Refinement

variable {Kind : Type uKind} {family : AuthorityFamily Kind}
    {Request : Type uRequest}

/-- A staged implementation may use any internal configurations.  It realizes
the default profile exactly when reachability of every public outcome agrees
with the reference frontend. -/
structure Machine (frontend : Frontend family Request) where
  theory : GSLT.{uMachine}
  submit : Request → theory.Term
  completed : SubmissionOutcome family.PackedClaim → theory.Term
  completes_iff : ∀ request outcome,
    theory.MultiStep (submit request) (completed outcome) ↔
      frontend.run request = outcome

/-- The atomic statusful GSLT realizes its own contract. -/
def atomic (frontend : Frontend family Request) : Machine frontend where
  theory := Atomic.theory frontend
  submit := Atomic.State.submitted
  completed := Atomic.State.completed
  completes_iff := Atomic.submitted_multiStep_completed_iff frontend

/-- Two independently implemented machines refining the same frontend agree
on every public result.  This is the core Stage-0/Stage-1 agreement theorem
for a Lean reference and a native Prime realization. -/
theorem machines_agree (frontend : Frontend family Request)
    (first second : Machine frontend) (request : Request)
    (outcome : SubmissionOutcome family.PackedClaim) :
    first.theory.MultiStep (first.submit request) (first.completed outcome) ↔
      second.theory.MultiStep (second.submit request)
        (second.completed outcome) :=
  (first.completes_iff request outcome).trans
    (second.completes_iff request outcome).symm

/-- Acceptance in any exact staged implementation inherits guest meaning from
the independently admitted authority family. -/
theorem acceptance_implies_meaning (frontend : Frontend family Request)
    (machine : Machine frontend) {request : Request}
    {claim : family.PackedClaim}
    (path : machine.theory.MultiStep (machine.submit request)
      (machine.completed (.accepted claim))) :
    family.packedMeaning claim := by
  apply frontend.accepted_implies_meaning
  exact (machine.completes_iff request (.accepted claim)).mp path

/-- Exact certificate scope remains complete for every staged realization. -/
theorem certified_has_accepting_execution (frontend : Frontend family Request)
    (machine : Machine frontend) (claim : family.PackedClaim)
    (certified : family.packedCertified claim) :
    ∃ certificate : family.Certificate claim.1,
      machine.theory.MultiStep
        (machine.submit
          (frontend.encode ⟨claim.1, claim.2, certificate⟩))
        (machine.completed (.accepted claim)) := by
  obtain ⟨certificate, accepted⟩ :=
    frontend.certified_has_accepted_request claim certified
  exact ⟨certificate,
    (machine.completes_iff _ (.accepted claim)).2 accepted⟩

end Refinement

/-! ## Logical outcomes versus operational execution status -/

/-- The outer runtime result.  Logical completion, resumable resource
expiration, and implementation fault are pairwise distinct.  A concrete
driver should additionally satisfy the generic resumption laws in
`ClosureCriteria`. -/
inductive ExecutionReport (Claim : Type uClaim) (Residual : Type uResidual)
    (Fault : Type uFault) where
  | completed (outcome : SubmissionOutcome Claim)
  | expired (residual : Residual)
  | fault (fault : Fault)

namespace ExecutionReport

variable {Claim : Type uClaim} {Residual : Type uResidual}
    {Fault : Type uFault}

theorem expired_ne_completed (residual : Residual)
    (outcome : SubmissionOutcome Claim) :
    (expired residual : ExecutionReport Claim Residual Fault) ≠
      completed outcome := by
  intro equal
  cases equal

theorem fault_ne_rejected (faultEvidence : Fault) (claim : Claim) :
    (fault faultEvidence : ExecutionReport Claim Residual Fault) ≠
      completed (.rejected claim) := by
  intro equal
  cases equal

end ExecutionReport

/-! ## Observation of honest bounded drivers -/

namespace BoundedExecution

variable {Claim : Type uClaim} {theory : GSLT}

/-- Interpret an honest bounded-driver report at the NIK protocol boundary.
An unrecognized quiescent term is an implementation fault, while expiration
retains the complete residual configuration. -/
def observe (observeTerminal : theory.Term → Option (SubmissionOutcome Claim))
    {State : Type uResidual}
    (report : BoundedRunReport theory.Term State) :
    ExecutionReport Claim (theory.Term × State) (theory.Term × State) :=
  match report with
  | .completed term state =>
      match observeTerminal term with
      | some outcome => .completed outcome
      | none => .fault (term, state)
  | .expired term state => .expired (term, state)

@[simp] theorem observe_expired
    (observeTerminal : theory.Term → Option (SubmissionOutcome Claim))
    {State : Type uResidual} (term : theory.Term) (state : State) :
    observe observeTerminal (.expired term state) =
      (ExecutionReport.expired (term, state) :
        ExecutionReport Claim (theory.Term × State) (theory.Term × State)) :=
  rfl

@[simp] theorem observe_completed_some
    (observeTerminal : theory.Term → Option (SubmissionOutcome Claim))
    {State : Type uResidual} (term : theory.Term) (state : State)
    (outcome : SubmissionOutcome Claim)
    (recognized : observeTerminal term = some outcome) :
    observe observeTerminal (.completed term state) =
      (ExecutionReport.completed outcome :
        ExecutionReport Claim (theory.Term × State) (theory.Term × State)) := by
  simp [observe, recognized]

/-- An observed logical completion came from a quiescent report whose terminal
term was explicitly recognized; it cannot arise from expiration or fault. -/
theorem completed_observation_source
    (observeTerminal : theory.Term → Option (SubmissionOutcome Claim))
    {State : Type uResidual}
    {report : BoundedRunReport theory.Term State}
    {outcome : SubmissionOutcome Claim}
    (completed : observe observeTerminal report = .completed outcome) :
    ∃ term state,
      report = .completed term state ∧
        observeTerminal term = some outcome := by
  cases report with
  | expired term state => simp [observe] at completed
  | completed term state =>
      cases recognized : observeTerminal term with
      | none => simp [observe, recognized] at completed
      | some observed =>
          have sameOutcome : observed = outcome := by
            simpa [observe, recognized] using completed
          subst observed
          exact ⟨term, state, rfl, recognized⟩

/-- Expiration remains externally distinguishable and carries a residual with
a genuine next move.  This combines the NIK status observation with the
generic honest-fuel theorem rather than re-proving a special runner. -/
theorem expired_observation_has_next
    (driver : HostedDriver theory)
    (observeTerminal : theory.Term → Option (SubmissionOutcome Claim))
    {fuel : Nat} {term finalTerm : theory.Term}
    {state finalState : driver.State}
    (expired : driver.runReport term state fuel =
      .expired finalTerm finalState) :
    observe observeTerminal (driver.runReport term state fuel) =
        ExecutionReport.expired (finalTerm, finalState) ∧
      ∃ next nextState,
        driver.step finalTerm finalState = some (next, nextState) := by
  constructor
  · rw [expired]
    rfl
  · exact driver.runReport_expired_has_next expired

end BoundedExecution

/-! ## Executable separating examples -/

namespace Canary

inductive Kind where
  | truth
deriving DecidableEq, Repr

def family : AuthorityFamily Kind where
  Claim := fun _ => Bool
  Certificate := fun _ => Unit
  checker := fun _ => { check := fun claim _ => claim }
  Certified := fun _ claim => claim = true
  Meaning := fun _ claim => claim = true
  projection := by
    intro kind
    exact
      { authority :=
          { sound := by
              intro claim certificate accepted
              exact accepted
            complete := by
              intro claim meaningful
              exact ⟨(), by simp [meaningful]⟩ }
        project := by
          intro claim certified
          exact certified }

inductive Request where
  | malformed
  | unknownAuthority
  | knownTruth (claim : Bool)
deriving DecidableEq, Repr

inductive Parsed where
  | unknownAuthority
  | knownTruth (claim : Bool)

def frontend : Frontend family Request where
  Parsed := Parsed
  parse
    | .malformed => none
    | .unknownAuthority => some .unknownAuthority
    | .knownTruth claim => some (.knownTruth claim)
  resolve
    | .unknownAuthority => none
    | .knownTruth claim => some ⟨.truth, claim, ()⟩
  encode
    | ⟨.truth, claim, ()⟩ => .knownTruth claim
  resolve_encode := by
    rintro ⟨kind, claim, certificate⟩
    cases kind
    cases certificate
    exact ⟨.knownTruth claim, rfl, rfl⟩

def truthClaim (claim : Bool) : family.PackedClaim :=
  ⟨.truth, claim⟩

theorem malformed_is_not_rejection :
    frontend.run .malformed = .malformed ∧
      frontend.run .malformed ≠ .rejected (truthClaim false) := by
  constructor
  · rfl
  · intro equal
    cases equal

theorem unknown_is_not_rejection :
    frontend.run .unknownAuthority = .unsupported ∧
      frontend.run .unknownAuthority ≠ .rejected (truthClaim false) := by
  constructor
  · rfl
  · intro equal
    cases equal

theorem false_is_rejected :
    frontend.run (.knownTruth false) = .rejected (truthClaim false) :=
  rfl

theorem true_is_accepted :
    frontend.run (.knownTruth true) = .accepted (truthClaim true) :=
  rfl

theorem accepted_true_has_meaning : family.packedMeaning (truthClaim true) :=
  frontend.accepted_implies_meaning true_is_accepted

/-- Two exact implementations—here two copies of the reference machine—have
identical public acceptance behavior by theorem, not by implementation
identity. -/
theorem independent_machines_agree_on_true :
    (Refinement.atomic frontend).theory.MultiStep
        ((Refinement.atomic frontend).submit (.knownTruth true))
        ((Refinement.atomic frontend).completed (.accepted (truthClaim true))) ↔
      (Refinement.atomic frontend).theory.MultiStep
        ((Refinement.atomic frontend).submit (.knownTruth true))
        ((Refinement.atomic frontend).completed
          (.accepted (truthClaim true))) :=
  Refinement.machines_agree frontend
    (Refinement.atomic frontend) (Refinement.atomic frontend)
    (.knownTruth true) (.accepted (truthClaim true))

end Canary

end Mettapedia.GSLT.LanguageDef.NIKDefaultProfile
