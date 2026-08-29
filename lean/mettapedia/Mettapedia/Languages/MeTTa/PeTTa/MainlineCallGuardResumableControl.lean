import Mettapedia.GSLT.Core.OpenTotalityObservation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl

/-!
# Resumable interaction control for mainline PeTTa call guards

The completed-call controller observes already evaluated arguments and a
candidate result.  This module supplies the operational layer beneath that
denotation: call-start-pinned requests, correlated service responses, honest
open/closed/exhausted outcomes, and resumable residuals.

The type-query soft cut is operational.  A metatype request is issued only
after an exact-type request closes with coverage evidence and no occurrence.
An open, exhausted, cancelled, or faulted exact query is never reclassified as
closed absence.  Evaluation occurrences remain an ordered list, so branching
multiplicity is not silently quotiented.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardResumableControl

open Mettapedia.GSLT.Core.OpenTotalityObservation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

set_option autoImplicit false

/-! ## Call-start-pinned request and response protocol -/

/-- One operational call sees one immutable owned snapshot.  Run and branch
generation identity prevent responses from crossing continuation lifetimes. -/
structure CallScope where
  runId : Nat
  branchGeneration : Nat
  owned : OwnedSnapshot
deriving DecidableEq, Repr

structure RequestKey where
  runId : Nat
  branchGeneration : Nat
  requestId : Nat
  owner : SpaceOwner
  revision : Nat
  declarationOccurrence : Nat
deriving DecidableEq, Repr

inductive GuardPosition where
  | argument (index : Nat)
  | result
deriving DecidableEq, Repr

inductive ServiceRequestKind where
  | evaluateArgument (index : Nat) (source : Term)
  | queryExactType (position : GuardPosition) (value expected : Term)
  | queryMetatype (position : GuardPosition) (value expected : Term)
  | evaluateCall (function : String) (arguments : List Term)
deriving DecidableEq, Repr

structure ServiceRequest where
  key : RequestKey
  kind : ServiceRequestKind
deriving DecidableEq, Repr

namespace ServiceRequest

def PinnedTo (request : ServiceRequest) (scope : CallScope) : Prop :=
  request.key.runId = scope.runId ∧
    request.key.branchGeneration = scope.branchGeneration ∧
    request.key.owner = scope.owned.owner ∧
    request.key.revision = scope.owned.snapshot.revision

instance (request : ServiceRequest) (scope : CallScope) :
    Decidable (request.PinnedTo scope) := by
  unfold PinnedTo
  infer_instance

end ServiceRequest

structure ServiceResidual where
  request : ServiceRequest
  token : Nat
deriving DecidableEq, Repr

structure ServiceReceipt where
  token : Nat
deriving DecidableEq, Repr

inductive ServiceFault where
  | unavailable
  | invalidResponse
  | resourceLimit
deriving DecidableEq, Repr

/-- A captured residual is admitted only for the exact immutable request and
revision named by the response envelope. -/
def CaptureAdmitted (request : ServiceRequest) (residual : ServiceResidual)
    (revision : Nat) : Prop :=
  residual.request = request ∧ revision = request.key.revision

/-- An untrusted service envelope retains exact answer occurrences and the
generic completion/capture boundary.  The complete immutable request remains
explicit so a decoder can reject replayed, wrong-phase, wrong-position, or
cross-authority responses. -/
structure ServiceResponse (Answer Coverage : Type*) where
  request : ServiceRequest
  observation :
    Observation Answer ServiceResidual Nat Coverage Nat ServiceReceipt
      ServiceFault (CaptureAdmitted request)

namespace ServiceResponse

def resume? {Answer Coverage : Type*}
    (response : ServiceResponse Answer Coverage) :
    Option (ServiceResidual × Nat) :=
  response.observation.resume?

end ServiceResponse

inductive ResponseInvalidReason where
  | wrongRun
  | wrongBranch
  | foreignOwner
  | staleRevision
  | wrongRequest
  | wrongRequestKind
deriving DecidableEq, Repr

/-- Validation is deliberately ordered.  The call-start snapshot, not later
live mutation, determines currentness for the call.  Authority and
continuation failures remain distinct from a payload mismatch. -/
def validateResponse {Answer Coverage : Type*}
    (scope : CallScope) (request : ServiceRequest)
    (response : ServiceResponse Answer Coverage) :
    Option ResponseInvalidReason :=
  if request.key.runId != scope.runId then
    some .wrongRun
  else if request.key.branchGeneration != scope.branchGeneration then
    some .wrongBranch
  else if request.key.owner != scope.owned.owner then
    some .foreignOwner
  else if request.key.revision != scope.owned.snapshot.revision then
    some .staleRevision
  else if response.request.key.runId != scope.runId then
    some .wrongRun
  else if response.request.key.branchGeneration != scope.branchGeneration then
    some .wrongBranch
  else if response.request.key.owner != scope.owned.owner then
    some .foreignOwner
  else if response.request.key.revision != scope.owned.snapshot.revision then
    some .staleRevision
  else if response.request != request then
    some .wrongRequest
  else
    none

/-! ## Query closure evidence and soft-cut control -/

def ServiceRequestKind.QueryJudgment
    (snapshot : Snapshot) : ServiceRequestKind → Prop
  | .queryExactType _ value expected => GetType snapshot value expected
  | .queryMetatype _ value expected => GetMetatype snapshot value expected
  | .evaluateArgument _ _ | .evaluateCall _ _ => False

instance (snapshot : Snapshot) (kind : ServiceRequestKind) :
    Decidable (kind.QueryJudgment snapshot) := by
  cases kind <;> unfold ServiceRequestKind.QueryJudgment <;> infer_instance

/-- Hook adequacy for positive query occurrences.  Correlation authenticates
the request envelope; this predicate separately requires the service meaning
to justify every positive witness. -/
def QueryResponseSound {Coverage : Type*} (scope : CallScope)
    (request : ServiceRequest) (response : ServiceResponse Unit Coverage) :
    Prop :=
  response.observation.occurrences ≠ [] →
    request.kind.QueryJudgment scope.owned.snapshot

/-- Coverage for a closed query records whether a witness was found and proves
that this bit is exact for the requested authored judgment. -/
structure QueryCoverage (scope : CallScope) (request : ServiceRequest)
    where
  found : Bool
  found_iff :
    found = true ↔ request.kind.QueryJudgment scope.owned.snapshot

def ClosedFor (scope : CallScope) (request : ServiceRequest)
    (response : ServiceResponse Unit (QueryCoverage scope request)) : Prop :=
  ∃ coverage,
    response.observation.completion = .closed coverage ∧
      response.observation.occurrences =
        if coverage.found then [()] else []

inductive QueryAction where
  | accepted
  | requestMetatype (request : ServiceRequest)
  | rejected
  | open (resumable : Option (ServiceResidual × Nat))
  | exhausted (bound : Nat) (receipt : ServiceReceipt)
      (resumable : Option (ServiceResidual × Nat))
  | cancelled
  | resourceFault (fault : ServiceFault)
  | invalid (reason : ResponseInvalidReason)
deriving DecidableEq, Repr

def exactTypeRequest (key : RequestKey) (position : GuardPosition)
    (value expected : Term) : ServiceRequest :=
  ⟨key, .queryExactType position value expected⟩

def metatypeQueryRequest (key : RequestKey) (position : GuardPosition)
    (value expected : Term) : ServiceRequest :=
  ⟨key, .queryMetatype position value expected⟩

def metatypeRequest (requestId : Nat) (exactRequest : ServiceRequest) :
    Option ServiceRequest :=
  match exactRequest.kind with
  | .queryExactType position value expected =>
      some {
        key := { exactRequest.key with requestId := requestId }
        kind := .queryMetatype position value expected }
  | _ => none

@[simp] theorem metatypeRequest_exactTypeRequest
    (requestId : Nat) (key : RequestKey) (position : GuardPosition)
    (value expected : Term) :
    metatypeRequest requestId
      (exactTypeRequest key position value expected) =
        some (metatypeQueryRequest { key with requestId := requestId }
          position value expected) :=
  rfl

private def incompleteQueryAction {Coverage : Type*}
    (response : ServiceResponse Unit Coverage) : QueryAction :=
  match response.observation.completion with
  | .open _ _ => .open response.resume?
  | .closed _ => .rejected
  | .exhausted bound receipt =>
      .exhausted bound receipt response.resume?
  | .cancelled => .cancelled
  | .resourceFault fault => .resourceFault fault

/-- Resume an exact-type query.  Only closed empty coverage constructs the
metatype request; every incomplete stop remains semantically incomplete. -/
def resumeExactQuery {Coverage : Type*}
    (scope : CallScope) (nextRequestId : Nat)
    (request : ServiceRequest) (response : ServiceResponse Unit Coverage) :
    QueryAction :=
  match validateResponse scope request response with
  | some reason => .invalid reason
  | none =>
      match request.kind with
      | .queryExactType _ _ _ =>
          if response.observation.occurrences.isEmpty then
            match response.observation.completion with
            | .closed _ =>
                match metatypeRequest nextRequestId request with
                | some metatype => .requestMetatype metatype
                | none => .invalid .wrongRequestKind
            | _ => incompleteQueryAction response
          else
            .accepted
      | _ => .invalid .wrongRequestKind

/-- Resume a metatype query.  Closed empty coverage is ordinary guard
rejection; incomplete stops remain distinct from rejection. -/
def resumeMetatypeQuery {Coverage : Type*}
    (scope : CallScope) (request : ServiceRequest)
    (response : ServiceResponse Unit Coverage) : QueryAction :=
  match validateResponse scope request response with
  | some reason => .invalid reason
  | none =>
      match request.kind with
      | .queryMetatype _ _ _ =>
          if response.observation.occurrences.isEmpty then
            incompleteQueryAction response
          else
            .accepted
      | _ => .invalid .wrongRequestKind

theorem closedFor_nonempty_iff_judgment
    {scope : CallScope} {request : ServiceRequest}
    {response : ServiceResponse Unit (QueryCoverage scope request)}
    (closed : ClosedFor scope request response) :
    response.observation.occurrences ≠ [] ↔
      request.kind.QueryJudgment scope.owned.snapshot := by
  rcases closed with ⟨coverage, completion, occurrences⟩
  rw [occurrences]
  by_cases found : coverage.found = true
  · simp [found, coverage.found_iff.mp found]
  · have notJudgment : ¬ request.kind.QueryJudgment scope.owned.snapshot := by
      intro judgment
      exact found (coverage.found_iff.mpr judgment)
    simp [Bool.eq_false_of_not_eq_true found, notJudgment]

theorem closedFor_completion
    {scope : CallScope} {request : ServiceRequest}
    {response : ServiceResponse Unit (QueryCoverage scope request)}
    (closed : ClosedFor scope request response) :
    ∃ coverage, response.observation.completion = .closed coverage := by
  rcases closed with ⟨coverage, completion, _⟩
  exact ⟨coverage, completion⟩

theorem exact_closed_empty_requests_metatype
    {scope : CallScope} {nextRequestId : Nat}
    {request : ServiceRequest} {position : GuardPosition}
    {value expected : Term}
    {response : ServiceResponse Unit (QueryCoverage scope request)}
    (kind : request.kind = .queryExactType position value expected)
    (valid : validateResponse scope request response = none)
    (closed : ClosedFor scope request response)
    (empty : response.observation.occurrences = []) :
    resumeExactQuery scope nextRequestId request response =
      .requestMetatype {
        key := { request.key with requestId := nextRequestId }
        kind := .queryMetatype position value expected } := by
  rcases closedFor_completion closed with ⟨coverage, completion⟩
  simp [resumeExactQuery, valid, kind, empty, completion, metatypeRequest]

theorem exact_exhausted_never_requests_metatype
    {Coverage : Type*} {scope : CallScope} {nextRequestId : Nat}
    {request : ServiceRequest} {response : ServiceResponse Unit Coverage}
    {position : GuardPosition} {value expected : Term}
    {bound : Nat} {receipt : ServiceReceipt}
    (kind : request.kind = .queryExactType position value expected)
    (valid : validateResponse scope request response = none)
    (empty : response.observation.occurrences = [])
    (exhausted : response.observation.completion =
      .exhausted (Residual := ServiceResidual) (Revision := Nat)
        (Coverage := Coverage) (Fault := ServiceFault) bound receipt) :
    resumeExactQuery scope nextRequestId request response =
      .exhausted bound receipt response.resume? := by
  simp [resumeExactQuery, valid, kind, empty, exhausted,
    incompleteQueryAction]

theorem exact_success_never_requests_metatype
    {Coverage : Type*} {scope : CallScope} {nextRequestId : Nat}
    {request : ServiceRequest} {response : ServiceResponse Unit Coverage}
    {position : GuardPosition} {value expected : Term}
    (kind : request.kind = .queryExactType position value expected)
    (valid : validateResponse scope request response = none)
    (nonempty : response.observation.occurrences ≠ []) :
    resumeExactQuery scope nextRequestId request response = .accepted := by
  cases occurrences : response.observation.occurrences with
  | nil => exact False.elim (nonempty occurrences)
  | cons answer answers =>
      simp [resumeExactQuery, valid, kind, occurrences]

theorem exact_success_sound
    {Coverage : Type*} {scope : CallScope} {nextRequestId : Nat}
    {request : ServiceRequest} {response : ServiceResponse Unit Coverage}
    {position : GuardPosition} {value expected : Term}
    (kind : request.kind = .queryExactType position value expected)
    (valid : validateResponse scope request response = none)
    (sound : QueryResponseSound scope request response)
    (accepted : resumeExactQuery scope nextRequestId request response =
      .accepted) :
    GetType scope.owned.snapshot value expected := by
  have nonempty : response.observation.occurrences ≠ [] := by
    intro empty
    cases completion : response.observation.completion <;>
      simp [resumeExactQuery, valid, kind, empty, completion,
        incompleteQueryAction, metatypeRequest] at accepted
  have judgment := sound nonempty
  simpa [ServiceRequestKind.QueryJudgment, kind] using judgment

theorem metatype_closed_empty_rejects
    {scope : CallScope} {request : ServiceRequest}
    {position : GuardPosition} {value expected : Term}
    {response : ServiceResponse Unit (QueryCoverage scope request)}
    (kind : request.kind = .queryMetatype position value expected)
    (valid : validateResponse scope request response = none)
    (closed : ClosedFor scope request response)
    (empty : response.observation.occurrences = []) :
    resumeMetatypeQuery scope request response = .rejected := by
  rcases closedFor_completion closed with ⟨coverage, completion⟩
  simp [resumeMetatypeQuery, valid, kind, empty, completion,
    incompleteQueryAction]

theorem metatype_success_accepts
    {Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Unit Coverage}
    {position : GuardPosition} {value expected : Term}
    (kind : request.kind = .queryMetatype position value expected)
    (valid : validateResponse scope request response = none)
    (nonempty : response.observation.occurrences ≠ []) :
    resumeMetatypeQuery scope request response = .accepted := by
  cases occurrences : response.observation.occurrences with
  | nil => exact False.elim (nonempty occurrences)
  | cons answer answers =>
      simp [resumeMetatypeQuery, valid, kind, occurrences]

theorem metatype_success_sound
    {Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Unit Coverage}
    {position : GuardPosition} {value expected : Term}
    (kind : request.kind = .queryMetatype position value expected)
    (valid : validateResponse scope request response = none)
    (sound : QueryResponseSound scope request response)
    (accepted : resumeMetatypeQuery scope request response = .accepted) :
    GetMetatype scope.owned.snapshot value expected := by
  have nonempty : response.observation.occurrences ≠ [] := by
    intro empty
    cases completion : response.observation.completion <;>
      simp [resumeMetatypeQuery, valid, kind, empty, completion,
        incompleteQueryAction] at accepted
  have judgment := sound nonempty
  simpa [ServiceRequestKind.QueryJudgment, kind] using judgment

/-- When both service queries close with exact coverage, the operational
request/response soft cut is exactly the completed G3 judgment. -/
theorem completed_softcut_accepted_iff
    (scope : CallScope) (key : RequestKey) (nextRequestId : Nat)
    (position : GuardPosition) (value expected : Term)
    (exactResponse : ServiceResponse Unit
      (QueryCoverage scope (exactTypeRequest key position value expected)))
    (metatypeResponse : ServiceResponse Unit
      (QueryCoverage scope
        (metatypeQueryRequest { key with requestId := nextRequestId }
          position value expected)))
    (exactValid : validateResponse scope
      (exactTypeRequest key position value expected) exactResponse = none)
    (metatypeValid : validateResponse scope
      (metatypeQueryRequest { key with requestId := nextRequestId }
        position value expected) metatypeResponse = none)
    (exactClosed : ClosedFor scope
      (exactTypeRequest key position value expected) exactResponse)
    (metatypeClosed : ClosedFor scope
      (metatypeQueryRequest { key with requestId := nextRequestId }
        position value expected) metatypeResponse) :
    (resumeExactQuery scope nextRequestId
          (exactTypeRequest key position value expected) exactResponse =
        .accepted ∨
      (resumeExactQuery scope nextRequestId
          (exactTypeRequest key position value expected) exactResponse =
            .requestMetatype
              (metatypeQueryRequest { key with requestId := nextRequestId }
                position value expected) ∧
        resumeMetatypeQuery scope
          (metatypeQueryRequest { key with requestId := nextRequestId }
            position value expected) metatypeResponse = .accepted)) ↔
      GetType scope.owned.snapshot value expected ∨
        (¬ GetType scope.owned.snapshot value expected ∧
          GetMetatype scope.owned.snapshot value expected) := by
  have exactCoverage :=
    closedFor_nonempty_iff_judgment exactClosed
  have metatypeCoverage :=
    closedFor_nonempty_iff_judgment metatypeClosed
  change exactResponse.observation.occurrences ≠ [] ↔
      GetType scope.owned.snapshot value expected at exactCoverage
  change metatypeResponse.observation.occurrences ≠ [] ↔
      GetMetatype scope.owned.snapshot value expected at metatypeCoverage
  by_cases exact : GetType scope.owned.snapshot value expected
  · have nonempty := exactCoverage.mpr exact
    have accepted : resumeExactQuery scope nextRequestId
        (exactTypeRequest key position value expected) exactResponse =
          .accepted :=
      exact_success_never_requests_metatype rfl exactValid nonempty
    simp [accepted, exact]
  · have empty : exactResponse.observation.occurrences = [] := by
      by_contra nonempty
      exact exact (exactCoverage.mp nonempty)
    have requestMeta : resumeExactQuery scope nextRequestId
        (exactTypeRequest key position value expected) exactResponse =
          .requestMetatype
            (metatypeQueryRequest { key with requestId := nextRequestId }
              position value expected) :=
      exact_closed_empty_requests_metatype rfl exactValid exactClosed empty
    by_cases metatype : GetMetatype scope.owned.snapshot value expected
    · have nonempty := metatypeCoverage.mpr metatype
      have accepted : resumeMetatypeQuery scope
          (metatypeQueryRequest { key with requestId := nextRequestId }
            position value expected) metatypeResponse = .accepted :=
        metatype_success_accepts rfl metatypeValid nonempty
      simp [requestMeta, accepted, exact, metatype]
    · have emptyMeta : metatypeResponse.observation.occurrences = [] := by
        by_contra nonempty
        exact metatype (metatypeCoverage.mp nonempty)
      have rejected : resumeMetatypeQuery scope
          (metatypeQueryRequest { key with requestId := nextRequestId }
            position value expected) metatypeResponse = .rejected :=
        metatype_closed_empty_rejects rfl metatypeValid metatypeClosed emptyMeta
      simp [requestMeta, rejected, exact, metatype]

theorem completed_softcut_accepted_iff_argModeAccepts
    (scope : CallScope) (key : RequestKey) (nextRequestId : Nat)
    (position : GuardPosition) (source value expected : Term)
    (exactResponse : ServiceResponse Unit
      (QueryCoverage scope (exactTypeRequest key position value expected)))
    (metatypeResponse : ServiceResponse Unit
      (QueryCoverage scope
        (metatypeQueryRequest { key with requestId := nextRequestId }
          position value expected)))
    (exactValid : validateResponse scope
      (exactTypeRequest key position value expected) exactResponse = none)
    (metatypeValid : validateResponse scope
      (metatypeQueryRequest { key with requestId := nextRequestId }
        position value expected) metatypeResponse = none)
    (exactClosed : ClosedFor scope
      (exactTypeRequest key position value expected) exactResponse)
    (metatypeClosed : ClosedFor scope
      (metatypeQueryRequest { key with requestId := nextRequestId }
        position value expected) metatypeResponse) :
    (resumeExactQuery scope nextRequestId
          (exactTypeRequest key position value expected) exactResponse =
        .accepted ∨
      (resumeExactQuery scope nextRequestId
          (exactTypeRequest key position value expected) exactResponse =
            .requestMetatype
              (metatypeQueryRequest { key with requestId := nextRequestId }
                position value expected) ∧
        resumeMetatypeQuery scope
          (metatypeQueryRequest { key with requestId := nextRequestId }
            position value expected) metatypeResponse = .accepted)) ↔
      (ArgMode.evalSoftcutType expected).Accepts
        scope.owned.snapshot source value := by
  simpa [ArgMode.Accepts] using
    completed_softcut_accepted_iff scope key nextRequestId position value
      expected exactResponse metatypeResponse exactValid metatypeValid
      exactClosed metatypeClosed

theorem completed_softcut_accepted_iff_resultModeAccepts
    (scope : CallScope) (key : RequestKey) (nextRequestId : Nat)
    (value expected : Term)
    (exactResponse : ServiceResponse Unit
      (QueryCoverage scope
        (exactTypeRequest key .result value expected)))
    (metatypeResponse : ServiceResponse Unit
      (QueryCoverage scope
        (metatypeQueryRequest { key with requestId := nextRequestId }
          .result value expected)))
    (exactValid : validateResponse scope
      (exactTypeRequest key .result value expected) exactResponse = none)
    (metatypeValid : validateResponse scope
      (metatypeQueryRequest { key with requestId := nextRequestId }
        .result value expected) metatypeResponse = none)
    (exactClosed : ClosedFor scope
      (exactTypeRequest key .result value expected) exactResponse)
    (metatypeClosed : ClosedFor scope
      (metatypeQueryRequest { key with requestId := nextRequestId }
        .result value expected) metatypeResponse) :
    (resumeExactQuery scope nextRequestId
          (exactTypeRequest key .result value expected) exactResponse =
        .accepted ∨
      (resumeExactQuery scope nextRequestId
          (exactTypeRequest key .result value expected) exactResponse =
            .requestMetatype
              (metatypeQueryRequest { key with requestId := nextRequestId }
                .result value expected) ∧
        resumeMetatypeQuery scope
          (metatypeQueryRequest { key with requestId := nextRequestId }
            .result value expected) metatypeResponse = .accepted)) ↔
      (ResultMode.resultSoftcutType expected).Accepts
        scope.owned.snapshot value := by
  simpa [ResultMode.Accepts] using
    completed_softcut_accepted_iff scope key nextRequestId .result value
      expected exactResponse metatypeResponse exactValid metatypeValid
      exactClosed metatypeClosed

/-! ## Evaluation multiplicity and response correlation -/

/-- One evaluator answer occurrence.  Equal values remain different when
their occurrence or child-branch identity differs. -/
structure EvaluationOccurrence where
  occurrenceId : Nat
  branchGeneration : Nat
  value : Term
deriving DecidableEq, Repr

/-- A completed body-evaluation branch paired with its exact completed call. -/
structure CompletedCallOccurrence where
  occurrenceId : Nat
  branchGeneration : Nat
  call : Call
deriving DecidableEq, Repr

def EvaluationOccurrence.childScope (occurrence : EvaluationOccurrence)
    (parent : CallScope) : CallScope :=
  { parent with branchGeneration := occurrence.branchGeneration }

/-- A successful envelope validation exposes the exact occurrence list.  It
does not deduplicate equal evaluated values. -/
def evaluatedOccurrences? {Coverage : Type*}
    (scope : CallScope) (request : ServiceRequest)
    (response : ServiceResponse EvaluationOccurrence Coverage) :
    ResponseInvalidReason ⊕ List EvaluationOccurrence :=
  match validateResponse scope request response with
  | some reason => .inl reason
  | none =>
      match request.kind with
      | .evaluateArgument _ _ | .evaluateCall _ _ =>
          .inr response.observation.occurrences
      | _ => .inl .wrongRequestKind

theorem evaluatedOccurrences?_exact
    {Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest}
    {response : ServiceResponse EvaluationOccurrence Coverage}
    (valid : validateResponse scope request response = none)
    (kind : (∃ index source,
        request.kind = .evaluateArgument index source) ∨
      (∃ function arguments,
        request.kind = .evaluateCall function arguments)) :
    evaluatedOccurrences? scope request response =
      .inr response.observation.occurrences := by
  rcases kind with ⟨index, source, kind⟩ | ⟨function, arguments, kind⟩ <;>
    simp [evaluatedOccurrences?, valid, kind]

theorem validateResponse_foreign_request
    {Answer Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Answer Coverage}
    (run : request.key.runId = scope.runId)
    (branch : request.key.branchGeneration = scope.branchGeneration)
    (foreign : request.key.owner ≠ scope.owned.owner) :
    validateResponse scope request response = some .foreignOwner := by
  simp [validateResponse, run, branch, foreign]

theorem validateResponse_stale_request
    {Answer Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Answer Coverage}
    (run : request.key.runId = scope.runId)
    (branch : request.key.branchGeneration = scope.branchGeneration)
    (owner : request.key.owner = scope.owned.owner)
    (stale : request.key.revision ≠ scope.owned.snapshot.revision) :
    validateResponse scope request response = some .staleRevision := by
  simp [validateResponse, run, branch, owner, stale]

theorem validateResponse_wrong_run
    {Answer Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Answer Coverage}
    (wrong : request.key.runId ≠ scope.runId) :
    validateResponse scope request response = some .wrongRun := by
  simp [validateResponse, wrong]

theorem validateResponse_wrong_branch
    {Answer Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Answer Coverage}
    (run : request.key.runId = scope.runId)
    (wrong : request.key.branchGeneration ≠ scope.branchGeneration) :
    validateResponse scope request response = some .wrongBranch := by
  simp [validateResponse, run, wrong]

theorem validateResponse_wrong_request
    {Answer Coverage : Type*} {scope : CallScope}
    {request : ServiceRequest} {response : ServiceResponse Answer Coverage}
    (requestPinned : request.PinnedTo scope)
    (responsePinned : response.request.PinnedTo scope)
    (different : response.request ≠ request) :
    validateResponse scope request response = some .wrongRequest := by
  rcases requestPinned with ⟨requestRun, requestBranch, requestOwner,
    requestRevision⟩
  rcases responsePinned with ⟨responseRun, responseBranch, responseOwner,
    responseRevision⟩
  simp [validateResponse, requestRun, requestBranch, requestOwner,
    requestRevision, responseRun, responseBranch, responseOwner,
    responseRevision, different]

/-! ## Typed argument interaction -/

/-- Cursor for one compiler-produced plan branch.  Evaluated arguments are
stored in reverse order so the hot transition is constant-time. -/
structure ArgumentCursor where
  scope : CallScope
  planIndex : Nat
  plan : GuardPlan
  nextRequestId : Nat
  index : Nat
  sourceArguments : List Term
  remainingModes : List ArgMode
  remainingSources : List Term
  evaluatedRev : List Term
deriving DecidableEq, Repr

def ArgumentCursor.start (scope : CallScope) (planIndex nextRequestId : Nat)
    (plan : GuardPlan) (sourceArguments : List Term) : ArgumentCursor :=
  { scope, planIndex, plan, nextRequestId, index := 0
    sourceArguments
    remainingModes := plan.argumentModes
    remainingSources := sourceArguments
    evaluatedRev := [] }

def ArgumentCursor.requestKey (cursor : ArgumentCursor) : RequestKey :=
  { runId := cursor.scope.runId
    branchGeneration := cursor.scope.branchGeneration
    requestId := cursor.nextRequestId
    owner := cursor.scope.owned.owner
    revision := cursor.scope.owned.snapshot.revision
    declarationOccurrence := cursor.plan.declarationOccurrence }

private def ArgumentCursor.advanceWith (cursor : ArgumentCursor)
    (scope : CallScope) (value : Term) (requestIncrement : Nat) :
    ArgumentCursor :=
  { cursor with
    scope
    nextRequestId := cursor.nextRequestId + requestIncrement
    index := cursor.index + 1
    remainingModes := cursor.remainingModes.drop 1
    remainingSources := cursor.remainingSources.drop 1
    evaluatedRev := value :: cursor.evaluatedRev }

inductive ArgumentContinuation where
  | evaluatedUnchecked (cursor : ArgumentCursor)
  | evaluatedChecked (cursor : ArgumentCursor) (expected : Term)
  | exactChecked (next : ArgumentCursor)
  | metatypeChecked (next : ArgumentCursor)
deriving DecidableEq, Repr

structure PendingArgumentInteraction where
  request : ServiceRequest
  continuation : ArgumentContinuation
deriving DecidableEq, Repr

inductive ArgumentAdvance where
  | continue (cursor : ArgumentCursor)
  | emit (event : MainlineCallGuardControl.ControlEvent)
      (cursor : ArgumentCursor)
  | request (pending : PendingArgumentInteraction)
  | ready (scope : CallScope) (planIndex : Nat) (plan : GuardPlan)
      (sourceArguments evaluatedArguments : List Term)
      (nextRequestId : Nat)
  | rejected (planIndex : Nat)
  | suspended (pending : PendingArgumentInteraction) (action : QueryAction)
  | invalid (reason : ResponseInvalidReason)
deriving DecidableEq, Repr

/-- One request-free argument transition, or one narrow service request. -/
def prepareArgument (cursor : ArgumentCursor) : ArgumentAdvance :=
  match cursor.remainingModes, cursor.remainingSources with
  | [], [] =>
      .ready cursor.scope cursor.planIndex cursor.plan cursor.sourceArguments
        cursor.evaluatedRev.reverse cursor.nextRequestId
  | .rawAtom :: _, source :: _ =>
      .emit (.useRawArgument cursor.index)
        (cursor.advanceWith cursor.scope source 0)
  | .evalUnchecked :: _, source :: _ =>
      let request : ServiceRequest :=
        ⟨cursor.requestKey, .evaluateArgument cursor.index source⟩
      .request ⟨request, .evaluatedUnchecked cursor⟩
  | .evalSoftcutType expected :: _, source :: _ =>
      let request : ServiceRequest :=
        ⟨cursor.requestKey, .evaluateArgument cursor.index source⟩
      .request ⟨request, .evaluatedChecked cursor expected⟩
  | _, _ => .rejected cursor.planIndex

private def exactRequestForOccurrence (cursor : ArgumentCursor)
    (expected : Term) (occurrence : EvaluationOccurrence) :
    ServiceRequest :=
  exactTypeRequest
    { cursor.requestKey with
      branchGeneration := occurrence.branchGeneration
      requestId := cursor.nextRequestId + 1 }
    (.argument cursor.index) occurrence.value expected

/-- An evaluation response forks into one continuation per exact occurrence.
Equal values are not collapsed, and each child receives its own branch scope. -/
def resumeArgumentEvaluation {Coverage : Type*}
    (pending : PendingArgumentInteraction)
    (response : ServiceResponse EvaluationOccurrence Coverage) :
    List ArgumentAdvance :=
  match pending.continuation with
  | .evaluatedUnchecked cursor =>
      match evaluatedOccurrences? cursor.scope pending.request response with
      | .inl reason => [.invalid reason]
      | .inr occurrences =>
          occurrences.map fun occurrence =>
            .continue (cursor.advanceWith
              (occurrence.childScope cursor.scope) occurrence.value 1)
  | .evaluatedChecked cursor expected =>
      match evaluatedOccurrences? cursor.scope pending.request response with
      | .inl reason => [.invalid reason]
      | .inr occurrences =>
          occurrences.map fun occurrence =>
            let next := cursor.advanceWith
              (occurrence.childScope cursor.scope) occurrence.value 2
            let request := exactRequestForOccurrence cursor expected occurrence
            .request ⟨request, .exactChecked next⟩
  | .exactChecked _ | .metatypeChecked _ =>
      [.invalid .wrongRequestKind]

private def suspendOrRejectExact (pending : PendingArgumentInteraction) :
    QueryAction → ArgumentAdvance
  | .accepted =>
      match pending.continuation with
      | .exactChecked next => .continue next
      | _ => .invalid .wrongRequestKind
  | .requestMetatype request =>
      match pending.continuation with
      | .exactChecked next => .request ⟨request, .metatypeChecked next⟩
      | _ => .invalid .wrongRequestKind
  | .rejected =>
      match pending.continuation with
      | .exactChecked next => .rejected next.planIndex
      | _ => .invalid .wrongRequestKind
  | action@(.open _) => .suspended pending action
  | action@(.exhausted _ _ _) => .suspended pending action
  | action@(.cancelled) => .suspended pending action
  | action@(.resourceFault _) => .suspended pending action
  | .invalid reason => .invalid reason

def resumeArgumentExact {Coverage : Type*}
    (nextRequestId : Nat) (pending : PendingArgumentInteraction)
    (response : ServiceResponse Unit Coverage) : ArgumentAdvance :=
  match pending.continuation with
  | .exactChecked next =>
      suspendOrRejectExact pending
        (resumeExactQuery next.scope nextRequestId pending.request response)
  | _ => .invalid .wrongRequestKind

private def suspendOrRejectMetatype
    (pending : PendingArgumentInteraction) : QueryAction → ArgumentAdvance
  | .accepted =>
      match pending.continuation with
      | .metatypeChecked next => .continue next
      | _ => .invalid .wrongRequestKind
  | .rejected =>
      match pending.continuation with
      | .metatypeChecked next => .rejected next.planIndex
      | _ => .invalid .wrongRequestKind
  | action@(.open _) => .suspended pending action
  | action@(.exhausted _ _ _) => .suspended pending action
  | action@(.cancelled) => .suspended pending action
  | action@(.resourceFault _) => .suspended pending action
  | .requestMetatype _ => .invalid .wrongRequestKind
  | .invalid reason => .invalid reason

def resumeArgumentMetatype {Coverage : Type*}
    (pending : PendingArgumentInteraction)
    (response : ServiceResponse Unit Coverage) : ArgumentAdvance :=
  match pending.continuation with
  | .metatypeChecked next =>
      suspendOrRejectMetatype pending
        (resumeMetatypeQuery next.scope pending.request response)
  | _ => .invalid .wrongRequestKind

theorem prepareArgument_raw_emits_no_request
    (cursor : ArgumentCursor) (source : Term) (modes : List ArgMode)
    (sources : List Term) (modesExact : cursor.remainingModes = .rawAtom :: modes)
    (sourcesExact : cursor.remainingSources = source :: sources) :
    ∃ next, prepareArgument cursor =
      .emit (.useRawArgument cursor.index) next := by
  simp [prepareArgument, modesExact, sourcesExact]

theorem resumeArgumentEvaluation_preserves_occurrence_count
    {Coverage : Type*} {pending : PendingArgumentInteraction}
    {response : ServiceResponse EvaluationOccurrence Coverage}
    {cursor : ArgumentCursor}
    (continuation : pending.continuation =
      .evaluatedUnchecked cursor)
    (valid : validateResponse cursor.scope pending.request response = none)
    (kind : (∃ index argument,
      pending.request.kind = .evaluateArgument index argument) ∨
      (∃ function arguments,
        pending.request.kind = .evaluateCall function arguments)) :
    (resumeArgumentEvaluation pending response).length =
      response.observation.occurrences.length := by
  simp [resumeArgumentEvaluation, continuation,
    evaluatedOccurrences?_exact valid kind]

/-! ## Typed body and result interaction -/

structure BodyCursor where
  scope : CallScope
  planIndex : Nat
  plan : GuardPlan
  sourceArguments : List Term
  evaluatedArguments : List Term
  nextRequestId : Nat
deriving DecidableEq, Repr

def BodyCursor.requestKey (cursor : BodyCursor) : RequestKey :=
  { runId := cursor.scope.runId
    branchGeneration := cursor.scope.branchGeneration
    requestId := cursor.nextRequestId
    owner := cursor.scope.owned.owner
    revision := cursor.scope.owned.snapshot.revision
    declarationOccurrence := cursor.plan.declarationOccurrence }

structure ResultCandidate where
  scope : CallScope
  planIndex : Nat
  plan : GuardPlan
  occurrence : CompletedCallOccurrence
deriving DecidableEq, Repr

inductive BodyContinuation where
  | evaluatedBody (cursor : BodyCursor)
  | exactResult (candidate : ResultCandidate)
  | metatypeResult (candidate : ResultCandidate)
deriving DecidableEq, Repr

structure PendingBodyInteraction where
  request : ServiceRequest
  continuation : BodyContinuation
deriving DecidableEq, Repr

inductive BodyAdvance where
  | request (pending : PendingBodyInteraction)
  | completed (candidate : ResultCandidate)
  | rejected (planIndex : Nat)
  | suspended (pending : PendingBodyInteraction) (action : QueryAction)
  | invalid (reason : ResponseInvalidReason)
deriving DecidableEq, Repr

def prepareBody (cursor : BodyCursor) : BodyAdvance :=
  let request : ServiceRequest :=
    ⟨cursor.requestKey,
      .evaluateCall cursor.plan.declaration.function cursor.evaluatedArguments⟩
  .request ⟨request, .evaluatedBody cursor⟩

private def resultCandidate (cursor : BodyCursor)
    (occurrence : EvaluationOccurrence) : ResultCandidate :=
  let scope := occurrence.childScope cursor.scope
  let call : Call :=
    ⟨cursor.plan.declaration.function, cursor.sourceArguments,
      cursor.evaluatedArguments, occurrence.value⟩
  { scope
    planIndex := cursor.planIndex
    plan := cursor.plan
    occurrence := ⟨occurrence.occurrenceId,
      occurrence.branchGeneration, call⟩ }

private def resultExactRequest (cursor : BodyCursor)
    (occurrence : EvaluationOccurrence) (expected : Term) : ServiceRequest :=
  exactTypeRequest
    { cursor.requestKey with
      branchGeneration := occurrence.branchGeneration
      requestId := cursor.nextRequestId + 1 }
    .result occurrence.value expected

/-- Body evaluation branches remain exact occurrences.  Result checking is
then issued once for each occurrence, never once for the value quotient. -/
def resumeBodyEvaluation {Coverage : Type*}
    (pending : PendingBodyInteraction)
    (response : ServiceResponse EvaluationOccurrence Coverage) :
    List BodyAdvance :=
  match pending.continuation with
  | .evaluatedBody cursor =>
      match evaluatedOccurrences? cursor.scope pending.request response with
      | .inl reason => [.invalid reason]
      | .inr occurrences =>
          occurrences.map fun occurrence =>
            let candidate := resultCandidate cursor occurrence
            match cursor.plan.resultMode with
            | .resultUnchecked => .completed candidate
            | .resultSoftcutType expected =>
                let request := resultExactRequest cursor occurrence expected
                .request ⟨request, .exactResult candidate⟩
  | .exactResult _ | .metatypeResult _ =>
      [.invalid .wrongRequestKind]

private def advanceResultExact (pending : PendingBodyInteraction) :
    QueryAction → BodyAdvance
  | .accepted =>
      match pending.continuation with
      | .exactResult candidate => .completed candidate
      | _ => .invalid .wrongRequestKind
  | .requestMetatype request =>
      match pending.continuation with
      | .exactResult candidate =>
          .request ⟨request, .metatypeResult candidate⟩
      | _ => .invalid .wrongRequestKind
  | .rejected =>
      match pending.continuation with
      | .exactResult candidate => .rejected candidate.planIndex
      | _ => .invalid .wrongRequestKind
  | action@(.open _) => .suspended pending action
  | action@(.exhausted _ _ _) => .suspended pending action
  | action@(.cancelled) => .suspended pending action
  | action@(.resourceFault _) => .suspended pending action
  | .invalid reason => .invalid reason

def resumeResultExact {Coverage : Type*}
    (nextRequestId : Nat) (pending : PendingBodyInteraction)
    (response : ServiceResponse Unit Coverage) : BodyAdvance :=
  match pending.continuation with
  | .exactResult candidate =>
      advanceResultExact pending
        (resumeExactQuery candidate.scope nextRequestId pending.request response)
  | _ => .invalid .wrongRequestKind

private def advanceResultMetatype (pending : PendingBodyInteraction) :
    QueryAction → BodyAdvance
  | .accepted =>
      match pending.continuation with
      | .metatypeResult candidate => .completed candidate
      | _ => .invalid .wrongRequestKind
  | .rejected =>
      match pending.continuation with
      | .metatypeResult candidate => .rejected candidate.planIndex
      | _ => .invalid .wrongRequestKind
  | action@(.open _) => .suspended pending action
  | action@(.exhausted _ _ _) => .suspended pending action
  | action@(.cancelled) => .suspended pending action
  | action@(.resourceFault _) => .suspended pending action
  | .requestMetatype _ => .invalid .wrongRequestKind
  | .invalid reason => .invalid reason

def resumeResultMetatype {Coverage : Type*}
    (pending : PendingBodyInteraction)
    (response : ServiceResponse Unit Coverage) : BodyAdvance :=
  match pending.continuation with
  | .metatypeResult candidate =>
      advanceResultMetatype pending
        (resumeMetatypeQuery candidate.scope pending.request response)
  | _ => .invalid .wrongRequestKind

theorem resumeBodyEvaluation_preserves_occurrence_count
    {Coverage : Type*} {pending : PendingBodyInteraction}
    {response : ServiceResponse EvaluationOccurrence Coverage}
    {cursor : BodyCursor}
    (continuation : pending.continuation = .evaluatedBody cursor)
    (valid : validateResponse cursor.scope pending.request response = none)
    (kind : (∃ index argument,
      pending.request.kind = .evaluateArgument index argument) ∨
      (∃ function arguments,
        pending.request.kind = .evaluateCall function arguments)) :
    (resumeBodyEvaluation pending response).length =
      response.observation.occurrences.length := by
  simp [resumeBodyEvaluation, continuation,
    evaluatedOccurrences?_exact valid kind]

/-! ## Occurrence-indexed completion store and observation projections -/

inductive PlanSlotStatus where
  | open
  | closed
deriving DecidableEq, Repr

/-- A plan slot may contain several completed call occurrences.  Closing a
slot asserts only that its evaluator branch has complete coverage. -/
structure PlanOccurrenceSlot where
  plan : GuardPlan
  occurrences : List CompletedCallOccurrence
  status : PlanSlotStatus
deriving DecidableEq, Repr

/-- The core store is observation-neutral.  Authored order belongs to the slot
list, while completion order and multiplicity remain explicit occurrences. -/
structure CompletionStore where
  scope : CallScope
  slots : List PlanOccurrenceSlot
deriving DecidableEq, Repr

structure ObservedCallOccurrence where
  planIndex : Nat
  plan : GuardPlan
  occurrence : CompletedCallOccurrence
deriving DecidableEq, Repr

def CompletionStore.start (scope : CallScope)
    (family : CompiledGuardFamily) : CompletionStore :=
  { scope
    slots := family.plans.map fun plan =>
      { plan, occurrences := [], status := .open } }

/-- The store retains exactly one compiler-produced plan family. -/
def CompletionStore.ValidFor (store : CompletionStore)
    (family : CompiledGuardFamily) : Prop :=
  family.ValidFor store.scope.owned ∧
    store.slots.map (fun slot => slot.plan) = family.plans

theorem CompletionStore.start_valid
    {scope : CallScope} {family : CompiledGuardFamily}
    (valid : family.ValidFor scope.owned) :
    (CompletionStore.start scope family).ValidFor family := by
  constructor
  · exact valid
  · simp [CompletionStore.start, Function.comp_def]

private def occurrenceIds : List PlanOccurrenceSlot → List Nat
  | [] => []
  | slot :: slots =>
      slot.occurrences.map (fun occurrence => occurrence.occurrenceId) ++
        occurrenceIds slots

private def recordInSlot : Nat → CompletedCallOccurrence →
    List PlanOccurrenceSlot → Option (List PlanOccurrenceSlot)
  | _, _, [] => none
  | 0, occurrence, slot :: slots =>
      match slot.status with
      | .open => some ({ slot with
          occurrences := slot.occurrences ++ [occurrence] } :: slots)
      | .closed => none
  | index + 1, occurrence, slot :: slots =>
      (recordInSlot index occurrence slots).map (fun updated => slot :: updated)

/-- Record one fresh occurrence.  Wrong-generation results and replayed global
occurrence identities cannot enter the store. -/
def CompletionStore.recordOccurrence (store : CompletionStore)
    (planIndex : Nat) (occurrence : CompletedCallOccurrence) :
    Option CompletionStore :=
  if occurrence.branchGeneration != store.scope.branchGeneration then
    none
  else if occurrence.occurrenceId ∈ occurrenceIds store.slots then
    none
  else
    (recordInSlot planIndex occurrence store.slots).map
      (fun slots => { store with slots })

private def closeSlot : Nat →
    List PlanOccurrenceSlot → Option (List PlanOccurrenceSlot)
  | _, [] => none
  | 0, slot :: slots =>
      match slot.status with
      | .open => some ({ slot with status := .closed } :: slots)
      | .closed => none
  | index + 1, slot :: slots =>
      (closeSlot index slots).map (fun updated => slot :: updated)

def CompletionStore.closePlan (store : CompletionStore) (planIndex : Nat) :
    Option CompletionStore :=
  (closeSlot planIndex store.slots).map (fun slots => { store with slots })

private def indexedSlotOccurrences (planIndex : Nat)
    (slot : PlanOccurrenceSlot) : List ObservedCallOccurrence :=
  slot.occurrences.map fun occurrence => ⟨planIndex, slot.plan, occurrence⟩

private def allSlotOccurrencesFrom : Nat → List PlanOccurrenceSlot →
    List ObservedCallOccurrence
  | _, [] => []
  | planIndex, slot :: slots =>
      indexedSlotOccurrences planIndex slot ++
        allSlotOccurrencesFrom (planIndex + 1) slots

/-- Completion-order-independent view used by bag observers. -/
def CompletionStore.allOccurrences (store : CompletionStore) :
    List ObservedCallOccurrence :=
  allSlotOccurrencesFrom 0 store.slots

private def authoredSlotOccurrencesFrom : Nat →
    List PlanOccurrenceSlot → List ObservedCallOccurrence
  | _, [] => []
  | planIndex, slot :: slots =>
      let current := indexedSlotOccurrences planIndex slot
      match slot.status with
      | .open => current
      | .closed => current ++ authoredSlotOccurrencesFrom (planIndex + 1) slots

private theorem authoredSlotOccurrencesFrom_plan_member
    {planIndex : Nat} {slots : List PlanOccurrenceSlot}
    {occurrence : ObservedCallOccurrence}
    (member : occurrence ∈ authoredSlotOccurrencesFrom planIndex slots) :
    occurrence.plan ∈ slots.map (fun slot => slot.plan) := by
  induction slots generalizing planIndex with
  | nil => simp [authoredSlotOccurrencesFrom] at member
  | cons slot slots inductionHypothesis =>
      cases status : slot.status with
      | «open» =>
          simp [authoredSlotOccurrencesFrom, status,
            indexedSlotOccurrences] at member
          rcases member with ⟨candidate, _, rfl⟩
          simp
      | closed =>
          simp only [authoredSlotOccurrencesFrom, status]
            at member
          rcases List.mem_append.mp member with current | remaining
          · simp [indexedSlotOccurrences] at current
            rcases current with ⟨candidate, _, rfl⟩
            simp
          · exact List.mem_cons_of_mem _
              (inductionHypothesis remaining)

/-- Ordered observers see completed occurrences from the first still-open plan
but do not let later overloads escape past it. -/
def CompletionStore.authoredOccurrences (store : CompletionStore) :
    List ObservedCallOccurrence :=
  authoredSlotOccurrencesFrom 0 store.slots

def ObservedCallOccurrence.acceptedAt (snapshot : Snapshot)
    (occurrence : ObservedCallOccurrence) : Bool :=
  (MainlineCallGuardControl.runPlan snapshot occurrence.occurrence.call
    occurrence.plan).accepted

def acceptedOccurrences (snapshot : Snapshot)
    (occurrences : List ObservedCallOccurrence) :
    List ObservedCallOccurrence :=
  occurrences.filter (ObservedCallOccurrence.acceptedAt snapshot)

/-- Acceptance is recomputed by the G3 controller; an admitted service
occurrence cannot manufacture a successful guard verdict. -/
theorem acceptedOccurrences_sound
    {snapshot : Snapshot} {occurrences : List ObservedCallOccurrence}
    {occurrence : ObservedCallOccurrence}
    (member : occurrence ∈ acceptedOccurrences snapshot occurrences) :
    occurrence.plan.Accepts snapshot occurrence.occurrence.call := by
  have accepted : occurrence.acceptedAt snapshot = true :=
    (List.mem_filter.mp member).2
  exact (MainlineCallGuardControl.runPlan_accepted_iff snapshot
    occurrence.occurrence.call occurrence.plan).mp accepted

def CompletionStore.authoredAcceptedOccurrences (store : CompletionStore) :
    List ObservedCallOccurrence :=
  acceptedOccurrences store.scope.owned.snapshot store.authoredOccurrences

theorem CompletionStore.authoredAccepted_sound
    {store : CompletionStore} {occurrence : ObservedCallOccurrence}
    (member : occurrence ∈ store.authoredAcceptedOccurrences) :
    occurrence.plan.Accepts store.scope.owned.snapshot
      occurrence.occurrence.call :=
  acceptedOccurrences_sound member

/-- Every occurrence exposed for installation is authorized by the authored
PeTTa `GuardedBy` judgment.  Store validity supplies compiler provenance;
service responses supply completed calls but never an acceptance verdict. -/
theorem CompletionStore.authoredAccepted_guardedBy
    {store : CompletionStore} {family : CompiledGuardFamily}
    {occurrence : ObservedCallOccurrence}
    (valid : store.ValidFor family)
    (member : occurrence ∈ store.authoredAcceptedOccurrences) :
    GuardedBy occurrence.plan.declaration
      ⟨store.scope.owned.snapshot, occurrence.occurrence.call⟩ := by
  have accepted := store.authoredAccepted_sound member
  have authoredMember : occurrence ∈ store.authoredOccurrences :=
    (List.mem_filter.mp member).1
  have storePlan : occurrence.plan ∈
      store.slots.map (fun slot => slot.plan) :=
    authoredSlotOccurrencesFrom_plan_member authoredMember
  have familyPlan : occurrence.plan ∈ family.plans := by
    rw [← valid.2]
    exact storePlan
  have planValid :=
    CompiledGuardFamily.validFor_plan_valid valid.1 familyPlan
  exact (validIn_accepts_iff_guardedBy planValid.1).mp accepted

def CompletionStore.acceptedOccurrenceBag (store : CompletionStore) :
    Multiset ObservedCallOccurrence :=
  (acceptedOccurrences store.scope.owned.snapshot store.allOccurrences :
    List ObservedCallOccurrence)

def CompletionStore.authoredAcceptedDeclarations (store : CompletionStore) :
    List ArrowDeclaration :=
  store.authoredAcceptedOccurrences.map (fun occurrence =>
    occurrence.plan.declaration)

def CompletionStore.once? (store : CompletionStore) :
    Option ObservedCallOccurrence :=
  store.authoredAcceptedOccurrences.head?

def CompletionStore.allClosed (store : CompletionStore) : Bool :=
  store.slots.all (fun slot => slot.status == .closed)

structure AuthoredPrefixResidual where
  store : CompletionStore
  emitted : Nat
deriving DecidableEq, Repr

structure BoundedAuthoredProjection where
  occurrences : List ObservedCallOccurrence
  residual : Option AuthoredPrefixResidual
deriving DecidableEq, Repr

/-- A bounded prefix never asserts semantic closure merely because its budget
is spent.  The residual retains the exact immutable store and emitted prefix. -/
def CompletionStore.boundedPrefix (store : CompletionStore) (bound : Nat) :
    BoundedAuthoredProjection :=
  let visible := store.authoredAcceptedOccurrences
  let emitted := min bound visible.length
  { occurrences := visible.take bound
    residual :=
      if store.allClosed && visible.length ≤ bound then none
      else some ⟨store, emitted⟩ }

/-- Raising only the observation budget cannot retract an already visible
authored occurrence. -/
theorem CompletionStore.boundedPrefix_monotone
    (store : CompletionStore) {smaller larger : Nat}
    (budget : smaller ≤ larger) :
    (store.boundedPrefix smaller).occurrences <+:
      (store.boundedPrefix larger).occurrences := by
  simp only [CompletionStore.boundedPrefix]
  exact List.take_prefix_take_left budget

def AuthoredPrefixResidual.resume (residual : AuthoredPrefixResidual)
    (bound : Nat) : BoundedAuthoredProjection :=
  let visible := residual.store.authoredAcceptedOccurrences
  let remaining := visible.drop residual.emitted
  let emittedNow := min bound remaining.length
  { occurrences := remaining.take bound
    residual :=
      if residual.store.allClosed && remaining.length ≤ bound then none
      else some ⟨residual.store, residual.emitted + emittedNow⟩ }

private def completedSlotsFrom (nextOccurrenceId branchGeneration : Nat)
    (call : Call) : List GuardPlan → List PlanOccurrenceSlot
  | [] => []
  | plan :: plans =>
      { plan
        occurrences := [⟨nextOccurrenceId, branchGeneration, call⟩]
        status := .closed } ::
      completedSlotsFrom (nextOccurrenceId + 1) branchGeneration call plans

/-- Canonical terminal store for comparing the interaction layer with G3's
completed-call denotation. -/
def completedStore (scope : CallScope) (call : Call)
    (plans : List GuardPlan) : CompletionStore :=
  ⟨scope, completedSlotsFrom 0 scope.branchGeneration call plans⟩

private theorem completedSlotsFrom_exact
    (snapshot : Snapshot) (call : Call) (plans : List GuardPlan)
    (nextOccurrenceId branchGeneration planIndex : Nat) :
    (acceptedOccurrences snapshot
      (authoredSlotOccurrencesFrom planIndex
        (completedSlotsFrom nextOccurrenceId branchGeneration call plans))).map
        (fun occurrence => occurrence.plan.declaration) =
      (MainlineCallGuardControl.runPlanList snapshot call plans).declarations := by
  induction plans generalizing nextOccurrenceId planIndex with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      cases resultEquation :
          MainlineCallGuardControl.runPlan snapshot call plan with
      | mk accepted events =>
          have tail := inductionHypothesis (nextOccurrenceId + 1)
            (planIndex + 1)
          cases accepted <;>
            simp [completedSlotsFrom, authoredSlotOccurrencesFrom,
              indexedSlotOccurrences, acceptedOccurrences,
              ObservedCallOccurrence.acceptedAt, resultEquation,
              MainlineCallGuardControl.runPlanList] <;>
            simpa only [acceptedOccurrences] using tail

/-- When every service branch has completed, the authored ordered projection
agrees exactly with the G3 completed-call controller. -/
theorem completedStore_authored_exact
    (scope : CallScope) (call : Call) (plans : List GuardPlan) :
    (completedStore scope call plans).authoredAcceptedDeclarations =
      (MainlineCallGuardControl.runPlanList scope.owned.snapshot call plans).declarations := by
  exact completedSlotsFrom_exact scope.owned.snapshot call plans 0
    scope.branchGeneration 0

theorem recordOccurrence_replay_rejected
    (store : CompletionStore) (planIndex : Nat)
    (occurrence : CompletedCallOccurrence)
    (generation : occurrence.branchGeneration = store.scope.branchGeneration)
    (present : occurrence.occurrenceId ∈ occurrenceIds store.slots) :
    store.recordOccurrence planIndex occurrence = none := by
  simp [CompletionStore.recordOccurrence, generation, present]

theorem recordOccurrence_wrong_generation_rejected
    (store : CompletionStore) (planIndex : Nat)
    (occurrence : CompletedCallOccurrence)
    (wrong : occurrence.branchGeneration ≠ store.scope.branchGeneration) :
    store.recordOccurrence planIndex occurrence = none := by
  simp [CompletionStore.recordOccurrence, wrong]

/-! ## Executable positive and negative canaries -/

namespace Canary

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan.Canary

def ownedCurrent : OwnedSnapshot := owned exactTypeSnapshot

def scope : CallScope := ⟨100, 3, ownedCurrent⟩

def exactKey : RequestKey :=
  { runId := scope.runId
    branchGeneration := scope.branchGeneration
    requestId := 40
    owner := scope.owned.owner
    revision := scope.owned.snapshot.revision
    declarationOccurrence := exactTypeDeclaration.occurrence }

def exactRequest : ServiceRequest :=
  ⟨exactKey,
    .queryExactType (.argument 0) (.string "not-a-number") numberType⟩

def closedExactEmpty : ServiceResponse Unit (QueryCoverage scope exactRequest) :=
  { request := exactRequest
    observation := Observation.withoutCapture [] (.closed {
      found := false
      found_iff := by decide }) }

def requestedMetatype : ServiceRequest :=
  ⟨{ exactKey with requestId := 41 },
    .queryMetatype (.argument 0) (.string "not-a-number") numberType⟩

theorem closed_empty_exact_requests_metatype :
    resumeExactQuery scope 41 exactRequest closedExactEmpty =
      .requestMetatype requestedMetatype := by
  decide

def exhaustedExactEmpty : ServiceResponse Unit Unit :=
  { request := exactRequest
    observation := Observation.withoutCapture []
      (.exhausted 8 ⟨17⟩) }

theorem exhausted_exact_does_not_request_metatype :
    resumeExactQuery scope 41 exactRequest exhaustedExactEmpty =
      .exhausted 8 ⟨17⟩ none := by
  decide

def exactSuccessRequest : ServiceRequest :=
  ⟨exactKey,
    .queryExactType (.argument 0) (.number "1") numberType⟩

def exactSuccess : ServiceResponse Unit Unit :=
  { request := exactSuccessRequest
    observation := Observation.withoutCapture [()] (.closed ()) }

theorem exact_success_stops_before_metatype :
    resumeExactQuery scope 41 exactSuccessRequest exactSuccess =
      .accepted := by
  decide

def openResidual : ServiceResidual := ⟨exactRequest, 55⟩

def openExactEmpty : ServiceResponse Unit Unit :=
  { request := exactRequest
    observation := Observation.openCaptured [] openResidual
      scope.owned.snapshot.revision ⟨rfl, rfl⟩ }

theorem open_exact_remains_resumable :
    resumeExactQuery scope 41 exactRequest openExactEmpty =
      .open (some (openResidual, scope.owned.snapshot.revision)) := by
  decide

def replayedResponse : ServiceResponse Unit Unit :=
  { request := { exactRequest with key := { exactKey with requestId := 39 } }
    observation := Observation.withoutCapture [()] (.closed ()) }

theorem replayed_request_id_does_not_advance :
    resumeExactQuery scope 41 exactRequest replayedResponse =
      .invalid .wrongRequest := by
  decide

def wrongPayloadRequest : ServiceRequest :=
  ⟨exactKey,
    .queryMetatype (.argument 0) (.string "not-a-number") numberType⟩

def wrongPayloadResponse : ServiceResponse Unit Unit :=
  { request := wrongPayloadRequest
    observation := Observation.withoutCapture [()] (.closed ()) }

theorem wrong_kind_payload_does_not_advance :
    resumeExactQuery scope 41 exactRequest wrongPayloadResponse =
      .invalid .wrongRequest := by
  decide

def wrongBranchResponse : ServiceResponse Unit Unit :=
  { request := { exactRequest with key := { exactKey with
      branchGeneration := scope.branchGeneration + 1 } }
    observation := Observation.withoutCapture [()] (.closed ()) }

theorem wrong_branch_response_does_not_advance :
    resumeExactQuery scope 41 exactRequest wrongBranchResponse =
      .invalid .wrongBranch := by
  decide

def newerOwned : OwnedSnapshot :=
  ⟨ownedCurrent.owner, { ownedCurrent.snapshot with revision :=
    ownedCurrent.snapshot.revision + 1 }⟩

/-- The live catalog may advance after call start without changing the pinned
call's meaning.  The argument makes this independence executable. -/
def resumePinnedAgainstLive (_live : OwnedSnapshot) : QueryAction :=
  resumeExactQuery scope 41 exactSuccessRequest exactSuccess

theorem call_start_snapshot_survives_later_mutation :
    resumePinnedAgainstLive newerOwned = .accepted := by
  decide

def restampedScope : CallScope := { scope with owned := newerOwned }

theorem stale_revision_during_suspension_does_not_advance :
    resumeExactQuery restampedScope 41 exactSuccessRequest exactSuccess =
      .invalid .staleRevision := by
  decide

def nextCallScope : CallScope := ⟨scope.runId + 1, 0, newerOwned⟩

theorem prior_run_response_does_not_enter_new_call :
    resumeExactQuery nextCallScope 41 exactSuccessRequest exactSuccess =
      .invalid .wrongRun := by
  decide

def evaluationKey : RequestKey :=
  { exactKey with requestId := 70 }

def evaluationRequest : ServiceRequest :=
  ⟨evaluationKey, .evaluateArgument 0 (.atom "source")⟩

def duplicateEvaluation : ServiceResponse EvaluationOccurrence Unit :=
  { request := evaluationRequest
    observation := Observation.withoutCapture
      [⟨200, 4, .number "2"⟩, ⟨201, 5, .number "2"⟩] (.closed ()) }

theorem duplicate_evaluation_occurrences_are_preserved :
    evaluatedOccurrences? scope evaluationRequest duplicateEvaluation =
      .inr [⟨200, 4, .number "2"⟩, ⟨201, 5, .number "2"⟩] := by
  decide

theorem duplicate_values_have_distinct_child_scopes :
    let first :=
      (EvaluationOccurrence.mk 200 4 (.number "2")).childScope scope
    let second :=
      (EvaluationOccurrence.mk 201 5 (.number "2")).childScope scope
    first ≠ second := by
  decide

def rawCursor : ArgumentCursor :=
  ArgumentCursor.start scope 0 80 rawPlan [.atom "source"]

theorem raw_argument_emits_no_service_request :
    ∃ next, prepareArgument rawCursor =
      .emit (.useRawArgument 0) next := by
  exact ⟨rawCursor.advanceWith scope (.atom "source") 0, rfl⟩

def uncheckedPlan : GuardPlan :=
  { rawPlan with argumentModes := [.evalUnchecked] }

def uncheckedCursor : ArgumentCursor :=
  ArgumentCursor.start scope 0 70 uncheckedPlan [.atom "source"]

def uncheckedRequest : ServiceRequest :=
  ⟨uncheckedCursor.requestKey, .evaluateArgument 0 (.atom "source")⟩

def uncheckedPending : PendingArgumentInteraction :=
  ⟨uncheckedRequest, .evaluatedUnchecked uncheckedCursor⟩

def uncheckedDuplicateResponse :
    ServiceResponse EvaluationOccurrence Unit :=
  { request := uncheckedRequest
    observation := Observation.withoutCapture
      [⟨200, 4, .number "2"⟩, ⟨201, 5, .number "2"⟩] (.closed ()) }

def continuedBranchAndValue : ArgumentAdvance → Option (Nat × Term)
  | .continue cursor =>
      cursor.evaluatedRev.head?.map fun value =>
        (cursor.scope.branchGeneration, value)
  | _ => none

theorem duplicate_evaluation_forks_distinct_continuations :
    (resumeArgumentEvaluation uncheckedPending
      uncheckedDuplicateResponse).map continuedBranchAndValue =
        [some (4, .number "2"), some (5, .number "2")] := by
  decide

def checkedPlan : GuardPlan :=
  { rawPlan with argumentModes := [.evalSoftcutType numberType] }

def checkedCursor : ArgumentCursor :=
  ArgumentCursor.start scope 0 90 checkedPlan [.number "1"]

def checkedOccurrence : EvaluationOccurrence :=
  ⟨300, 6, .number "1"⟩

def checkedNext : ArgumentCursor :=
  checkedCursor.advanceWith (checkedOccurrence.childScope scope)
    checkedOccurrence.value 2

def checkedExactRequest : ServiceRequest :=
  exactRequestForOccurrence checkedCursor numberType checkedOccurrence

def checkedExactPending : PendingArgumentInteraction :=
  ⟨checkedExactRequest, .exactChecked checkedNext⟩

def checkedExactSuccess : ServiceResponse Unit Unit :=
  { request := checkedExactRequest
    observation := Observation.withoutCapture [()] (.closed ()) }

theorem checked_argument_exact_success_continues_child_branch :
    resumeArgumentExact 93 checkedExactPending checkedExactSuccess =
      .continue checkedNext := by
  decide

def uncheckedResultPlan : GuardPlan :=
  { rawPlan with resultMode := .resultUnchecked }

def uncheckedBodyCursor : BodyCursor :=
  { scope
    planIndex := 0
    plan := uncheckedResultPlan
    sourceArguments := [.atom "source"]
    evaluatedArguments := [.atom "source"]
    nextRequestId := 100 }

def uncheckedBodyRequest : ServiceRequest :=
  ⟨uncheckedBodyCursor.requestKey,
    .evaluateCall "f" [.atom "source"]⟩

def uncheckedBodyPending : PendingBodyInteraction :=
  ⟨uncheckedBodyRequest, .evaluatedBody uncheckedBodyCursor⟩

def duplicateBodyResponse :
    ServiceResponse EvaluationOccurrence Unit :=
  { request := uncheckedBodyRequest
    observation := Observation.withoutCapture
      [⟨400, 7, .number "2"⟩, ⟨401, 8, .number "2"⟩] (.closed ()) }

def completedBodyOccurrenceId : BodyAdvance → Option Nat
  | .completed candidate => some candidate.occurrence.occurrenceId
  | _ => none

theorem duplicate_body_results_are_checked_as_distinct_occurrences :
    (resumeBodyEvaluation uncheckedBodyPending duplicateBodyResponse).map
      completedBodyOccurrenceId = [some 400, some 401] := by
  decide

theorem body_preparation_only_requests_evaluation :
    prepareBody uncheckedBodyCursor = .request uncheckedBodyPending := by
  decide

def checkedBodyCursor : BodyCursor :=
  { uncheckedBodyCursor with plan := rawPlan, nextRequestId := 110 }

def checkedResultOccurrence : EvaluationOccurrence :=
  ⟨410, 9, .number "2"⟩

def checkedResultCandidate : ResultCandidate :=
  resultCandidate checkedBodyCursor checkedResultOccurrence

def checkedResultRequest : ServiceRequest :=
  resultExactRequest checkedBodyCursor checkedResultOccurrence numberType

def checkedResultPending : PendingBodyInteraction :=
  ⟨checkedResultRequest, .exactResult checkedResultCandidate⟩

def checkedResultSuccess : ServiceResponse Unit Unit :=
  { request := checkedResultRequest
    observation := Observation.withoutCapture [()] (.closed ()) }

theorem result_check_follows_body_occurrence :
    resumeResultExact 112 checkedResultPending checkedResultSuccess =
      .completed checkedResultCandidate := by
  decide

def secondDeclaration : ArrowDeclaration :=
  ⟨81, "f", [atomType], numberType⟩

def secondPlan : GuardPlan :=
  { declarationOccurrence := secondDeclaration.occurrence
    argumentModes := [.rawAtom]
    resultMode := .resultSoftcutType numberType
    declaration := secondDeclaration }

def twoPlanFamily : CompiledGuardFamily :=
  { rawFamily with plans := [rawPlan, secondPlan] }

def firstOccurrence : CompletedCallOccurrence :=
  ⟨100, scope.branchGeneration, CallGuardNativeKernel.Canary.claim.call⟩

def secondOccurrence : CompletedCallOccurrence :=
  ⟨101, scope.branchGeneration, CallGuardNativeKernel.Canary.claim.call⟩

def storeAfterSecond : CompletionStore :=
  ((CompletionStore.start scope twoPlanFamily).recordOccurrence 1
    secondOccurrence).get rfl

def storeAfterBoth : CompletionStore :=
  (storeAfterSecond.recordOccurrence 0 firstOccurrence).get rfl

def storeAfterFirstClosed : CompletionStore :=
  (storeAfterBoth.closePlan 0).get rfl

theorem later_completion_is_bag_visible_but_order_hidden :
    storeAfterSecond.authoredOccurrences = [] ∧
      storeAfterSecond.allOccurrences.map
        (fun occurrence => occurrence.occurrence.occurrenceId) = [101] := by
  decide

theorem closing_earlier_plan_reveals_authored_order :
    storeAfterFirstClosed.authoredAcceptedDeclarations =
      [rawPlan.declaration, secondPlan.declaration] := by
  decide

theorem equal_values_keep_distinct_occurrence_identity :
    storeAfterFirstClosed.acceptedOccurrenceBag.card = 2 ∧
      storeAfterFirstClosed.allOccurrences.map
        (fun occurrence => occurrence.occurrence.occurrenceId) = [100, 101] := by
  decide

theorem once_uses_authored_projection :
    storeAfterFirstClosed.once?.map
        (fun occurrence => occurrence.plan.declaration) =
      some rawPlan.declaration := by
  decide

theorem replayed_occurrence_is_rejected :
    storeAfterBoth.recordOccurrence 1 firstOccurrence = none := by
  decide

def terminalTwoPlanStore : CompletionStore :=
  completedStore scope CallGuardNativeKernel.Canary.claim.call
    [rawPlan, secondPlan]

def terminalPrefix : BoundedAuthoredProjection :=
  terminalTwoPlanStore.boundedPrefix 1

theorem terminalPrefix_has_residual : terminalPrefix.residual.isSome = true := by
  decide

def terminalPrefixResidual : AuthoredPrefixResidual :=
  terminalPrefix.residual.get (by
    simpa [Option.isSome_iff_ne_none] using terminalPrefix_has_residual)

theorem bounded_prefix_resumes_without_duplication :
    terminalPrefix.occurrences.map
        (fun occurrence => occurrence.occurrence.occurrenceId) = [0] ∧
      (terminalPrefixResidual.resume 1).occurrences.map
        (fun occurrence => occurrence.occurrence.occurrenceId) = [1] := by
  decide

def cancelledExactEmpty : ServiceResponse Unit Unit :=
  { request := exactRequest
    observation := Observation.withoutCapture [] .cancelled }

def faultedExactEmpty : ServiceResponse Unit Unit :=
  { request := exactRequest
    observation := Observation.withoutCapture []
      (.resourceFault .resourceLimit) }

theorem cancellation_and_fault_are_not_rejection :
    resumeExactQuery scope 41 exactRequest cancelledExactEmpty = .cancelled ∧
      resumeExactQuery scope 41 exactRequest faultedExactEmpty =
        .resourceFault .resourceLimit := by
  decide

end Canary

#print axioms closedFor_nonempty_iff_judgment
#print axioms exact_closed_empty_requests_metatype
#print axioms exact_exhausted_never_requests_metatype
#print axioms exact_success_never_requests_metatype
#print axioms exact_success_sound
#print axioms metatype_closed_empty_rejects
#print axioms metatype_success_sound
#print axioms completed_softcut_accepted_iff
#print axioms completed_softcut_accepted_iff_argModeAccepts
#print axioms completed_softcut_accepted_iff_resultModeAccepts
#print axioms evaluatedOccurrences?_exact
#print axioms prepareArgument_raw_emits_no_request
#print axioms resumeArgumentEvaluation_preserves_occurrence_count
#print axioms resumeBodyEvaluation_preserves_occurrence_count
#print axioms validateResponse_foreign_request
#print axioms validateResponse_stale_request
#print axioms validateResponse_wrong_run
#print axioms validateResponse_wrong_branch
#print axioms validateResponse_wrong_request
#print axioms acceptedOccurrences_sound
#print axioms CompletionStore.start_valid
#print axioms CompletionStore.authoredAccepted_sound
#print axioms CompletionStore.authoredAccepted_guardedBy
#print axioms CompletionStore.boundedPrefix_monotone
#print axioms completedStore_authored_exact
#print axioms recordOccurrence_replay_rejected
#print axioms recordOccurrence_wrong_generation_rejected
#print axioms Canary.closed_empty_exact_requests_metatype
#print axioms Canary.open_exact_remains_resumable
#print axioms Canary.replayed_request_id_does_not_advance
#print axioms Canary.wrong_kind_payload_does_not_advance
#print axioms Canary.wrong_branch_response_does_not_advance
#print axioms Canary.call_start_snapshot_survives_later_mutation
#print axioms Canary.stale_revision_during_suspension_does_not_advance
#print axioms Canary.prior_run_response_does_not_enter_new_call
#print axioms Canary.duplicate_evaluation_occurrences_are_preserved
#print axioms Canary.duplicate_values_have_distinct_child_scopes
#print axioms Canary.raw_argument_emits_no_service_request
#print axioms Canary.duplicate_evaluation_forks_distinct_continuations
#print axioms Canary.checked_argument_exact_success_continues_child_branch
#print axioms Canary.duplicate_body_results_are_checked_as_distinct_occurrences
#print axioms Canary.body_preparation_only_requests_evaluation
#print axioms Canary.result_check_follows_body_occurrence
#print axioms Canary.later_completion_is_bag_visible_but_order_hidden
#print axioms Canary.closing_earlier_plan_reveals_authored_order
#print axioms Canary.equal_values_keep_distinct_occurrence_identity
#print axioms Canary.once_uses_authored_projection
#print axioms Canary.replayed_occurrence_is_rejected
#print axioms Canary.bounded_prefix_resumes_without_duplication
#print axioms Canary.cancellation_and_fault_are_not_rejection

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardResumableControl
