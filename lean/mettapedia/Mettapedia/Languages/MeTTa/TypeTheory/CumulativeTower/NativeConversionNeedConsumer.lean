import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeConversionChecking
import Mettapedia.TypeTheory.DisplayedEvidence
import Mettapedia.Languages.MeTTa.PrimeNeedDependentService
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDependentComputation

/-!
# Dependent consumption of native conversion replies

A conversion request names its complete pair of scoped endpoints and an
immutable revision. The MIL package and root decoder are fixed by this
service, not selected by an unchecked request label. A reply retains the
candidate code and its exact Boolean verdict. Rejection concerns that code;
it is not a refutation of conversion or of a mathematical proposition.

Accepted replies enter the formation-sensitive judgment only with a source
admission and a separately formed target. The returned term keeps this
request-dependent type. This is a consumer of the candidate logical profile,
not a change to Prime's canonical typing or its runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeConversionNeedConsumer

open Presentation StructuralConversionCode NativeConversionChecking
open Mettapedia.TypeTheory.DisplayedEvidence

open Mettapedia.Languages.MeTTa

variable {n : Nat}

/-- The scope is the type index; the full endpoints, not just a cache key,
identify the obligation at its revision. The logical package is fixed. -/
structure Request (n : Nat) where
  revision : Nat
  left : Tower.Tm n
  right : Tower.Tm n
  deriving DecidableEq

/-- A reply keeps the actual candidate as well as the verdict. In particular,
two accepted codes for the same endpoints remain different data. -/
structure Reply (request : Request n) where
  candidate : MILCode n
  accepted : Bool
  checked : checkMIL candidate request.left request.right = accepted

/-- Execute the existing finite checker on a supplied candidate. This does
not search for a conversion code or check formation of either endpoint. -/
def produce (candidate : Request n → MILCode n) (request : Request n) : Reply request where
  candidate := candidate request
  accepted := checkMIL (candidate request) request.left request.right
  checked := rfl

abbrev family (n : Nat) : Family where
  Raw := Request n
  Exact := Reply

/-- The independent structural-checker soundness theorem supplies the meaning
of an accepted reply. No statement is admitted from a bare Boolean. -/
theorem Reply.conversion {request : Request n} (reply : Reply request)
    (accepted : reply.accepted = true) :
    Conv IntrinsicMILHypothesis.rules.headEq request.left request.right
      IntrinsicMILHypothesis.rules.computation :=
  mil_conversion_iff_checked.mpr ⟨reply.candidate, reply.checked.trans accepted⟩

/-- Neither source admission nor target formation is supplied by conversion
checking. Both remain independent inputs to this dependent consumer. -/
theorem Reply.admit {request : Request n} (reply : Reply request)
    (accepted : reply.accepted = true)
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.right :=
  ⟨source.context, .conv source.typing targetFormed isUniverse (reply.conversion accepted)⟩

/-- Expose the same term at the request's target type, or retain a rejected
candidate as non-admission. Proof inputs are already qualified derivations;
this function is not an algorithm for finding those derivations. -/
def admit? {request : Request n} (reply : Reply request)
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    Option { result : Tower.Tm n //
      FormationSensitive.Judgment IntrinsicMILHypothesis.rules context result request.right } :=
  if accepted : reply.accepted = true then
    some ⟨term, reply.admit accepted source targetFormed isUniverse⟩
  else none

theorem admit?_isSome_iff {request : Request n} (reply : Reply request)
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    (admit? reply source targetFormed isUniverse).isSome = true ↔ reply.accepted = true := by
  unfold admit?
  split <;> simp_all

/-- An unindexed runtime packet is usable only at its complete request.
Successful conversion still does not replace the independent formation inputs. -/
def consumePacket? (request : Request n) (packet : PrimeNeedDependentService.Packet (family n))
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    Option { result : Tower.Tm n //
      FormationSensitive.Judgment IntrinsicMILHypothesis.rules context result request.right } :=
  (PrimeNeedDependentService.project? (family n) request packet).bind fun reply =>
    admit? reply source targetFormed isUniverse

theorem consumePacket?_matching (request : Request n) (reply : Reply request)
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    consumePacket? request ⟨request, reply⟩ source targetFormed isUniverse =
      admit? reply source targetFormed isUniverse := by
  unfold consumePacket?
  rw [PrimeNeedDependentService.project?_matching (family n) request reply]
  rfl

theorem consumePacket?_mismatched {expected actual : Request n}
    (different : actual ≠ expected) (reply : Reply actual)
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead : Tower.Head}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term expected.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context expected.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead) :
    consumePacket? expected ⟨actual, reply⟩ source targetFormed isUniverse = none := by
  simp [consumePacket?, PrimeNeedDependentService.project?_mismatched (family n) different reply]

/-- Continue with a native dependent pair only after index validation and
conversion admission. The continuation remains an effectful existing Program;
failure supplies no mathematical continuation, rather than a false theorem. -/
def continuePacket? {State Intent : Type}
    (request : Request n) (packet : PrimeNeedDependentService.Packet (family n))
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead sigmaHead : Tower.Head}
    {body : Tower.Tm (n + 1)}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead)
    (sigmaFormed : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context
      (.sigma request.right body) (.head sigmaHead))
    (sigmaUniverse : IntrinsicMILHypothesis.rules.isUniverse sigmaHead)
    (next : (first : FormationSensitive.DependentComputation.TypedValue
        IntrinsicMILHypothesis.rules context request.right) →
      Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program State
        (FormationSensitive.DependentComputation.TypedValue IntrinsicMILHypothesis.rules
          context (inst0 first.val body)) Intent) :=
  (consumePacket? request packet source targetFormed isUniverse).map fun first =>
    FormationSensitive.DependentComputation.sigmaProgram sigmaFormed sigmaUniverse (.pure first) next

/-- Every raw result of an admitted effectful continuation has the specified
native dependent Sigma type. Both packet admission and world membership are
used; a result is not authorized by a claimed endpoint or a bare verdict. -/
theorem continued_result_judgment {State Intent : Type}
    (request : Request n) (packet : PrimeNeedDependentService.Packet (family n))
    {context : Tower.Ctx n} {term : Tower.Tm n} {sortHead sigmaHead : Tower.Head}
    {body : Tower.Tm (n + 1)}
    (source : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term request.left)
    (targetFormed : FormationSensitive.Typing IntrinsicMILHypothesis.rules
      context request.right (.head sortHead))
    (isUniverse : IntrinsicMILHypothesis.rules.isUniverse sortHead)
    (sigmaFormed : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context
      (.sigma request.right body) (.head sigmaHead))
    (sigmaUniverse : IntrinsicMILHypothesis.rules.isUniverse sigmaHead)
    (next : (first : FormationSensitive.DependentComputation.TypedValue
        IntrinsicMILHypothesis.rules context request.right) →
      Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program State
        (FormationSensitive.DependentComputation.TypedValue IntrinsicMILHypothesis.rules
          context (inst0 first.val body)) Intent)
    {program : Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program State
      (FormationSensitive.DependentComputation.TypedValue IntrinsicMILHypothesis.rules
        context (.sigma request.right body)) Intent}
    (admitted : continuePacket? request packet source targetFormed isUniverse
      sigmaFormed sigmaUniverse next = some program)
    (state : State) (branch : Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.BranchTrace)
    (output : Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.WorldResult State (Tower.Tm n) Intent)
    (returned : output ∈ Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.runWorldsAt
      (Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program.map Subtype.val program) state branch) :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules context output.answer
      (.sigma request.right body) := by
  obtain ⟨first, _, equality⟩ := Option.map_eq_some_iff.mp admitted
  subst program
  exact FormationSensitive.DependentComputation.result_judgment sigmaFormed sigmaUniverse
    (.pure first) next state branch output returned

/-- One already allocated, still suspended service cell. This is a boundary
fixture for the existing machine, not a new evaluation algorithm. -/
def requestCell : PrimeNeedReference.CellId := ⟨1, [], 0, 0⟩

def initialWorld (request : Request n) : PrimeNeedDependentService.ServiceWorld (family n) where
  lineage := 1
  path := []
  heap :=
    { current := fun cell => if cell = requestCell then some ⟨request, .suspended⟩ else none
      spine := [.allocate requestCell request] }
  receipts := PrimeNeedReference.ReceiptGraph.empty
  nextCell := 1
  nextEvaluator := 1

def initialMachine (request : Request n) : PrimeNeedDependentService.ServiceMachine (family n) :=
  ⟨initialWorld request, .run (.demand request requestCell) [], {}⟩

@[simp] theorem initial_lookup (request : Request n) :
    (initialWorld request).heap.lookup requestCell = some ⟨request, .suspended⟩ := by
  simp [initialWorld, PrimeNeedReference.Heap.lookup]

/-- Complete answer-list equality for a fresh native request. All machine
branches are accounted for, not only a chosen successful route. -/
theorem fresh_answers (candidate : Request n → MILCode n) (request : Request n) :
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family n) (produce candidate)) 7 (initialMachine request) =
      [.value ⟨request, produce candidate request⟩] := by
  have run := PrimeNeedDependentService.fresh_consumer_runFrontier (family n) (produce candidate)
    ({} : PrimeNeedReference.Work) (initial_lookup request)
  simpa only [PrimeNeedReference.answers, initialMachine, PrimeNeedReference.haltedOutcome,
    List.filterMap_cons, List.filterMap_nil] using
    congrArg (List.filterMap PrimeNeedReference.haltedOutcome) run

/-- The erased execution machine returns exactly the same indexed native
reply. The existing erasure theorem supplies the implementation connection. -/
theorem fresh_execution_answers (candidate : Request n → MILCode n) (request : Request n) :
    Mettapedia.Languages.MeTTa.PrimeNeedExecution.answers
      (PrimeNeedDependentService.spec (family n) (produce candidate)) 7
      (Mettapedia.Languages.MeTTa.PrimeNeedExecution.eraseMachine (initialMachine request)) =
      [.value ⟨request, produce candidate request⟩] := by
  rw [PrimeNeedDependentService.answers_erasure, fresh_answers]

/-- A later invocation uses the world completed by the first invocation,
including the cached packet. Its requested query is still checked on resumption. -/
def cachedMachine (candidate : Request n → MILCode n) (request expected : Request n) :
    PrimeNeedDependentService.ServiceMachine (family n) :=
  ⟨PrimeNeedDependentService.producedWorld (family n) (produce candidate)
      (initialWorld request) requestCell request,
    .run (.demand expected requestCell) [],
    PrimeNeedDependentService.consumerFinishWork
      (PrimeNeedDependentService.freshForceWork (({} : PrimeNeedReference.Work).bump 0 0 0 0))⟩

/-- Later consumption returns the retained packet or its explicit index
mismatch. It does not ask the producer to find another candidate. -/
theorem cached_answers (candidate : Request n → MILCode n) (request expected : Request n) :
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family n) (produce candidate)) 5
        (cachedMachine candidate request expected) =
      [PrimeNeedDependentService.consumeOutcome (family n) expected
        (.value ⟨request, produce candidate request⟩)] := by
  have run := PrimeNeedDependentService.cached_consumer_runFrontier (family n) (produce candidate)
    expected (cachedMachine candidate request expected).work
    (PrimeNeedDependentService.producedWorld_lookup (family n) (produce candidate)
      (initialWorld request) requestCell request)
  simpa [PrimeNeedReference.answers, cachedMachine, PrimeNeedReference.haltedOutcome] using
    congrArg (List.filterMap PrimeNeedReference.haltedOutcome) run

/-- Producer replacement may change search/checking candidates, but cannot
change the already retained reply at this unchanged logical request. -/
theorem cached_answers_other_producer (candidate other : Request n → MILCode n)
    (request expected : Request n) :
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family n) (produce other)) 5
        (cachedMachine candidate request expected) =
      [PrimeNeedDependentService.consumeOutcome (family n) expected
        (.value ⟨request, produce candidate request⟩)] := by
  have run := PrimeNeedDependentService.cached_consumer_runFrontier (family n) (produce other)
    expected (cachedMachine candidate request expected).work
    (PrimeNeedDependentService.producedWorld_lookup (family n) (produce candidate)
      (initialWorld request) requestCell request)
  simpa [PrimeNeedReference.answers, cachedMachine, PrimeNeedReference.haltedOutcome] using
    congrArg (List.filterMap PrimeNeedReference.haltedOutcome) run

/-- Any accepted reply returned by the actual machine establishes the
requested conversion, with source admission and formation still separate. -/
theorem returned_reply_contract (candidate : Request n → MILCode n)
    (request : Request n) (reply : Reply request)
    (returned : PrimeNeedReference.Produced.value ⟨request, reply⟩ ∈
      PrimeNeedReference.answers (PrimeNeedDependentService.spec (family n) (produce candidate)) 7 (initialMachine request))
    (accepted : reply.accepted = true) :
    reply.candidate = candidate request ∧
      Conv IntrinsicMILHypothesis.rules.headEq request.left request.right
        IntrinsicMILHypothesis.rules.computation := by
  have samePacket : (⟨request, reply⟩ : PrimeNeedDependentService.Packet (family n)) =
      ⟨request, produce candidate request⟩ := by
    rw [fresh_answers candidate request] at returned
    simpa only [List.mem_singleton, PrimeNeedReference.Produced.value.injEq]
      using returned
  have sameReply : reply = produce candidate request :=
    eq_of_heq (Sigma.mk.inj samePacket).2
  exact ⟨congrArg Reply.candidate sameReply, reply.conversion accepted⟩

namespace Examples

open IntrinsicMILHypothesis
open NativeConversionChecking.Examples

/-- The target changes both indices of a genuinely dependent identity type. -/
def identityRequest (revision : Nat) : Request 8 :=
  ⟨revision, .id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft,
    .id primitiveIotaResultType primitiveIotaRight primitiveIotaRight⟩

abbrev identityProducer : (request : Request 8) → Reply request :=
  produce (fun _ => primitiveIdentityTypeCode)

theorem identity_reply_accepted (revision : Nat) :
    (identityProducer (identityRequest revision)).accepted = true :=
  primitive_identity_type_checked

/-- Target formation uses independently proved native preservation, including
the original dependent result type; it is not inferred from the reply. -/
theorem identity_reply_admits (revision : Nat) :
    FormationSensitive.Judgment rules contextSPMPCSourceTargetSymbol
      (.refl primitiveIotaLeft)
      (identityRequest revision).right := by
  have source := FormationSensitiveMILElimination.primitiveIota_judgments.1
  have target := checked_mil_step_preserves source primitive_step_checked
  obtain ⟨sortHead, isUniverse, typeFormed⟩ := source.regularity
    (FormationSensitive.towerUniverseRegularity.includeSignature rawSignature)
  exact (identityProducer (identityRequest revision)).admit (identity_reply_accepted revision)
    ⟨source.context, .reflIntro source.typing⟩
    (.idForm typeFormed.typing isUniverse target.typing target.typing) isUniverse

def sameEndpointRequest : Request 0 :=
  ⟨0, .head secondHead, .head secondHead⟩

/-- A malformed proposed path can fail although its endpoints do convert.
Stable rejection of this candidate must not become a theorem of inequality. -/
theorem rejected_candidate_has_convertible_endpoints :
    (produce (fun _ : Request 0 => brokenJoin) sameEndpointRequest).accepted = false ∧
      Conv rules.headEq sameEndpointRequest.left sameEndpointRequest.right
        rules.computation :=
  ⟨by decide, .refl _⟩

def reflexiveReply : Reply sameEndpointRequest :=
  produce (fun _ => .refl (.head secondHead)) sameEndpointRequest

def headReply : Reply sameEndpointRequest :=
  produce (fun _ => .single (.head secondHead secondHead)) sameEndpointRequest

theorem equal_claims_retain_distinct_candidates :
    reflexiveReply.accepted = true ∧ headReply.accepted = true ∧
      reflexiveReply.candidate ≠ headReply.candidate := by
  refine ⟨by decide, by decide, ?_⟩
  intro impossible
  cases impossible

/-- The first and second invocations expose the same exact dependent code,
although the second follows the cached path of the actual machine. -/
theorem first_and_cached_identity_answers (revision : Nat) :
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family 8) identityProducer) 7
        (initialMachine (identityRequest revision)) =
      [.value ⟨identityRequest revision, identityProducer (identityRequest revision)⟩] ∧
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family 8) identityProducer) 5
        (cachedMachine (fun _ => primitiveIdentityTypeCode)
          (identityRequest revision) (identityRequest revision)) =
      [.value ⟨identityRequest revision, identityProducer (identityRequest revision)⟩] := by
  constructor
  · exact fresh_answers _ _
  · simpa only [PrimeNeedDependentService.consumeOutcome_matching (family 8)
      (identityRequest revision) (identityProducer (identityRequest revision))] using
      cached_answers (fun _ => primitiveIdentityTypeCode)
        (identityRequest revision) (identityRequest revision)

theorem wrong_revision_rejected :
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family 8) identityProducer) 5
        (cachedMachine (fun _ => primitiveIdentityTypeCode) (identityRequest 0) (identityRequest 1)) =
      [.retryableFault (.domain ⟨identityRequest 1, identityRequest 0⟩)] := by
  rw [cached_answers]
  rw [PrimeNeedDependentService.consumeOutcome_mismatched (family 8)
    (show identityRequest 0 ≠ identityRequest 1 from by
      intro same
      have impossible := congrArg Request.revision same
      cases impossible)]

def changedEndpointRequest : Request 8 :=
  { identityRequest 0 with right := .head .legacyGround }

/-- Matching only a revision would accept this stale obligation; matching the
full request rejects the changed target before it can be used. -/
theorem changed_endpoint_rejected :
    PrimeNeedReference.answers (PrimeNeedDependentService.spec (family 8) identityProducer) 5
        (cachedMachine (fun _ => primitiveIdentityTypeCode) (identityRequest 0) changedEndpointRequest) =
      [.retryableFault (.domain ⟨changedEndpointRequest, identityRequest 0⟩)] := by
  rw [cached_answers]
  rw [PrimeNeedDependentService.consumeOutcome_mismatched (family 8)
    (show identityRequest 0 ≠ changedEndpointRequest from by
      intro same
      have impossible := congrArg Request.right same
      cases impossible)]

/-- A new producer that supplies a bad code cannot damage a previously
checked proof. This changes neither its logical package nor its revision. -/
theorem cached_proof_independent_of_failed_new_candidate (revision : Nat) :
    (produce (fun request : Request 8 => .refl request.left)
      (identityRequest revision)).accepted = false ∧
    PrimeNeedReference.answers
        (PrimeNeedDependentService.spec (family 8)
          (produce (fun request : Request 8 => .refl request.left))) 5
        (cachedMachine (fun _ => primitiveIdentityTypeCode)
          (identityRequest revision) (identityRequest revision)) =
      [.value ⟨identityRequest revision, identityProducer (identityRequest revision)⟩] := by
  constructor
  · rfl
  · simpa only [PrimeNeedDependentService.consumeOutcome_matching (family 8)
      (identityRequest revision) (identityProducer (identityRequest revision))] using
      cached_answers_other_producer (fun _ => primitiveIdentityTypeCode)
        (fun request => .refl request.left) (identityRequest revision) (identityRequest revision)

end Examples

end NativeConversionNeedConsumer
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
