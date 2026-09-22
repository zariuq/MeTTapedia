import Mettapedia.GSLT.LanguageDef.NIKServiceInvocation
import Mettapedia.GSLT.Dynamics.ServiceResumption

/-!
# Nested invocation of native inference services

An existentially packed service/request lets the existing resumption syntax
change service faces between calls. Its reply fibre is the existing invocation
response: claims, guest proof objects, external certificates, and raw operation
inputs are not recoded into a common evidence format.

The success-only call combinator continues with the actual accepted value. A
rejection instead returns the exact request and response as a stopped outcome;
the existing evaluator retains that receipt in chronological history. Operation
source meaning remains an explicit qualification premise, never a runtime
decision inferred from producing a raw value.

The qualification theorem concerns this typed callback and the existing
isolated-world resumption evaluator. It asserts neither an authored backend or
OSLF realization nor an interpretation shared by different native languages.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKServiceResumption

open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIK
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uArtifact uEvidence uState uIntent

/-- Packing only supplies the common request carrier required by the existing
dependent resumption. The selected service and its full input remain present. -/
abbrev PackedRequest (target : AdmissionObject.{uArtifact}) :=
  Σ service : Service.{uArtifact, uEvidence} target, NIKServiceInvocation.Request service

abbrev Reply {target : AdmissionObject.{uArtifact}}
    (input : PackedRequest.{uArtifact, uEvidence} target) := NIKServiceInvocation.Response input.2

/-- The callback executes exactly the existing face-specific invocation. -/
def invoke {target : AdmissionObject.{uArtifact}}
    (input : PackedRequest.{uArtifact, uEvidence} target) : Reply input :=
  NIKServiceInvocation.invoke input.2

abbrev Receipt (target : AdmissionObject.{uArtifact}) :=
  Sigma (Reply.{uArtifact, uEvidence} (target := target))

/-- Stopped outcomes retain their actual response, including whether the stop
was a false decision, a rejected native proof, or a rejected certificate. -/
abbrev Outcome (target : AdmissionObject.{uArtifact}) :=
  Sum (Receipt.{uArtifact, uEvidence} target) target.Carrier

abbrev Computation (target : AdmissionObject.{uArtifact})
    (State : Type uState) (Intent : Type uIntent) :=
  ServiceResumption.Resumption (PackedRequest.{uArtifact, uEvidence} target) Reply State
    (Outcome.{uArtifact, uEvidence} target) Intent

variable {target : AdmissionObject.{uArtifact}}
variable {State : Type uState} {Intent : Type uIntent}

/-- Only a successful actual response enters the value-dependent continuation.
The declined response remains a result, not an empty collection of worlds. -/
def call (input : PackedRequest.{uArtifact, uEvidence} target)
    (next : target.Carrier → Computation.{uArtifact, uEvidence} target State Intent) :
    Computation.{uArtifact, uEvidence} target State Intent :=
  .request input fun response => match response.acceptedValue with
    | none => .pure (.inl ⟨input, response⟩)
    | some value => next value

/-- Success sequencing reuses the existing bind and never resumes a stopped
outcome. Its earlier replies and effects are retained by that bind. -/
def andThen (computation : Computation.{uArtifact, uEvidence} target State Intent)
    (next : target.Carrier → Computation.{uArtifact, uEvidence} target State Intent) :
    Computation.{uArtifact, uEvidence} target State Intent :=
  computation.bind fun outcome => match outcome with
    | .inl receipt => .pure (.inl receipt)
    | .inr value => next value

theorem call_andThen (input : PackedRequest.{uArtifact, uEvidence} target)
    (first next : target.Carrier →
      Computation.{uArtifact, uEvidence} target State Intent) :
    andThen (call input first) next = call input (fun value => andThen (first value) next) := by
  simp only [andThen, call, ServiceResumption.Resumption.request_bind]
  congr 1
  funext response
  cases response.acceptedValue <;> rfl

theorem andThen_assoc
    (computation : Computation.{uArtifact, uEvidence} target State Intent)
    (first next : target.Carrier →
      Computation.{uArtifact, uEvidence} target State Intent) :
    andThen (andThen computation first) next =
      andThen computation (fun value => andThen (first value) next) := by
  simp only [andThen, ServiceResumption.Resumption.bind_assoc]
  congr 1
  funext outcome
  cases outcome <;> rfl

/-- Qualification is syntax-directed. Calls use the existing source admission
judgment, and successful continuations may use the resulting target meaning.
There is no arbitrary constructor asserting qualification of an entire run. -/
inductive Qualified : Computation.{uArtifact, uEvidence} target State Intent → Prop where
  | returned {value : target.Carrier} (meaningful : target.Meaning value) :
      Qualified (.pure (.inr value))
  | choose {left right} (leftQualified : Qualified left) (rightQualified : Qualified right) :
      Qualified (.choose left right)
  | read {next} (qualified : ∀ state, Qualified (next state)) : Qualified (.read next)
  | write {state next} (qualified : Qualified next) : Qualified (.write state next)
  | intent {value next} (qualified : Qualified next) : Qualified (.intent value next)
  | call {input : PackedRequest.{uArtifact, uEvidence} target} {next}
      (admitted : NIKServiceInvocation.InputAdmission input.2)
      (qualified : ∀ value, target.Meaning value → Qualified (next value)) :
      Qualified (call input next)

theorem Qualified.andThen
    {computation : Computation.{uArtifact, uEvidence} target State Intent}
    (qualified : Qualified computation)
    (next : target.Carrier → Computation.{uArtifact, uEvidence} target State Intent)
    (nextQualified : ∀ value, target.Meaning value → Qualified (next value)) :
    Qualified (andThen computation next) := by
  induction qualified with
  | returned meaningful => exact nextQualified _ meaningful
  | choose _ _ leftIH rightIH => exact .choose leftIH rightIH
  | read _ nextIH => exact .read nextIH
  | write _ nextIH => exact .write nextIH
  | intent _ nextIH => exact .intent nextIH
  | call admitted _ nextIH =>
      rw [call_andThen]
      exact .call admitted nextIH

/-- On success the existing request rule prefixes the actual receipt to every
world of the continuation at the unchanged private state and branch. -/
theorem runWorldsAt_call_success
    (input : PackedRequest.{uArtifact, uEvidence} target)
    (next : target.Carrier → Computation.{uArtifact, uEvidence} target State Intent)
    (state : State) (branch : List Bool) {value : target.Carrier}
    (accepted : (invoke input).acceptedValue = some value) :
    ServiceResumption.runWorldsAt invoke (call input next) state branch =
      (ServiceResumption.runWorldsAt invoke (next value) state branch).map
        (ServiceResumption.Result.prepend [] [⟨input, invoke input⟩]) := by
  simp only [call, ServiceResumption.runWorldsAt_request, accepted]

/-- A stopped call is exactly one world with its original state, branch, and
request-indexed response; it does not run the success continuation. -/
theorem runWorldsAt_call_stopped
    (input : PackedRequest.{uArtifact, uEvidence} target)
    (next : target.Carrier → Computation.{uArtifact, uEvidence} target State Intent)
    (state : State) (branch : List Bool)
    (rejected : (invoke input).acceptedValue = none) :
    ServiceResumption.runWorldsAt invoke (call input next) state branch =
      [{ world := { branch := branch, answer := .inl ⟨input, invoke input⟩,
                    state := state, intents := [] },
         replies := [⟨input, invoke input⟩] }] := by
  simp [call, ServiceResumption.runWorldsAt_request, rejected, ServiceResumption.Result.prepend]

/-- This is the existing bind equation specialized to success sequencing.
Histories are concatenated chronologically, and stopped outcomes make no
subsequent call. -/
theorem runWorldsAt_andThen
    (computation : Computation.{uArtifact, uEvidence} target State Intent)
    (next : target.Carrier → Computation.{uArtifact, uEvidence} target State Intent)
    (state : State) (branch : List Bool) :
    ServiceResumption.runWorldsAt invoke (andThen computation next) state branch =
      (ServiceResumption.runWorldsAt invoke computation state branch).flatMap fun prior =>
        match prior.world.answer with
        | .inl _ => [prior]
        | .inr value =>
            (ServiceResumption.runWorldsAt invoke (next value) prior.world.state prior.world.branch).map
              (ServiceResumption.Result.prepend prior.world.intents prior.replies) := by
  rw [andThen, ServiceResumption.runWorldsAt_bind]
  congr 1
  funext prior
  cases outcome : prior.world.answer with
  | inr value => rfl
  | inl receipt =>
      simp only [ServiceResumption.runWorldsAt_pure, List.map_cons, List.map_nil]
      congr 1
      cases prior with
      | mk world replies =>
          cases world
          simp_all [ServiceResumption.Result.prepend]

/-- Every actual call in a qualified run has its own source admission premise
and exact callback reply. Success has target meaning. A stopped outcome is a
rejected reply and is the final chronological receipt, not a countermodel or
an erased branch. -/
theorem qualified_run
    {computation : Computation.{uArtifact, uEvidence} target State Intent}
    (qualified : Qualified computation) (state : State) (branch : List Bool)
    {result} (member : result ∈ ServiceResumption.runWorldsAt invoke computation state branch) :
    (∀ receipt ∈ result.replies,
      NIKServiceInvocation.InputAdmission receipt.1.2 ∧ receipt.2 = invoke receipt.1) ∧
    (match result.world.answer with
      | .inr value => target.Meaning value
      | .inl stopped => stopped.2.acceptedValue = none ∧
          ∃ earlier, result.replies = earlier ++ [stopped]) := by
  induction qualified generalizing state branch result with
  | returned meaningful =>
      simp only [ServiceResumption.runWorldsAt_pure, List.mem_singleton] at member
      subst result
      exact ⟨by simp, meaningful⟩
  | choose _ _ leftIH rightIH =>
      rw [ServiceResumption.runWorldsAt_choose, List.mem_append] at member
      rcases member with member | member
      · exact leftIH state (false :: branch) member
      · exact rightIH state (true :: branch) member
  | read _ nextIH =>
      rw [ServiceResumption.runWorldsAt_read] at member
      exact nextIH state state branch member
  | write _ nextIH =>
      rw [ServiceResumption.runWorldsAt_write] at member
      exact nextIH _ branch member
  | intent _ nextIH =>
      rw [ServiceResumption.runWorldsAt_intent, List.mem_map] at member
      obtain ⟨later, laterMember, rfl⟩ := member
      exact nextIH state branch (result := later) laterMember
  | @call input next admitted _ nextIH =>
      cases response : (invoke input).acceptedValue with
      | none =>
          rw [runWorldsAt_call_stopped input next state branch response,
            List.mem_singleton] at member
          subst result
          refine ⟨?_, response, [], rfl⟩
          intro receipt receiptMember
          obtain rfl := List.mem_singleton.mp receiptMember
          exact ⟨admitted, rfl⟩
      | some value =>
          rw [runWorldsAt_call_success input next state branch response,
            List.mem_map] at member
          obtain ⟨later, laterMember, rfl⟩ := member
          have valueMeaning := NIKServiceInvocation.accepted_meaning input.2 admitted response
          obtain ⟨history, outcome⟩ := nextIH value valueMeaning state branch laterMember
          refine ⟨?_, ?_⟩
          · intro receipt receiptMember
            change receipt ∈ ⟨input, invoke input⟩ :: later.replies at receiptMember
            rcases List.mem_cons.mp receiptMember with rfl | receiptMember
            · exact ⟨admitted, rfl⟩
            · exact history receipt receiptMember
          · change match later.world.answer with
              | .inr answer => target.Meaning answer
              | .inl stopped => stopped.2.acceptedValue = none ∧
                  ∃ earlier, ⟨input, invoke input⟩ :: later.replies = earlier ++ [stopped]
            cases resultOutcome : later.world.answer with
            | inr answer => simpa only [resultOutcome] using outcome
            | inl stopped =>
                simp only [resultOutcome] at outcome
                obtain ⟨rejected, earlier, historyEq⟩ := outcome
                exact ⟨rejected, ⟨input, invoke input⟩ :: earlier, by rw [historyEq]; rfl⟩


/-- The success projection is independent of the number of nested calls. -/
theorem qualified_success
    {computation : Computation.{uArtifact, uEvidence} target State Intent}
    (qualified : Qualified computation) (state : State) (branch : List Bool)
    {result} (member : result ∈ ServiceResumption.runWorldsAt invoke computation state branch)
    {value : target.Carrier} (returned : result.world.answer = .inr value) :
    target.Meaning value := by
  have outcome := (qualified_run qualified state branch member).2
  simpa only [returned] using outcome

/-- A terminal stopped receipt was really invoked; rejection never means that
the resumption had no result or that a submitted proposition was refuted. -/
theorem qualified_stopped
    {computation : Computation.{uArtifact, uEvidence} target State Intent}
    (qualified : Qualified computation) (state : State) (branch : List Bool)
    {result} (member : result ∈ ServiceResumption.runWorldsAt invoke computation state branch)
    {stopped : Receipt.{uArtifact, uEvidence} target}
    (returned : result.world.answer = .inl stopped) :
    NIKServiceInvocation.InputAdmission stopped.1.2 ∧
      stopped.2 = invoke stopped.1 ∧ stopped.2.acceptedValue = none ∧
      ∃ earlier, result.replies = earlier ++ [stopped] := by
  obtain ⟨history, outcome⟩ := qualified_run qualified state branch member
  simp only [returned] at outcome
  obtain ⟨rejected, earlier, historyEq⟩ := outcome
  have present : stopped ∈ result.replies := by simp [historyEq]
  exact ⟨(history stopped present).1, (history stopped present).2,
    rejected, earlier, historyEq⟩

/-! ## Value-dependent four-face execution and stopped-evidence controls -/

namespace PositiveNaturalControl

open AdmissionCanary
open NIKServiceInvocation.PositiveNaturalControl

def decision (claim : Nat) : PackedRequest.{0, 0} positiveNaturals :=
  ⟨Canary.direct, .directDecision claim⟩

def operation (input : Nat) : PackedRequest.{0, 0} positiveNaturals :=
  ⟨Canary.native, .nativeOperation input⟩

def proof (claim predecessor : Nat) : PackedRequest.{0, 0} positiveNaturals :=
  ⟨proofService, .nativeProof claim (Proof.successor predecessor)⟩

def boundary (claim : Nat) (certificate : List Bool) : PackedRequest.{0, 0} positiveNaturals :=
  ⟨boundaryService, .certificateBoundary claim certificate⟩

/-- The continuation stores the actual decided claim as private state. -/
def decidedPrefix (initial : Nat) : Computation.{0, 0} positiveNaturals Nat Nat :=
  call (decision initial) fun decided => .write decided (.pure (.inr decided))

theorem decidedPrefix_qualified (initial : Nat) : Qualified (decidedPrefix initial) :=
  .call .directDecision fun _ meaningful => .write (.returned meaningful)

/-- Both submitted evidence objects are constructed from earlier actual
returned values. The operation input is the accepted initial claim, and the
read observes state written by the prefix, not the run's initial state. -/
def pipeline (initial : Nat) : Computation.{0, 0} positiveNaturals Nat Nat :=
  andThen (decidedPrefix initial) fun decided =>
    .read fun saved => .intent saved (
      call (operation decided) fun produced => .intent produced (
        call (proof produced (Nat.pred produced)) fun proved =>
          call (boundary proved (List.replicate (Nat.pred proved) false)) fun checked =>
            .pure (.inr checked)))

theorem pipeline_qualified (initial : Nat) : Qualified (pipeline initial) := by
  apply Qualified.andThen (decidedPrefix_qualified initial)
  intro decided decidedMeaning
  apply Qualified.read
  intro saved
  apply Qualified.intent
  apply Qualified.call (.nativeOperation decidedMeaning)
  intro produced _
  apply Qualified.intent
  apply Qualified.call .nativeProof
  intro proved _
  apply Qualified.call .certificateBoundary
  intro checked checkedMeaning
  exact .returned checkedMeaning

theorem pipeline_exact :
    ServiceResumption.runWorlds invoke (pipeline 2) 90 =
      [{ world := { branch := [], answer := .inr (3 : Nat), state := 2, intents := [2, 3] },
         replies := [⟨decision 2, .decided true⟩,
           ⟨operation 2, .produced (3 : Nat)⟩,
           ⟨proof 3 2, .proofChecked true⟩,
           ⟨boundary 3 [false, false], .boundaryChecked true⟩] }] := rfl

theorem pipeline_all_four_faces :
    (ServiceResumption.runWorlds invoke (pipeline 2) 90).map
      (fun result => result.replies.map (fun receipt => receipt.1.1.face)) =
      [[.directDecision, .nativeOperation, .nativeProof, .certificateBoundary]] := rfl

/-- Changing the initial claim changes the later native input, proved claim,
and external certificate, as well as the final answer and private state. -/
theorem later_requests_depend_on_actual_values :
    ServiceResumption.runWorlds invoke (pipeline 3) 90 =
      [{ world := { branch := [], answer := .inr (4 : Nat), state := 3, intents := [3, 4] },
         replies := [⟨decision 3, .decided true⟩,
           ⟨operation 3, .produced (4 : Nat)⟩,
           ⟨proof 4 3, .proofChecked true⟩,
           ⟨boundary 4 [false, false, false], .boundaryChecked true⟩] }] := rfl

/-- The general theorem proves meaning for every run, not just these two
normalization examples. Even a declined initial decision is qualified. -/
theorem pipeline_success_meaning (initial state : Nat) (branch : List Bool)
    {result} (member : result ∈ ServiceResumption.runWorldsAt invoke (pipeline initial) state branch)
    {value : positiveNaturals.Carrier} (returned : result.world.answer = .inr value) :
    positiveNaturals.Meaning value :=
  qualified_success (pipeline_qualified initial) state branch member returned

/-- A further actual native call used after either submitted evidence face. -/
def operationSuffix (value : Nat) : Computation.{0, 0} positiveNaturals Nat Nat :=
  call (operation value) fun produced => .intent produced (.pure (.inr produced))

theorem operationSuffix_qualified (value : Nat) (meaningful : positiveNaturals.Meaning value) :
    Qualified (operationSuffix value) :=
  .call (.nativeOperation meaningful) fun _ resultMeaning => .intent (.returned resultMeaning)

def submittedProof (predecessor : Nat) : Computation.{0, 0} positiveNaturals Nat Nat :=
  andThen (decidedPrefix 2) fun decided =>
    call (proof decided predecessor) operationSuffix

theorem submittedProof_qualified (predecessor : Nat) : Qualified (submittedProof predecessor) :=
  (decidedPrefix_qualified 2).andThen _
    (fun _ _ => .call .nativeProof operationSuffix_qualified)

/-- A valid introduction reaches the subsequent operation. -/
theorem valid_proof_resumes :
    ServiceResumption.runWorlds invoke (submittedProof 1) 90 =
      [{ world := { branch := [], answer := .inr (3 : Nat), state := 2, intents := [3] },
         replies := [⟨decision 2, .decided true⟩,
           ⟨proof 2 1, .proofChecked true⟩,
           ⟨operation 2, .produced (3 : Nat)⟩] }] := rfl

/-- The same meaningful claim with a bad submitted proof stops before that
operation. Earlier state and the two chronological receipts remain. -/
theorem rejected_proof_stops_without_refuting :
    positiveNaturals.Meaning (2 : Nat) ∧
      ServiceResumption.runWorlds invoke (submittedProof 0) 90 =
        [{ world := { branch := [], answer := .inl ⟨proof 2 0, .proofChecked false⟩,
                      state := 2, intents := [] },
           replies := [⟨decision 2, .decided true⟩,
             ⟨proof 2 0, .proofChecked false⟩] }] :=
  ⟨Nat.succ_ne_zero 1, rfl⟩

def submittedBoundary (certificate : List Bool) : Computation.{0, 0} positiveNaturals Nat Nat :=
  andThen (decidedPrefix 2) fun decided =>
    call (boundary decided certificate) operationSuffix

theorem submittedBoundary_qualified (certificate : List Bool) :
    Qualified (submittedBoundary certificate) :=
  (decidedPrefix_qualified 2).andThen _
    (fun _ _ => .call .certificateBoundary operationSuffix_qualified)

theorem valid_certificate_resumes :
    ServiceResumption.runWorlds invoke (submittedBoundary [false]) 90 =
      [{ world := { branch := [], answer := .inr (3 : Nat), state := 2, intents := [3] },
         replies := [⟨decision 2, .decided true⟩,
           ⟨boundary 2 [false], .boundaryChecked true⟩,
           ⟨operation 2, .produced (3 : Nat)⟩] }] := rfl

theorem rejected_certificate_stops_without_refuting :
    positiveNaturals.Meaning (2 : Nat) ∧
      ServiceResumption.runWorlds invoke (submittedBoundary []) 90 =
        [{ world := { branch := [], answer := .inl ⟨boundary 2 [], .boundaryChecked false⟩,
                      state := 2, intents := [] },
           replies := [⟨decision 2, .decided true⟩,
             ⟨boundary 2 [], .boundaryChecked false⟩] }] :=
  ⟨Nat.succ_ne_zero 1, rfl⟩

/-- A false direct decision is a different retained response and really does
refute this claim. It stops before the prefix's state write. -/
theorem false_decision_stops_and_refutes :
    ¬ positiveNaturals.Meaning (0 : Nat) ∧
      ServiceResumption.runWorlds invoke (pipeline 0) 90 =
        [{ world := { branch := [], answer := .inl ⟨decision 0, .decided false⟩,
                      state := 90, intents := [] },
           replies := [⟨decision 0, .decided false⟩] }] :=
  ⟨fun meaningful => meaningful rfl, rfl⟩

/-- The raw operation API still executes inadmissible source inputs. Nesting
does not turn such an execution into a qualified one. -/
def rawZero : Computation.{0, 0} positiveNaturals Nat Nat :=
  call ⟨.nativeOperation positiveNaturals doubling, .nativeOperation (0 : Nat)⟩
    fun value => .pure (.inr value)

theorem raw_execution_does_not_supply_source_admission : ¬ Qualified rawZero := by
  intro qualified
  have member :
      { world := { branch := [], answer := .inr (0 : Nat), state := 90, intents := [] },
        replies := [⟨⟨.nativeOperation positiveNaturals doubling, .nativeOperation (0 : Nat)⟩,
          .produced (0 : Nat)⟩] } ∈
        ServiceResumption.runWorldsAt invoke rawZero (90 : Nat) [] :=
    List.mem_cons_self
  have meaningful := qualified_success qualified (90 : Nat) [] member rfl
  exact meaningful rfl

end PositiveNaturalControl

#print axioms Qualified.andThen
#print axioms runWorldsAt_call_success
#print axioms runWorldsAt_call_stopped
#print axioms runWorldsAt_andThen
#print axioms qualified_run
#print axioms qualified_success
#print axioms qualified_stopped
#print axioms PositiveNaturalControl.pipeline_qualified
#print axioms PositiveNaturalControl.pipeline_success_meaning
#print axioms PositiveNaturalControl.pipeline_exact
#print axioms PositiveNaturalControl.pipeline_all_four_faces
#print axioms PositiveNaturalControl.later_requests_depend_on_actual_values
#print axioms PositiveNaturalControl.valid_proof_resumes
#print axioms PositiveNaturalControl.rejected_proof_stops_without_refuting
#print axioms PositiveNaturalControl.valid_certificate_resumes
#print axioms PositiveNaturalControl.rejected_certificate_stops_without_refuting
#print axioms PositiveNaturalControl.false_decision_stops_and_refutes
#print axioms PositiveNaturalControl.raw_execution_does_not_supply_source_admission

end Mettapedia.GSLT.LanguageDef.NIKServiceResumption
