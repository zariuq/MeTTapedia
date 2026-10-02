import Mettapedia.Machines.RunContracts.TestPlan
import Mettapedia.Machines.RunContracts.Completion
import Mettapedia.Machines.RunContracts.Diagnostics
import Mettapedia.Machines.RunContracts.ScopedOutcome

/-!
# A framed run reporter with checked test and observation contracts

The wire protocol must end with exactly one terminal record. A parser checks
this independently of the declarative encoding equation. A reporter then
combines the test-plan checker, demand-relative completion monitor and bounded
diagnostic collector. Its success theorem is a conjunction of their reference
contracts; an empty answer bag, Error-shaped payload, or truncated diagnostic
display cannot substitute for those contracts.

No first diagnostic is part of the success observation. Existing dialect
handlers still own which failures escape a scope. These are executable Lean
models and reference relations, not a theorem about CeTTa C, a serializer, or
the correctness of discovery/foreign adapters. Finite traces model completed
observations; the absence of a terminal record is never successful. Actual
nontermination or external termination need not produce a record at all.

Each report covers one declared observation demand. A file containing several
queries must check their contracts separately rather than pool answer counts.
Worker identifiers name fresh ownership lifecycles, not reusable thread IDs.
Output acknowledgement covers answer transport in this model; serialization
and delivery of the final diagnostic/test report remain external obligations.

Exit integers here follow the proposed convention: 0 succeeds, 2 reports
unhandled fault evidence, 1 reports other unsuccessful contracts or framing.
They are a boundary policy, not a definition of language-level Error values.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.Runner

variable {E S : Type*}

inductive Packet (E S : Type*) where
  | event (value : E)
  | terminal (stop : S)
  deriving DecidableEq, Repr

/-- Reject missing, repeated or non-final terminal records. -/
def decode : List (Packet E S) → Option (List E × S)
  | [] => none
  | .terminal stop :: [] => some ([], stop)
  | .terminal _ :: _ :: _ => none
  | .event e :: rest => (decode rest).map fun decoded => (e :: decoded.1, decoded.2)

theorem decode_encode (body : List E) (stop : S) :
    decode (body.map Packet.event ++ [.terminal stop]) = some (body, stop) := by
  induction body with
  | nil => rfl
  | cons e rest ih => simp [decode, ih]

theorem decode_sound (wire : List (Packet E S)) (body : List E) (stop : S)
    (accepted : decode wire = some (body, stop)) :
    wire = body.map Packet.event ++ [.terminal stop] := by
  induction wire generalizing body stop with
  | nil => simp [decode] at accepted
  | cons packet rest ih =>
      cases packet with
      | terminal s =>
          cases rest with
          | nil =>
              simp only [decode, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              rfl
          | cons x xs => simp [decode] at accepted
      | event e =>
          cases hr : decode rest with
          | none => simp [decode, hr] at accepted
          | some decoded =>
              obtain ⟨tail, terminal⟩ := decoded
              simp only [decode, hr, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              simp [ih tail terminal hr]

theorem decode_iff (wire : List (Packet E S)) (body : List E) (stop : S) :
    decode wire = some (body, stop) ↔
      wire = body.map Packet.event ++ [.terminal stop] := by
  constructor
  · exact decode_sound wire body stop
  · intro h
    rw [h, decode_encode]

variable {Answer Id Fault State : Type}

inductive Event (Answer Id Fault : Type) where
  | activity (event : Completion.Event Answer)
  | test (verdict : TestPlan.Result Id)
  | unhandled (fault : Fault)
  deriving DecidableEq, Repr

def activities (body : List (Event Answer Id Fault)) : List (Completion.Event Answer) :=
  body.filterMap fun e => match e with
    | .activity a => some a
    | _ => none

def verdicts (body : List (Event Answer Id Fault)) : List (TestPlan.Result Id) :=
  body.filterMap fun e => match e with
    | .test r => some r
    | _ => none

def diagnosticEvents (body : List (Event Answer Id Fault)) :
    List (Diagnostics.Event Answer Fault) :=
  body.filterMap fun e => match e with
    | .activity (.answer a) => some (.returned a)
    | .unhandled d => some (.unhandled d)
    | _ => none

/-- A terminal fault is itself evidence even without an earlier fault event.
Adapters must not report a single occurrence twice if exact fault counts matter. -/
def terminalEvents (stop : Completion.ProducerStop State Fault) :
    List (Diagnostics.Event Answer Fault) :=
  match stop with
  | .fault d => [.unhandled d]
  | _ => []

def allDiagnostics (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) : List (Diagnostics.Event Answer Fault) :=
  diagnosticEvents body ++ terminalEvents stop

/-- Ordinary evaluation needs no declared tests, but an actual resolved failed
assertion still fails. Test mode additionally checks the declared identity bag. -/
def TestContract (plan : Option (TestPlan.Plan Id))
    (results : List (TestPlan.Result Id)) : Prop :=
  match plan with
  | none => TestPlan.AllPassed results
  | some p => TestPlan.Satisfied p results

def testsAccepted [DecidableEq Id] (plan : Option (TestPlan.Plan Id))
    (results : List (TestPlan.Result Id)) : Bool :=
  match plan with
  | none => results.all TestPlan.Result.passed
  | some p => TestPlan.accepts p results

theorem testsAccepted_iff [DecidableEq Id] (plan : Option (TestPlan.Plan Id))
    (results : List (TestPlan.Result Id)) :
    testsAccepted plan results = true ↔ TestContract plan results := by
  cases plan <;> simp [testsAccepted, TestContract, TestPlan.accepts_iff,
    TestPlan.AllPassed, List.all_eq_true]

/-- Resource readiness is independent of the answer and test predicates. -/
def ResourcesReady (events : List (Completion.Event Answer)) : Prop :=
  Completion.LegalResourceTrace events ∧
  (∀ id, Completion.Event.workerStarted id ∈ events →
    Completion.Event.workerSettled id ∈ events) ∧
  Completion.OutputHistorySucceeded events ∧
  Completion.CleanupHistorySucceeded events

def BodyContract (demand : Completion.Demand) (plan : Option (TestPlan.Plan Id))
    (body : List (Event Answer Id Fault)) (stop : Completion.ProducerStop State Fault) : Prop :=
  Diagnostics.faultEvidence (allDiagnostics body stop) = 0 ∧
  TestContract plan (verdicts body) ∧
  Completion.ObservationComplete demand (Completion.occurrences (activities body)) stop ∧
  ResourcesReady (activities body)

structure Report (Fault : Type) where
  exitCode : Nat
  diagnostics : Diagnostics.Collected Fault
  observationComplete : Bool
  testsPassed : Bool
  finalizationReady : Bool

def resourcesReadyB (summary : Completion.Summary) : Bool :=
  summary.protocolOK && (summary.pendingWorkers == ∅) &&
    (summary.output == .success) && (summary.cleanup == .success)

theorem resourcesReadyB_iff (events : List (Completion.Event Answer)) :
    resourcesReadyB (Completion.scan events) = true ↔ ResourcesReady events := by
  have complete : Completion.ObservationComplete .exhaustive (Completion.occurrences events)
      (.observed .complete : Completion.ProducerStop Unit Unit) := .exhaustive _
  simpa only [Completion.commandSucceeded, Completion.completeB, Bool.true_and,
    complete, true_and, resourcesReadyB, ResourcesReady] using
    (Completion.commandSucceeded_full_reference_iff .exhaustive
      (.observed .complete : Completion.ProducerStop Unit Unit) events)

/-- The bounded detail budget never bounds failure accounting. -/
def report [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id)) (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) : Report Fault :=
  let diagnostics := Diagnostics.collect budget (allDiagnostics body stop)
  let complete := Completion.commandSucceeded demand stop (Completion.scan (activities body))
  let tested := testsAccepted plan (verdicts body)
  { exitCode := if diagnostics.total = 0 then (if complete && tested then 0 else 1) else 2
    diagnostics := diagnostics
    observationComplete := Completion.completeB demand
      (Completion.scan (activities body)).answerCount stop
    testsPassed := tested
    finalizationReady := resourcesReadyB (Completion.scan (activities body)) }

/-- Reporting observation completion does not erase it when a later output or
cleanup action fails. Overall process success still requires both. -/
theorem report_completion_iff [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id)) (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) :
    (report budget demand plan body stop).observationComplete = true ↔
      Completion.ObservationComplete demand (Completion.occurrences (activities body)) stop := by
  simp only [report, Completion.scan_count, Completion.Summary.initial, Nat.zero_add,
    Completion.completeB_iff]

theorem report_finalization_iff [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id)) (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) :
    (report budget demand plan body stop).finalizationReady = true ↔ ResourcesReady (activities body) :=
  resourcesReadyB_iff (activities body)

/-- Fault identity and the number of additional observed faults do not matter
to this failure class. A diagnostic bag is not required to survive unchanged. -/
theorem report_fault_iff [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id)) (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) :
    (report budget demand plan body stop).exitCode = 2 ↔
      Diagnostics.faultEvidence (allDiagnostics body stop) ≠ 0 := by
  dsimp only [report]
  rw [Diagnostics.collect_total]
  split_ifs <;> simp_all [Multiset.card_eq_zero]

theorem terminal_fault_reports_failure [DecidableEq Id] (budget : Nat)
    (demand : Completion.Demand) (plan : Option (TestPlan.Plan Id))
    (body : List (Event Answer Id Fault)) (fault : Fault) :
    (report budget demand plan body (.fault fault : Completion.ProducerStop State Fault)).exitCode
      = 2 := by
  apply (report_fault_iff budget demand plan body (.fault fault)).mpr
  simp only [allDiagnostics, terminalEvents]
  suffices appended : ∀ events : List (Diagnostics.Event Answer Fault),
      Diagnostics.faultEvidence (events ++ [.unhandled fault]) ≠ 0 from appended _
  intro events
  induction events with
  | nil => simp [Diagnostics.faultEvidence]
  | cons event rest ih =>
      cases event <;> simp [Diagnostics.faultEvidence, ih]

/-- Two faulting runs may stop with different witnesses and may have observed
different numbers of further faults. Neither is forced to finish enumerating
faults merely to preserve the exit status. -/
theorem faulting_reports_same_status [DecidableEq Id] (a b : Nat)
    (demand : Completion.Demand) (plan : Option (TestPlan.Plan Id))
    (left right : List (Event Answer Id Fault))
    (leftStop rightStop : Completion.ProducerStop State Fault)
    (leftFault : Diagnostics.faultEvidence (allDiagnostics left leftStop) ≠ 0)
    (rightFault : Diagnostics.faultEvidence (allDiagnostics right rightStop) ≠ 0) :
    (report a demand plan left leftStop).exitCode = (report b demand plan right rightStop).exitCode :=
  ((report_fault_iff a demand plan left leftStop).mpr leftFault).trans
    ((report_fault_iff b demand plan right rightStop).mpr rightFault).symm

/-- Report success agrees with the independently specified occurrence and
test contracts. Resource protocol readiness is also required, not inferred
from answer counts or diagnostic text. -/
theorem report_zero_iff [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id)) (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) :
    (report budget demand plan body stop).exitCode = 0 ↔ BodyContract demand plan body stop := by
  simp only [report]
  split
  next clear =>
    have he : Diagnostics.faultEvidence (allDiagnostics body stop) = 0 := by
      simpa only [Diagnostics.collect_total, Multiset.card_eq_zero] using clear
    simp only [BodyContract, he, true_and, ResourcesReady]
    rw [ite_eq_left_iff]
    simp only [Bool.and_eq_true, Completion.commandSucceeded_full_reference_iff, testsAccepted_iff]
    tauto
  next failed =>
    have he : Diagnostics.faultEvidence (allDiagnostics body stop) ≠ 0 := by
      simpa only [Diagnostics.collect_total, Multiset.card_eq_zero] using failed
    simp [BodyContract, he]

def exitCode [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id))
    (wire : List (Packet (Event Answer Id Fault) (Completion.ProducerStop State Fault))) : Nat :=
  match decode wire with
  | none => 1
  | some (body, stop) => (report budget demand plan body stop).exitCode

/-- Independent external contract includes an explicit final record. -/
def RunContract (demand : Completion.Demand) (plan : Option (TestPlan.Plan Id))
    (wire : List (Packet (Event Answer Id Fault) (Completion.ProducerStop State Fault))) : Prop :=
  ∃ body stop, wire = body.map Packet.event ++ [.terminal stop] ∧
    BodyContract demand plan body stop

theorem exitCode_zero_iff [DecidableEq Id] (budget : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id))
    (wire : List (Packet (Event Answer Id Fault) (Completion.ProducerStop State Fault))) :
    exitCode budget demand plan wire = 0 ↔ RunContract demand plan wire := by
  constructor
  · intro h
    cases hd : decode wire with
    | none => simp [exitCode, hd] at h
    | some pair =>
        obtain ⟨body, stop⟩ := pair
        refine ⟨body, stop, decode_sound wire body stop hd, ?_⟩
        apply (report_zero_iff budget demand plan body stop).mp
        simpa [exitCode, hd] using h
  · rintro ⟨body, stop, hwire, hbody⟩
    rw [hwire]
    simp only [exitCode, decode_encode]
    exact (report_zero_iff budget demand plan body stop).mpr hbody

/-- Details may be truncated or expanded without changing process status. -/
theorem report_budget_independent [DecidableEq Id] (a b : Nat) (demand : Completion.Demand)
    (plan : Option (TestPlan.Plan Id)) (body : List (Event Answer Id Fault))
    (stop : Completion.ProducerStop State Fault) :
    (report a demand plan body stop).exitCode = (report b demand plan body stop).exitCode := by
  simp only [report, Diagnostics.collect_total]

theorem testsAccepted_perm [DecidableEq Id] (plan : Option (TestPlan.Plan Id))
    {xs ys : List (TestPlan.Result Id)} (permutation : xs.Perm ys) :
    testsAccepted plan xs = testsAccepted plan ys := by
  cases plan with
  | none => exact permutation.all_eq
  | some p => exact TestPlan.accepts_perm p permutation

/-- Scheduling may reorder independent resolved verdicts and fault records.
The resource/effect trace is held fixed here; that stronger equivalence must
come from a separate optimization theorem. No error identity is preferred. -/
theorem report_observation_invariant [DecidableEq Id] (a b : Nat)
    (demand : Completion.Demand) (plan : Option (TestPlan.Plan Id))
    (left right : List (Event Answer Id Fault)) (stop : Completion.ProducerStop State Fault)
    (resources : activities left = activities right)
    (tests : (verdicts left).Perm (verdicts right))
    (faults : (allDiagnostics left stop).Perm (allDiagnostics right stop)) :
    (report a demand plan left stop).exitCode = (report b demand plan right stop).exitCode := by
  simp only [report, Diagnostics.collect_total, resources, testsAccepted_perm plan tests,
    Diagnostics.faultEvidence_perm faults]

/-- Attach a checked scope resolver to a stable test identity. -/
def resolvedTest (id : Id) (expectation : ScopedOutcome.Expectation Answer Fault)
    (program : ScopedOutcome.Computation Answer Fault) : TestPlan.Result Id :=
  ⟨id, ScopedOutcome.resolve expectation program⟩

theorem resolvedTest_correct (id : Id) (expectation : ScopedOutcome.Expectation Answer Fault)
    (program : ScopedOutcome.Computation Answer Fault) :
    (resolvedTest id expectation program).passed = true ↔
      ∃ observations, ScopedOutcome.Observes program observations ∧
        ScopedOutcome.Satisfies expectation observations :=
  ScopedOutcome.resolve_correct expectation program

namespace Controls

abbrev B := Event Nat Nat String
abbrev W := Packet B (Completion.ProducerStop Unit String)

def done : List B := [.activity .outputComplete, .activity .cleanupComplete]
def close (body : List B) : List W :=
  body.map Packet.event ++ [.terminal (.observed .complete)]
def oneTest : TestPlan.Plan Nat := ⟨{7}, false⟩

example : exitCode 1 .exhaustive none (close done) = 0 := by decide
example : exitCode 1 .exhaustive none ([] : List W) = 1 := by decide
example : exitCode 1 .exhaustive none (close done ++ [.terminal (.observed .complete)]) = 1 := by
  decide
example : exitCode 1 .exhaustive none (close done ++ [.event (.activity (.answer 9))]) = 1 := by
  decide
example : exitCode 1 .exhaustive (some oneTest) (close done) = 1 := by decide
example : exitCode 1 .exhaustive (some oneTest) (close (.test ⟨7, true⟩ :: done)) = 0 := by
  decide
example : exitCode 1 .exhaustive none (close (.test ⟨7, false⟩ :: done)) = 1 := by decide
example : exitCode 0 .exhaustive none (close (.unhandled "boom" :: done)) = 2 := by decide
example : exitCode 1 .exhaustive none
    (close [.activity (.answer 9), .activity .outputFailed, .activity .cleanupComplete]) = 1 := by
  decide

theorem output_failure_does_not_erase_completed_observation :
    let failedOutput : List B :=
      [.activity (.answer 9), .activity .outputFailed, .activity .cleanupComplete]
    let r := report 1 (.prefix 1) none failedOutput
      (.demandSatisfied : Completion.ProducerStop Unit String)
    r.observationComplete = true ∧ r.finalizationReady = false ∧ r.exitCode = 1 := by decide

def expectsBoom : ScopedOutcome.Expectation Nat String := .raises (· == "boom")

/-- A fault consumed by an expected-error test contributes a passing verdict,
not an escaped fault event. A sibling escaped fault remains independently fatal. -/
theorem expected_error_test_passes : exitCode 0 .exhaustive (some oneTest)
    (close (.test (resolvedTest 7 expectsBoom (.raise "boom")) :: done)) = 0 := by decide

theorem expected_error_cannot_hide_sibling : exitCode 0 .exhaustive (some oneTest)
    (close (.test (resolvedTest 7 expectsBoom (.raise "boom")) ::
      .unhandled "elsewhere" :: done)) = 2 := by decide

theorem missing_expected_error_fails : exitCode 0 .exhaustive (some oneTest)
    (close (.test (resolvedTest 7 expectsBoom .empty) :: done)) = 1 := by decide

theorem zero_details_cannot_hide_terminal_fault :
    exitCode 0 .exhaustive none
      (done.map Packet.event ++ [.terminal (.fault "boom")] : List W) = 2 := by decide

theorem independent_fault_order_same_status :
    exitCode 1 .exhaustive none (close (.unhandled "first" :: .unhandled "second" :: done)) =
    exitCode 1 .exhaustive none (close (.unhandled "second" :: .unhandled "first" :: done)) := by
  decide

theorem bounded_completion_passes : exitCode 1 (.prefix 1) none
    ((.activity (.answer 8) :: done).map Packet.event ++
      [.terminal .demandSatisfied] : List W) = 0 := by decide

theorem short_demand_stop_fails : exitCode 1 (.prefix 5) none
    ((.activity (.answer 8) :: done).map Packet.event ++
      [.terminal .demandSatisfied] : List W) = 1 := by decide

theorem short_exhaustion_passes : exitCode 1 (.prefix 5) none
    (close (.activity (.answer 8) :: done)) = 0 := by decide

theorem error_shaped_data_passes : exitCode (Answer := String) (Id := Nat) (Fault := String)
    1 .exhaustive none
    ([.event (.activity (.answer "(Error payload message)")),
      .event (.activity .outputComplete), .event (.activity .cleanupComplete),
      .terminal (.observed (.complete : RunStop Unit))]) = 0 := by decide

end Controls

end Mettapedia.Machines.RunContracts.Runner
