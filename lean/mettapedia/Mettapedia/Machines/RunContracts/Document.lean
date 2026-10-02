import Mettapedia.Machines.RunContracts.Runner

/-!
# Documents containing independently contracted queries

A finite declared query catalogue assigns each query its demand and optional
test plan. The document checker consumes query identities using the existing
incremental test-plan algorithm. Each resolved query is checked against its
own framed runner contract; answer counts are never pooled across queries.

Document output and cleanup have their own resource trace and terminal record.
Query completion cannot acknowledge delivery of the document's final report.
The specification states framing, an exact identity bag, every query's runner
contract, and the document boundary contract independently of the checker.

This is a finite protocol composition theorem. Catalogue discovery, authentic
native event production, serializers, OS delivery and concrete C correspondence
remain separate obligations. Query arrival order does not promise that effectful
queries can be reordered during execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.Document

variable {QueryId TestId Answer Fault State : Type}

structure QuerySpec (TestId : Type) where
  demand : Completion.Demand
  tests : Option (TestPlan.Plan TestId)

structure Plan (QueryId TestId : Type) where
  expected : Finset QueryId
  specification : QueryId → QuerySpec TestId

structure Query (QueryId TestId Answer Fault State : Type) where
  id : QueryId
  wire : List (Runner.Packet (Runner.Event Answer TestId Fault)
    (Completion.ProducerStop State Fault))

inductive Event (QueryId TestId Answer Fault State : Type) where
  | query (record : Query QueryId TestId Answer Fault State)
  | resource (event : Completion.Event Unit)
  | unhandled (fault : Fault)

def queries (body : List (Event QueryId TestId Answer Fault State)) :
    List (Query QueryId TestId Answer Fault State) :=
  body.filterMap fun event => match event with
    | .query q => some q
    | _ => none

def boundaryEvents (body : List (Event QueryId TestId Answer Fault State)) :
    List (Runner.Event Unit Unit Fault) :=
  body.filterMap fun event => match event with
    | .resource r => some (.activity r)
    | .unhandled fault => some (.unhandled fault)
    | .query _ => none

def queryStatus [DecidableEq TestId] (budget : Nat) (plan : Plan QueryId TestId)
    (query : Query QueryId TestId Answer Fault State) : Nat :=
  let spec := plan.specification query.id
  Runner.exitCode budget spec.demand spec.tests query.wire

def queryVerdicts [DecidableEq TestId] (budget : Nat) (plan : Plan QueryId TestId)
    (records : List (Query QueryId TestId Answer Fault State)) :
    List (TestPlan.Result QueryId) :=
  records.map fun q => ⟨q.id, decide (queryStatus budget plan q = 0)⟩

def queriesAccepted [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (records : List (Query QueryId TestId Answer Fault State)) : Bool :=
  TestPlan.accepts ⟨plan.expected, true⟩ (queryVerdicts budget plan records)

/-- Empty ordinary documents are permitted; a query's own test discovery
policy remains checked independently by its runner. -/
theorem queriesAccepted_iff [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (records : List (Query QueryId TestId Answer Fault State)) :
    queriesAccepted budget plan records = true ↔
      plan.expected.val = (records.map Query.id : Multiset QueryId) ∧
      ∀ q ∈ records, Runner.RunContract
        (plan.specification q.id).demand (plan.specification q.id).tests q.wire := by
  rw [queriesAccepted, TestPlan.accepts_iff]
  simp only [TestPlan.Satisfied, true_or, true_and,
    TestPlan.identities, queryVerdicts, List.map_map, Function.comp_def]
  constructor
  · rintro ⟨identities, passed⟩
    refine ⟨identities, ?_⟩
    intro q present
    have resolved := passed _ (List.mem_map.mpr ⟨q, present, rfl⟩)
    exact (Runner.exitCode_zero_iff budget _ _ _).mp (of_decide_eq_true resolved)
  · rintro ⟨identities, contracts⟩
    refine ⟨identities, ?_⟩
    intro result present
    obtain ⟨q, queryPresent, same⟩ := List.mem_map.mp present
    cases same
    exact decide_eq_true ((Runner.exitCode_zero_iff budget _ _ _).mpr
      (contracts q queryPresent))

def BodyContract (plan : Plan QueryId TestId)
    (body : List (Event QueryId TestId Answer Fault State))
    (stop : Completion.ProducerStop State Fault) : Prop :=
  Runner.BodyContract .exhaustive none (boundaryEvents body) stop ∧
  plan.expected.val = ((queries body).map Query.id : Multiset QueryId) ∧
  ∀ q ∈ queries body, Runner.RunContract
    (plan.specification q.id).demand (plan.specification q.id).tests q.wire

def bodyExitCode [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (body : List (Event QueryId TestId Answer Fault State))
    (stop : Completion.ProducerStop State Fault) : Nat :=
  let boundary := (Runner.report budget .exhaustive none (boundaryEvents body) stop).exitCode
  let records := queries body
  if boundary = 0 ∧ queriesAccepted budget plan records = true then 0
  else if boundary = 2 ∨ records.any (fun q => queryStatus budget plan q == 2) then 2
  else 1

theorem bodyExitCode_zero_iff [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (body : List (Event QueryId TestId Answer Fault State))
    (stop : Completion.ProducerStop State Fault) :
    bodyExitCode budget plan body stop = 0 ↔ BodyContract plan body stop := by
  have zero : bodyExitCode budget plan body stop = 0 ↔
      (Runner.report budget .exhaustive none (boundaryEvents body) stop).exitCode = 0 ∧
        queriesAccepted budget plan (queries body) = true := by
    dsimp only [bodyExitCode]
    split_ifs <;> simp_all
  rw [zero, Runner.report_zero_iff, queriesAccepted_iff]
  rfl

theorem failed_query_cannot_be_masked [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (body : List (Event QueryId TestId Answer Fault State))
    (stop : Completion.ProducerStop State Fault)
    (q : Query QueryId TestId Answer Fault State) (present : q ∈ queries body)
    (failed : ¬ Runner.RunContract (plan.specification q.id).demand
      (plan.specification q.id).tests q.wire) :
    bodyExitCode budget plan body stop ≠ 0 := by
  intro accepted
  exact failed (((bodyExitCode_zero_iff budget plan body stop).mp accepted).2.2 q present)

/-- Any escaped query fault determines the fault status; no query or diagnostic
identity is preferred and no further fault enumeration is required. -/
theorem query_fault_reports_two [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (body : List (Event QueryId TestId Answer Fault State))
    (stop : Completion.ProducerStop State Fault)
    (q : Query QueryId TestId Answer Fault State) (present : q ∈ queries body)
    (fault : queryStatus budget plan q = 2) :
    bodyExitCode budget plan body stop = 2 := by
  have rejected : ¬ ((Runner.report budget .exhaustive none
      (boundaryEvents body) stop).exitCode = 0 ∧
      queriesAccepted budget plan (queries body) = true) := by
    rintro ⟨_, accepted⟩
    have contract := ((queriesAccepted_iff budget plan (queries body)).mp accepted).2 q present
    have zero : queryStatus budget plan q = 0 :=
      (Runner.exitCode_zero_iff budget _ _ _).mpr contract
    omega
  have found : (queries body).any (fun record => queryStatus budget plan record == 2) = true :=
    List.any_eq_true.mpr ⟨q, present, by simp [fault]⟩
  simp [bodyExitCode, rejected, found]

def exitCode [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (wire : List (Runner.Packet (Event QueryId TestId Answer Fault State)
      (Completion.ProducerStop State Fault))) : Nat :=
  match Runner.decode wire with
  | none => 1
  | some (body, stop) => bodyExitCode budget plan body stop

def Contract (plan : Plan QueryId TestId)
    (wire : List (Runner.Packet (Event QueryId TestId Answer Fault State)
      (Completion.ProducerStop State Fault))) : Prop :=
  ∃ body stop, wire = body.map Runner.Packet.event ++ [.terminal stop] ∧
    BodyContract plan body stop

theorem exitCode_zero_iff [DecidableEq TestId] [DecidableEq QueryId]
    (budget : Nat) (plan : Plan QueryId TestId)
    (wire : List (Runner.Packet (Event QueryId TestId Answer Fault State)
      (Completion.ProducerStop State Fault))) :
    exitCode budget plan wire = 0 ↔ Contract plan wire := by
  constructor
  · intro accepted
    cases framed : Runner.decode wire with
    | none => simp [exitCode, framed] at accepted
    | some decoded =>
        obtain ⟨body, stop⟩ := decoded
        refine ⟨body, stop, Runner.decode_sound wire body stop framed, ?_⟩
        exact (bodyExitCode_zero_iff budget plan body stop).mp
          (by simpa [exitCode, framed] using accepted)
  · rintro ⟨body, stop, framed, correct⟩
    rw [framed]
    simpa only [exitCode, Runner.decode_encode] using
      (bodyExitCode_zero_iff budget plan body stop).mpr correct

namespace Controls

abbrev Q := Query Nat Nat Nat String Unit
abbrev E := Event Nat Nat Nat String Unit
abbrev W := Runner.Packet E (Completion.ProducerStop Unit String)

def two : Plan Nat Nat := ⟨{1, 2}, fun _ => ⟨.prefix 1, none⟩⟩
def noneDeclared : Plan Nat Nat := ⟨∅, fun _ => ⟨.exhaustive, none⟩⟩

def query (id : Nat) (answers : List Nat) : Q :=
  ⟨id, (answers.map (fun a => Runner.Event.activity (.answer a)) ++
    ([.activity .outputComplete, .activity .cleanupComplete] :
      List (Runner.Event Nat Nat String))).map Runner.Packet.event ++
    [.terminal .demandSatisfied]⟩

def close (body : List E) : List W :=
  (body ++ ([.resource .outputComplete, .resource .cleanupComplete] : List E)).map
    Runner.Packet.event ++
    [.terminal (.observed .complete)]

theorem each_query_completed : exitCode 0 two
    (close [.query (query 1 [7]), .query (query 2 [8])]) = 0 := by decide

/-- Two answers in query 2 cannot satisfy query 1's missing answer. -/
theorem answers_cannot_mask_another_query : exitCode 0 two
    (close [.query (query 1 []), .query (query 2 [8, 9])]) = 1 := by decide

theorem matching_count_does_not_hide_duplicate_identity : exitCode 0 two
    (close [.query (query 1 [7]), .query (query 1 [8])]) = 1 := by decide

theorem missing_query_fails : exitCode 0 two
    (close [.query (query 1 [7])]) = 1 := by decide

theorem extra_query_fails : exitCode 0 two
    (close [.query (query 1 [7]), .query (query 2 [8]), .query (query 3 [9])]) = 1 := by decide

theorem empty_ordinary_document_succeeds : exitCode 0 noneDeclared (close []) = 0 := by decide

theorem missing_document_terminal_fails : exitCode 0 noneDeclared ([] : List W) = 1 := by decide

theorem duplicate_document_terminal_fails : exitCode 0 noneDeclared
    (close [] ++ [.terminal (.observed .complete)]) = 1 := by decide

theorem record_after_terminal_fails : exitCode 0 noneDeclared
    (close [] ++ [.event (.unhandled "late")]) = 1 := by decide

theorem zero_detail_budget_cannot_hide_fault : exitCode 0 noneDeclared
    (close [.unhandled "boom"]) = 2 := by decide

theorem document_output_failure_survives_query_success : exitCode 0 two
    (close [.query (query 1 [7]), .query (query 2 [8]), .resource .outputFailed]) = 1 := by decide

theorem document_cleanup_failure_survives_query_success : exitCode 0 two
    (close [.query (query 1 [7]), .query (query 2 [8]), .resource .cleanupFailed]) = 1 := by decide

end Controls

end Mettapedia.Machines.RunContracts.Document
