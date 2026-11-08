import Mettapedia.Machines.ReadOnlyQueryDemand

/-!
# Demand-preserving expansion of read services

A high-level read may itself be a finite adaptive query of lower-level
observations. Expansion substitutes that query at the actual read position.
An unfinished service aborts the query there, distinctly from a completed
negative reply. Unread services are never executed or included in the
certificate.

The independent high-level partial interpreter is `demand`. Its replies are
the completed results of the lower-level services. Expansion has the same
answer, and its lower-level certificate is exactly the concatenation of the
service certificates selected by that high-level execution, in order.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQueryExpansion

open ReadOnlyQuery ReadOnlyQueryDemand

variable {Key Reply PrimitiveKey PrimitiveReply Answer : Type}

def expand (service : Key → Program PrimitiveKey PrimitiveReply (Option Reply)) :
    Program Key Reply Answer → Program PrimitiveKey PrimitiveReply (Option Answer)
  | .pure answer => .pure (some answer)
  | .read key next => bind (service key) fun
      | none => .pure none
      | some reply => expand service (next reply)

def replies (store : PrimitiveKey → PrimitiveReply)
    (service : Key → Program PrimitiveKey PrimitiveReply (Option Reply)) : Key → Option Reply :=
  fun key => (run store (service key)).answer

def flatten (store : PrimitiveKey → PrimitiveReply)
    (service : Key → Program PrimitiveKey PrimitiveReply (Option Reply))
    (reads : ReadOnlyQuery.Reads Key (Option Reply)) : ReadOnlyQuery.Reads PrimitiveKey PrimitiveReply :=
  reads.flatMap fun read => (run store (service read.1)).reads

theorem expansion_answer (store : PrimitiveKey → PrimitiveReply)
    (service : Key → Program PrimitiveKey PrimitiveReply (Option Reply))
    (program : Program Key Reply Answer) :
    (run store (expand service program)).answer =
      (run (replies store service) (demand program)).answer := by
  induction program with
  | pure answer => rfl
  | read key next ih =>
      simp only [expand, run_bind, demand, run, replies]
      cases result : (run store (service key)).answer with
      | none => rfl
      | some reply => exact ih reply

theorem expansion_reads (store : PrimitiveKey → PrimitiveReply)
    (service : Key → Program PrimitiveKey PrimitiveReply (Option Reply))
    (program : Program Key Reply Answer) :
    (run store (expand service program)).reads =
      flatten store service (run (replies store service) (demand program)).reads := by
  induction program with
  | pure answer => rfl
  | read key next ih =>
      simp only [expand, run_bind, demand, run, replies]
      cases result : (run store (service key)).answer with
      | none => simp [flatten, run]
      | some reply =>
          simpa only [flatten, List.flatMap_cons] using
            (congrArg (fun tail => (run store (service key)).reads ++ tail) (ih reply))

/-- Validating the expanded primitive certificate is sufficient. No
high-level inference result is retained as an unexplained atomic read. -/
theorem expanded_replay (before after : PrimitiveKey → PrimitiveReply)
    (service : Key → Program PrimitiveKey PrimitiveReply (Option Reply))
    (program : Program Key Reply Answer)
    (agrees : Agrees after (run before (expand service program)).reads) :
    run after (expand service program) = run before (expand service program) :=
  run_eq_of_agrees before after (expand service program) agrees

theorem successful_demand_reads_some (available : Key → Option Reply)
    (program : Program Key Reply Answer)
    (success : (run available (demand program)).answer ≠ none) :
    ∀ read ∈ (run available (demand program)).reads, ∃ reply, read.2 = some reply := by
  induction program with
  | pure answer => intro read member; cases member
  | read key next ih =>
      cases found : available key with
      | none => simp [demand, run, found] at success
      | some reply =>
          have later : (run available (demand (next reply))).answer ≠ none := by
            simpa [demand, run, found] using success
          intro read member
          simp only [demand, run, found, List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨reply, rfl⟩
          · exact ih reply later read member

namespace Controls

def child : Nat → Program Nat Bool (Option Bool)
  | 0 => .read 10 fun value => .pure (some value)
  | _ => .read 20 fun _ => .pure none

def branch : Program Nat Bool Nat :=
  .read 0 fun take => if take then .pure 7 else .read 1 fun _ => .pure 8

theorem held_branch_never_requests_unfinished_child :
    (run (fun _ => true) (expand child branch)).answer = some 7 ∧
    (run (fun _ => true) (expand child branch)).reads = [(10, true)] := by cbv

theorem demanded_unfinished_child_stops_with_its_reads :
    (run (fun _ => false) (expand child branch)).answer = none ∧
    (run (fun _ => false) (expand child branch)).reads = [(10, false), (20, false)] := by cbv

theorem completed_false_is_not_unfinished :
    (run (fun _ => false) (expand child (.read 0 fun answer => .pure answer))).answer = some false := by cbv

end Controls

end Mettapedia.Machines.ReadOnlyQueryExpansion
