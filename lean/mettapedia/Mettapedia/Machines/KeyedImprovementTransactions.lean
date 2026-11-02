import Mettapedia.Machines.KeyedImprovement

/-!
# Validated publication of a prepared keyed improvement

Preparation may use a captured value, but publication validates that value
against the live key. Refusal is a retry, not a negative improvement answer.
An exact fallback recomputes the decision against the live store. This is an
atomic logical publication operation, not a proof of a native compare/exchange
or of an arbitrary remove/add spelling under intermediate observers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.Transactions

variable {Key Value : Type} [DecidableEq Key] [LinearOrder Value]

structure Ticket (Key Value : Type) where
  key : Key
  candidate : Value
  observed : Option Value

def prepare (store : Store Key Value) (key : Key) (candidate : Value) : Ticket Key Value :=
  ⟨key, candidate, store key⟩

def branch (observed : Option Value) (candidate : Value) : Bool :=
  match observed with
  | none => true
  | some old => decide (candidate < old)

def executePlan (store : Store Key Value) (key : Key) (candidate : Value) (replace : Bool) : Store Key Value × Bool :=
  if replace then (Function.update store key (some candidate), true) else (store, false)

theorem planned_branch_exact (store : Store Key Value) (key : Key) (candidate : Value) :
    executePlan store key candidate (branch (store key) candidate) = improve store key candidate := by
  cases held : store key with
  | none => simp [executePlan, branch, improve, held]
  | some old => by_cases better : candidate < old <;> simp [executePlan, branch, improve, held, better]

def tryCommit (store : Store Key Value) (ticket : Ticket Key Value) : Option (Store Key Value × Bool) :=
  if store ticket.key = ticket.observed then
    some (executePlan store ticket.key ticket.candidate (branch ticket.observed ticket.candidate))
  else none

theorem accepted_exact (store : Store Key Value) (ticket : Ticket Key Value)
    (result : Store Key Value × Bool) (accepted : tryCommit store ticket = some result) :
    result = improve store ticket.key ticket.candidate := by
  by_cases current : store ticket.key = ticket.observed
  · unfold tryCommit at accepted
    rw [if_pos current, ← current, planned_branch_exact] at accepted
    exact (Option.some.inj accepted).symm
  · simp [tryCommit, current] at accepted

theorem stale_retries (store : Store Key Value) (ticket : Ticket Key Value)
    (changed : store ticket.key ≠ ticket.observed) : tryCommit store ticket = none := by
  simp [tryCommit, changed]

def afterAttempt (store : Store Key Value) (ticket : Ticket Key Value) : Store Key Value :=
  ((tryCommit store ticket).map Prod.fst).getD store

theorem refused_keeps_store (store : Store Key Value) (ticket : Ticket Key Value)
    (refused : tryCommit store ticket = none) : afterAttempt store ticket = store := by simp [afterAttempt, refused]

def commitOrRefresh (store : Store Key Value) (ticket : Ticket Key Value) : Store Key Value × Bool :=
  (tryCommit store ticket).getD (improve store ticket.key ticket.candidate)

theorem refresh_exact (store : Store Key Value) (ticket : Ticket Key Value) :
    commitOrRefresh store ticket = improve store ticket.key ticket.candidate := by
  cases result : tryCommit store ticket with
  | none => simp [commitOrRefresh, result]
  | some value => simpa [commitOrRefresh, result] using accepted_exact store ticket value result

theorem unrelated_write_does_not_force_retry (store : Store Key Value) (key other : Key)
    (candidate replacement : Value) (apart : key ≠ other) :
    (tryCommit (Function.update store other (some replacement)) (prepare store key candidate)).isSome = true := by
  simp [tryCommit, prepare, apart]

namespace Controls

def start : Store Unit Nat := fun _ => some 10
def seven : Ticket Unit Nat := prepare start () 7
def five : Ticket Unit Nat := prepare start () 5

theorem stale_improvement_is_retry_not_false :
    (tryCommit (improve start () 5).1 seven).isNone = true ∧
      (commitOrRefresh (improve start () 5).1 seven).2 = false ∧
      (commitOrRefresh (improve start () 5).1 seven).1 () = some 5 := by decide

theorem stale_better_candidate_refreshes_successfully :
    (tryCommit (improve start () 7).1 five).isNone = true ∧
      (commitOrRefresh (improve start () 7).1 five).2 = true ∧
      (commitOrRefresh (improve start () 7).1 five).1 () = some 5 := by decide

end Controls

end Mettapedia.Machines.KeyedImprovement.Transactions
