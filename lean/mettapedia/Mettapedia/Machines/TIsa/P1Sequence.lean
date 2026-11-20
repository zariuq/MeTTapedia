import Mettapedia.Machines.TIsa.P1WordExecution

/-! # Sequential association and the empty statement in p1 -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.P1Sequence

open P1Source (Stmt)
open P1WordExecution (State Flow execute)
def runBefore (commands : List Stmt) (tail : Stmt) : Stmt :=
  commands.foldr Stmt.seq tail

def statements : Stmt → List Stmt
  | .skip => []
  | .seq first rest => statements first ++ statements rest
  | .instruction value => [.instruction value]
  | .branch condition yes no => [.branch condition yes no]
  | .counted index bound cap body => [.counted index bound cap body]
  | .early index bound continuation cap body => [.early index bound continuation cap body]
  | .ret outcome source => [.ret outcome source]
  | .fund units => [.fund units]

theorem execute_append (first rest : List Stmt) (state : State) :
    execute state (runBefore (first ++ rest) .skip) =
      (execute state (runBefore first .skip)).thenContinue (fun active => execute active (runBefore rest .skip)) := by
  induction first generalizing state with
  | nil => rfl
  | cons current later ih =>
    change (execute state current).thenContinue (fun active => execute active (runBefore (later ++ rest) .skip)) =
      ((execute state current).thenContinue (fun active => execute active (runBefore later .skip))).thenContinue
        (fun active => execute active (runBefore rest .skip))
    cases execute state current with
    | continuing active => exact ih active
    | returned status word active => rfl

private theorem empty_continuation (flow : Flow) :
    flow.thenContinue .continuing = flow := by cases flow <;> rfl

theorem execute_statements (statement : Stmt) (state : State) :
    execute state statement = execute state (runBefore (statements statement) .skip) := by
  induction statement generalizing state
  case skip => rfl
  case seq first rest firstIH restIH =>
    rw [statements, execute_append, ← firstIH]
    change (execute state first).thenContinue (execute · rest) =
      (execute state first).thenContinue (fun active => execute active (runBefore (statements rest) .skip))
    congr
    funext active
    exact restIH active
  all_goals
    rw [statements]
    exact (empty_continuation _).symm

theorem execute_prefix {whole first : Stmt} (rest : List Stmt)
    (partition : statements whole = statements first ++ rest) (state : State) :
    execute state whole =
      (execute state first).thenContinue (fun active => execute active (runBefore rest .skip)) := by
  rw [execute_statements whole, partition, execute_append, ← execute_statements first]

end Mettapedia.Machines.TIsa.P1Sequence
