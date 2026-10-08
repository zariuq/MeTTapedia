import Mettapedia.Logic.LP.RigidUnification

/-! # Joint protection and orientation controls for the finite-term solver -/

namespace Mettapedia.Logic.LP.RigidUnificationControls

open RigidUnification

abbrev signature : LPSignature :=
  { constants := Bool, vars := Nat, relationSymbols := Unit,
    relationArity := fun _ => 0, functionSymbols := Bool,
    functionArity := fun _ => 1 }

def p (argument : Term signature) : Term signature := .app true (fun _ => argument)
def q (argument : Term signature) : Term signature := .app false (fun _ => argument)

def jointConflict : List (Term signature × Term signature) :=
  [(p (.var 0), p (.var 1)), (q (.var 0), q (.const true))]

-- The captured subject variable stays protected at the second constraint.
/-- info: false -/
#guard_msgs in
#eval (solve (σ := signature) (fun v => v = 1) jointConflict).isSome

-- The same equations are satisfiable when both variables may be bound.
/-- info: true -/
#guard_msgs in
#eval (solve (σ := signature) (fun _ => False) jointConflict).isSome

-- A rigid variable on the left must not prevent the valid opposite binding.
/-- info: some 1 -/
#guard_msgs in
#eval match solve (σ := signature) (fun v => v = 1) [(.var 1, .var 0)] with
  | some substitution => match substitution 0 with
    | .var v => some v
    | _ => none
  | none => none

-- Repeated holes across pairs agree.
/-- info: true -/
#guard_msgs in
#eval (solve (σ := signature) (fun _ => False)
  [(p (.var 0), p (.const true)), (q (.var 0), q (.const true))]).isSome

-- Conflicting captures across pairs are rejected.
/-- info: false -/
#guard_msgs in
#eval (solve (σ := signature) (fun _ => False)
  [(p (.var 0), p (.const true)), (q (.var 0), q (.const false))]).isSome

-- Moving constraints does not remove the protection requirement.
/-- info: false -/
#guard_msgs in
#eval (solve (σ := signature) (fun v => v = 1) jointConflict.reverse).isSome

-- The empty batch succeeds without needing a flexible variable.
/-- info: true -/
#guard_msgs in
#eval (solve (σ := signature) (fun _ => True) []).isSome

-- A variable cannot be equal to a finite term that properly contains it.
/-- info: false -/
#guard_msgs in
#eval (solve (σ := signature) (fun _ => False) [(.var 0, p (.var 0))]).isSome

#print axioms solve_sound
#print axioms solve_complete
#print axioms solve_none_iff
#print axioms solve_mgu

end Mettapedia.Logic.LP.RigidUnificationControls
