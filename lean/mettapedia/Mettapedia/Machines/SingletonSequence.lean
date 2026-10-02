import Mathlib.Data.List.Basic

/-!
# Eliminating one-child sequential wrappers

The source interpreter gathers a sequence's child values in source order,
threading each branch's state and preserving escaped faults. The compiled
one-child case executes that child directly. Both `progn` and `prog1` select
the only child, so the ordered replies, multiplicities, state and faults agree.
State may include an effect trace and the branch's bindings. This is a control
component law, not a C refinement theorem or a physical cost claim. Empty and
multiple-child sequences are deliberately outside the elimination rule.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SingletonSequence

inductive Reply (Value State Fault : Type) where
  | value (value : Value) (state : State)
  | fault (error : Fault) (state : State)
  deriving DecidableEq, Repr

variable {Op Value State Fault : Type}

def collect (execute : Op → State → List (Reply Value State Fault)) :
    List Op → State → List (Reply (List Value) State Fault)
  | [], state => [.value [] state]
  | op :: rest, state =>
      (execute op state).flatMap fun
        | .fault error next => [.fault error next]
        | .value value next =>
            (collect execute rest next).map fun
              | .fault error final => .fault error final
              | .value values final => .value (value :: values) final

def observeFirst : Reply (List Value) State Fault → List (Reply Value State Fault)
  | .fault error state => [.fault error state]
  | .value [] _ => []
  | .value (value :: _) state => [.value value state]

def observeLast : Reply (List Value) State Fault → List (Reply Value State Fault)
  | .fault error state => [.fault error state]
  | .value values state =>
      match values.getLast? with
      | none => []
      | some value => [.value value state]

theorem first_singleton (execute : Op → State → List (Reply Value State Fault))
    (op : Op) (state : State) :
    (collect execute [op] state).flatMap observeFirst = execute op state := by
  simp only [collect, List.map_cons, List.map_nil]
  rw [List.flatMap_assoc]
  have each : ∀ reply : Reply Value State Fault,
      (match reply with
        | .fault error next => [Reply.fault error next]
        | .value value next => [Reply.value [value] next]).flatMap observeFirst =
      [reply] := by
    intro reply
    cases reply <;> rfl
  simp only [each, List.flatMap_singleton']

theorem last_singleton (execute : Op → State → List (Reply Value State Fault))
    (op : Op) (state : State) :
    (collect execute [op] state).flatMap observeLast = execute op state := by
  simp only [collect, List.map_cons, List.map_nil]
  rw [List.flatMap_assoc]
  have each : ∀ reply : Reply Value State Fault,
      (match reply with
        | .fault error next => [Reply.fault error next]
        | .value value next => [Reply.value [value] next]).flatMap observeLast =
      [reply] := by
    intro reply
    cases reply <;> rfl
  simp only [each, List.flatMap_singleton']

private def choices (_ : Unit) (trace : List Nat) : List (Reply Nat (List Nat) String) :=
  [.value 2 (trace ++ [2]), .value 2 (trace ++ [2]), .fault "raised" (trace ++ [9])]

example : (collect choices [()] [1]).flatMap observeLast =
    [.value 2 [1, 2], .value 2 [1, 2], .fault "raised" [1, 9]] := by
  rw [last_singleton]
  rfl

example : (collect choices [] []).flatMap observeLast ≠ choices () [] := by
  decide

example : (collect choices [(), ()] []).flatMap observeLast ≠ choices () [] := by
  decide

#print axioms first_singleton
#print axioms last_singleton

end Mettapedia.Machines.SingletonSequence
