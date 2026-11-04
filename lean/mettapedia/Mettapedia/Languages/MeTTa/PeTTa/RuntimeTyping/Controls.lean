import Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping

/-!
# Executable controls for runtime predicate typing

All examples instantiate the same generic theory. They cover constructor
recognition, shared polymorphism, delayed overload choice, ordinary collection,
live membership, held arguments, and route-independent rejection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.Controls

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Label where
  | number (n : Int)
  | text (s : String)
  | nil
  | cons
  deriving DecidableEq

def arity : Label → Nat
  | .cons => 2
  | _ => 0

inductive ValueType where
  | number
  | string
  | list (element : ValueType)
  deriving DecidableEq, Repr

def grammar : Grammar ValueType Label arity where
  productions state label := match label with
    | .number _ => if state == .number then [Fin.elim0] else []
    | .text _ => if state == .string then [Fin.elim0] else []
    | .nil => match state with
        | .list _ => [Fin.elim0]
        | _ => []
    | .cons => match state with
        | .list element => [fun i => if i.val == 0 then element else .list element]
        | _ => []

abbrev Value := Tree Label arity
abbrev Term := OpenTree Nat Label arity

def number (n : Int) : Value := .node (.number n) Fin.elim0
def text (s : String) : Value := .node (.text s) Fin.elim0
def nil : Value := .node .nil Fin.elim0
def cons (head tail : Value) : Value := .node .cons (fun i => if i.val == 0 then head else tail)

theorem recursive_number_list_accepted :
    grammar.accepts (cons (number 2) (cons (number 3) nil)) (.list .number) = true := by decide

theorem recursive_mixed_list_rejected :
    grammar.accepts (cons (number 2) (cons (text "bad") nil)) (.list .number) = false := by decide

theorem recursive_acceptance_has_a_derivation :
    grammar.Derives (.list .number) (cons (number 2) (cons (number 3) nil)) :=
  (grammar.accepts_iff_derives _ _).1 recursive_number_list_accepted

def openList (head : Term) : Term :=
  .node .cons (fun i => if i.val == 0 then head else .var 0)

theorem bad_head_rejected_before_tail_is_bound :
    Formula.compile grammar (openList (.node (.text "bad") Fin.elim0)) (.list .number) = .no := by
  decide

theorem good_head_transfers_the_tail_requirement :
    Formula.compile grammar (openList (.node (.number 2) Fin.elim0)) (.list .number) =
      .atom 0 (.list .number) := by decide

def jointOverload : Formula Nat ValueType := .either (.atom 0 .number) (.atom 0 .string)

theorem open_overload_accepts_a_later_string :
    (jointOverload.obligation (fun (_ : Unit) => grammar)).check () nil
      (fun _ => some (text "ok")) = true := by decide

theorem open_number_rejects_a_later_string :
    ((Formula.atom 0 ValueType.number).obligation (fun (_ : Unit) => grammar)).check () nil
      (fun _ => some (text "bad")) = false := by decide

theorem wrong_binding_fails_while_another_argument_remains_open :
    Formula.transferPending grammar
      (fun x : Nat => if x == 0 then OpenTree.node (.text "bad") Fin.elim0 else .var x)
      [Formula.both (.atom 0 ValueType.number) (.atom 1 ValueType.number)] = none := by decide

def typeArity : Empty → Nat := Empty.elim

def construct (c : Empty) : (Fin (typeArity c) → ValueType) → ValueType := nomatch c

def sameInputType : Signature Unit ValueType Empty typeArity 2 where
  argument _ := .parameter ()
  result := .closed .number

def instances : List (Unit → ValueType) := [fun _ => .number, fun _ => .string]

theorem shared_type_variable_rejects_mixed_arguments :
    Overloads.check (fun (_ : Unit) q v => grammar.accepts v q) construct instances [sameInputType]
      () (fun i => if i.val == 0 then number 1 else text "a") (number 7) = false := by decide

theorem shared_type_variable_accepts_different_numbers :
    Overloads.check (fun (_ : Unit) q v => grammar.accepts v q) construct instances [sameInputType]
      () (fun i => if i.val == 0 then number 1 else number 2) (number 7) = true := by decide

/-- The executable open-scheme compiler is checked against the same signature
judgment, not a second typing relation chosen for this example. -/
theorem compiled_shared_type_variable_rejects_mixed_arguments :
    (OpenContract.compile grammar construct instances [sameInputType]
      (fun i => .var i.val) (.node (.number 7) Fin.elim0)).evaluate
      (fun x q => grammar.accepts (if x == 0 then number 1 else text "a") q) = false := by
  rw [OpenContract.compile_correct]
  exact shared_type_variable_rejects_mixed_arguments

/-- An infinite universe of type names does not require enumerating all type
assignments. The result occurrence rules out the first input-only witness. -/
def observedMember (q : Nat) (value : Bool) : Bool :=
  if value then q == 7 || q == 11 else q == 11

def observedTypes : Bool → List Nat
  | true => [7, 11]
  | false => [11]

theorem joint_witness_from_an_infinite_type_universe :
    (WitnessSolver.solve observedMember observedTypes 0
      [(TypeExpr.parameter (), true), (TypeExpr.parameter (), false)]).map
        (fun assignment => assignment ()) = some 11 := by decide

theorem a_ground_answer_exports_no_hidden_constraints :
    Obligation.project
      [jointOverload.obligation (fun (_ : Unit) => grammar)] [] = [] :=
  Obligation.no_roots_no_residuals _

def newlyDeclared (world : Bool) (_ : String) : Bool := world

theorem declaration_added_in_body_is_visible_at_return :
    Boundary.call (Fault := String) (Effect := String)
      ⟨fun (_ : Bool) (_ : Unit) => true, fun world _ out => newlyDeclared world out⟩
      (fun _ _ => .answer ("new-sym", true) .done) false () =
      .answer ("new-sym", true) .done :=
  live_result_membership newlyDeclared false true "new-sym" rfl

theorem failed_output_check_does_not_hide_a_body_fault :
    Trace.filter (fun (_ : Nat) => false)
      (.effect "before" (.fault "zero_divisor") : Trace Nat String String) =
      .effect "before" (.fault "zero_divisor") := rfl

def isNumber : Atom → Bool
  | .grounded (.int _) => true
  | _ => false

def identityRuntime : Runtime Unit String String where
  modes _ f _ := if f.name == "hold" then .hold else .evaluate
  evaluate world term := match term with
    | .expression _ => .fault "zero_divisor"
    | _ => .answer (term, world) .done
  contract _ f := if f.name == "hold" then none else
    some (.ofPredicate ⟨fun _ args => args.all isNumber, fun _ _ out => isNumber out⟩)
  worker _ _ world args := match args with
    | [value] => .answer (value, world) .done
    | _ => .done
  wrongArity _ _ := "wrong arity"

def numericIdentity : FunctionKey := ⟨"num-id", 1⟩
def heldIdentity : FunctionKey := ⟨"hold", 1⟩
def badArgument : Argument := .syntax (.grounded (.string "bad"))
def divisionByZero : Atom :=
  .expression [.symbol "/", .grounded (.int 1), .grounded (.int 0)]

theorem direct_number_call_rejects_string :
    (identityRuntime.run (fun _ _ => none) () (.direct numericIdentity [badArgument])).answers = [] := by
  decide

theorem indirect_number_call_rejects_string :
    (identityRuntime.run (fun _ _ => some (.inl numericIdentity)) () (.indirect "f" [badArgument])).answers = [] := by
  decide

theorem direct_Atom_call_holds_its_argument :
    (identityRuntime.run (fun _ _ => none) ()
      (.direct heldIdentity [.syntax divisionByZero])).answers = [(divisionByZero, ())] := by
  decide

theorem indirect_Atom_call_holds_its_argument :
    (identityRuntime.run (fun _ _ => some (.inl heldIdentity)) ()
      (.indirect "f" [.syntax divisionByZero])).answers = [(divisionByZero, ())] := by
  decide

theorem completed_partial_call_holds_its_argument :
    (identityRuntime.run (fun _ _ => none) ()
      (.partialApply heldIdentity [] [.syntax divisionByZero])).answers = [(divisionByZero, ())] := by
  decide

theorem ordinary_evaluated_argument_keeps_its_fault :
    (identityRuntime.run (fun _ _ => none) ()
      (.direct numericIdentity [.syntax divisionByZero])).terminalFault = some "zero_divisor" := by
  decide

theorem nonfunction_head_returns_data :
    (identityRuntime.run (fun _ _ => some (.inr (.symbol "datum"))) ()
      (.indirect "f" [.value (.grounded (.int 42))])).answers =
      [(.expression [.symbol "datum", .grounded (.int 42)], ())] := by decide

theorem unbound_head_returns_data :
    (identityRuntime.run (fun _ _ => none) ()
      (.indirect "f" [.value (.grounded (.int 42))])).answers =
      [(.expression [.var "f", .grounded (.int 42)], ())] := by decide

def lateHeadRuntime : Runtime Bool String String where
  modes _ _ _ := .evaluate
  evaluate _ term := .effect "argument" (.answer (term, true) .done)
  contract _ _ := none
  worker _ _ world args := match args with
    | [value] => .answer (value, world) .done
    | _ => .done
  wrongArity _ _ := "wrong arity"

def lateHeadEnvironment (bound : Bool) : HeadEnvironment :=
  fun _ => if bound then some (.inl numericIdentity) else none

theorem a_head_bound_during_argument_evaluation_is_called :
    (lateHeadRuntime.run lateHeadEnvironment false
      (.indirect "f" [.syntax (.grounded (.int 42))])).answers =
      [(.grounded (.int 42), true)] := by decide

theorem binding_the_head_does_not_repeat_argument_effects :
    (lateHeadRuntime.run lateHeadEnvironment false
      (.indirect "f" [.syntax (.grounded (.int 42))])).effects = ["argument"] := by decide

theorem duplicated_evidence_does_not_repeat_body_effects :
    (Boundary.call (W := Unit) (Input := Unit) (Output := Nat) (Fault := String)
      ⟨fun _ _ => true || true, fun _ _ _ => true || true⟩
      (fun _ _ => Trace.effect "body" (.answer (7, ()) .done)) () ()).effects = ["body"] := rfl

end Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.Controls
