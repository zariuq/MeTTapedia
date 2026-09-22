import Mettapedia.GSLT.Parsing.GeneratedPeTTaEquationDispatch
import Mettapedia.GSLT.Parsing.GeneratedPeTTaTemplateInstantiation
import Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundCondition

/-!
# Completed execution of selected ground generated PeTTa bodies

This proof model reads the actual equation S-expressions. It covers finite,
pure, ground calls with static data arguments, atoms, quote, empty, lazy conditions,
nonempty literal-list superpose, finite semideterministic once, and inert-constructor
result-binding let. Calls receive fresh local bindings; ordered equation
and answer occurrences are not deduplicated. A depth bound limits the proof
model's execution and is never interpreted as a completed empty answer list.

The explicit data-head inventory determines which authored argument forms
are constructors, not calls. Values substituted for variables stay opaque.
This is not a production evaluator, all of PeTTa, or a model of once over
infinite/effectful generators. In particular, finite let is factored as full
value generation followed by compatible binding; operational equivalence to
constraint-first scheduling requires the selected pure complete-call laws.
In particular, literal `(superpose (collapse CALL))` branches over the atom
`collapse` and CALL; it does not materialize and redistribute CALL's answers.
The once case only qualifies a fully completed inner computation with at most
one answer occurrence. Larger lists are outside this profile: result constraints
can select a later answer before PeTTa commits. Unknown tail outcomes are not a
model of early success followed by divergence/effects.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaEquationDispatch
open GeneratedPeTTaTemplateInstantiation (instantiate? instantiateList?)
open GeneratedPeTTaResultBinding (bindAnswers)

inductive Outcome where
  | complete (answers : List SExpr)
  | exhausted
  | outsideFragment
  deriving DecidableEq, Repr

/-- All branches must complete before their complete ordered answer list is
returned. A missing completion does not erase a branch or invent failure. -/
def collect {α : Type} (run : α → Outcome) : List α → Outcome
  | [] => .complete []
  | first :: rest =>
      match run first with
      | .exhausted => .exhausted
      | .outsideFragment => .outsideFragment
      | .complete answers =>
          match collect run rest with
          | .complete following => .complete (answers ++ following)
          | .exhausted => .exhausted
          | .outsideFragment => .outsideFragment

@[simp] theorem collect_nil {α : Type} (run : α → Outcome) :
    collect run [] = .complete [] := rfl

@[simp] theorem collect_singleton {α : Type} (run : α → Outcome) (value : α) :
    collect run [value] = run value := by
  cases result : run value <;> simp [collect, result]

theorem collect_map_complete {α : Type} (values : List α) (run : α → List SExpr) :
    collect (fun value => .complete (run value)) values =
      .complete (values.flatMap run) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [collect, ih]

mutual
  /-- This inspects authored templates only, before substituting payloads. -/
  def dataTemplate (dataHeads : List String) : SExpr → Bool
    | .atom _ => true
    | .list (.atom head :: arguments) =>
        dataHeads.contains head && dataTemplates dataHeads arguments
    | _ => false

  def dataTemplates (dataHeads : List String) : List SExpr → Bool
    | [] => true
    | first :: rest => dataTemplate dataHeads first && dataTemplates dataHeads rest
end

/-- The supported forms cannot be reclassified as ordinary function calls. -/
def reserved (head : String) : Bool :=
  ["quote", "empty", "let", "if", "once", "collapse", "superpose", "+", "<", ">=", "=="].contains head

def knownFunction (program : List (Nat × SExpr)) (head : String) : Bool :=
  !(equationsFor head program).isEmpty

/-- Partial applications have their own PeTTa behavior and are not completed
failed calls. This selected model admits only an authored full arity. -/
def hasArity (program : List (Nat × SExpr)) (head : String) (arity : Nat) : Bool :=
  (equationsFor head program).any fun row =>
    match equation? row.2 with
    | some (.list (_ :: arguments), _) => arguments.length == arity
    | _ => false

mutual
  /-- Generated result patterns must be inert data. In particular, PeTTa can
interpret quoted or callable patterns, which plain result matching does not
model. Such patterns are outside this selected execution profile. -/
  def inertBinder (program : List (Nat × SExpr)) (dataHeads : List String) : SExpr → Bool
    | .atom _ => true
    | .list (.atom head :: arguments) =>
        !reserved head && !knownFunction program head && dataHeads.contains head &&
          inertBinders program dataHeads arguments
    | _ => false

  def inertBinders (program : List (Nat × SExpr)) (dataHeads : List String) : List SExpr → Bool
    | [] => true
    | first :: rest => first != .atom "$_" && inertBinder program dataHeads first &&
        inertBinders program dataHeads rest
end

/-- `call` is already ground data, not a template to be instantiated again.
Each matching equation starts with its own empty local environment. -/
def runWith (body : Bindings → SExpr → Outcome)
    (program : List (Nat × SExpr)) (call : SExpr) : Outcome :=
  match call with
  | .list (.atom head :: arguments) =>
      if reserved head || !knownFunction program head || !hasArity program head arguments.length
      then .outsideFragment
      else collect (fun matched =>
        match equation? matched.1.2 with
        | some (_, expression) => body matched.2 expression
        | none => .outsideFragment) (dispatch [] call program)
  | _ => .outsideFragment

def eval : Nat → List (Nat × SExpr) → List String → Bindings → SExpr → Outcome
  | 0, _, _, _, _ => .exhausted
  | depth + 1, program, dataHeads, env, expression =>
      match expression with
      | .list [.atom "quote", payload] =>
          match instantiate? env payload with
          | some value => .complete [value]
          | none => .outsideFragment
      | .list [.atom "empty"] => .complete []
      | .list [.atom "superpose", .list (first :: rest)] =>
          collect (eval depth program dataHeads env) (first :: rest)
      | .list [.atom "once", inner] =>
          match eval depth program dataHeads env inner with
          | .complete answers =>
              if answers.length ≤ 1 then .complete (answers.take 1) else .outsideFragment
          | .exhausted => .exhausted
          | .outsideFragment => .outsideFragment
      | .list [.atom "if", condition, yes, no] =>
          match GeneratedPeTTaGroundCondition.condition? env condition with
          | some true => eval depth program dataHeads env yes
          | some false => eval depth program dataHeads env no
          | none => .outsideFragment
      | .list [.atom "let", schema, value, continuation] =>
          if !inertBinder program dataHeads schema then .outsideFragment
          else match eval depth program dataHeads env value with
          | .complete answers =>
              collect (fun next => eval depth program dataHeads next continuation)
                (bindAnswers env schema answers)
          | .exhausted => .exhausted
          | .outsideFragment => .outsideFragment
      | .list (.atom head :: templates) =>
          if reserved head || !dataTemplates dataHeads templates then .outsideFragment
          else match instantiateList? env templates with
          | some arguments => runWith (eval depth program dataHeads) program
              (.list (.atom head :: arguments))
          | none => .outsideFragment
      | .atom token =>
          match instantiate? env (.atom token) with
          | some value => .complete [value]
          | none => .outsideFragment
      | _ => .outsideFragment

def run (depth : Nat) (program : List (Nat × SExpr)) (dataHeads : List String)
    (call : SExpr) : Outcome :=
  runWith (eval depth program dataHeads) program call

theorem quote_exact (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (payload value : SExpr)
    (closed : instantiate? env payload = some value) :
    eval (depth + 1) program dataHeads env (.list [.atom "quote", payload]) =
      .complete [value] := by simp [eval, closed]

theorem empty_exact (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) :
    eval (depth + 1) program dataHeads env (.list [.atom "empty"]) =
      .complete [] := by rfl

theorem atom_exact (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (token : String) (value : SExpr)
    (closed : instantiate? env (.atom token) = some value) :
    eval (depth + 1) program dataHeads env (.atom token) = .complete [value] := by
  simp [eval, closed]

/-- Source-literal superpose evaluates each authored alternative, not the
alternative list as a function application. Empty/dynamic lists and their
translation policies are outside this selected case. -/
theorem literal_superpose (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (first : SExpr) (rest : List SExpr) :
    eval (depth + 1) program dataHeads env
      (.list [.atom "superpose", .list (first :: rest)]) =
      collect (eval depth program dataHeads env) (first :: rest) := rfl

theorem once_complete (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (inner : SExpr) (answers : List SExpr)
    (semidet : answers.length ≤ 1)
    (completed : eval depth program dataHeads env inner = .complete answers) :
    eval (depth + 1) program dataHeads env (.list [.atom "once", inner]) =
      .complete (answers.take 1) := by simp [eval, completed, semidet]

theorem once_multiple_outside (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (inner : SExpr) (answers : List SExpr)
    (multiple : 1 < answers.length)
    (completed : eval depth program dataHeads env inner = .complete answers) :
    eval (depth + 1) program dataHeads env (.list [.atom "once", inner]) =
      .outsideFragment := by simp [eval, completed, Nat.not_le.mpr multiple]

/-- A finite two-answer call is deliberately not certified through once:
PeTTa can constrain its output before choosing the first compatible answer. -/
theorem constrained_multiple_once_outside :
    eval 4 [] [] []
      (.list [.atom "let", .atom "second",
        .list [.atom "once", .list [.atom "superpose",
          .list [.atom "first", .atom "second"]]],
        .list [.atom "quote", .atom "ok"]]) = .outsideFragment := by
  simp [eval, inertBinder, collect, GeneratedPeTTaTemplateInstantiation.instantiate_atom,
    GeneratedPeTTaResultBinding.variableToken]

/-- Equal values still occupy two answer positions, so they do not license
the selected semideterministic once case. -/
theorem duplicated_value_once_outside :
    eval 3 [] [] []
      (.list [.atom "once", .list [.atom "superpose",
        .list [.atom "same", .atom "same"]]]) = .outsideFragment := by
  simp [eval, collect, GeneratedPeTTaTemplateInstantiation.instantiate_atom,
    GeneratedPeTTaResultBinding.variableToken]

/-- These parentheses actually request collapse as a branch operation,
unlike the generated literal wrapper. Real collection is not modeled here. -/
theorem actual_collection_outside :
    eval 3 [] [] []
      (.list [.atom "superpose", .list [
        .list [.atom "collapse", .list [.atom "quote", .atom "answer"]]]]) =
      .outsideFragment := by
  simp [eval, collect, reserved]

theorem once_exhaustion_is_not_empty (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (inner : SExpr) :
    eval 1 program dataHeads env (.list [.atom "once", inner]) = .exhausted := rfl

theorem depth_exhaustion_is_not_failure (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (expression : SExpr) :
    eval 0 program dataHeads env expression ≠ .complete [] := by simp [eval]

theorem conditional_true (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (condition yes no : SExpr)
    (selected : GeneratedPeTTaGroundCondition.condition? env condition = some true) :
    eval (depth + 1) program dataHeads env (.list [.atom "if", condition, yes, no]) =
      eval depth program dataHeads env yes := by simp [eval, selected]

theorem conditional_false (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (condition yes no : SExpr)
    (selected : GeneratedPeTTaGroundCondition.condition? env condition = some false) :
    eval (depth + 1) program dataHeads env (.list [.atom "if", condition, yes, no]) =
      eval depth program dataHeads env no := by simp [eval, selected]

/-- The selected provider branches execute, including genuine completed
absence of answers. No provider result is supplied as a target hook. -/
theorem conditional_quote_empty (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (condition payload value : SExpr)
    (truth : Bool)
    (selected : GeneratedPeTTaGroundCondition.condition? env condition = some truth)
    (closed : instantiate? env payload = some value) :
    eval (depth + 2) program dataHeads env
      (.list [.atom "if", condition, .list [.atom "quote", payload], .list [.atom "empty"]]) =
      .complete (if truth then [value] else []) := by
  cases truth <;> simp [eval, selected, closed]

theorem let_complete (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (schema value continuation : SExpr)
    (answers : List SExpr)
    (inert : inertBinder program dataHeads schema = true)
    (completed : eval depth program dataHeads env value = .complete answers) :
    eval (depth + 1) program dataHeads env (.list [.atom "let", schema, value, continuation]) =
      collect (fun next => eval depth program dataHeads next continuation)
        (bindAnswers env schema answers) := by simp [eval, inert, completed]

/-- Quoted patterns require PeTTa's pattern interpretation; they must not be
misreported as a completed mismatch by this inert-pattern model. -/
theorem quoted_binder_outside (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (pattern value continuation : SExpr) :
    eval (depth + 1) program dataHeads env
      (.list [.atom "let", .list [.atom "quote", pattern], value, continuation]) =
      .outsideFragment := by
  simp [eval, inertBinder, reserved]

/-- The existing binding service implements the ignored binder at the root,
not as a recursively interpreted anonymous variable. -/
theorem nested_ignored_binder_outside (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (env : Bindings) (head : String) (value continuation : SExpr) :
    eval (depth + 1) program dataHeads env
      (.list [.atom "let", .list [.atom head, .atom "$_"], value, continuation]) =
      .outsideFragment := by
  simp [eval, inertBinder, inertBinders]

theorem call_single_match (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (head : String) (arguments : List SExpr)
    (row : Nat × SExpr) (localEnv : Bindings) (lhs body : SExpr)
    (ordinary : reserved head = false) (known : knownFunction program head = true)
    (arity : hasArity program head arguments.length = true)
    (matched : dispatch [] (.list (.atom head :: arguments)) program = [(row, localEnv)])
    (equation : equation? row.2 = some (lhs, body)) :
    run depth program dataHeads (.list (.atom head :: arguments)) =
      eval depth program dataHeads localEnv body := by
  simp [run, runWith, ordinary, known, arity, matched, equation]

theorem unsupported_arity_outside (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (head : String) (arguments : List SExpr)
    (unsupported : hasArity program head arguments.length = false) :
    run depth program dataHeads (.list (.atom head :: arguments)) = .outsideFragment := by
  simp [run, runWith, unsupported]

theorem unknown_not_completed_empty (depth : Nat) (program : List (Nat × SExpr))
    (dataHeads : List String) (head : String) (arguments : List SExpr)
    (unknown : knownFunction program head = false) :
    run depth program dataHeads (.list (.atom head :: arguments)) ≠ .complete [] := by
  simp [run, runWith, unknown]

end Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundExecution
