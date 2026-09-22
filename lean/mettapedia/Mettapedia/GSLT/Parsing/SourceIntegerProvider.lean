import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Std.Data.String.ToInt

/-!
# Selected integer-provider expressions on canonical source syntax

The expression carrier is the existing `SExpr` used by authored GSLT sources.
This module supplies no program representation, rule search, Horn interpretation,
or target runtime. A read-only integer environment closes source `?name`
variables. Integer atoms retain canonical decimal spelling; quote closes its
payload without evaluating it; the exact source `(metta-nullary empty)` denotes
completed absence of answers. Conditional evaluation visits only its chosen
branch.

Independent inductive judgments specify integer arithmetic, comparisons and
ordered answer lists. The executable functions are proved equivalent to those
judgments. `none` is unsupported or ill-typed syntax, not completed emptiness.

The selected clauses follow the ground integer/quotation/lazy-conditional
fragment audited in SWI-PeTTa at commit
`ae66fa8e41dcd5539d614706bd4e5cfb34f9608d`: `translator.pl` integer/atomic leaves,
left-to-right arguments, three-argument `if` (173-185), quotation (320), and
`metta.pl` `+`, `<`, `>=`, `empty` (34, 39, 48, 108). This is the source-encoded
typed fragment, not full PeTTa evaluation: arbitrary Boolean guards, exceptions,
mutable definitions, caller unification and finite-width C arithmetic remain
separate boundaries. No source-to-C refinement is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceIntegerProvider

open Algorithms.MeTTa.Simple.Parser (SExpr)

abbrev Env := List (String × Int)

def sourceVariableToken (token : String) : Bool :=
  token.startsWith "?" && token != "?" && token != "?_"

/-- First-binding lookup. Repeated names do not silently change that policy. -/
def lookup? : Env → String → Option Int
  | [], _ => none
  | (name, value) :: rest, token =>
      if token = name then some value else lookup? rest token

@[simp] theorem lookup?_head (env : Env) (name : String) (value : Int) :
    lookup? ((name, value) :: env) name = some value := by simp [lookup?]

theorem lookup?_tail (env : Env) (name token : String) (value : Int)
    (different : token ≠ name) :
    lookup? ((name, value) :: env) token = lookup? env token := by
  simp [lookup?, different]

/-- Integer admission is exact, including spelling. Floats, quoted numerals,
leading zeros and explicit positive signs are not integer atoms of this wire. -/
def integerValue? (token : String) : Option Int := do
  let value ← token.toInt?
  if toString value = token then some value else none

@[simp] theorem integerValue?_repr (value : Int) :
    integerValue? (toString value) = some value := by
  simp [integerValue?, Int.toInt?_repr]

theorem integerValue?_iff (token : String) (value : Int) :
    integerValue? token = some value ↔ token = toString value := by
  constructor
  · intro accepted
    cases parsed : token.toInt? with
    | none => simp [integerValue?, parsed] at accepted
    | some actual =>
      have conditions : toString actual = token ∧ actual = value := by
        simpa [integerValue?, parsed] using accepted
      simpa [conditions.2] using conditions.1.symm
  · rintro rfl
    exact integerValue?_repr value

mutual
  /-- Structural substitution in source syntax, including quoted payloads.
  Ordinary atoms and atom/list distinctions are retained exactly. -/
  def closeTerm? (env : Env) : SExpr → Option SExpr
    | .atom token =>
        if sourceVariableToken token then
          (lookup? env token).map fun value => .atom (toString value)
        else some (.atom token)
    | .list terms => (closeTerms? env terms).map SExpr.list
  termination_by term => sizeOf term

  def closeTerms? (env : Env) : List SExpr → Option (List SExpr)
    | [] => some []
    | term :: rest => do
        let first ← closeTerm? env term
        let tail ← closeTerms? env rest
        return first :: tail
  termination_by terms => sizeOf terms
end

theorem closeTerm?_variable (env : Env) (token : String) (value : Int)
    (isVariable : sourceVariableToken token = true)
    (bound : lookup? env token = some value) :
    closeTerm? env (.atom token) = some (.atom (toString value)) := by
  simp [closeTerm?, isVariable, bound]

theorem closeTerm?_atom (env : Env) (token : String)
    (ordinary : sourceVariableToken token = false) :
    closeTerm? env (.atom token) = some (.atom token) := by
  simp [closeTerm?, ordinary]

def evalInteger? (env : Env) : SExpr → Option Int
  | .atom token =>
      if sourceVariableToken token then lookup? env token else integerValue? token
  | .list [.atom "+", left, right] => do
      let first ← evalInteger? env left
      let second ← evalInteger? env right
      return first + second
  | _ => none
termination_by expression => sizeOf expression

theorem evalInteger?_variable (env : Env) (token : String) (value : Int)
    (isVariable : sourceVariableToken token = true)
    (bound : lookup? env token = some value) :
    evalInteger? env (.atom token) = some value := by
  simp [evalInteger?, isVariable, bound]

inductive IntegerEval (env : Env) : SExpr → Int → Prop where
  | integer {token : String} {value : Int}
      (ordinary : sourceVariableToken token = false)
      (spelling : token = toString value) :
      IntegerEval env (.atom token) value
  | sourceVar {token : String} {value : Int}
      (isVariable : sourceVariableToken token = true)
      (bound : lookup? env token = some value) :
      IntegerEval env (.atom token) value
  | add {left right : SExpr} {first second : Int}
      (leftValue : IntegerEval env left first)
      (rightValue : IntegerEval env right second) :
      IntegerEval env (.list [.atom "+", left, right]) (first + second)

theorem evalInteger?_sound (env : Env) (expression : SExpr) (value : Int)
    (evaluated : evalInteger? env expression = some value) :
    IntegerEval env expression value := by
  unfold evalInteger? at evaluated
  split at evaluated
  · rename_i token
    cases isVariable : sourceVariableToken token with
    | false =>
      exact .integer isVariable ((integerValue?_iff token value).mp
        (by simpa [isVariable] using evaluated))
    | true => exact .sourceVar isVariable (by simpa [isVariable] using evaluated)
  · rename_i left right
    cases firstEval : evalInteger? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
      cases secondEval : evalInteger? env right with
      | none => simp [firstEval, secondEval] at evaluated
      | some second =>
        have same : first + second = value := by simpa [firstEval, secondEval] using evaluated
        subst value
        exact .add (evalInteger?_sound env left first firstEval)
          (evalInteger?_sound env right second secondEval)
  · simp at evaluated
termination_by sizeOf expression

theorem evalInteger?_complete {env : Env} {expression : SExpr} {value : Int}
    (evaluated : IntegerEval env expression value) :
    evalInteger? env expression = some value := by
  induction evaluated with
  | integer ordinary spelling =>
    simp [evalInteger?, ordinary, (integerValue?_iff _ _).mpr spelling]
  | sourceVar isVariable bound => simp [evalInteger?, isVariable, bound]
  | add _ _ first second => simp [evalInteger?, first, second]

theorem evalInteger?_iff (env : Env) (expression : SExpr) (value : Int) :
    evalInteger? env expression = some value ↔ IntegerEval env expression value :=
  ⟨evalInteger?_sound env expression value, evalInteger?_complete⟩

def evalBoolean? (env : Env) : SExpr → Option Bool
  | .list [.atom "<", left, right] => do
      let first ← evalInteger? env left
      let second ← evalInteger? env right
      return decide (first < second)
  | .list [.atom ">=", left, right] => do
      let first ← evalInteger? env left
      let second ← evalInteger? env right
      return decide (first ≥ second)
  | _ => none

inductive BooleanEval (env : Env) : SExpr → Bool → Prop where
  | less {left right : SExpr} {first second : Int}
      (leftValue : IntegerEval env left first)
      (rightValue : IntegerEval env right second) :
      BooleanEval env (.list [.atom "<", left, right]) (decide (first < second))
  | notLess {left right : SExpr} {first second : Int}
      (leftValue : IntegerEval env left first)
      (rightValue : IntegerEval env right second) :
      BooleanEval env (.list [.atom ">=", left, right]) (decide (first ≥ second))

theorem evalBoolean?_sound (env : Env) (expression : SExpr) (value : Bool)
    (evaluated : evalBoolean? env expression = some value) :
    BooleanEval env expression value := by
  unfold evalBoolean? at evaluated
  split at evaluated
  · rename_i left right
    cases firstEval : evalInteger? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
      cases secondEval : evalInteger? env right with
      | none => simp [firstEval, secondEval] at evaluated
      | some second =>
        have same : decide (first < second) = value := by
          simpa [firstEval, secondEval] using evaluated
        subst value
        exact .less (evalInteger?_sound env left first firstEval)
          (evalInteger?_sound env right second secondEval)
  · rename_i left right
    cases firstEval : evalInteger? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
      cases secondEval : evalInteger? env right with
      | none => simp [firstEval, secondEval] at evaluated
      | some second =>
        have same : decide (first ≥ second) = value := by
          simpa [firstEval, secondEval] using evaluated
        subst value
        exact .notLess (evalInteger?_sound env left first firstEval)
          (evalInteger?_sound env right second secondEval)
  · simp at evaluated

theorem evalBoolean?_complete {env : Env} {expression : SExpr} {value : Bool}
    (evaluated : BooleanEval env expression value) :
    evalBoolean? env expression = some value := by
  cases evaluated with
  | less first second | notLess first second =>
    simp [evalBoolean?, evalInteger?_complete first, evalInteger?_complete second]

theorem evalBoolean?_iff (env : Env) (expression : SExpr) (value : Bool) :
    evalBoolean? env expression = some value ↔ BooleanEval env expression value :=
  ⟨evalBoolean?_sound env expression value, evalBoolean?_complete⟩

def evalAnswers? (env : Env) : SExpr → Option (List SExpr)
  | .list [.atom "quote", payload] => (closeTerm? env payload).map fun value => [value]
  | .list [.atom "metta-nullary", .atom "empty"] => some []
  | .list [.atom "if", guard, yes, no] => do
      let condition ← evalBoolean? env guard
      if condition then evalAnswers? env yes else evalAnswers? env no
  | _ => none
termination_by expression => sizeOf expression

inductive AnswersEval (env : Env) : SExpr → List SExpr → Prop where
  | quote {payload value : SExpr} (closed : closeTerm? env payload = some value) :
      AnswersEval env (.list [.atom "quote", payload]) [value]
  | empty : AnswersEval env (.list [.atom "metta-nullary", .atom "empty"]) []
  | ifTrue {guard yes no : SExpr} {answers : List SExpr}
      (condition : BooleanEval env guard true) (branch : AnswersEval env yes answers) :
      AnswersEval env (.list [.atom "if", guard, yes, no]) answers
  | ifFalse {guard yes no : SExpr} {answers : List SExpr}
      (condition : BooleanEval env guard false) (branch : AnswersEval env no answers) :
      AnswersEval env (.list [.atom "if", guard, yes, no]) answers

theorem evalAnswers?_sound (env : Env) (expression : SExpr) (answers : List SExpr)
    (evaluated : evalAnswers? env expression = some answers) :
    AnswersEval env expression answers := by
  unfold evalAnswers? at evaluated
  split at evaluated
  · rename_i payload
    cases closed : closeTerm? env payload with
    | none => simp [closed] at evaluated
    | some value =>
      have same : [value] = answers := by simpa [closed] using evaluated
      subst answers
      exact .quote closed
  · cases evaluated
    exact .empty
  · rename_i guard yes no
    cases condition : evalBoolean? env guard with
    | none => simp [condition] at evaluated
    | some result =>
      cases result with
      | false =>
        exact .ifFalse (evalBoolean?_sound env guard false condition)
          (evalAnswers?_sound env no answers (by simpa [condition] using evaluated))
      | true =>
        exact .ifTrue (evalBoolean?_sound env guard true condition)
          (evalAnswers?_sound env yes answers (by simpa [condition] using evaluated))
  · simp at evaluated
termination_by sizeOf expression

theorem evalAnswers?_complete {env : Env} {expression : SExpr} {answers : List SExpr}
    (evaluated : AnswersEval env expression answers) :
    evalAnswers? env expression = some answers := by
  induction evaluated with
  | quote closed => simp [evalAnswers?, closed]
  | empty => simp [evalAnswers?]
  | ifTrue condition _ branch => simp [evalAnswers?, evalBoolean?_complete condition, branch]
  | ifFalse condition _ branch => simp [evalAnswers?, evalBoolean?_complete condition, branch]

theorem evalAnswers?_iff (env : Env) (expression : SExpr) (answers : List SExpr) :
    evalAnswers? env expression = some answers ↔ AnswersEval env expression answers :=
  ⟨evalAnswers?_sound env expression answers, evalAnswers?_complete⟩

theorem AnswersEval.at_most_one {env : Env} {expression : SExpr} {answers : List SExpr}
    (evaluated : AnswersEval env expression answers) : answers.length ≤ 1 := by
  induction evaluated <;> simp_all

theorem evalAnswers?_at_most_one {env : Env} {expression : SExpr} {answers : List SExpr}
    (evaluated : evalAnswers? env expression = some answers) : answers.length ≤ 1 :=
  (evalAnswers?_sound env expression answers evaluated).at_most_one

theorem AnswersEval.deterministic {env : Env} {expression : SExpr} {first second : List SExpr}
    (left : AnswersEval env expression first) (right : AnswersEval env expression second) :
    first = second :=
  Option.some.inj ((evalAnswers?_complete left).symm.trans (evalAnswers?_complete right))

theorem quote_iff (env : Env) (payload : SExpr) (answers : List SExpr) :
    AnswersEval env (.list [.atom "quote", payload]) answers ↔
      ∃ value, closeTerm? env payload = some value ∧ answers = [value] := by
  rw [← evalAnswers?_iff]
  simp [evalAnswers?, Option.map_eq_some_iff]
  aesop

theorem unsupported_not_completed {env : Env} {expression : SExpr}
    (unsupported : evalAnswers? env expression = none) (answers : List SExpr) :
    ¬ AnswersEval env expression answers := by
  intro completed
  have computed := evalAnswers?_complete completed
  simp [unsupported] at computed

/-! ## Executable boundary controls -/

private theorem repr_seven : Int.repr 7 = "7" := by
  rw [Int.repr_eq_if]
  decide

@[simp] theorem integerValue?_one : integerValue? "1" = some 1 := by
  have spelling : toString (1 : Int) = "1" := by
    rw [Int.toString_eq_repr, Int.repr_eq_if]
    decide
  simpa only [spelling] using integerValue?_repr 1

@[simp] theorem integerValue?_two : integerValue? "2" = some 2 := by
  have spelling : toString (2 : Int) = "2" := by
    rw [Int.toString_eq_repr, Int.repr_eq_if]
    decide
  simpa only [spelling] using integerValue?_repr 2

private theorem decimal_point_not_integer : "1.0".toInt? = none := by
  have notNat : "1.0".isNat = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have character := (String.isNat_iff.mp accepted).2.1 '.' (by decide)
    simp [Char.isDigit] at character
  rw [String.toInt?_eq_toNat?_of_startsWith_eq_false (by decide),
    String.toNat?_eq_none notNat]
  rfl

private theorem integer_float_refused : integerValue? "1.0" = none := by
  simp [integerValue?, decimal_point_not_integer]

example : evalInteger? [("?x", 7), ("?x", 99)] (.atom "?x") = some 7 := by
  simp [evalInteger?, sourceVariableToken, lookup?]

example : evalInteger? [] (.atom "1.0") = none := by
  simp [evalInteger?, sourceVariableToken, integer_float_refused]

example : integerValue? "+1" = none := by
  have notNat : "+1".isNat = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have character := (String.isNat_iff.mp accepted).2.1 '+' (by decide)
    simp [Char.isDigit] at character
  have refused : "+1".toInt? = none := by
    rw [String.toInt?_eq_toNat?_of_startsWith_eq_false (by decide),
      String.toNat?_eq_none notNat]
    rfl
  simp [integerValue?, refused]

example : evalAnswers? [] (.atom "empty") = none ∧
    evalAnswers? [] (.list [.atom "empty"]) = none ∧
    evalAnswers? [] (.list [.atom "metta-nullary", .atom "empty"]) = some [] := by
  simp [evalAnswers?]

example : evalAnswers? [("?x", 7)]
    (.list [.atom "quote", .list [.atom "+", .atom "?x", .atom "1"]]) =
      some [.list [.atom "+", .atom "7", .atom "1"]] := by
  simp [evalAnswers?, closeTerm?, closeTerms?, sourceVariableToken, lookup?, repr_seven]

example : evalAnswers? [] (.list [.atom "quote", .atom "?missing"]) = none := by
  simp [evalAnswers?, closeTerm?, sourceVariableToken, lookup?]

example : evalAnswers? []
    (.list [.atom "if", .list [.atom "<", .atom "1", .atom "2"],
      .list [.atom "quote", .atom "yes"], .atom "unsupported"])
    = some [.atom "yes"] := by
  simp [evalAnswers?, evalBoolean?, evalInteger?, closeTerm?, sourceVariableToken,
    integerValue?_one, integerValue?_two]

example : evalAnswers? []
    (.list [.atom "if", .list [.atom "<", .atom "2", .atom "1"],
      .list [.atom "quote", .atom "yes"], .atom "unsupported"]) = none := by
  simp [evalAnswers?, evalBoolean?, evalInteger?, closeTerm?, sourceVariableToken,
    integerValue?_one, integerValue?_two]

example : evalAnswers? []
    (.list [.atom "if", .list [.atom "<", .atom "1.0", .atom "2"],
      .list [.atom "quote", .atom "yes"],
      .list [.atom "metta-nullary", .atom "empty"]]) = none := by
  simp [evalAnswers?, evalBoolean?, evalInteger?, sourceVariableToken, integer_float_refused]

theorem no_duplicate_answer_completion (env : Env) (expression value : SExpr) :
    ¬ AnswersEval env expression [value, value] := by
  intro completed
  have bound := completed.at_most_one
  simp at bound

#print axioms evalInteger?_iff
#print axioms evalBoolean?_iff
#print axioms evalAnswers?_iff
#print axioms no_duplicate_answer_completion

end Mettapedia.GSLT.Parsing.SourceIntegerProvider
