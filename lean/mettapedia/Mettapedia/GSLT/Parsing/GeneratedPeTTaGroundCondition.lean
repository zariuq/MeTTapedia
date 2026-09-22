import Mettapedia.GSLT.Parsing.GeneratedPeTTaTemplateInstantiation
import Mettapedia.GSLT.Parsing.SourceIntegerProviderNativeType

/-!
# Selected generated PeTTa ground conditions

Only authored integer atoms, addition, integer comparisons and quoted data
equality are interpreted here. Dollar operands use the established template
instantiation boundary. A value supplied through a variable is not revisited
as expression syntax. Mathematical Int is explicit; no fixed-width C
arithmetic, whole PeTTa evaluator or provider-body interpreter is asserted.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundCondition

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaTemplateInstantiation (instantiate?)
open SourceIntegerProvider (integerValue?)

def integer? (env : Bindings) : SExpr → Option Int
  | .atom token => do
      let .atom closed ← instantiate? env (.atom token) | none
      integerValue? closed
  | .list [.atom "+", left, right] => do
      return (← integer? env left) + (← integer? env right)
  | _ => none
termination_by expression => sizeOf expression

inductive IntegerEval (env : Bindings) : SExpr → Int → Prop where
  | atom {token : String} {value : Int}
      (closed : instantiate? env (.atom token) = some (.atom (toString value))) :
      IntegerEval env (.atom token) value
  | add {left right : SExpr} {first second : Int}
      (leftValue : IntegerEval env left first)
      (rightValue : IntegerEval env right second) :
      IntegerEval env (.list [.atom "+", left, right]) (first + second)

theorem integer?_sound (env : Bindings) (expression : SExpr) (value : Int)
    (evaluated : integer? env expression = some value) : IntegerEval env expression value := by
  unfold integer? at evaluated
  split at evaluated
  · rename_i token
    cases closed : instantiate? env (.atom token) with
    | none => simp [closed] at evaluated
    | some result =>
        cases result with
        | list values => simp [closed] at evaluated
        | atom spelling =>
            have accepted : integerValue? spelling = some value := by simpa [closed] using evaluated
            have exactSpelling := (SourceIntegerProvider.integerValue?_iff spelling value).mp accepted
            exact .atom (by simpa [exactSpelling] using closed)
  · rename_i left right
    cases firstEval : integer? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
        cases secondEval : integer? env right with
        | none => simp [firstEval, secondEval] at evaluated
        | some second =>
            have same : first + second = value := by simpa [firstEval, secondEval] using evaluated
            subst value
            exact .add (integer?_sound env left first firstEval)
              (integer?_sound env right second secondEval)
  · simp at evaluated
termination_by sizeOf expression

theorem integer?_complete {env : Bindings} {expression : SExpr} {value : Int}
    (evaluated : IntegerEval env expression value) : integer? env expression = some value := by
  induction evaluated with
  | atom closed =>
      simp only [integer?, closed]
      exact SourceIntegerProvider.integerValue?_repr _
  | add _ _ first second => simp [integer?, first, second]

theorem integer?_iff (env : Bindings) (expression : SExpr) (value : Int) :
    integer? env expression = some value ↔ IntegerEval env expression value :=
  ⟨integer?_sound env expression value, integer?_complete⟩

def condition? (env : Bindings) : SExpr → Option Bool
  | .list [.atom "<", left, right] => do
      return decide ((← integer? env left) < (← integer? env right))
  | .list [.atom ">=", left, right] => do
      return decide ((← integer? env left) ≥ (← integer? env right))
  | .list [.atom "==", .list [.atom "quote", left], .list [.atom "quote", right]] => do
      return decide ((← instantiate? env left) = (← instantiate? env right))
  | _ => none

inductive ConditionEval (env : Bindings) : SExpr → Bool → Prop where
  | less {left right : SExpr} {first second : Int}
      (leftValue : IntegerEval env left first)
      (rightValue : IntegerEval env right second) :
      ConditionEval env (.list [.atom "<", left, right]) (decide (first < second))
  | notLess {left right : SExpr} {first second : Int}
      (leftValue : IntegerEval env left first)
      (rightValue : IntegerEval env right second) :
      ConditionEval env (.list [.atom ">=", left, right]) (decide (first ≥ second))
  | quotedEqual {left right first second : SExpr}
      (leftValue : instantiate? env left = some first)
      (rightValue : instantiate? env right = some second) :
      ConditionEval env
        (.list [.atom "==", .list [.atom "quote", left], .list [.atom "quote", right]])
        (decide (first = second))

theorem condition?_sound (env : Bindings) (expression : SExpr) (value : Bool)
    (evaluated : condition? env expression = some value) : ConditionEval env expression value := by
  unfold condition? at evaluated
  split at evaluated
  · rename_i left right
    cases firstEval : integer? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
        cases secondEval : integer? env right with
        | none => simp [firstEval, secondEval] at evaluated
        | some second =>
            have same : decide (first < second) = value := by simpa [firstEval, secondEval] using evaluated
            subst value
            exact .less (integer?_sound env left first firstEval) (integer?_sound env right second secondEval)
  · rename_i left right
    cases firstEval : integer? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
        cases secondEval : integer? env right with
        | none => simp [firstEval, secondEval] at evaluated
        | some second =>
            have same : decide (first ≥ second) = value := by simpa [firstEval, secondEval] using evaluated
            subst value
            exact .notLess (integer?_sound env left first firstEval) (integer?_sound env right second secondEval)
  · rename_i left right
    cases firstEval : instantiate? env left with
    | none => simp [firstEval] at evaluated
    | some first =>
        cases secondEval : instantiate? env right with
        | none => simp [firstEval, secondEval] at evaluated
        | some second =>
            have same : decide (first = second) = value := by simpa [firstEval, secondEval] using evaluated
            subst value
            exact .quotedEqual firstEval secondEval
  · simp at evaluated

theorem condition?_complete {env : Bindings} {expression : SExpr} {value : Bool}
    (evaluated : ConditionEval env expression value) : condition? env expression = some value := by
  cases evaluated with
  | less first second | notLess first second =>
      simp [condition?, integer?_complete first, integer?_complete second]
  | quotedEqual first second => simp [condition?, first, second]

theorem condition?_iff (env : Bindings) (expression : SExpr) (value : Bool) :
    condition? env expression = some value ↔ ConditionEval env expression value :=
  ⟨condition?_sound env expression value, condition?_complete⟩

end Mettapedia.GSLT.Parsing.GeneratedPeTTaGroundCondition
