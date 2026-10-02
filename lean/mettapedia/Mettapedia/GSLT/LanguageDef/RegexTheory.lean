import Mettapedia.GSLT.LanguageDef.RegexDerivatives
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Authored regex derivative theory

The finite rewrite presentation implements structural nullability,
Brzozowski derivatives and whole-word matching. Ordered congruence premises
request the recursive computations. The relation environment supplies only
equality and inequality on the native string scalar carrier.

This is a raw constructor presentation, not a textual regex parser. Its
alphabet consists of `String` values; a character interpretation can use
singleton strings without enumerating Unicode or encoding letters as variables.

The theory declares the seven core constructors of regular expressions and
no equations, and its derivative rules do not simplify their results. A
request is a term of the sort of its result. Optionality, repetition and
ranges are elaborated into the core constructors before encoding; search and
replacement are not declared.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexTheory

open Mettapedia.Computability.RegularLanguages
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Match

/-- A scalar uses the existing native string representation. -/
def scalar (value : String) : Pattern := .apply value []

def boolean : Bool → Pattern
  | false => .apply "rx:false" []
  | true => .apply "rx:true" []

def encode : Regex String → Pattern
  | .zero => .apply "rx:zero" []
  | .epsilon => .apply "rx:epsilon" []
  | .char (.literal a) => .apply "rx:literal" [scalar a]
  | .char .any => .apply "rx:any" []
  | .plus p q => .apply "rx:union" [encode p, encode q]
  | .comp p q => .apply "rx:concat" [encode p, encode q]
  | .star p => .apply "rx:star" [encode p]

def word : List String → Pattern
  | [] => .apply "rx:nil" []
  | a :: rest => .apply "rx:cons" [scalar a, word rest]

/-- Decode only the constructor image; native scalar strings remain data. -/
def decode : Pattern → Option (Regex String)
  | .apply "rx:zero" [] => some 0
  | .apply "rx:epsilon" [] => some 1
  | .apply "rx:literal" [.apply a []] => some (literal a)
  | .apply "rx:any" [] => some any
  | .apply "rx:union" [p, q] => do return (← decode p) + (← decode q)
  | .apply "rx:concat" [p, q] => do return (← decode p) * (← decode q)
  | .apply "rx:star" [p] => do return (← decode p).star
  | _ => none
termination_by input => sizeOf input
decreasing_by all_goals sizeOf_pattern_dec

def decodeWord : Pattern → Option (List String)
  | .apply "rx:nil" [] => some []
  | .apply "rx:cons" [.apply a [], rest] => (decodeWord rest).map (a :: ·)
  | _ => none
termination_by input => sizeOf input
decreasing_by all_goals sizeOf_pattern_dec

@[simp] theorem decode_encode (p : Regex String) : decode (encode p) = some p := by
  induction p with
  | zero => simp [encode, decode]
  | epsilon => simp [encode, decode]
  | char atom => cases atom <;> simp [encode, decode, scalar, literal, any]
  | plus p q hp hq => simp [encode, decode, hp, hq]
  | comp p q hp hq => simp [encode, decode, hp, hq]
  | star p hp => simp [encode, decode, hp]

@[simp] theorem decodeWord_word (input : List String) : decodeWord (word input) = some input := by
  induction input with
  | nil => simp [word, decodeWord]
  | cons a rest ih => simp [word, decodeWord, scalar, ih]

theorem encode_injective : Function.Injective encode := by
  intro p q h
  have decoded := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem word_injective : Function.Injective word := by
  intro p q h
  have decoded := congrArg decodeWord h
  simpa only [decodeWord_word, Option.some.injEq] using decoded

theorem boolean_injective : Function.Injective boolean := by
  intro left right h
  cases left <;> cases right <;> simp_all [boolean]

def nullable (p : Pattern) : Pattern := .apply "rx:nullable" [p]
def derivative (a p : Pattern) : Pattern := .apply "rx:derivative" [a, p]
def matchRequest (p input : Pattern) : Pattern := .apply "rx:match" [p, input]
def disjoin (left right : Pattern) : Pattern := .apply "rx:or" [left, right]
def conjoin (left right : Pattern) : Pattern := .apply "rx:and" [left, right]

private def grammar (label category : String) (parameters : List (String × String)) :
    GrammarRule where
  label := label
  category := category
  params := parameters.map fun parameter => .simple parameter.1 (.base parameter.2)
  syntaxPattern := .terminal label :: parameters.map fun parameter => .nonTerminal parameter.1

def terms : List GrammarRule := [
  grammar "rx:zero" "Regex" [],
  grammar "rx:epsilon" "Regex" [],
  grammar "rx:literal" "Regex" [("a", "Scalar")],
  grammar "rx:any" "Regex" [],
  grammar "rx:union" "Regex" [("p", "Regex"), ("q", "Regex")],
  grammar "rx:concat" "Regex" [("p", "Regex"), ("q", "Regex")],
  grammar "rx:star" "Regex" [("p", "Regex")],
  grammar "rx:false" "Bool" [],
  grammar "rx:true" "Bool" [],
  grammar "rx:nil" "Word" [],
  grammar "rx:cons" "Word" [("a", "Scalar"), ("rest", "Word")],
  grammar "rx:nullable" "Bool" [("p", "Regex")],
  grammar "rx:derivative" "Regex" [("a", "Scalar"), ("p", "Regex")],
  grammar "rx:match" "Bool" [("p", "Regex"), ("input", "Word")],
  grammar "rx:or" "Bool" [("left", "Bool"), ("right", "Bool")],
  grammar "rx:and" "Bool" [("left", "Bool"), ("right", "Bool")]
]

/-- An authored rule schema; exposing its fields supports semantic correspondence proofs. -/
def rewriteSchema (name : String) (parameters : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule where
  name := name
  typeContext := parameters.map fun parameter => (parameter.1, .base parameter.2)
  premises := premises
  left := left
  right := right

/-- A named capture in an authored rule schema. -/
def capture (name : String) : Pattern := .fvar name
/-- A constructor application in the authored syntax. -/
def constructor (label : String) (arguments : List Pattern) : Pattern := .apply label arguments

def orFF := rewriteSchema "OR-FF" [] [] (disjoin (boolean false) (boolean false)) (boolean false)
def orFT := rewriteSchema "OR-FT" [] [] (disjoin (boolean false) (boolean true)) (boolean true)
def orTF := rewriteSchema "OR-TF" [] [] (disjoin (boolean true) (boolean false)) (boolean true)
def orTT := rewriteSchema "OR-TT" [] [] (disjoin (boolean true) (boolean true)) (boolean true)
def andFF := rewriteSchema "AND-FF" [] [] (conjoin (boolean false) (boolean false)) (boolean false)
def andFT := rewriteSchema "AND-FT" [] [] (conjoin (boolean false) (boolean true)) (boolean false)
def andTF := rewriteSchema "AND-TF" [] [] (conjoin (boolean true) (boolean false)) (boolean false)
def andTT := rewriteSchema "AND-TT" [] [] (conjoin (boolean true) (boolean true)) (boolean true)

def nullableZero := rewriteSchema "NULL-ZERO" [] [] (nullable (constructor "rx:zero" [])) (boolean false)
def nullableEpsilon := rewriteSchema "NULL-EPSILON" [] [] (nullable (constructor "rx:epsilon" [])) (boolean true)
def nullableLiteral := rewriteSchema "NULL-LITERAL" [("a", "Scalar")] []
  (nullable (constructor "rx:literal" [capture "a"])) (boolean false)
def nullableAny := rewriteSchema "NULL-ANY" [] [] (nullable (constructor "rx:any" [])) (boolean false)
def nullableUnion := rewriteSchema "NULL-UNION"
  [("p", "Regex"), ("q", "Regex"), ("left", "Bool"), ("right", "Bool"), ("result", "Bool")]
  [.congruence (nullable (capture "p")) (capture "left"),
    .congruence (nullable (capture "q")) (capture "right"),
    .congruence (disjoin (capture "left") (capture "right")) (capture "result")]
  (nullable (constructor "rx:union" [capture "p", capture "q"])) (capture "result")
def nullableConcat := rewriteSchema "NULL-CONCAT"
  [("p", "Regex"), ("q", "Regex"), ("left", "Bool"), ("right", "Bool"), ("result", "Bool")]
  [.congruence (nullable (capture "p")) (capture "left"),
    .congruence (nullable (capture "q")) (capture "right"),
    .congruence (conjoin (capture "left") (capture "right")) (capture "result")]
  (nullable (constructor "rx:concat" [capture "p", capture "q"])) (capture "result")
def nullableStar := rewriteSchema "NULL-STAR" [("p", "Regex")] []
  (nullable (constructor "rx:star" [capture "p"])) (boolean true)

def derivativeZero := rewriteSchema "DERIV-ZERO" [("a", "Scalar")] []
  (derivative (capture "a") (constructor "rx:zero" [])) (constructor "rx:zero" [])
def derivativeEpsilon := rewriteSchema "DERIV-EPSILON" [("a", "Scalar")] []
  (derivative (capture "a") (constructor "rx:epsilon" [])) (constructor "rx:zero" [])
def derivativeLiteralEq := rewriteSchema "DERIV-LITERAL-EQ" [("a", "Scalar"), ("expected", "Scalar")]
  [.relationQuery "rx:scalar_eq" [capture "expected", capture "a"]]
  (derivative (capture "a") (constructor "rx:literal" [capture "expected"])) (constructor "rx:epsilon" [])
def derivativeLiteralNe := rewriteSchema "DERIV-LITERAL-NE" [("a", "Scalar"), ("expected", "Scalar")]
  [.relationQuery "rx:scalar_ne" [capture "expected", capture "a"]]
  (derivative (capture "a") (constructor "rx:literal" [capture "expected"])) (constructor "rx:zero" [])
def derivativeAny := rewriteSchema "DERIV-ANY" [("a", "Scalar")] []
  (derivative (capture "a") (constructor "rx:any" [])) (constructor "rx:epsilon" [])
def derivativeUnion := rewriteSchema "DERIV-UNION"
  [("a", "Scalar"), ("p", "Regex"), ("q", "Regex"), ("dp", "Regex"), ("dq", "Regex")]
  [.congruence (derivative (capture "a") (capture "p")) (capture "dp"),
    .congruence (derivative (capture "a") (capture "q")) (capture "dq")]
  (derivative (capture "a") (constructor "rx:union" [capture "p", capture "q"])) (constructor "rx:union" [capture "dp", capture "dq"])
def derivativeConcatNullable := rewriteSchema "DERIV-CONCAT-NULLABLE"
  [("a", "Scalar"), ("p", "Regex"), ("q", "Regex"), ("dp", "Regex"), ("dq", "Regex")]
  [.congruence (nullable (capture "p")) (boolean true),
    .congruence (derivative (capture "a") (capture "p")) (capture "dp"),
    .congruence (derivative (capture "a") (capture "q")) (capture "dq")]
  (derivative (capture "a") (constructor "rx:concat" [capture "p", capture "q"]))
  (constructor "rx:union" [constructor "rx:concat" [capture "dp", capture "q"], capture "dq"])
def derivativeConcatNonnullable := rewriteSchema "DERIV-CONCAT-NONNULLABLE"
  [("a", "Scalar"), ("p", "Regex"), ("q", "Regex"), ("dp", "Regex")]
  [.congruence (nullable (capture "p")) (boolean false),
    .congruence (derivative (capture "a") (capture "p")) (capture "dp")]
  (derivative (capture "a") (constructor "rx:concat" [capture "p", capture "q"])) (constructor "rx:concat" [capture "dp", capture "q"])
def derivativeStar := rewriteSchema "DERIV-STAR"
  [("a", "Scalar"), ("p", "Regex"), ("dp", "Regex")]
  [.congruence (derivative (capture "a") (capture "p")) (capture "dp")]
  (derivative (capture "a") (constructor "rx:star" [capture "p"])) (constructor "rx:concat" [capture "dp", constructor "rx:star" [capture "p"]])

def matchNil := rewriteSchema "MATCH-NIL" [("p", "Regex"), ("result", "Bool")]
  [.congruence (nullable (capture "p")) (capture "result")]
  (matchRequest (capture "p") (constructor "rx:nil" [])) (capture "result")
def matchCons := rewriteSchema "MATCH-CONS"
  [("p", "Regex"), ("a", "Scalar"), ("rest", "Word"), ("next", "Regex"), ("result", "Bool")]
  [.congruence (derivative (capture "a") (capture "p")) (capture "next"),
    .congruence (matchRequest (capture "next") (capture "rest")) (capture "result")]
  (matchRequest (capture "p") (constructor "rx:cons" [capture "a", capture "rest"])) (capture "result")

def rewrites : List RewriteRule := [
  orFF, orFT, orTF, orTT, andFF, andFT, andTF, andTT,
  nullableZero, nullableEpsilon, nullableLiteral, nullableAny,
  nullableUnion, nullableConcat, nullableStar,
  derivativeZero, derivativeEpsilon, derivativeLiteralEq, derivativeLiteralNe, derivativeAny,
  derivativeUnion, derivativeConcatNullable, derivativeConcatNonnullable, derivativeStar,
  matchNil, matchCons
]

def theory : LanguageDef where
  name := "RegexDerivatives"
  types := [{ name := "Scalar", carrier := .builtinString }, "Regex", "Word", "Bool"]
  terms := terms
  equations := []
  rewrites := rewrites

/-- Data-only comparison: neither relation receives or evaluates a regex. -/
def scalarRelations : RelationEnv where
  tuples relation arguments :=
    match arguments with
    | [.apply left [], .apply right []] =>
        if relation = "rx:scalar_eq" then if left = right then [arguments] else []
        else if relation = "rx:scalar_ne" then if left ≠ right then [arguments] else []
        else []
    | _ => []

abbrev Step := Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
  (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises scalarRelations) theory

theorem schema_count : theory.rewrites.length = 26 := by decide

theorem scalar_eq_exact (left right : String) :
    scalarRelations.tuples "rx:scalar_eq" [scalar left, scalar right] =
      if left = right then [[scalar left, scalar right]] else [] := by
  simp [scalarRelations, scalar]

theorem scalar_ne_exact (left right : String) :
    scalarRelations.tuples "rx:scalar_ne" [scalar left, scalar right] =
      if left ≠ right then [[scalar left, scalar right]] else [] := by
  simp [scalarRelations, scalar]

theorem rule_depth_aligned {selected : RewriteRule} (member : selected ∈ theory.rewrites) :
    Mettapedia.OSLF.MeTTaIL.Match.ruleDepthAligned selected = true := by
  have all : theory.rewrites.all Mettapedia.OSLF.MeTTaIL.Match.ruleDepthAligned = true := by
    decide
  exact List.all_eq_true.mp all selected member

theorem rule_left_match_correct {selected : RewriteRule} (member : selected ∈ theory.rewrites) :
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect selected.left = true := by
  have all : theory.rewrites.all (fun selected => Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect selected.left) = true := by
    decide
  exact List.all_eq_true.mp all selected member

theorem applyBindingsForRule_plain (selected : RewriteRule)
    (member : selected ∈ theory.rewrites) (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule theory selected bindings =
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings selected.right := by
  exact Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing_empty_eq_applyBindings
    selected bindings (rule_depth_aligned member)


end Mettapedia.GSLT.LanguageDef.RegexTheory
