import Mettapedia.Languages.Chaitin.Reader
import Mettapedia.Languages.Chaitin.Expressions

/-!
# Chaitin's 1997 M-expression frontend

This is the source-file reader `word2`/`word`/`get` in Chaitin's `lisp.m`.
Unlike binary `read-exp`, it expands fixed-arity M-expressions and nested bracket
comments. A double quote switches one expression to literal S-expression mode;
an apostrophe is the unary Lisp quote operator, whose argument is still read in
M-expression mode. Top-level `define` commands install unevaluated definitions.
-/

namespace Mettapedia.Languages.Chaitin.Frontend

open Reader (Token)
open Expressions

inductive Mode where
  | mExpression
  | sExpression
deriving DecidableEq, Repr

inductive Frame where
  | list (mode : Mode) (reversedValues : List SExpr)
  | arguments (head : SExpr) (remaining : Nat) (reversedArguments : List SExpr)
deriving Repr

structure State where
  mode : Mode := .mExpression
  frames : List Frame := []
deriving Repr

inductive Progress where
  | waiting (state : State)
  | complete (expression : SExpr)
deriving Repr

/-- Arity is a source-reading convention, not an evaluator restriction. -/
def arity : SExpr → Option Nat
  | .symbol name =>
      if name = "read-bit" ∨ name = "read-exp" then some 0
      else if name = "car" ∨ name = "cdr" ∨ name = "atom" ∨ name = "'" ∨
          name = "display" ∨ name = "eval" ∨ name = "bits" ∨ name = "debug" ∨
          name = "length" ∨ name = "size" ∨ name = "base2-to-10" ∨
          name = "base10-to-2" ∨ name = "cadr" ∨ name = "caddr" then some 1
      else if name = "cons" ∨ name = "=" ∨ name = "lambda" ∨ name = "append" ∨
          name = "define" ∨ name = "+" ∨ name = "-" ∨ name = "*" ∨ name = "^" ∨
          name = "<" ∨ name = ">" ∨ name = "<=" ∨ name = ">=" then some 2
      else if name = "if" ∨ name = "let" ∨ name = "try" then some 3
      else none
  | _ => none

/-- The `let` expansion retains dynamic binding and recursive function names. -/
def expandLet (name definition body : SExpr) : SExpr :=
  let actualName := if name.atom then name else name.car
  let actualDefinition := if name.atom then definition
    else quote (.list [.symbol "lambda", name.cdr, definition])
  .list [quote (.list [.symbol "lambda", .list [actualName], body]), actualDefinition]

def elaborate (head : SExpr) (arguments : List SExpr) : SExpr :=
  if head = .symbol "cadr" then
    .list [.symbol "car", .list [.symbol "cdr", arguments.headD SExpr.nil]]
  else if head = .symbol "caddr" then
    .list [.symbol "car", .list [.symbol "cdr",
      .list [.symbol "cdr", arguments.headD SExpr.nil]]]
  else if head = .symbol "let" then
    expandLet (arguments.headD SExpr.nil) (arguments.tail.headD SExpr.nil)
      (arguments.tail.tail.headD SExpr.nil)
  else .list (head :: arguments)

def deliver (expression : SExpr) : List Frame → Progress
  | [] => .complete expression
  | .list mode reversedValues :: rest =>
      .waiting { mode := mode, frames := .list mode (expression :: reversedValues) :: rest }
  | .arguments head 0 reversedArguments :: rest =>
      deliver (elaborate head (reversedArguments.reverse ++ [expression])) rest
  | .arguments head (remaining + 1) reversedArguments :: rest =>
      .waiting { frames := .arguments head remaining (expression :: reversedArguments) :: rest }

def receive (state : State) : Token → Progress
  | .leftParen =>
      .waiting { state with frames := .list state.mode [] :: state.frames }
  | .rightParen =>
      match state.frames with
      | .list _ reversedValues :: rest => deliver (.list reversedValues.reverse) rest
      | _ => deliver SExpr.nil state.frames
  | .atom value =>
      match state.mode with
      | .sExpression => deliver value state.frames
      | .mExpression =>
          if value = .symbol "\"" then
            .waiting { state with mode := .sExpression }
          else
            match arity value with
            | none => deliver value state.frames
            | some 0 => deliver (.list [value]) state.frames
            | some (remaining + 1) =>
                .waiting { frames := .arguments value remaining [] :: state.frames }

/-- Failure means the source ended while a required expression was missing. -/
def parseTokensAux : State → List Token → Option (SExpr × List Token)
  | _, [] => none
  | state, token :: rest =>
      match receive state token with
      | .waiting next => parseTokensAux next rest
      | .complete expression => some (expression, rest)

def parseTokens (tokens : List Token) : Option (SExpr × List Token) :=
  parseTokensAux {} tokens

def tokenizeAux : List Char → List Char → List Token → List Token
  | [], reversedWord, reversedTokens => (Reader.flushWord reversedWord reversedTokens).reverse
  | character :: rest, reversedWord, reversedTokens =>
      if character = ' ' then
        tokenizeAux rest [] (Reader.flushWord reversedWord reversedTokens)
      else if character = '(' then
        tokenizeAux rest [] (.leftParen :: Reader.flushWord reversedWord reversedTokens)
      else if character = ')' then
        tokenizeAux rest [] (.rightParen :: Reader.flushWord reversedWord reversedTokens)
      else if character = '[' ∨ character = ']' ∨ character = '\'' ∨ character = '"' then
        tokenizeAux rest [] (.atom (.symbol (String.singleton character)) ::
          Reader.flushWord reversedWord reversedTokens)
      else tokenizeAux rest (character :: reversedWord) reversedTokens

def removeComments : Nat → List Token → List Token
  | _, [] => []
  | depth, .atom (.symbol "[") :: rest => removeComments (depth + 1) rest
  | depth + 1, .atom (.symbol "]") :: rest => removeComments depth rest
  | 0, token :: rest => token :: removeComments 0 rest
  | depth + 1, _ :: rest => removeComments (depth + 1) rest

def tokenize (source : String) : List Token :=
  let characters := source.toList.map (fun character => if character = '\n' then ' ' else character)
  removeComments 0 (tokenizeAux (characters.filter Reader.printable) [] [])

def parseSource (source : String) : Option (SExpr × List Token) :=
  parseTokens (tokenize source)

inductive Command where
  | evaluate (expression : SExpr)
  | define (name definition : SExpr)
deriving Repr

/-- The file driver recognizes `define` after reading, before evaluation. -/
def command : SExpr → Command
  | .list [.symbol "define", .list (name :: parameters), definition] =>
      .define name (.list [.symbol "lambda", .list parameters, definition])
  | .list [.symbol "define", name, definition] => .define name definition
  | expression => .evaluate expression

def installDefinition (name definition : SExpr) (environment : Environment) : Environment :=
  (name, definition) :: environment

/-- A completed source expression leaves all later source tokens available. -/
theorem parseTokensAux_append (state : State) (input rest suffix : List Token)
    (expression : SExpr) (parsed : parseTokensAux state input = some (expression, rest)) :
    parseTokensAux state (input ++ suffix) = some (expression, rest ++ suffix) := by
  induction input generalizing state with
  | nil => cases parsed
  | cons token input ih =>
      cases progress : receive state token with
      | waiting next =>
          simp only [parseTokensAux, progress] at parsed
          simpa only [List.cons_append, parseTokensAux, progress] using ih next parsed
      | complete value =>
          simp only [parseTokensAux, progress, Option.some.injEq, Prod.mk.injEq] at parsed
          rcases parsed with ⟨rfl, rfl⟩
          simp only [List.cons_append, parseTokensAux, progress]

set_option cbv.warning false

theorem atom_source : parseSource "aa" = some (.symbol "aa", []) := by cbv
theorem read_bit_source : parseSource "read-bit" = some (.list [.symbol "read-bit"], []) := by cbv
theorem quote_source : parseSource "'aa" = some (quote (.symbol "aa"), []) := by cbv
theorem literal_primitive_source : parseSource "\"car" = some (.symbol "car", []) := by cbv
theorem cadr_source : parseSource "cadr x" =
    some (.list [.symbol "car", .list [.symbol "cdr", .symbol "x"]], []) := by cbv
theorem lambda_source : parseSource "'lambda(x y)x" =
    some (quote (.list [.symbol "lambda", .list [.symbol "x", .symbol "y"], .symbol "x"]), []) := by cbv
theorem let_source : parseSource "let x a x" =
    some (expandLet (.symbol "x") (.symbol "a") (.symbol "x"), []) := by cbv
theorem function_let_source : parseSource "let (f x) x (f a)" =
    some (expandLet (.list [.symbol "f", .symbol "x"]) (.symbol "x")
      (.list [.symbol "f", .symbol "a"]), []) := by cbv
theorem nested_comment_source : parseSource "[outer [inner] ignored]aa" =
    some (.symbol "aa", []) := by cbv
theorem comments_separate_words : parseSource "a[ignored]b" =
    some (.symbol "a", [.atom (.symbol "b")]) := by cbv
theorem line_boundaries_separate_words : parseSource "a\nb" =
    some (.symbol "a", [.atom (.symbol "b")]) := by cbv
theorem missing_argument_source : parseSource "car" = none := by cbv
theorem source_does_not_supply_closing_parentheses : parseSource "(a" = none := by cbv
theorem closing_parenthesis_as_missing_argument : parseSource "(cons a)" = none := by cbv
theorem define_function (name : SExpr) (parameters : List SExpr) (body : SExpr) :
    command (.list [.symbol "define", .list (name :: parameters), body]) =
      .define name (.list [.symbol "lambda", .list parameters, body]) := rfl

/-- Ordinary variable `let` uses the shared expression constructor. -/
theorem expandLet_symbol (name : String) (definition body : SExpr) :
    expandLet (.symbol name) definition body = letValue name definition body := rfl

end Mettapedia.Languages.Chaitin.Frontend
