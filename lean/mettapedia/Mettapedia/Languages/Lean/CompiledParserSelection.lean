import Mettapedia.Languages.Lean.LeanSyntaxReadback4331
import Mettapedia.GSLT.Parsing.ParserAttemptSelection

/-!
# Local control policy for compiled declarative parser rows

The generalized parser supplies the candidate language. This policy interprets
the precedence, sequencing and longest-attempt control of compiled rows. Its
result is not an acceptance certificate: the caller must retain only results
whose choice expansions occur among independently replayed GSLT derivations.

The lexical observation covers the bootstrap's identifiers, decimal numerals
and registered symbols. Other lexical forms and exhausted evaluation are
explicit boundaries. No host parser is invoked and operator spellings are
read from compiled rows.
-/

namespace Mettapedia.Languages.Lean.CompiledParserSelection

open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler PresentationExprSemantics
open LeanSyntaxBootstrap LeanSyntaxReadback4331

structure Token where
  spelling : String
  kind : String
  start : Nat
  stop : Nat
  next : Nat
  deriving Repr

def spaces (input : List Nat) (start : Nat) : Nat :=
  start + ((input.drop start).takeWhile fun cp => [32, 9, 10, 13].contains cp).length

def digit (cp : Nat) : Bool := 48 ≤ cp && cp ≤ 57

/-- Qualified segments use the same declared identifier alphabet as the
bootstrap. A reserved word loses to a strictly longer identifier. -/
def identifierLength (input : List Nat) : Nat := Id.run do
  let mut length := 0
  let mut atStart := true
  for index in [:input.length] do
    let cp := input[index]!
    if atStart then
      unless identifierStart cp do break
      atStart := false
      length := index + 1
    else if continuation cp then length := index + 1
    else if cp == 46 && (input[index + 1]?).any identifierStart then atStart := true
    else break
  return length

def token (tokens : List String) (input : List Nat) (start : Nat) : Option Token := Id.run do
  let remaining := input.drop start
  let some first := remaining.head? | return none
  let mut width := 0
  let mut kind := "symbol"
  if digit first then
    width := (remaining.takeWhile digit).length
    kind := "number"
  else
    for text in tokens do
      let values := text.toList.map Char.toNat
      if values.isPrefixOf remaining && width < values.length then width := values.length
    let idWidth := identifierLength remaining
    if width < idWidth then
      width := idWidth
      kind := "identifier"
  if width == 0 then return none
  return some ⟨String.ofList ((remaining.take width).map Char.ofNat), kind,
    start, start + width, spaces input (start + width)⟩

structure Result where
  stop : Nat
  succeeded : Bool
  output : List CST := []
  lhsPrec : Nat := 1024
  deriving Repr

def failure (stop : Nat) : Result := ⟨stop, false, [], 1024⟩
def success (stop : Nat) (output : List CST) (prec := 1024) : Result := ⟨stop, true, output, prec⟩

def firstLiteral : Expr → Option String
  | .literal values => some (String.ofList (values.map Char.ofNat))
  | .seq first _ | .left first _ | .node _ first => firstLiteral first
  | _ => none

def body (row : DynamicRow) : Expr :=
  match row.row.leftPrecedence, row.row.body with
  | some _, .seq _ remainder => remainder
  | _, expression => expression

def dispatch (rows : List DynamicRow) (leading : Bool) (spelling : String) : List DynamicRow :=
  rows.filter fun row => row.key.precedence == 0 && row.row.leftPrecedence.isNone == leading &&
    firstLiteral (body row) == some spelling

def choose (start : Nat) (attempts : List (ParserAttemptSelection.Attempt Result)) : Result :=
  match ParserAttemptSelection.select attempts with
  | [] => failure start
  | [winner] => winner.payload
  | first :: rest =>
      if first.succeeded then
        success first.stop [.node "selected.choice" start first.stop
          ((first :: rest).flatMap (·.payload.output))]
          ((rest.map (·.payload.lhsPrec)).foldl min first.payload.lhsPrec)
      else first.payload

structure Context where
  rows : List DynamicRow
  tokens : List String
  input : List Nat

mutual
  def expression (context : Context) : Nat → Expr → Nat → Except String Result
    | 0, _, _ => .error "parser policy budget exhausted"
    | fuel + 1, expression, start => do
      match expression with
      | .epsilon => return success start []
      | .literal expected =>
          let some next := token context.tokens context.input start | return failure start
          if next.kind == "symbol" && next.spelling.toList.map Char.toNat == expected then
            return success next.stop [.terminal expected start next.stop]
          return failure start
      | .seq first second | .left first second | .right first second =>
          let firstResult ← CompiledParserSelection.expression context fuel first start
          unless firstResult.succeeded do return firstResult
          let secondResult ← CompiledParserSelection.expression context fuel second firstResult.stop
          unless secondResult.succeeded do return secondResult
          let output := match expression with
            | .left .. => firstResult.output
            | .right .. => secondResult.output
            | _ => firstResult.output ++ secondResult.output
          return success secondResult.stop output secondResult.lhsPrec
      | .node label inner =>
          let result ← CompiledParserSelection.expression context fuel inner start
          if result.succeeded then return { result with output := [.node label start result.stop result.output] }
          return result
      | .ref name =>
          if name == "ws" then return success (spaces context.input start) []
          if name.startsWith "dynamic.term." then
            let some precedence := (name.drop "dynamic.term.".length).toString.toNat?
              | throw "malformed compiled category reference"
            return ← category context fuel precedence start
          if name == "bootstrap.number" || name == "bootstrap.identifier" then
            let some next := token context.tokens context.input start | return failure start
            let expected := if name == "bootstrap.number" then "number" else "identifier"
            if next.kind != expected then return failure start
            return success next.next [.node expected start next.stop
              [.terminal (next.spelling.toList.map Char.toNat) start next.stop]]
          throw ("parser policy primitive boundary: " ++ name)
      | _ => throw "parser policy expression boundary"

  def attempt (context : Context) : Nat → Nat → Option Result → Nat → DynamicRow → Except String Result
    | 0, _, _, _, _ => .error "parser policy budget exhausted"
    | fuel + 1, precedence, left, start, row => do
        if row.row.precedence < precedence then return failure start
        if let some required := row.row.leftPrecedence then
          let some left := left | throw "trailing parser policy has no left operand"
          if left.lhsPrec < required then return failure start
        let result ← expression context fuel (body row) start
        unless result.succeeded do return result
        let children := (left.toList.flatMap (·.output)) ++ result.output
        let nodeStart := match left.bind (·.output.head?) with
          | some (.node _ position ..) | some (.terminal _ position _) => position
          | none => start
        return success result.stop [.node row.label nodeStart result.stop children] row.row.precedence

  def category (context : Context) : Nat → Nat → Nat → Except String Result
    | 0, _, _ => .error "parser policy budget exhausted"
    | fuel + 1, precedence, start => do
        let some next := token context.tokens context.input start | return failure start
        let mut attempts := []
        if next.kind == "number" || next.kind == "identifier" then
          let tree := .node next.kind start next.stop [.terminal (next.spelling.toList.map Char.toNat) start next.stop]
          attempts := [⟨next.next, true, 1000, success next.next [tree]⟩]
        else if next.spelling == "(" then
          let inner ← category context fuel 0 next.next
          let result ← if inner.succeeded then do
            let close ← expression context fuel (.literal [41]) inner.stop
            if close.succeeded then
              pure (success (spaces context.input close.stop) [.node "term.parenthesized" start close.stop
                ([.terminal [40] start next.stop] ++ inner.output ++ close.output)])
            else pure close
          else pure inner
          attempts := [⟨result.stop, result.succeeded, 1000, result⟩]
        for row in dispatch context.rows true next.spelling do
          let result ← attempt context fuel precedence none start row
          attempts := attempts ++ [⟨result.stop, result.succeeded, row.row.priority, result⟩]
        if attempts.isEmpty then return failure start
        let result := choose start attempts
        if result.succeeded then tail context fuel precedence result else pure result

  def tail (context : Context) : Nat → Nat → Result → Except String Result
    | 0, _, _ => .error "parser policy budget exhausted"
    | fuel + 1, precedence, left => do
        let some next := token context.tokens context.input left.stop | return left
        let rows := dispatch context.rows false next.spelling
        if rows.isEmpty then return left
        let attempts ← rows.mapM fun row => do
          let result ← attempt context fuel precedence (some left) left.stop row
          return (⟨result.stop, result.succeeded, row.row.priority, result⟩ : ParserAttemptSelection.Attempt Result)
        let result := choose left.stop attempts
        if !result.succeeded then return if result.stop == left.stop then left else result
        unless left.stop < result.stop do throw "trailing parser policy did not advance"
        tail context fuel precedence result
end

end Mettapedia.Languages.Lean.CompiledParserSelection
