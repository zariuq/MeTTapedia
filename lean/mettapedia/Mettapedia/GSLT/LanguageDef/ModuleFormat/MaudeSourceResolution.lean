import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax
import Mettapedia.Languages.Maude.Syntax

/-! Signature-directed resolution of Maude term bubbles. Source parentheses,
operator precedence and gathering are frontend information. Resolved runtime
terms contain declaration identifiers and sorted arguments. Alternatives are
retained until the caller checks uniqueness; traversal order never selects a
parse. This module does not provide normalization or module certificates.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceResolution

open SourcePacket
abbrev Lower := Except String
abbrev MTerm := Mettapedia.Languages.Maude.Term
abbrev MOperator := Mettapedia.Languages.Maude.Operator
abbrev MContext := Mettapedia.Languages.Maude.VariableContext

def requireSome {α : Type} (message : String) : Option α → Lower α :=
  SourcePacketView.requireSome message

def description : Lower Portable.SyntaxDescription :=
  requireSome "Maude syntax description is unavailable" GoldCoreSyntax.Maude.description?

def text (sort : String) (source : Packet) : Lower String :=
  SourcePacketView.text description sort source

def keepField : Mettapedia.OSLF.MeTTaIL.Syntax.TermParam → Bool
    | .simple _ (.base "SrcTrivia") | .simple _ (.base "SrcSpacing") => false
    | _ => true

def view (source : Packet) : Lower (String × List Packet) :=
  SourcePacketView.view description keepField source

def series (family : String) : Nat → Packet → Lower (List Packet) :=
  SourcePacketView.series view family

private def unescape : List Char → Lower (List Char)
  | [] => pure []
  | '`' :: char :: rest => (char :: ·) <$> unescape rest
  | ['`'] => .error "unfinished name escape"
  | char :: rest => (char :: ·) <$> unescape rest

def name (source : Packet) : Lower String := do
  pure (String.ofList (← unescape (← text "MdName" source).toList))

def atoms : Nat → Packet → Lower (List Packet)
  | 0, _ => .error "term bubble exceeds its packet size"
  | fuel + 1, source => do
      match ← view source with
      | ("maude-src:term-atom", [atom]) => pure [atom]
      | ("maude-src:term-juxtaposition", [left, right]) => pure ((← atoms fuel left) ++ [right])
      | _ => .error "expected a term bubble"

structure SurfaceOperator where
  declaration : MOperator
  precedence : Nat
  deriving Repr

def defaultPrecedence (name : String) (arity : Nat) : Nat :=
  if !name.contains '_' || (!name.startsWith "_" && !name.endsWith "_") then 0
  else if arity == 1 && !(name.startsWith "_" && name.endsWith "_") then 15 else 41

structure Candidate where
  term : MTerm
  sort : String
  precedence : Nat
  deriving Repr, BEq

private def gatherAllows (operator : SurfaceOperator) (segments : List String)
    (index : Nat) (argument : Candidate) : Bool :=
  let name := operator.declaration.sourceName
  if operator.declaration.attributes.associative && operator.precedence > 0 &&
      operator.declaration.arguments.length == 2 && name.startsWith "_" && name.endsWith "_" && index == 0 then
    argument.precedence < operator.precedence
  else if segments[index]?.getD "" != "" && segments[index + 1]?.getD "" != "" then true
  else argument.precedence ≤ operator.precedence

mutual
  def candidates : Nat → List SurfaceOperator → MContext → List Packet → Lower (List Candidate)
    | 0, _, _, _ => .error "term resolution exceeds its finite bubble bound"
    | fuel + 1, operators, context, source => do
        let mut found := []
        if let [single] := source then
          match ← view single with
          | ("maude-src:term-name", [spelling]) =>
              let spelling ← name spelling
              if let some sort := context.lookup spelling then
                found := found ++ [⟨.var spelling, sort, 0⟩]
              found := found ++ (operators.filterMap fun operator =>
                if operator.declaration.sourceName == spelling && operator.declaration.arguments.isEmpty then
                  some ⟨.app operator.declaration.id [], operator.declaration.result, 0⟩ else none)
          | ("maude-src:term-parenthesized", [body]) =>
              found := (← candidates fuel operators context (← atoms fuel body)).map fun candidate =>
                {candidate with precedence := 0}
          | ("maude-src:term-call", [spelling, arguments]) =>
              let spelling ← name spelling
              let arguments ← series "maude-src:arguments" fuel arguments
              for operator in operators do
                if operator.declaration.sourceName == spelling &&
                    operator.declaration.arguments.length == arguments.length then
                  let fields ← callArguments fuel operators context operator.declaration.arguments arguments
                  found := found ++ fields.map fun fields =>
                    ⟨.app operator.declaration.id fields, operator.declaration.result, 0⟩
          | _ => pure ()
        for operator in operators do
          let segments := operator.declaration.sourceName.splitOn "_"
          if segments.length == operator.declaration.arguments.length + 1 && segments.length > 1 &&
              (segments.length > 2 || segments.any (· != "")) then
            let fields ← template fuel operators context operator segments 0 source
            found := found ++ fields.map fun fields =>
              ⟨.app operator.declaration.id fields, operator.declaration.result, operator.precedence⟩
        pure found.eraseDups

  private def callArguments : Nat → List SurfaceOperator → MContext → List String → List Packet →
      Lower (List (List MTerm))
    | 0, _, _, _, _ => .error "argument resolution exceeds its finite bubble bound"
    | fuel + 1, operators, context, sorts, arguments => do
        match sorts, arguments with
        | [], [] => pure [[]]
        | sort :: sorts, first :: rest =>
            let choices ← candidates fuel operators context (← atoms fuel first)
            let later ← callArguments fuel operators context sorts rest
            pure ((choices.filter (·.sort == sort)).flatMap fun choice => later.map (choice.term :: ·))
        | _, _ => pure []

  private def template : Nat → List SurfaceOperator → MContext → SurfaceOperator → List String → Nat →
      List Packet → Lower (List (List MTerm))
    | 0, _, _, _, _, _, _ => .error "mixfix resolution exceeds its finite bubble bound"
    | fuel + 1, operators, context, operator, segments, index, source => do
        let segment := segments[index]?.getD ""
        let source ← if segment.isEmpty then pure (some source) else do
            match source with
            | [] => pure none
            | first :: rest =>
                match ← view first with
                | ("maude-src:term-name", [spelling]) =>
                    pure (if (← name spelling) == segment then some rest else none)
                | _ => pure none
        let some source := source | pure []
        match operator.declaration.arguments[index]? with
        | none => pure (if source.isEmpty then [[]] else [])
        | some sort =>
            let mut found := []
            let remaining := operator.declaration.arguments.length - (index + 1) +
              ((segments.drop (index + 1)).filter (· != "")).length
            for length in List.range (source.length - remaining) do
              let length := length + 1
              let choices ← candidates fuel operators context (source.take length)
              let choices := choices.filter fun choice => choice.sort == sort && gatherAllows operator segments index choice
              if !choices.isEmpty then
                let later ← template fuel operators context operator segments (index + 1) (source.drop length)
                found := found ++ choices.flatMap fun choice => later.map (choice.term :: ·)
            pure found
end

def terms (operators : List SurfaceOperator) (context : MContext) (source : Packet) : Lower (List Candidate) := do
  candidates (packetNodes source * 4 + 8) operators context (← atoms (packetNodes source + 1) source)

def unique (expected : Option String) (choices : List Candidate) : Lower MTerm := do
  let choices := (choices.filter (fun candidate => expected.all (· == candidate.sort))).map (·.term) |>.eraseDups
  match choices with
  | [term] => pure term
  | [] => .error "no sorted interpretation of the term"
  | _ => .error "ambiguous sorted term; provide an explicit selection or parentheses"

def resolve (operators : List SurfaceOperator) (context : MContext)
    (source : Packet) (expected : Option String := none) : Lower MTerm := do
  unique expected (← terms operators context source)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceResolution
