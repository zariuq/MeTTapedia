import Mettapedia.GSLT.Parsing.LeanCommandProfile
import Mettapedia.GSLT.Parsing.PresentationWire
import Mettapedia.Languages.Lean.ParserRegistrationCompiler

/-!
# Bootstrap grammar for an evolving declarative Lean command stream

Scope commands and identifier syntax reuse the existing authored command
profile. The additional grammar reads named syntax, notation and infix
declarations with numeric precedence, plus term-observation commands.
Operator spellings are string data in these declarations, never productions
authored separately for a test operator.

This profile admits ordinary unescaped, single-line string literals.
General quotations, declaration macros and arbitrary parser callbacks remain
explicit extension boundaries.
-/

namespace Mettapedia.Languages.Lean.LeanSyntaxBootstrap

open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler PresentationExprSemantics ParserProfileSemantics
open ParserDescription ParserRegistrationCompiler

def text (value : String) : Expr := .literal (value.toList.map Char.toNat)
def sequence (items : List Expr) : Expr := items.foldr Expr.seq .epsilon
def alternative (items : List Expr) : Expr := items.foldr Expr.alt (.ref "bootstrap.never")
def node (label : String) (items : List Expr) : Expr := .node label (sequence items)
def definition (name label : String) (items : List Expr) : Definition := ⟨name, node label items⟩
def whitespace : Expr := .ref "ws"
def symbol (value : String) : Expr := .left (text value) whitespace

def termName : Name := .str .anonymous "term"
def termKey (precedence : Nat) : String := "dynamic.term." ++ toString precedence

def bindings : ParserDescriptorLowering.Bindings where
  categoryRef := fun category precedence =>
    if category == termName then termKey precedence else "unresolved.category." ++ reprStr category ++ "." ++ toString precedence
  primitiveRef := fun name =>
    if name == .str .anonymous "num" then some "bootstrap.number"
    else if name == .str .anonymous "ident" then some "bootstrap.identifier"
    else none
  whitespace := "ws"

def baseCategories : List String :=
  ["ws", "ws1", "space", "letter", "continuation", "segment", "tail", "identifier", "qualifiedTail", "names", "namesTail"]

def scopeLabels : List String :=
  ["namespace", "section.empty", "section.named", "end.empty", "end.named", "open", "open.scoped", "import"]

def commandHeads : List String :=
  ["namespace", "section", "end", "open", "import", "local", "scoped", "infixl", "infixr", "infix", "syntax", "notation", "#check"]

/-- Combine adjacent exact terminals into one literal. Readback expands its
scalar leaves when using the existing scope-command decoder. -/
def sourceSymbols : List CompilerCorrespondence.SourceSymbol → Expr
  | [] => .epsilon
  | .exact cp :: rest =>
      match sourceSymbols rest with
      | .seq (.literal codepoints) tail => .seq (.literal (cp :: codepoints)) tail
      | other => .seq (.literal [cp]) other
  | .any :: rest => .seq (.class "bootstrap.any") (sourceSymbols rest)
  | .call category :: rest => .seq (.ref category) (sourceSymbols rest)

def inherited : List Definition :=
  (LeanCommandProfile.presentation.rules.filter fun rule =>
    baseCategories.contains rule.category || scopeLabels.contains rule.sourceRule).map fun rule =>
      ⟨rule.category, .node rule.sourceRule (sourceSymbols rule.symbols)⟩

def profile : ParserProfileLayer where
  name := "lean-declarative-bootstrap-v1"
  startSort := "front.command"
  classes := [
    ⟨"bootstrap.any", .except []⟩,
    ⟨"bootstrap.digit", .points ((List.range 10).map (· + 48))⟩,
    ⟨"bootstrap.string-character", .except [34, 92, 10, 13]⟩]
  states := []

def declarations : List Definition := [
  ⟨"bootstrap.never", .seq .eof (.class "bootstrap.any")⟩,
  ⟨"bootstrap.number", .node "number" (.plus (.class "bootstrap.digit"))⟩,
  ⟨"bootstrap.identifier", .left (.ref "identifier") whitespace⟩,
  definition "bootstrap.string" "quoted" [.char 34, .star (.class "bootstrap.string-character"), .char 34],
  definition "bootstrap.attribute" "attribute.global" [],
  definition "bootstrap.attribute" "attribute.local" [text "local", .ref "ws1"],
  definition "bootstrap.attribute" "attribute.scoped" [text "scoped", .ref "ws1"],
  definition "bootstrap.precedence" "precedence" [symbol ":", .ref "bootstrap.number"],
  definition "bootstrap.name" "declaration.name"
    [symbol "(", symbol "name", symbol ":=", .ref "identifier", whitespace, symbol ")"],
  definition "bootstrap.priority" "priority.default" [],
  definition "bootstrap.priority" "priority.explicit"
    [symbol "(", symbol "priority", symbol ":=", .ref "bootstrap.number", whitespace, symbol ")"],
  definition "bootstrap.infix-kind" "infix.left" [text "infixl"],
  definition "bootstrap.infix-kind" "infix.right" [text "infixr"],
  definition "bootstrap.infix-kind" "infix.none" [text "infix"],
  definition "command" "declaration.infix"
    [.ref "bootstrap.attribute", .ref "bootstrap.infix-kind", .ref "bootstrap.precedence", whitespace,
     .ref "bootstrap.name", whitespace, .ref "bootstrap.priority", whitespace,
     .ref "bootstrap.string", whitespace, symbol "=>", .ref "identifier"],
  definition "bootstrap.part" "part.literal" [.ref "bootstrap.string", whitespace],
  definition "bootstrap.part" "part.category"
    [.ref "identifier", .ref "bootstrap.precedence", whitespace],
  definition "bootstrap.parts" "parts" [.plus (.ref "bootstrap.part")],
  definition "command" "declaration.syntax"
    [.ref "bootstrap.attribute", text "syntax", .ref "bootstrap.precedence", whitespace,
     .ref "bootstrap.name", whitespace, .ref "bootstrap.priority", whitespace,
     .ref "bootstrap.parts", symbol ":", .ref "identifier"],
  definition "command" "declaration.notation"
    [.ref "bootstrap.attribute", text "notation", .ref "bootstrap.precedence", whitespace,
     .ref "bootstrap.name", whitespace, .ref "bootstrap.priority", whitespace,
     .ref "bootstrap.parts", symbol "=>", .ref "names"],
  definition "command" "observe.term" [symbol "#check", .ref (termKey 0)],
  ⟨"front.follow", .right whitespace (.alt .eof (.seq (alternative (commandHeads.map text)) (.star (.class "bootstrap.any"))))⟩,
  ⟨"front.command", .left (.right whitespace (.left (.ref "command") (.ref "front.follow"))) .eof⟩,
  ⟨"front.end", .left whitespace .eof⟩]

def baseTerms (precedence : Nat) : List Definition :=
  if precedence ≤ 1024 then [
    ⟨termKey precedence, .node "term.number" (.left (.ref "bootstrap.number") whitespace)⟩,
    ⟨termKey precedence, .node "term.identifier" (.left (.ref "identifier") whitespace)⟩,
    definition (termKey precedence) "term.parenthesized" [symbol "(", .ref (termKey 0), symbol ")"]]
  else []

def requestedPrecedences : Description → List Nat
  | .category category precedence => if category == termName then [precedence] else []
  | .node _ _ body | .nodeWithAntiquot _ _ body | .unary _ body => requestedPrecedences body
  | .trailingNode _ _ left body => left :: requestedPrecedences body
  | .binary _ first second | .sepBy first _ second _ | .sepBy1 first _ second _ =>
      requestedPrecedences first ++ requestedPrecedences second
  | _ => []

structure DynamicRow where
  label : String
  key : Key
  row : Row
  occurrence : Nat
  deriving Repr

def materialize (source : SourceState) (target : TargetState) : Except String (Presentation × List DynamicRow) := do
  let some sourceTop := source.frames.head? | throw "missing source grammar scope"
  let some targetTop := target.frames.head? | throw "missing target grammar scope"
  let precedences := (0 :: sourceTop.value.flatMap (requestedPrecedences ∘ Registration.descriptor)).eraseDups
  let mut definitions := inherited ++ declarations
  let mut rows := []
  let mut ordinal := 0
  for precedence in precedences do
    definitions := definitions ++ baseTerms precedence
    let key : Key := ⟨termName, precedence⟩
    for result in targetTop.value.table key do
      match result with
      | .error reason => throw ("parser descriptor boundary: " ++ reprStr reason)
      | .ok row =>
          let label := "dynamic.rule." ++ toString ordinal
          definitions := definitions ++ [⟨termKey precedence, .node label row.body⟩]
          rows := rows ++ [⟨label, key, row, ordinal⟩]
          ordinal := ordinal + 1
  return (⟨"lean-declarative-stream-v1", definitions, []⟩, rows)

end Mettapedia.Languages.Lean.LeanSyntaxBootstrap
