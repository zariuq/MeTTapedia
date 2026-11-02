import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePolicy

/-! Canonical source printing from independent program IR. The visitor builds
transient grammar constructor data; the shared declared printer supplies all
punctuation. Names and unsupported source forms receive explicit diagnostics. -/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

def node (name : String) (children : List Pattern) : Pattern := .apply ("dl-src:" ++ name) children
def empty : Pattern := node "trivia-empty" []

def scalar? (sort : String) (character : Char) : Except String Pattern := do
  let some row := CorePrinter.lexicalRow? sort | .error s!"unknown lexical sort {sort}"
  if formed : SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className character.toNat then
    pure (ScalarCore.leaf row character.toNat formed)
  else .error s!"character is outside lexical sort {sort}"

def space : Pattern := node "trivia-space"
  [ScalarCore.leaf ⟨7,by decide⟩ 32 (by decide +kernel),empty]
def newline : Pattern := node "trivia-space"
  [ScalarCore.leaf ⟨7,by decide⟩ 10 (by decide +kernel),empty]
def directiveSpace : Pattern := node "directive-space"
  [ScalarCore.leaf ⟨8,by decide⟩ 32 (by decide +kernel),empty]

def identifierTail? : List Char → Except String Pattern
  | [] => .error "identifier tail must be nonempty"
  | [character] => do pure (node "identifier-tail-one" [← scalar? "DlIdentifierRestScalar" character])
  | character :: rest => do
      pure (node "identifier-tail-more" [← scalar? "DlIdentifierRestScalar" character,← identifierTail? rest])

def identifier? (name : String) : Except String Pattern :=
  if name ∈ SourcePolicy.reservedWords then .error "source identifier is a reserved word" else
  match name.toList with
  | [] => .error "source identifier must be nonempty"
  | [character] => do pure (node "identifier-one" [← scalar? "DlSingleIdentifierScalar" character])
  | character :: rest => do
      pure (node "identifier-more" [← scalar? "DlIdentifierFirstScalar" character,← identifierTail? rest])

theorem identifier_not_reserved (name : String) (pattern : Pattern)
    (built : identifier? name = .ok pattern) : name ∉ SourcePolicy.reservedWords := by
  intro reserved
  simp [identifier?, reserved] at built

def qualifiedName? : QualifiedName → Except String Pattern
  | [] => .error "source relation name must be nonempty"
  | [name] => do pure (node "qualified-name-one" [← identifier? name])
  | name :: rest => do pure (node "qualified-name-more" [← identifier? name,← qualifiedName? rest])

def digits? : List Char → Except String Pattern
  | [] => .error "numeric literal must contain a digit"
  | [character] => do pure (node "digits-one" [← scalar? "DlDigitScalar" character])
  | character :: rest => do pure (node "digits-more" [← scalar? "DlDigitScalar" character,← digits? rest])

def escapeLabel? : Char → Option String
  | '"' => some "escape-quote"
  | '\\' => some "escape-slash"
  | '\n' => some "escape-newline"
  | '\r' => some "escape-return"
  | '\t' => some "escape-tab"
  | character => match character.toNat with
    | 7 => some "escape-bell" | 8 => some "escape-backspace"
    | 11 => some "escape-vertical-tab" | 12 => some "escape-formfeed"
    | _ => none

def symbolBody? : List Char → Except String Pattern
  | [] => .ok (node "symbol-empty" [])
  | character :: rest => do
      let tail ← symbolBody? rest
      match escapeLabel? character with
      | some label => pure (node "symbol-escape" [node label [],tail])
      | none => pure (node "symbol-body" [← scalar? "DlStringScalar" character,tail])

def value? : Mettapedia.Languages.Datalog.Value → Except String Pattern
  | .symbol text => do pure (node "constant-symbol" [node "symbol" [← symbolBody? text.toList]])
  | .number value => do
      unless Mettapedia.Languages.Datalog.Value.fits64 (.number value) do .error "signed literal is outside the 64-bit profile"
      let digits ← digits? value.natAbs.repr.toList
      pure (node "constant-integer" [node (if value < 0 then "integer-negative" else "integer-decimal") [digits]])
  | .unsigned value => do
      unless Mettapedia.Languages.Datalog.Value.fits64 (.unsigned value) do .error "unsigned literal is outside the 64-bit profile"
      pure (node "constant-unsigned" [node "unsigned-decimal" [← digits? value.repr.toList]])
  | .floating _ => .error "floating literals require a declared floating source profile"

def nonemptySeparated (oneName moreName : String) (first : Pattern) : List Pattern → Pattern
  | [] => node oneName [first,empty]
  | second :: rest => node moreName [first,empty,space,nonemptySeparated oneName moreName second rest]

def separated (emptyName oneName moreName : String) : List Pattern → Pattern
  | [] => node emptyName []
  | first :: rest => nonemptySeparated oneName moreName first rest

def argument? : Argument → Except String Pattern
  | .literal value => do pure (node "term-constant" [← value? value])
  | .var name => do pure (node "term-variable" [← identifier? name])
  | .anonymous => pure (node "term-anonymous" [])

def atom? (atom : Mettapedia.Languages.Datalog.Atom) : Except String Pattern := do
  let name ← qualifiedName? atom.relation
  let arguments ← atom.arguments.mapM argument?
  pure (node "atom" [name,empty,empty,separated "terms-empty" "terms-one" "terms-more" arguments])

def fact? (fact : GroundFact) : Except String Pattern := do
  let name ← qualifiedName? fact.relation
  let values ← fact.values.mapM value?
  pure (node "fact" [node "ground-atom" [name,empty,empty,separated "constants-empty" "constants-one" "constants-more" values],empty])

def operator (operator : ComparisonOperator) : Pattern := node (match operator with
  | .equal => "comparison-equal" | .different => "comparison-different"
  | .less => "comparison-less" | .lessEqual => "comparison-less-equal"
  | .greater => "comparison-greater" | .greaterEqual => "comparison-greater-equal") []

def premise? : Mettapedia.Languages.Datalog.Premise → Except String Pattern
  | .atom atom => do pure (node "positive-atom" [← atom? atom])
  | .comparison comparison => do
      pure (node "positive-comparison" [node "comparison"
        [← argument? comparison.left,space,operator comparison.operator,space,← argument? comparison.right]])

def clause? (clause : Clause) : Except String Pattern := do
  if clause.body.isEmpty then .error "an empty-body rule has no ordinary source rule form; use a fact" else do
    let head ← atom? clause.head
    let body ← clause.body.mapM premise?
    let first :: rest := body | .error "source rule body must be nonempty"
    pure (node "rule" [head,space,space,nonemptySeparated "body-one" "body-more" first rest])

def attributeType? : AttributeType → Except String Pattern
  | .symbol => pure (node "type-symbol" [])
  | .number => pure (node "type-number" [])
  | .unsigned => pure (node "type-unsigned" [])
  | .floating => .error "floating declarations require a declared floating source profile"

def attribute? (column : Attribute) : Except String Pattern := do
  pure (node "attr" [← identifier? column.name,empty,space,← attributeType? column.type])

def declaration? (declaration : RelationDeclaration) : Except String Pattern := do
  let [name] := declaration.name | .error "ordinary core declarations require one unqualified relation name"
  let identifier ← identifier? name
  let attributes ← declaration.attributes.mapM attribute?
  pure (node "declaration" [directiveSpace,node "relations-one" [identifier],empty,empty,
    separated "attributes-empty" "attributes-one" "attributes-more" attributes])

def statement? : Statement → Except String Pattern
  | .declaration declaration => do pure (node "item-declaration" [← declaration? declaration])
  | .fact fact => do pure (node "item-fact" [← fact? fact])
  | .rule clause => do pure (node "item-rule" [← clause? clause])
  | .input name => do pure (node "item-input" [node "input" [directiveSpace,← qualifiedName? name]])
  | .output name => do pure (node "item-output" [node "output" [directiveSpace,← qualifiedName? name]])

def items : List Pattern → Pattern
  | [] => node "items-empty" []
  | first :: rest => node "items-more" [first,newline,items rest]

def programTree? (program : Program) : Except String Pattern := do
  pure (node "program" [empty,items (← program.statements.mapM statement?)])

def print? (program : Program) : Except String String := do
  let tree ← programTree? program
  let some text := CorePrinter.printText? "DlProgram" tree
    | .error "declared grammar printer refused the generated source tree"
  pure text

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
