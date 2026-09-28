import Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-!
# Native action-compiler controls from typed constructor routes

These fixtures exercise the constructor-only compiler and the existing native
ParserPack executors. They are not a TPTP grammar or a corpus qualification.
Expected results come from typed route evaluation, independently of native
action decoding and bytecode execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Tools.ExportGrammarConstructorActions

open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.GSLT.Parsing.GrammarConstructorActions
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

inductive Kind where
  | name | formula | binders | record
  deriving DecidableEq

inductive Constructor : List Kind → Kind → Type where
  | neg : Constructor [.formula] .formula
  | inequality : Constructor [.formula, .formula] .formula
  | quantify : Constructor [.binders, .formula] .formula
  | annotated : Constructor [.name, .formula] .record

def constructorHead : {inputs : List Kind} → {output : Kind} →
    Constructor inputs output → String
  | _, _, .neg => "¬"
  | _, _, .inequality => "≉"
  | _, _, .quantify => "∀"
  | _, _, .annotated => "fof"

/-- This fixture algebra tests syntax construction, not TPTP semantic typing. -/
abbrev algebra : ManySortedConstructionAlgebra where
  Kind := Kind
  Object := fun _ => Term
  Source := fun _ => Term
  Operation := Constructor
  interpretSource := id
  interpretOperation := fun operation values =>
    .application (constructorHead operation) (encodeValues (fun _ => id) values)

def encoding : ConstructorEncoding algebra where
  value := fun _ => id
  head := constructorHead
  operation_exact := fun _ _ => rfl

abbrev Route := OpenConstructionRoute algebra

def inequality : Route [.formula, .formula] .formula :=
  .apply .inequality (.cons (.input .here) (.cons (.input (.there .here)) .nil))

def nested : Route [.binders, .formula, .formula] .formula :=
  .apply .quantify (.cons (.input .here)
    (.cons (.apply .inequality
      (.cons (.input (.there .here))
        (.cons (.apply .neg (.cons (.input (.there (.there .here))) .nil)) .nil))) .nil))

def duplicate : Route [.formula] .formula :=
  .apply .inequality (.cons (.input .here) (.cons (.input .here) .nil))

def swapped : Route [.formula, .formula] .formula :=
  .apply .inequality (.cons (.input (.there .here)) (.cons (.input .here) .nil))

def annotated : Route [.name, .formula] .record :=
  .apply .annotated (.cons (.input .here) (.cons (.input (.there .here)) .nil))

theorem formula_slot_cannot_supply_name
    (position : ConstructionVariable [Kind.formula] Kind.name) : False := by
  cases position with
  | there impossible => nomatch impossible

/-- One test packet contains the actual source action, its prepared postfix
code, input values, and the independently evaluated expected value. -/
def packet {context : List Kind} {output : Kind} (name : String)
    (route : Route context output) (values : FamilyList algebra.Object context) : Term :=
  let action := compile encoding route
  .application "GrammarConstructorActionCaseV1"
    [.symbol name, .natural context.length, action.encode, action.encodeCode,
      .application "Slots" (encodeValues encoding.value values),
      OpenConstructionRoute.evaluate algebra values route]

/-- Interleaved literal slots exercise the source-row relocation independently
of the native runner's production layout. This is a compiler fixture only. -/
def punctuatedRow : List StructuralAtom :=
  [.terminal "(" "open", .nonterminal "left" "Formula" "formula",
    .terminal "!=" "unequal", .nonterminal "right" "Formula" "formula",
    .terminal ")" "close"]

def formulaSort : String → Kind := fun _ => .formula

def rowPacket {output : Kind} (name : String) (row : List StructuralAtom)
    (route : Route ((childSorts row).map formulaSort) output)
    (values : FamilyList algebra.Object ((childSorts row).map formulaSort)) : Term :=
  let action := compileWithSlots encoding (parserSlot formulaSort row) route
  .application "GrammarConstructorActionCaseV1"
    [.symbol name, .natural row.length, action.encode, action.encodeCode,
      .application "Slots" (parserValues formulaSort encoding.value
        (fun token _ => .string token) row values),
      OpenConstructionRoute.evaluate algebra values route]

/-- Dense child indices would read punctuation instead of operands. -/
theorem unrelocated_action_is_wrong :
    (compile encoding inequality).execute
      (parserValues formulaSort encoding.value (fun token _ => .string token) punctuatedRow
        (.cons (.symbol "X") (.cons (.symbol "Y") .nil))) ≠
      some (.application "≉" [.symbol "X", .symbol "Y"]) := by
  intro equal
  change some (Term.application "≉" [.string "(", .symbol "X"]) =
    some (Term.application "≉" [.symbol "X", .symbol "Y"]) at equal
  cases equal

def cases : List Term :=
  [packet "inequality" inequality
      (.cons (.symbol "X") (.cons (.symbol "Y") .nil)),
    packet "nested" nested
      (.cons (.application "X" [])
        (.cons (.application "p" [.symbol "X"])
          (.cons (.application "q" [.symbol "X"]) .nil))),
    packet "duplicate" duplicate (.cons (.symbol "same") .nil),
    packet "swapped" swapped
      (.cons (.symbol "left") (.cons (.symbol "right") .nil)),
    packet "slot" (.input .here : Route [.formula] .formula)
      (.cons (.application "=" [.symbol "X", .symbol "Y"]) .nil),
    packet "empty-constant" (.source (.application "Empty" []) : Route [] .formula) .nil,
    packet "string-constant" (.source (.string "space \"quote\" λ") : Route [] .formula) .nil,
    packet "annotated" annotated
      (.cons (.string "quoted name") (.cons (.application "!" [.natural 17]) .nil)),
    rowPacket "punctuated" punctuatedRow inequality
      (.cons (.symbol "X") (.cons (.symbol "Y") .nil)),
    rowPacket "punctuation-only" [.terminal "(" "open", .terminal ")" "close"]
      (.source (.application "Empty" []) : Route [] .formula) .nil]

def rendered : String :=
  String.intercalate "\n"
    ((cases.map Term.render).mergeSort (fun left right => decide (left ≤ right))) ++ "\n"

end Mettapedia.GSLT.Tools.ExportGrammarConstructorActions

def main : IO Unit :=
  IO.print Mettapedia.GSLT.Tools.ExportGrammarConstructorActions.rendered
