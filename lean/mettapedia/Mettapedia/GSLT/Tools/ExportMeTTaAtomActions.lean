import Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler
import Mettapedia.GSLT.Tools.MeTTaAtomFixtureRender

/-!
# Native controls exported from typed atom construction actions

The packets use the existing action-test protocol. Both action and postfix
code are derived from the typed route; the expected atom is evaluated from
that route rather than copied from native execution. These are compiler and
executor controls for the generic atom-construction operations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Tools.ExportMeTTaAtomActions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.Parsing
open MeTTaAtomConstruction

def app (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

def packet {context : List Kind} {output : Kind} (name : String)
    (route : Action context output) (values : FamilyList Value context) : Atom :=
  let action := MeTTaAtomActionCompiler.compile route
  app "GrammarConstructorActionCaseV1"
    [.symbol name, .grounded (.int context.length),
     MeTTaAtomActionCompiler.encodeAction action, MeTTaAtomActionCompiler.encodeCode action,
     app "Slots" (MeTTaAtomActionCompiler.encodeValues values),
     MeTTaAtomActionCompiler.encodeValue output (Action.run route values)]

/-- Rejection controls keep the source action well typed but supply external
values outside the primitive's admitted operand domain. -/
def rejectPacket {context : List Kind} {output : Kind} (name : String)
    (route : Action context output) (slots : List Atom)
    (_rejected : MeTTaAtomActionCompiler.execute slots
      (MeTTaAtomActionCompiler.compile route) = none) : Atom :=
  let action := MeTTaAtomActionCompiler.compile route
  app "GrammarConstructorActionRejectV1"
    [.symbol name, .grounded (.int context.length),
     MeTTaAtomActionCompiler.encodeAction action, MeTTaAtomActionCompiler.encodeCode action,
     app "Slots" slots, .symbol "Rejected"]

def integerAction : Action [.integer] .atom :=
  .apply .integer (.cons (.input .here) .nil)

def textAppendAction : Action [.text, .text] .text :=
  .apply .textAppend (.cons (.input .here) (.cons (.input (.there .here)) .nil))

def cases : List Atom :=
  [packet "expression-head" applicationAction
      (.cons (app "f" [.symbol "x"])
        (.cons [.symbol "y", .symbol "z"] .nil)),
   packet "nested-application" MeTTaAtomConstruction.Examples.nestedApplication
      (.cons (.symbol "f") (.cons (.symbol "g") (.cons (.symbol "x") .nil))),
   packet "ordered-duplicates" appendAction
      (.cons [.symbol "a", .symbol "b"] (.cons [.symbol "a"] .nil)),
   packet "empty-sequence" (.apply .empty .nil : Action [] .atoms) .nil,
   packet "symbol-from-text" symbolAction (.cons "source_name" .nil),
   packet "string-identity" stringAction (.cons "a \"quoted\" string" .nil),
   packet "text-append" textAppendAction (.cons "alpha" (.cons "λ" .nil)),
   packet "integer-positive" integerAction (.cons 42 .nil),
   packet "integer-negative" integerAction (.cons (-17) .nil),
   rejectPacket "symbol-wrong-kind" symbolAction [.symbol "not-a-string"] rfl,
   rejectPacket "application-wrong-tail" applicationAction
      [.symbol "f", .grounded (.string "not-an-expression")] rfl,
   rejectPacket "append-wrong-kind" appendAction
      [.expression [], .grounded (.string "not-an-expression")] rfl,
   rejectPacket "text-append-wrong-kind" textAppendAction
      [.grounded (.string "left"), .symbol "not-a-string"] rfl]

def rendered : Except String String := do
  let lines ← MeTTaAtomFixtureRender.renderList cases
  return String.intercalate "\n"
    (lines.mergeSort (fun left right => decide (left ≤ right))) ++ "\n"

end Mettapedia.GSLT.Tools.ExportMeTTaAtomActions

def main : IO Unit :=
  match Mettapedia.GSLT.Tools.ExportMeTTaAtomActions.rendered with
  | .ok text => IO.print text
  | .error message => throw (IO.userError message)
