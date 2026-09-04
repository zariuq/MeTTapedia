import Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan

/-!
# Canonical wire for the MM2 syntax-tree elaboration plan

The native reader consumes this finite plan as data.  Each row comes directly
from the proved elaboration inventory; native code does not carry a second
label-to-operation table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlanWire

open Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlan

def instructionName : Instruction -> String
  | .lexicalScalar => "MM2ElabLexicalScalarV1"
  | .programEmpty => "MM2ElabProgramEmptyV1"
  | .programDropScalar => "MM2ElabProgramDropScalarV1"
  | .programDropUnit => "MM2ElabProgramDropUnitV1"
  | .programCons => "MM2ElabProgramConsV1"
  | .programFromUnit => "MM2ElabProgramFromUnitV1"
  | .atomsEmpty => "MM2ElabAtomsEmptyV1"
  | .atomsDropScalar => "MM2ElabAtomsDropScalarV1"
  | .atomsDropUnit => "MM2ElabAtomsDropUnitV1"
  | .atomsCons => "MM2ElabAtomsConsV1"
  | .atomExpression => "MM2ElabAtomExpressionV1"
  | .atomIdentity => "MM2ElabAtomIdentityV1"
  | .atomSymbolHeadTail => "MM2ElabAtomSymbolHeadTailV1"
  | .atomSymbolCodepoints => "MM2ElabAtomSymbolCodepointsV1"
  | .atomVariableCodepoints => "MM2ElabAtomVariableCodepointsV1"
  | .commentLine => "MM2ElabCommentLineV1"
  | .commentEOF => "MM2ElabCommentEofV1"
  | .codepointsEmpty => "MM2ElabCodepointsEmptyV1"
  | .codepointsCons => "MM2ElabCodepointsConsV1"
  | .codepointsIdentity => "MM2ElabCodepointsIdentityV1"
  | .codepointsQuote => "MM2ElabCodepointsQuoteV1"
  | .codepointsEscape => "MM2ElabCodepointsEscapeV1"

def allInstructions : List Instruction := [
  .lexicalScalar,
  .programEmpty,
  .programDropScalar,
  .programDropUnit,
  .programCons,
  .programFromUnit,
  .atomsEmpty,
  .atomsDropScalar,
  .atomsDropUnit,
  .atomsCons,
  .atomExpression,
  .atomIdentity,
  .atomSymbolHeadTail,
  .atomSymbolCodepoints,
  .atomVariableCodepoints,
  .commentLine,
  .commentEOF,
  .codepointsEmpty,
  .codepointsCons,
  .codepointsIdentity,
  .codepointsQuote,
  .codepointsEscape
]

theorem instruction_names_nodup :
    (allInstructions.map instructionName).Nodup := by
  decide +kernel

private def quoteLabel (label : String) : String :=
  "\"" ++ label ++ "\""

def renderRow (planRow : PlanRow) : String :=
  "(MM2ElaborationRowV1 " ++ quoteLabel planRow.label ++ " " ++
    toString planRow.arity ++ " " ++ instructionName planRow.instruction ++ ")"

private def renderRows : List PlanRow -> String
  | [] => "LNil"
  | planRow :: rest =>
      "(LCons " ++ renderRow planRow ++ " " ++ renderRows rest ++ ")"

/-- Canonical generated wire text for the complete elaboration plan. -/
def wire : String :=
  "(MM2ElaborationPlanV1 \"MM2MaximalTokenElaborationPlanV1\" " ++
    renderRows rows ++ ")\n"

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

theorem rendered_row_inventory : (rows.map renderRow).length = 43 := by
  decide

/-- Removing a plan row changes both its cardinality and its source coverage;
the shortened plan cannot authenticate as the complete plan. -/
theorem removing_last_row_breaks_inventory : rows.dropLast.length = 42 := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms instruction_names_nodup
#print axioms wire_nonempty
#print axioms rendered_row_inventory
#print axioms removing_last_row_breaks_inventory

end Mettapedia.Languages.ProcessCalculi.MORK.MM2MaximalTokenElaborationPlanWire
