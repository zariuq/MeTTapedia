import Mettapedia.Languages.Metamath.SourceGSLTOperations

/-!
# Export admitted Metamath source-operation bindings as a dense C program

The emitted table is data for the language-neutral statement program and
streaming transaction APIs.  Numeric operation and field identities are
derived from the validated source-operation presentation; native code does
not select behavior by production-name convention.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTOperationsCExport

open Mettapedia.Languages.Metamath.SourceGSLTOperations

inductive FieldCardinality where
  | exactlyOne
  | oneOrMore
  | zeroOrMore
deriving Repr, DecidableEq, BEq

structure FieldPlan where
  role : FoldRole
  cardinality : FieldCardinality
deriving Repr, DecidableEq, BEq

def foldFieldPlans : FoldContract → List FieldPlan
  | .none => []
  | .one role => [{ role, cardinality := .exactlyOne }]
  | .plus role => [{ role, cardinality := .oneOrMore }]
  | .star role => [{ role, cardinality := .zeroOrMore }]
  | .seq first second => foldFieldPlans first ++ foldFieldPlans second

def allFoldRoles : List FoldRole :=
  [.label, .symbol, .proofStep, .compressedWord, .includePath,
   .scopeOpen, .scopeClose]

def roleIndex : FoldRole → Nat
  | .label => 0
  | .symbol => 1
  | .proofStep => 2
  | .compressedWord => 3
  | .includePath => 4
  | .scopeOpen => 5
  | .scopeClose => 6

structure OperationPlan where
  operation : SourceOperation
  productionName : String
  fields : List FieldPlan
deriving Repr, DecidableEq, BEq

def operationPlan (operation : SourceOperation) : OperationPlan :=
  match shiftBindings.find? fun binding => binding.operation == operation with
  | some binding =>
      { operation
        productionName := ""
        fields := [{ role := binding.role, cardinality := .exactlyOne }] }
  | none =>
      match compiledNodeBindings.find? fun binding =>
          binding.operation == operation with
      | some binding =>
          { operation
            productionName := binding.source.label
            fields := foldFieldPlans binding.contract }
      | none =>
          { operation, productionName := "", fields := [] }

def operationPlans : List OperationPlan :=
  allSourceOperations.map operationPlan

theorem operationPlan_count : operationPlans.length = 12 := by
  decide

theorem fieldPlan_count :
    (operationPlans.flatMap (·.fields)).length = 21 := by
  decide

theorem role_indices_in_bounds :
    ∀ role ∈ allFoldRoles, roleIndex role < allFoldRoles.length := by
  decide

private def cString (value : String) : String :=
  "\"" ++ value ++ "\""

private def uint32 (value : Nat) : String :=
  s!"UINT32_C({value})"

private def renderRole (role : FoldRole) : String :=
  "    " ++ cString role.atom

private def renderCardinality : FieldCardinality → String × String
  | .exactlyOne => (uint32 1, uint32 1)
  | .oneOrMore => (uint32 1, "CETTA_STATEMENT_UNBOUNDED")
  | .zeroOrMore => (uint32 0, "CETTA_STATEMENT_UNBOUNDED")

private def renderField (field : FieldPlan) : String :=
  let bounds := renderCardinality field.cardinality
  "    { " ++ uint32 (roleIndex field.role) ++ ", " ++ bounds.1 ++
    ", " ++ bounds.2 ++ " }"

private def renderOperations : List OperationPlan → Nat → List String
  | [], _ => []
  | plan :: rest, firstField =>
      let row :=
        "    { " ++ cString plan.operation.atom ++ ", " ++
          cString plan.operation.checkerEffect ++ ", " ++
          cString plan.productionName ++ ", " ++ uint32 firstField ++
          ", " ++ uint32 plan.fields.length ++ " }"
      row :: renderOperations rest (firstField + plan.fields.length)

private def renderArray (rows : List String) : String :=
  String.intercalate ",\n" rows

def renderedCHeader : String :=
  let fields := operationPlans.flatMap (·.fields)
  "/* Generated from the admitted Metamath source operation presentation. */\n" ++
  "#ifndef CETTA_METAMATH_SOURCE_PROGRAM_V1_GENERATED_H\n" ++
  "#define CETTA_METAMATH_SOURCE_PROGRAM_V1_GENERATED_H\n\n" ++
  "#include <stdint.h>\n" ++
  "#include \"statement_program.h\"\n\n" ++
  "static const char *const cetta_metamath_source_roles_v1[] = {\n" ++
  renderArray (allFoldRoles.map renderRole) ++ "\n};\n\n" ++
  "static const CettaStatementFieldPlan " ++
  "cetta_metamath_source_fields_v1[] = {\n" ++
  renderArray (fields.map renderField) ++ "\n};\n\n" ++
  "static const CettaStatementOperationPlan " ++
  "cetta_metamath_source_operations_v1[] = {\n" ++
  renderArray (renderOperations operationPlans 0) ++ "\n};\n\n" ++
  "static const CettaStatementProgram cetta_metamath_source_program_v1 = {\n" ++
  "    cetta_metamath_source_roles_v1, UINT32_C(7),\n" ++
  "    cetta_metamath_source_fields_v1, UINT32_C(21),\n" ++
  "    cetta_metamath_source_operations_v1, UINT32_C(12)\n" ++
  "};\n\n" ++
  "#endif\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      if validateSourceOperationPresentation then
        if outputPath == "-" then
          IO.print renderedCHeader
        else
          IO.FS.writeFile outputPath renderedCHeader
          IO.println s!"wrote {renderedCHeader.toUTF8.size} C-header bytes"
        pure 0
      else
        IO.eprintln "Metamath source-operation presentation is invalid"
        pure 1
  | _ =>
      IO.eprintln "usage: SourceGSLTOperationsCExport <output.h>"
      pure 2

end Mettapedia.Languages.Metamath.SourceGSLTOperationsCExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTOperationsCExport.main arguments
