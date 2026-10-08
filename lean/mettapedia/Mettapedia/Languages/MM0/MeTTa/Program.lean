import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.StdLib
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# The pinned MM0 MeTTa program

These packages quote the retained service files, including their exact text
and digest. No checker body is restated here. Lake tracks the files as source
inputs; quotation fails if a digest differs from this qualified version.

The source-reader boundary is the one declared by ProgramQuotation. Program
execution and its MM0 agreement are separate theorems about this data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa

open Mettapedia.Languages.MeTTa.PeTTa
open SpaceSemantics (Program)
open scoped ProgramQuotation

deriving instance DecidableEq for SpaceSemantics.Equation

def kernelSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/kernel.generated.metta"
    sha256 "e78b478b59f0d527f92333d1ceb86d64e100f0d102876ea1cb3ac37b1a020a6e"

def dataSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/data.metta"
    sha256 "79783cec682ee65da5e87844b4eafe4fb40a99e0db455b225769320d54dc60d6"

def serviceSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/service.metta"
    sha256 "5e3fb8b14e74293d594a60a976550eec6ab3c1bca0b5ac3451df62db2dbba1e9"

def streamSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/mm0/stream.metta"
    sha256 "c2c3c71d1bd65e2cda3cf83e412c8bfeaed74acf41391bfd8555707e2bb7b00d"

def program : Program := {
  equations := dataSource.program.equations ++ kernelSource.program.equations ++
    serviceSource.program.equations ++ streamSource.program.equations
  declarations := dataSource.program.declarations ++ kernelSource.program.declarations ++
    serviceSource.program.declarations ++ streamSource.program.declarations
  initializers := dataSource.program.initializers ++ kernelSource.program.initializers ++
    serviceSource.program.initializers ++ streamSource.program.initializers
  facts := dataSource.program.facts ++ kernelSource.program.facts ++
    serviceSource.program.facts ++ streamSource.program.facts
  layout := dataSource.program.layout ++ kernelSource.program.layout ++
    serviceSource.program.layout ++ streamSource.program.layout }

/-- The service loads data, kernel, service and stream in the frontend’s order. -/
theorem program_eq_append :
    program = ((dataSource.program.append kernelSource.program).append
      serviceSource.program).append streamSource.program := by
  simp [program, SpaceSemantics.Program.append, List.append_assoc]

/-- These are projections of the retained source, not additional function bodies. -/
def proofEquation : SpaceSemantics.Equation := kernelSource.program.equations[0]'(by
  exact List.length_pos_iff.mpr (by decide))

def dataAtEquation : SpaceSemantics.Equation := dataSource.program.equations[8]'(by decide)

def listViewEquation : SpaceSemantics.Equation := dataSource.program.equations[3]'(by decide)

def natZeroEquation : SpaceSemantics.Equation := dataSource.program.equations[16]'(by decide)

def natPredEquation : SpaceSemantics.Equation := dataSource.program.equations[17]'(by decide)

def natEqualEquation : SpaceSemantics.Equation := dataSource.program.equations[23]'(by decide)

def vectorSnocEquation : SpaceSemantics.Equation := dataSource.program.equations[11]'(by decide)

def vectorEquation : SpaceSemantics.Equation := dataSource.program.equations[9]'(by decide)

def vectorLoadEquation : SpaceSemantics.Equation := dataSource.program.equations[10]'(by decide)

def clearSpaceEquation : SpaceSemantics.Equation := dataSource.program.equations[12]'(by decide)

def removeRowsEquation : SpaceSemantics.Equation := dataSource.program.equations[13]'(by decide)

def cachedInferEquation : SpaceSemantics.Equation := dataSource.program.equations[15]'(by decide)

def submitEquation : SpaceSemantics.Equation := serviceSource.program.equations[4]'(by decide)

def substEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 58)[57]'(by decide)

def substFunctionEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 59)[58]'(by decide)

def substArgumentEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 60)[59]'(by decide)

def lookupEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 61)[60]'(by decide)

def lookupZeroEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 62)[61]'(by decide)

/-! ## Source-package structure controls -/

theorem only_stream_has_initializer :
    kernelSource.program.initializers = [] ∧ dataSource.program.initializers = [] ∧
      serviceSource.program.initializers = [] ∧
      streamSource.program.initializers = [.expression [.symbol "mm0:stream"]] := by
  decide

theorem proof_is_one_authored_equation :
    program.equations.filter (fun equation => equation.head == "mm0:proof") =
      kernelSource.program.equations.take 1 := by
  decide

theorem proof_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:proof") =
      [proofEquation] := by
  decide

theorem data_at_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:data-at") =
      [dataAtEquation] := by
  decide

theorem proof_formals :
    proofEquation.arguments = [.var "table", .var "definitions", .var "theorems",
      .var "context", .var "hypotheses", .var "witness"] := by
  decide

theorem data_at_formals :
    dataAtEquation.arguments = [.var "items", .var "index"] := by
  decide

theorem list_view_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:list-view") =
      [listViewEquation] := by decide

theorem list_view_formals :
    listViewEquation.arguments = [.expression [.symbol "MM0:L", .var "items"]] := by decide

theorem list_cons_is_data_constructor :
    (Eval.ioHead "List:Cons" || StdLib.known "List:Cons" ||
      program.equations.any (·.head == "List:Cons")) = false := by
  change program.equations.any (·.head == "List:Cons") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem vector_snoc_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:vector-snoc") =
      [vectorSnocEquation] := by decide

theorem vector_snoc_formals :
    vectorSnocEquation.arguments =
      [.expression [.symbol "MM0:Vector", .var "space", .var "size"], .var "value"] := by decide

theorem vector_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:vector") = [vectorEquation] := by decide

theorem vector_formals :
    vectorEquation.arguments = [.expression [.symbol "MM0:L", .var "items"]] := by decide

theorem vector_load_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:vector-load") = [vectorLoadEquation] := by decide

theorem vector_load_formals :
    vectorLoadEquation.arguments = [.var "space", .var "items", .var "index", .var "size"] := by decide

theorem clear_space_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:clear-space") =
      [clearSpaceEquation] := by decide

theorem clear_space_formals : clearSpaceEquation.arguments = [.var "space", .var "pattern"] := by decide

theorem remove_rows_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:remove-rows") =
      [removeRowsEquation] := by decide

theorem remove_rows_formals :
    removeRowsEquation.arguments = [.var "space", .var "rows", .var "index", .var "size"] := by decide

theorem cached_infer_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:infer") =
      [cachedInferEquation] := by decide

theorem cached_infer_formals :
    cachedInferEquation.arguments = [.var "terms", .var "ctx", .var "expression"] := by decide

theorem submit_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:submit") =
      [submitEquation] := by decide

theorem submit_formals : submitEquation.arguments = [.var "command"] := by decide

theorem vector_is_data_constructor :
    (Eval.ioHead "MM0:Vector" || StdLib.known "MM0:Vector" ||
      program.equations.any (·.head == "MM0:Vector")) = false := by
  change program.equations.any (·.head == "MM0:Vector") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem nat_zero_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:nat-zero") =
      [natZeroEquation] := by
  decide

theorem nat_zero_formals : natZeroEquation.arguments = [.var "n"] := by decide

theorem nat_zero_body :
    natZeroEquation.body = .expression [.symbol "==", .var "n", .grounded (.int 0)] := by
  decide

theorem nat_zero_is_computational :
    Eval.argumentIsRaw program "mm0:nat-zero" 0 = false := by
  decide

theorem nat_pred_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:nat-pred") =
      [natPredEquation] := by
  decide

theorem nat_pred_formals : natPredEquation.arguments = [.var "n"] := by decide

theorem nat_pred_body :
    natPredEquation.body = .expression [.symbol "if", natZeroEquation.body,
      .grounded (.int 0), .expression [.symbol "-", .var "n", .grounded (.int 1)]] := by
  decide

theorem nat_equal_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:nat-eq") =
      [natEqualEquation] := by decide

theorem nat_equal_formals : natEqualEquation.arguments = [.var "a", .var "b"] := by decide

theorem nat_equal_body :
    natEqualEquation.body = .expression [.symbol "==", .var "a", .var "b"] := by decide

theorem lookup_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:lookup") =
      [lookupEquation] := by decide

theorem subst_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:subst") =
      [substEquation] := by decide

theorem subst_function_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:subst-function") =
      [substFunctionEquation] := by decide

theorem subst_argument_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:subst-argument") =
      [substArgumentEquation] := by decide

theorem subst_formals : substEquation.arguments = [.var "expression", .var "values"] := by decide

theorem subst_function_formals :
    substFunctionEquation.arguments = [.var "valueInput", .var "x", .var "values"] := by decide

theorem subst_argument_formals :
    substArgumentEquation.arguments = [.var "f", .var "valueInput"] := by decide

theorem term_is_data_constructor :
    (Eval.ioHead "MM0:Term" || StdLib.known "MM0:Term" ||
      program.equations.any (·.head == "MM0:Term")) = false := by
  change program.equations.any (·.head == "MM0:Term") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem app_is_data_constructor :
    (Eval.ioHead "MM0:App" || StdLib.known "MM0:App" ||
      program.equations.any (·.head == "MM0:App")) = false := by
  change program.equations.any (·.head == "MM0:App") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem lookup_zero_equation_is_unique :
    program.equations.filter (fun equation => equation.head == "mm0:lookup-zero") =
      [lookupZeroEquation] := by decide

theorem lookup_formals : lookupEquation.arguments = [.var "valueInput", .var "i"] := by decide

theorem lookup_zero_formals :
    lookupZeroEquation.arguments = [.var "conditionInput", .var "h", .var "t", .var "i"] := by decide

theorem some_is_data_constructor :
    (Eval.ioHead "Some" || StdLib.known "Some" ||
      program.equations.any (·.head == "Some")) = false := by
  change program.equations.any (·.head == "Some") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem list_is_data_constructor :
    (Eval.ioHead "MM0:L" || StdLib.known "MM0:L" ||
      program.equations.any (·.head == "MM0:L")) = false := by
  change program.equations.any (·.head == "MM0:L") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem inferred_is_data_constructor :
    (Eval.ioHead "MM0:Inferred" || StdLib.known "MM0:Inferred" ||
      program.equations.any (·.head == "MM0:Inferred")) = false := by
  change program.equations.any (·.head == "MM0:Inferred") = false
  simp only [program, kernelSource, dataSource, serviceSource, streamSource,
    List.any_append, Bool.or_eq_false_iff]
  repeat' constructor <;> decide

theorem authored_heads_are_not_native_intrinsics :
    (program.equations.map (·.head)).all
      (fun head => !StdLib.known head) = true := by
  simp only [program, List.map_append, List.all_append, Bool.and_eq_true]
  repeat' constructor <;> decide

/-- The retained files require no computed case/let/equation patterns. This
checks nested patterns as well, including patterns in branches never reached
by the corpus. It does not claim that the source model covers active patterns. -/
theorem pinned_patterns_are_passive : Eval.constructorPatterns program = true := by
  decide +kernel

end Mettapedia.Languages.MM0.MeTTa
