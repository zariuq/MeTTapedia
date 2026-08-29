import Mettapedia.GSLT.LanguageDef.StructuredC
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.StructuralModal.Formula

/-!
# OSLF and native-type diagnostics for StructuredC

The modal construction consumes the authored `StructuredC.language` and an
explicit primitive relation environment.  The positive and faulting examples
exercise distinct operational fibres; the negative example confirms that a
missing primitive fact cannot invent execution.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuredCNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.StructuralModal
open Mettapedia.GSLT.LanguageDef.StructuredC

theorem return_expression_crossing :
    ("structured-c:return", "Expression", "Statement") ∈
      unaryCrossings language := by
  decide

theorem named_type_crossing :
    ("structured-c:type-named", "Identifier", "CType") ∈
      unaryCrossings language := by
  decide

theorem no_value_statement_crossing :
    ("structured-c:invented-value-statement", "Value", "Statement") ∉
      unaryCrossings language := by
  decide

private def token (name : String) : Pattern := a name
private def environmentZero : Pattern := a "structured-c:environment-empty"
private def receiptZero : Pattern := a "structured-c:receipt-ready"
private def demoVariable : Pattern :=
  a "structured-c:identifier" [token "structured-c:demo-variable-name"]
private def value : Pattern := a "structured-c:value-unit"
private def environmentOne : Pattern :=
  a "structured-c:environment-bind" [demoVariable, value, environmentZero]
private def expression : Pattern :=
  a "structured-c:expression-constant" [value]
private def statement : Pattern :=
  a "structured-c:assign" [demoVariable, expression]
private def statementList : Pattern :=
  consStatement statement nilStatements
private def fault : Pattern :=
  a "structured-c:fault-engine" [token "structured-c:demo-fault-message"]

/-- A finite adequate primitive handler for one successful assignment. -/
def valueRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "StructuredCEvaluate" then
      [[expression, environmentZero, receiptZero, evaluationValue value,
        environmentZero, receiptZero]]
    else if relation == "StructuredCStore" then
      [[environmentZero, demoVariable, value, environmentOne]]
    else
      []

/-- A finite primitive handler for the explicit fault branch of the same
expression. -/
def faultRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "StructuredCEvaluate" then
      [[expression, environmentZero, receiptZero, evaluationFault fault,
        environmentZero, receiptZero]]
    else
      []

def emptyRelationEnv : RelationEnv where
  tuples := fun _relation _arguments => []

def structuredCOSLF :=
  langOSLFUsing valueRelationEnv language "Config"

/-- A genuinely derived spatial-behavioral native type: one step reaches an
empty continuation, a well-shaped environment extension, and a receipt. -/
def assignmentCompletionFormula : Formula :=
  .diamond (.headed "structured-c:run" [
    .headed "structured-c:statements-nil" [],
    .headed "structured-c:environment-bind" [.top, .top, .top],
    .headed "structured-c:receipt-ready" []])

theorem structuredC_galois :
    GaloisConnection
      (langDiamondUsing valueRelationEnv language)
      (langBoxUsing valueRelationEnv language) :=
  langGaloisUsing valueRelationEnv language

theorem assignment_value_step_exact :
    rewriteAt (engineBasePremises valueRelationEnv) language 1
        (run statementList environmentZero receiptZero) =
      [run nilStatements environmentOne receiptZero] := by
  decide +kernel

theorem assignment_inhabits_derived_native_type :
    satisfiesUsing valueRelationEnv language assignmentCompletionFormula
      (run statementList environmentZero receiptZero) := by
  have executable :
      run nilStatements environmentOne receiptZero ∈
        rewriteAt (engineBasePremises valueRelationEnv) language 1
          (run statementList environmentZero receiptZero) := by
    rw [assignment_value_step_exact]
    simp
  have reduction :
      langReducesUsing valueRelationEnv language
        (run statementList environmentZero receiptZero)
        (run nilStatements environmentOne receiptZero) :=
    (langReducesUsing_iff_execUsing valueRelationEnv language _ _).2
      ⟨1, executable⟩
  refine ⟨⟨((run statementList environmentZero receiptZero),
      (run nilStatements environmentOne receiptZero)), reduction⟩, rfl, ?_⟩
  refine ⟨[nilStatements, environmentOne, receiptZero], rfl, ?_⟩
  refine ⟨⟨[], rfl, trivial⟩, ?_⟩
  constructor
  · refine ⟨[demoVariable, value, environmentZero], rfl, ?_⟩
    simp [satisfiesAllOver, satisfiesOver]
  · constructor
    · exact ⟨[], rfl, trivial⟩
    · trivial

theorem assignment_fault_step_exact :
    rewriteAt (engineBasePremises faultRelationEnv) language 1
        (run statementList environmentZero receiptZero) =
      [halted (a "structured-c:outcome-fault" [fault])
        environmentZero receiptZero] := by
  decide +kernel

theorem assignment_without_handler_is_stuck :
    rewriteAt (engineBasePremises emptyRelationEnv) language 1
        (run statementList environmentZero receiptZero) = [] := by
  decide +kernel

theorem halted_is_normal :
    rewriteAt (engineBasePremises valueRelationEnv) language 1
        (halted (a "structured-c:outcome-return" [value])
          environmentOne receiptZero) = [] := by
  decide +kernel

#print axioms return_expression_crossing
#print axioms structuredC_galois
#print axioms assignment_value_step_exact
#print axioms assignment_inhabits_derived_native_type
#print axioms assignment_fault_step_exact
#print axioms assignment_without_handler_is_stuck

end Mettapedia.GSLT.LanguageDef.StructuredCNTT
