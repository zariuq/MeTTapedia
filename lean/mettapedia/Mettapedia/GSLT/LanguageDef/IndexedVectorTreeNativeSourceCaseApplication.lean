import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedVariableArguments

/-!
# Applying the original case variables in their complete source contexts

The solved case keeps all eight binders. The branch keeps all ten, including
its original All-W argument and the seven ambient binders. The guarded
variable-spine receiver checks the actual source lookup at each application;
source typing and logical membership are constructed by the common realizer.
The motive and case functions remain arbitrary guarded inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceCaseApplication

open Mettapedia.Logic Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
local infixr:60 " ⇒ " => HOL.Ty.arr
namespace Source
export IndexedVectorTreeNativeSourceReading (context target theory)
end Source
namespace Native
export IndexedVectorTreeNativeSourceReading.Native
  (Base Const N E V W original pairs witness selection lex elementLevel resultLevel separated)
end Native
open Native

abbrev solvedCarrier := Source.target 0
abbrev branchCarrier := Source.target 1
def solvedContext := Source.context 0
def branchContext := Source.context 1

private def variableAt (Γ : HOL.Ctx Base) (carrier : HOL.Ty Base) (index : Fin Γ.length)
    (same : Γ.get index = carrier) : HOL.Var Γ carrier :=
  same ▸ HOL.Var.ofFin Γ index

def solvedCaseIndex := variableAt solvedCarrier (E ⇒ W) ⟨2,by decide +kernel⟩ (by decide +kernel)
def solvedFieldIndex := variableAt solvedCarrier E ⟨0,by decide +kernel⟩ (by decide +kernel)
def solvedConstructorIndex := variableAt solvedCarrier (E ⇒ E) ⟨4,by decide +kernel⟩ (by decide +kernel)
def solvedMotiveIndex := variableAt solvedCarrier (E ⇒ W ⇒ .prop) ⟨5,by decide +kernel⟩ (by decide +kernel)

def branchCaseIndex := variableAt branchCarrier (N ⇒ V ⇒ W ⇒ W) ⟨3,by decide +kernel⟩ (by decide +kernel)
def branchLengthIndex := variableAt branchCarrier N ⟨2,by decide +kernel⟩ (by decide +kernel)
def branchVectorIndex := variableAt branchCarrier V ⟨1,by decide +kernel⟩ (by decide +kernel)
def branchAllIndex := variableAt branchCarrier W ⟨0,by decide +kernel⟩ (by decide +kernel)
def branchConstructorIndex := variableAt branchCarrier (N ⇒ V ⇒ E) ⟨5,by decide +kernel⟩ (by decide +kernel)
def branchMotiveIndex := variableAt branchCarrier (E ⇒ W ⇒ .prop) ⟨7,by decide +kernel⟩ (by decide +kernel)

def solvedPositions : VariablePositions solvedCarrier := [⟨E,solvedFieldIndex⟩]
def branchPositions : VariablePositions branchCarrier :=
  [⟨N,branchLengthIndex⟩,⟨V,branchVectorIndex⟩,⟨W,branchAllIndex⟩]

def solvedResultSource : CTm Tower.Head solvedCarrier.length :=
  .app (.var solvedMotiveIndex.toFin) (.app (.var solvedConstructorIndex.toFin) (.var solvedFieldIndex.toFin))
def branchResultSource : CTm Tower.Head branchCarrier.length :=
  .app (.var branchMotiveIndex.toFin)
    (.app (.app (.var branchConstructorIndex.toFin) (.var branchLengthIndex.toFin)) (.var branchVectorIndex.toFin))

def solvedType := solvedContext.source.lookup solvedCaseIndex.toFin
def branchType := branchContext.source.lookup branchCaseIndex.toFin

def solvedArguments? (roots : List (HOL.ClosedFormula Const)) :=
  SuppliedArguments.readVariables? roots solvedContext solvedPositions solvedType (E ⇒ W)
def branchArguments? (roots : List (HOL.ClosedFormula Const)) :=
  SuppliedArguments.readVariables? roots branchContext branchPositions branchType (N ⇒ V ⇒ W ⇒ W)

theorem solved_empty_received : (solvedArguments? []).isSome = true := by decide +kernel
theorem branch_empty_received : (branchArguments? []).isSome = true := by decide +kernel

def solvedEmpty := (solvedArguments? []).get solved_empty_received
def branchEmpty := (branchArguments? []).get branch_empty_received

theorem solved_empty_type : solvedEmpty.target = solvedResultSource := by decide +kernel
theorem solved_empty_carrier : solvedEmpty.resultCarrier = W := by decide +kernel
theorem branch_empty_type : branchEmpty.target = branchResultSource := by decide +kernel
theorem branch_empty_carrier : branchEmpty.resultCarrier = W := by decide +kernel

theorem solvedShape : VariablesSupply solvedContext solvedPositions solvedType (E ⇒ W) solvedResultSource W := by
  simpa only [solved_empty_type, solved_empty_carrier] using solvedEmpty.shape
theorem branchShape : VariablesSupply branchContext branchPositions branchType (N ⇒ V ⇒ W ⇒ W) branchResultSource W := by
  simpa only [branch_empty_type, branch_empty_carrier] using branchEmpty.shape

theorem solved_arguments_received (roots : List (HOL.ClosedFormula Const)) :
    (solvedArguments? roots).isSome = true := SuppliedArguments.readVariables?_complete solvedShape
theorem branch_arguments_received (roots : List (HOL.ClosedFormula Const)) :
    (branchArguments? roots).isSome = true := SuppliedArguments.readVariables?_complete branchShape

def solvedArguments (roots : List (HOL.ClosedFormula Const)) :=
  (solvedArguments? roots).get (solved_arguments_received roots)
def branchArguments (roots : List (HOL.ClosedFormula Const)) :=
  (branchArguments? roots).get (branch_arguments_received roots)

theorem solved_target_type (roots : List (HOL.ClosedFormula Const)) :
    (solvedArguments roots).target = solvedResultSource :=
  (VariablesSupply.unique (solvedArguments roots).shape solvedShape).1
theorem solved_target_carrier (roots : List (HOL.ClosedFormula Const)) :
    (solvedArguments roots).resultCarrier = W :=
  (VariablesSupply.unique (solvedArguments roots).shape solvedShape).2
theorem branch_target_type (roots : List (HOL.ClosedFormula Const)) :
    (branchArguments roots).target = branchResultSource :=
  (VariablesSupply.unique (branchArguments roots).shape branchShape).1
theorem branch_target_carrier (roots : List (HOL.ClosedFormula Const)) :
    (branchArguments roots).resultCarrier = W :=
  (VariablesSupply.unique (branchArguments roots).shape branchShape).2

def solvedSpine (roots : List (HOL.ClosedFormula Const)) :=
  (solvedArguments roots).argumentsAt solvedResultSource W (solved_target_type roots) (solved_target_carrier roots)
def branchSpine (roots : List (HOL.ClosedFormula Const)) :=
  (branchArguments roots).argumentsAt branchResultSource W (branch_target_type roots) (branch_target_carrier roots)

def solvedApplication (roots : List (HOL.ClosedFormula Const)) :=
  (solvedSpine roots).apply (GuardedRealizer.ofVariable roots solvedContext solvedCaseIndex)
def branchApplication (roots : List (HOL.ClosedFormula Const)) :=
  (branchSpine roots).apply (GuardedRealizer.ofVariable roots branchContext branchCaseIndex)

theorem solvedApplication_free (roots : List (HOL.ClosedFormula Const)) :
    (solvedApplication roots).Free :=
  (solvedSpine roots).apply_free _
    ((solvedArguments roots).argumentsAt_free _ _ _ _)
    (GuardedRealizer.ofVariable_free roots solvedContext solvedCaseIndex)

theorem branchApplication_free (roots : List (HOL.ClosedFormula Const)) :
    (branchApplication roots).Free :=
  (branchSpine roots).apply_free _
    ((branchArguments roots).argumentsAt_free _ _ _ _)
    (GuardedRealizer.ofVariable_free roots branchContext branchCaseIndex)

def solvedResultPredicate : HOL.Term Const solvedCarrier (W ⇒ .prop) :=
  .app (.var solvedMotiveIndex) (.app (.var solvedConstructorIndex) (.var solvedFieldIndex))
def branchResultPredicate : HOL.Term Const branchCarrier (W ⇒ .prop) :=
  .app (.var branchMotiveIndex)
    (.app (.app (.var branchConstructorIndex) (.var branchLengthIndex)) (.var branchVectorIndex))

theorem solved_application_predicate (roots : List (HOL.ClosedFormula Const)) :
    (solvedApplication roots).predicate = solvedResultPredicate :=
  Reader.term_unique (solvedApplication roots).typeRead
    (.application (.var solvedMotiveIndex) (.application (.var solvedConstructorIndex) (.var solvedFieldIndex)))

theorem branch_application_predicate (roots : List (HOL.ClosedFormula Const)) :
    (branchApplication roots).predicate = branchResultPredicate :=
  Reader.term_unique (branchApplication roots).typeRead
    (.application (.var branchMotiveIndex)
      (.application (.application (.var branchConstructorIndex) (.var branchLengthIndex)) (.var branchVectorIndex)))

theorem complete_solved_source_retained : solvedContext.source = IndexedVectorTreeNativeSourceReading.checkedSource 0 := rfl
theorem complete_branch_source_retained : branchContext.source = IndexedVectorTreeNativeSourceReading.checkedSource 1 := rfl
theorem solved_context_size : solvedCarrier.length = 8 := by decide +kernel
theorem branch_context_size : branchCarrier.length = 10 := by decide +kernel

#print axioms solved_arguments_received
#print axioms branch_arguments_received
#print axioms solvedApplication_free
#print axioms branchApplication_free
#print axioms solved_application_predicate
#print axioms branch_application_predicate

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceCaseApplication
