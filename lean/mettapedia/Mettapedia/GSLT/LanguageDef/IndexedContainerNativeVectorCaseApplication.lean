import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseContext
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerAnnotatedMethods
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedVariableArguments
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedContextAbstraction

/-!
# Application of an original supplied constructor case

An ambient case function precedes the original five fields and three induction
hypotheses. The generated dependent argument spines retain their exact source
domains and guards. A nested field contributes its whole All bundle as one
argument. This constructs a method-application clause; it does not synthesize
a case function for an arbitrary motive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseApplication

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedContainerNativeVectorMethodReading
local infixr:60 " ⇒ " => HOL.Ty.arr
private abbrev caseCarrier := IndexedContainerNativeVectorCaseContext.carrier
private abbrev caseContext := IndexedContainerNativeVectorCaseContext.context
private abbrev methodCarrier := IndexedContainerNativeVectorCaseContext.methodCarrier

def variableAt (type : HOL.Ty Base) (position : Fin caseCarrier.length) (same : caseCarrier.get position = type) :
    HOL.Var caseCarrier type := same ▸ HOL.Var.ofFin caseCarrier position

def methodIndex : HOL.Var caseCarrier methodCarrier := variableAt _ 8 (by decide +kernel)
def lengthIndex : HOL.Var caseCarrier N := variableAt _ 7 (by decide +kernel)
def beforeIndex : HOL.Var caseCarrier E := variableAt _ 6 (by decide +kernel)
def tagIndex : HOL.Var caseCarrier E := variableAt _ 5 (by decide +kernel)
def vectorIndex : HOL.Var caseCarrier V := variableAt _ 4 (by decide +kernel)
def afterIndex : HOL.Var caseCarrier E := variableAt _ 3 (by decide +kernel)
def beforeIH : HOL.Var caseCarrier W := variableAt _ 2 (by decide +kernel)
def bundleIndex : HOL.Var caseCarrier W := variableAt _ 1 (by decide +kernel)
def afterIH : HOL.Var caseCarrier W := variableAt _ 0 (by decide +kernel)
def constructorIndex : HOL.Var caseCarrier constructorCarrier := variableAt _ 9 (by decide +kernel)
def motiveIndex : HOL.Var caseCarrier motiveCarrier := variableAt _ 10 (by decide +kernel)

def methodValue (roots : List (HOL.ClosedFormula Const)) :=
  GuardedRealizer.ofVariable roots caseContext methodIndex

def fieldPositions : VariablePositions caseCarrier :=
  [⟨N, lengthIndex⟩, ⟨E, beforeIndex⟩, ⟨E, tagIndex⟩, ⟨V, vectorIndex⟩, ⟨E, afterIndex⟩]

def inductionPositions : VariablePositions caseCarrier := [⟨W, beforeIH⟩, ⟨W, bundleIndex⟩, ⟨W, afterIH⟩]

def expectedHypotheses : List (CTm Tower.Head caseCarrier.length) :=
  [.app (.var 10) (.var 6),
   NativeVectorAll.Annotated.Formation.allType resultLevel (.var 11) (.var 10) (.var 7) (.var 4),
   .app (.var 10) (.var 3)]

def expectedConstructor : CTm Tower.Head caseCarrier.length :=
  .app (.app (.app (.app (.app (.var 9) (.var 7)) (.var 6)) (.var 5)) (.var 4)) (.var 3)

def expectedConclusion : CTm Tower.Head caseCarrier.length := .app (.var 10) expectedConstructor
def expectedResidual : CTm Tower.Head caseCarrier.length :=
  .pi (.app (.var 10) (.var 6))
    (.pi (NativeVectorAll.Annotated.Formation.allType resultLevel (.var 12) (.var 11) (.var 8) (.var 5))
      (.pi (.app (.var 12) (.var 5)) (expectedConclusion.rename (fun index => index.succ.succ.succ))))

theorem residual_generated : expectedResidual = IndexedContainerAnnotated.hypotheses expectedHypotheses expectedConclusion := by
  simp only [expectedHypotheses, IndexedContainerAnnotated.hypotheses,
    List.map_cons, List.map_nil, NativeVectorAll.Annotated.Formation.allType_rename, CTm.rename, CTm.rename_comp]
  rfl
abbrev residualCarrier := W ⇒ W ⇒ W ⇒ W

theorem fields_shape : VariablesSupply caseContext fieldPositions
    (caseContext.source.lookup methodIndex.toFin) methodCarrier expectedResidual residualCarrier := by
  refine VariablesSupply.step (context := caseContext) (A := .const NativeNaturalVectorFamilies.natName) lengthIndex (by rfl) ?_
  refine VariablesSupply.step (context := caseContext) beforeIndex (by rfl) ?_
  refine VariablesSupply.step (context := caseContext) tagIndex (by rfl) ?_
  refine VariablesSupply.step (context := caseContext) vectorIndex (by rfl) ?_
  refine VariablesSupply.step (context := caseContext) afterIndex (by rfl) ?_
  convert VariablesSupply.done (context := caseContext) expectedResidual residualCarrier using 1
  decide +kernel

theorem induction_shape : VariablesSupply caseContext inductionPositions expectedResidual residualCarrier
    expectedConclusion W := by
  refine VariablesSupply.step (context := caseContext) (A := .app (.var 10) (.var 6)) beforeIH (by rfl) ?_
  refine VariablesSupply.step (context := caseContext) bundleIndex (by rfl) ?_
  refine VariablesSupply.step (context := caseContext) afterIH (by rfl) ?_
  convert VariablesSupply.done (context := caseContext) expectedConclusion W using 1
  decide +kernel

variable (roots : List (HOL.ClosedFormula Const))

def receivedFields := SuppliedArguments.readVariables? roots caseContext fieldPositions
  (caseContext.source.lookup methodIndex.toFin) methodCarrier

theorem fields_accepted : (receivedFields roots).isSome = true := SuppliedArguments.readVariables?_complete fields_shape

def fieldValues := (receivedFields roots).get (fields_accepted roots)

theorem fields_spec : (fieldValues roots).target = expectedResidual ∧
    (fieldValues roots).resultCarrier = residualCarrier :=
  VariablesSupply.unique (fieldValues roots).shape fields_shape

def receivedInduction := SuppliedArguments.readVariables? roots caseContext inductionPositions expectedResidual residualCarrier

theorem induction_accepted : (receivedInduction roots).isSome = true :=
  SuppliedArguments.readVariables?_complete induction_shape

def inductionValues := (receivedInduction roots).get (induction_accepted roots)

theorem induction_spec : (inductionValues roots).target = expectedConclusion ∧
    (inductionValues roots).resultCarrier = W :=
  VariablesSupply.unique (inductionValues roots).shape induction_shape

def fields : Fin (IndexedContainerAnnotated.fieldCount IndexedContainerNativeVectorMethodFormation.code) →
    CTm Tower.Head caseCarrier.length := ![.var 7, .var 6, .var 5, .var 4, .var 3]

theorem field_sources : List.ofFn fields = variableSources fieldPositions := by decide +kernel

def suppliedFields : SuppliedArguments roots caseContext (List.ofFn fields)
    (caseContext.source.lookup methodIndex.toFin) methodCarrier expectedResidual residualCarrier :=
  (fieldValues roots).argumentsAt expectedResidual residualCarrier (fields_spec roots).1 (fields_spec roots).2

def suppliedInduction : SuppliedArguments roots caseContext (variableSources inductionPositions)
    expectedResidual residualCarrier expectedConclusion W :=
  (inductionValues roots).argumentsAt expectedConclusion W (induction_spec roots).1 (induction_spec roots).2

def application := IndexedPositiveContainerAnnotatedMethods.realizeMethod IndexedContainerNativeVectorMethodFormation.code fields
  (suppliedFields roots) (suppliedInduction roots) (methodValue roots)

theorem application_free : (application roots).Free := by
  apply IndexedPositiveContainerAnnotatedMethods.realizeMethod_free
  · exact SuppliedArguments.VariableResult.argumentsAt_free (fieldValues roots) _ _ _ _
  · exact SuppliedArguments.VariableResult.argumentsAt_free (inductionValues roots) _ _ _ _
  · exact GuardedRealizer.ofVariable_free roots caseContext methodIndex

def body : CTm Tower.Head caseCarrier.length :=
  CTm.appSpine
    (IndexedPositiveContainerAnnotatedMethods.applyFields IndexedContainerNativeVectorMethodFormation.code fields (.var 8))
    (variableSources inductionPositions)

def constructorCode : HOL.Term Const caseCarrier E :=
  .app (.app (.app (.app (.app (.var constructorIndex) (.var lengthIndex)) (.var beforeIndex))
    (.var tagIndex)) (.var vectorIndex)) (.var afterIndex)

def resultPredicate : HOL.Term Const caseCarrier (W ⇒ .prop) := .app (.var motiveIndex) constructorCode

def applicationCode : HOL.Term Const caseCarrier W :=
  .app (.app (.app (.app (.app (.app (.app (.app (.var methodIndex) (.var lengthIndex))
    (.var beforeIndex)) (.var tagIndex)) (.var vectorIndex)) (.var afterIndex))
    (.var beforeIH)) (.var bundleIndex)) (.var afterIH)

theorem applicationCode_read : Reads lex body applicationCode :=
  .application (.application (.application (.application (.application
    (.application (.application (.application (.var methodIndex) (.var lengthIndex))
      (.var beforeIndex)) (.var tagIndex)) (.var vectorIndex)) (.var afterIndex))
    (.var beforeIH)) (.var bundleIndex)) (.var afterIH)

theorem resultPredicate_read : Reads lex expectedConclusion resultPredicate :=
  .application (.var motiveIndex)
    (.application (.application (.application (.application (.application (.var constructorIndex)
      (.var lengthIndex)) (.var beforeIndex)) (.var tagIndex)) (.var vectorIndex)) (.var afterIndex))

theorem application_term : (application roots).term = applicationCode :=
  Reader.term_unique (application roots).termRead applicationCode_read

theorem application_predicate : (application roots).predicate = resultPredicate :=
  Reader.term_unique (application roots).typeRead resultPredicate_read

def applicationProof : HOL.ProofSyntax Const (caseContext.hypotheses roots) (.app resultPredicate applicationCode) :=
  HOL.ProofSyntax.castIndices rfl (congrArg₂ HOL.Term.app (application_predicate roots) (application_term roots))
    (application roots).member

theorem applicationProof_free : (applicationProof roots).FunctionExtensionalityFree := by
  simpa only [applicationProof, GuardedRealizer.Free, HOL.ProofSyntax.functionExtensionalityFree_castIndices]
    using application_free roots

def clause : GuardedRealizer roots
    (GuardedContext.empty IndexedContainerNativeVectorCaseContext.theory lex)
    (TypedEquality.Impredicative.Domain.lamsCtx caseContext.source body)
    (TypedEquality.Impredicative.Domain.pisCtx caseContext.source expectedConclusion)
    (telescopeCarrier caseCarrier W) :=
  (application roots).abstractContext
    (NativeVectorAll.Annotated.Profile.levelModel elementLevel resultLevel (fun _ => false)) caseContext

theorem clause_free : (clause roots).Free :=
  GuardedRealizer.abstractContext_free
    (NativeVectorAll.Annotated.Profile.levelModel elementLevel resultLevel (fun _ => false))
    caseContext (application roots) (application_free roots)

theorem clause_apply (roots : List (HOL.ClosedFormula Const)) {n : Nat} {recipient : CCtx Tower.Head n}
    (images : CSub Tower.Head caseCarrier.length n)
    (typed : CSubstMor IndexedContainerNativeVectorCaseContext.theory caseContext.source recipient images) :
    CEqual IndexedContainerNativeVectorCaseContext.theory recipient
      (applyAlong images
        (TypedEquality.Impredicative.Domain.lamsCtx caseContext.source body).liftClosed)
      (body.subst images) (expectedConclusion.subst images) :=
  lamsCtx_apply (NativeVectorAll.Annotated.Profile.levelModel elementLevel resultLevel (fun _ => false))
    caseContext.formed ((application roots).typed.isType
      (NativeVectorAll.Annotated.Profile.levelModel elementLevel resultLevel (fun _ => false)) caseContext.formed)
    (application roots).typed images typed

#print axioms application
#print axioms application_free
#print axioms clause_free
#print axioms clause_apply

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseApplication
