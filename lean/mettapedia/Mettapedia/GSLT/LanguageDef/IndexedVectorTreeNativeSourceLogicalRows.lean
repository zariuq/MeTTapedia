import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceCaseApplication
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedContextLogicalClosure
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence

/-!
# Logical case rows of the complete parsed Vector-tree contexts

The two actual source case-variable applications supply result witnesses.
The branch's original All-W binder is opened from its existential bundle
premise. The original field guards are then universally closed, leaving all
seven ambient parameters and method guards in scope. No global evidence
selection or closed implementation of an arbitrary case method is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceLogicalRows

open Mettapedia.Logic Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedVectorTreeNativeSourceCaseApplication
open Native
local infixr:60 " ⇒ " => HOL.Ty.arr

def solvedAmbient := solvedContext.previous
def branchFields := branchContext.previous
def branchLength := branchFields.previous
def branchAmbient := branchLength.previous

abbrev fieldCarrier : HOL.Ctx Base := V :: N :: IndexedVectorTreeNativeSourceReading.ambient

private def variableAt (carrier : HOL.Ty Base) (index : Fin fieldCarrier.length)
    (same : fieldCarrier.get index = carrier) : HOL.Var fieldCarrier carrier :=
  same ▸ HOL.Var.ofFin fieldCarrier index

def motiveIndex := variableAt (E ⇒ W ⇒ .prop) ⟨6,by decide +kernel⟩ (by decide +kernel)
def familyIndex := variableAt (E ⇒ .prop) ⟨7,by decide +kernel⟩ (by decide +kernel)
def lengthIndex := variableAt N ⟨1,by decide +kernel⟩ (by decide +kernel)
def vectorIndex := variableAt V ⟨0,by decide +kernel⟩ (by decide +kernel)
def constructorIndex := variableAt (N ⇒ V ⇒ E) ⟨4,by decide +kernel⟩ (by decide +kernel)

def bundlePredicate : HOL.Term Const fieldCarrier (W ⇒ .prop) :=
  NativeVectorAll.Reading.allCode original pairs witness selection
    (.var familyIndex) (.var motiveIndex) (.var lengthIndex) (.var vectorIndex)

def resultPredicate : HOL.Term Const fieldCarrier (W ⇒ .prop) :=
  .app (.var motiveIndex) (.app (.app (.var constructorIndex) (.var lengthIndex)) (.var vectorIndex))

def existsAt {Γ : HOL.Ctx Base} (predicate : HOL.Term Const Γ (W ⇒ .prop)) : HOL.Formula Const Γ :=
  HOL.CurriedPredicates.existsValue [] predicate

def solvedGoal : HOL.Formula Const solvedCarrier := existsAt solvedResultPredicate
def branchGoal : HOL.Formula Const fieldCarrier := existsAt resultPredicate
def branchRow : HOL.Formula Const fieldCarrier := .imp (existsAt bundlePredicate) branchGoal

def vectorFamilyIndex : HOL.Var (N :: IndexedVectorTreeNativeSourceReading.ambient) (E ⇒ .prop) :=
  .vs (.vs (.vs (.vs (.vs (.vs .vz)))))
def vectorFieldPredicate : HOL.Term Const (N :: IndexedVectorTreeNativeSourceReading.ambient) (V ⇒ .prop) :=
  NativeVectorAll.Reading.vectorCode original selection (.var vectorFamilyIndex) (.var .vz)
def lengthFieldPredicate : HOL.Term Const IndexedVectorTreeNativeSourceReading.ambient (N ⇒ .prop) :=
  HOL.weakenCtx _ (HOL.PredicateProducts.full N)

theorem solved_field_source : solvedContext.lastType =
    (.var ⟨6,by decide +kernel⟩ : CTm Tower.Head IndexedVectorTreeNativeSourceReading.ambient.length) := by decide +kernel
theorem vector_field_source : branchFields.lastType =
    NativeVectorAll.Annotated.vector (.var vectorFamilyIndex.toFin) (.var HOL.Var.vz.toFin) := by decide +kernel
theorem length_field_source : branchLength.lastType =
    (.const NativeNaturalVectorFamilies.natName : CTm Tower.Head IndexedVectorTreeNativeSourceReading.ambient.length) := by decide +kernel

theorem solved_field_domain : solvedContext.lastPredicate = IndexedVectorTreeNativeSourceReading.answerPredicate := by
  apply Reader.term_unique solvedContext.last_read
  rw [solved_field_source]
  exact IndexedVectorTreeNativeSourceReading.answer_parameter_read
theorem vector_field_domain : branchFields.lastPredicate = vectorFieldPredicate := by
  apply Reader.term_unique branchFields.last_read
  rw [vector_field_source]
  exact NativeVectorAll.Reading.vector_application original pairs witness selection elementLevel resultLevel
    (.var vectorFamilyIndex) (.var .vz)
theorem length_field_domain : branchLength.lastPredicate = lengthFieldPredicate := by
  apply Reader.term_unique branchLength.last_read
  rw [length_field_source]
  exact NativeVectorAll.Reading.natural_reads original pairs witness selection elementLevel resultLevel

theorem branch_all_source : branchContext.lastType =
    NativeVectorAll.Annotated.Formation.allType resultLevel
      (.var familyIndex.toFin) (.var motiveIndex.toFin) (.var lengthIndex.toFin) (.var vectorIndex.toFin) := by
  decide +kernel

theorem branch_all_domain : branchContext.lastPredicate = bundlePredicate := by
  apply Reader.term_unique branchContext.last_read
  rw [branch_all_source]
  exact NativeVectorAll.Reading.all_reads original pairs witness selection elementLevel resultLevel separated
    (.var familyIndex) (.var motiveIndex) (.var lengthIndex) (.var vectorIndex)

theorem bundle_query_exact : existsAt bundlePredicate =
    NativeVectorAll.Existence.query original pairs witness selection
      (.var familyIndex) (.var motiveIndex) (.var lengthIndex) (.var vectorIndex) := rfl

variable (roots : List (HOL.ClosedFormula Const))

def solvedWitness : HOL.ProofSyntax Const (solvedContext.hypotheses roots) solvedGoal := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (solvedApplication roots).witness
  rw [solved_application_predicate]
  rfl

theorem solvedWitness_free : (solvedWitness roots).FunctionExtensionalityFree := by
  unfold solvedWitness
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedRealizer.witness_free _ (solvedApplication_free roots)

def branchWitness : HOL.ProofSyntax Const (branchContext.hypotheses roots) (HOL.weaken branchGoal) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (branchApplication roots).witness
  rw [branch_application_predicate]
  rfl

theorem branchWitness_free : (branchWitness roots).FunctionExtensionalityFree := by
  unfold branchWitness
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedRealizer.witness_free _ (branchApplication_free roots)

def branchRowProof : HOL.ProofSyntax Const (branchFields.hypotheses roots) branchRow := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (branchContext.closeLastWitness branchGoal (branchWitness roots))
  rw [branch_all_domain]
  rfl

theorem branchRowProof_free : (branchRowProof roots).FunctionExtensionalityFree := by
  unfold branchRowProof
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedContext.closeLastWitness_free _ _ _ (branchWitness_free roots)

def solvedRow := HOL.Term.all (.imp (.app (HOL.weaken solvedContext.lastPredicate) (.var .vz)) solvedGoal)
def vectorRow := HOL.Term.all (.imp (.app (HOL.weaken branchFields.lastPredicate) (.var .vz)) branchRow)
def closedBranchRow := HOL.Term.all (.imp (.app (HOL.weaken branchLength.lastPredicate) (.var .vz)) vectorRow)

def solvedRowProof : HOL.ProofSyntax Const (solvedAmbient.hypotheses roots) solvedRow :=
  solvedContext.closeLastGuard solvedGoal (solvedWitness roots)

def vectorRowProof : HOL.ProofSyntax Const (branchLength.hypotheses roots) vectorRow :=
  branchFields.closeLastGuard branchRow (branchRowProof roots)

def closedBranchRowProof : HOL.ProofSyntax Const (branchAmbient.hypotheses roots) closedBranchRow :=
  branchLength.closeLastGuard vectorRow (vectorRowProof roots)

def solvedBody : CTm Tower.Head solvedCarrier.length :=
  CTm.appSpine (.var solvedCaseIndex.toFin) (variableSources solvedPositions)
def branchBody : CTm Tower.Head branchCarrier.length :=
  CTm.appSpine (.var branchCaseIndex.toFin) (variableSources branchPositions)

theorem solved_source_typed : CTyped Source.theory solvedContext.source solvedBody solvedResultSource :=
  (solvedApplication []).typed
theorem branch_source_typed : CTyped Source.theory branchContext.source branchBody branchResultSource :=
  (branchApplication []).typed

theorem solvedRowProof_free : (solvedRowProof roots).FunctionExtensionalityFree :=
  GuardedContext.closeLastGuard_free _ _ _ (solvedWitness_free roots)

theorem vectorRowProof_free : (vectorRowProof roots).FunctionExtensionalityFree :=
  GuardedContext.closeLastGuard_free _ _ _ (branchRowProof_free roots)

theorem closedBranchRowProof_free : (closedBranchRowProof roots).FunctionExtensionalityFree :=
  GuardedContext.closeLastGuard_free _ _ _ (vectorRowProof_free roots)

theorem solved_original_ambient_source : solvedAmbient.source =
    IndexedVectorTreeNativeSourceReading.ambientSource := by decide +kernel
theorem branch_original_ambient_source : branchAmbient.source =
    IndexedVectorTreeNativeSourceReading.ambientSource := by decide +kernel
theorem solved_original_ambient_telescope : solvedAmbient.telescope =
    IndexedVectorTreeNativeSourceReading.ambientContext.telescope := by
  have reading : ContextReads lex IndexedVectorTreeNativeSourceReading.ambientSource solvedAmbient.telescope := by
    rw [← solved_original_ambient_source]
    exact solvedAmbient.reading
  exact Reader.context_unique reading IndexedVectorTreeNativeSourceReading.ambientContext.reading
theorem branch_original_ambient_telescope : branchAmbient.telescope =
    IndexedVectorTreeNativeSourceReading.ambientContext.telescope := by
  have reading : ContextReads lex IndexedVectorTreeNativeSourceReading.ambientSource branchAmbient.telescope := by
    rw [← branch_original_ambient_source]
    exact branchAmbient.reading
  exact Reader.context_unique reading IndexedVectorTreeNativeSourceReading.ambientContext.reading
theorem field_context_size : fieldCarrier.length = 9 := by decide +kernel

#print axioms branch_all_domain
#print axioms solvedRowProof_free
#print axioms closedBranchRowProof_free

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceLogicalRows
