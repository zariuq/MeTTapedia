import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseApplication
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedContextLogicalClosure

/-!
# The logical row of the original supplied mixed source case

The actual source application supplies one result witness. Its three IH
arguments are then opened from existential premises, without selecting any
global witness. All five original field guards are universally closed. The
case function remains ambient. The nested premise is existence of the actual
All bundle; constructing it from generic child conditions remains separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorLogicalRow

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedContainerNativeVectorMethodReading
local infixr:60 " ⇒ " => HOL.Ty.arr

def afterContext := IndexedContainerNativeVectorCaseContext.context.previous
def bundleContext := afterContext.previous
def fieldContext := bundleContext.previous
abbrev fieldCarrier : HOL.Ctx Base :=
  [E, V, E, E, N, IndexedContainerNativeVectorCaseContext.methodCarrier,
    constructorCarrier, motiveCarrier, E ⇒ .prop, E ⇒ .prop]

def variableAt (type : HOL.Ty Base) (position : Fin fieldCarrier.length)
    (same : fieldCarrier.get position = type) : HOL.Var fieldCarrier type :=
  same ▸ HOL.Var.ofFin fieldCarrier position

def motiveIndex := variableAt motiveCarrier 7 (by decide +kernel)
def familyIndex := variableAt (E ⇒ .prop) 8 (by decide +kernel)
def lengthIndex := variableAt N 4 (by decide +kernel)
def beforeIndex := variableAt E 3 (by decide +kernel)
def tagIndex := variableAt E 2 (by decide +kernel)
def vectorIndex := variableAt V 1 (by decide +kernel)
def afterIndex := variableAt E 0 (by decide +kernel)
def constructorIndex := variableAt constructorCarrier 6 (by decide +kernel)

def beforePredicate : HOL.Term Const fieldCarrier (W ⇒ .prop) := .app (.var motiveIndex) (.var beforeIndex)
def bundlePredicate : HOL.Term Const fieldCarrier (W ⇒ .prop) :=
  NativeVectorAll.Reading.allCode original pairs witness selection
    (.var familyIndex) (.var motiveIndex) (.var lengthIndex) (.var vectorIndex)
def afterPredicate : HOL.Term Const fieldCarrier (W ⇒ .prop) := .app (.var motiveIndex) (.var afterIndex)
def constructorCode : HOL.Term Const fieldCarrier E :=
  .app (.app (.app (.app (.app (.var constructorIndex) (.var lengthIndex)) (.var beforeIndex))
    (.var tagIndex)) (.var vectorIndex)) (.var afterIndex)
def resultPredicate : HOL.Term Const fieldCarrier (W ⇒ .prop) := .app (.var motiveIndex) constructorCode

def existsAt {Γ : HOL.Ctx Base} (predicate : HOL.Term Const Γ (W ⇒ .prop)) : HOL.Formula Const Γ :=
  .ex (.app (HOL.weaken predicate) (.var .vz))

theorem existsAt_rename {Γ Ξ : HOL.Ctx Base} (predicate : HOL.Term Const Γ (W ⇒ .prop))
    (rho : HOL.Rename Base Γ Ξ) :
    HOL.rename rho (existsAt predicate) = existsAt (HOL.rename rho predicate) := by
  change HOL.Term.ex (.app (HOL.rename (HOL.Rename.lift rho) (HOL.weaken predicate)) (.var .vz)) =
    HOL.Term.ex (.app (HOL.weaken (HOL.rename rho predicate)) (.var .vz))
  exact congrArg (fun code => HOL.Term.ex (.app code (.var .vz))) (HOL.rename_lift_weaken rho predicate)

theorem existsAt_weaken {Γ : HOL.Ctx Base} {bound : HOL.Ty Base}
    (predicate : HOL.Term Const Γ (W ⇒ .prop)) :
    HOL.weaken (σ := bound) (existsAt predicate) = existsAt (HOL.weaken predicate) :=
  existsAt_rename predicate HOL.Rename.weaken

private theorem weaken_imp {Γ : HOL.Ctx Base} {bound : HOL.Ty Base} (left right : HOL.Formula Const Γ) :
    HOL.weaken (σ := bound) (.imp left right) = .imp (HOL.weaken left) (HOL.weaken right) := rfl

theorem after_source : IndexedContainerNativeVectorCaseContext.context.lastType =
    (.app (.var 9) (.var 2) : CTm Tower.Head 12) := by decide +kernel

theorem bundle_source : afterContext.lastType =
    NativeVectorAll.Annotated.Formation.allType resultLevel
      (.var 9) (.var 8) (.var 5) (.var 2) := by decide +kernel

theorem after_domain : IndexedContainerNativeVectorCaseContext.context.lastPredicate =
    HOL.weaken (HOL.weaken afterPredicate) := by
  apply Reader.term_unique IndexedContainerNativeVectorCaseContext.context.last_read
  rw [after_source]
  have actual : Reads (Γ := W :: W :: fieldCarrier) lex (.app (.var 9) (.var 2))
      (.app (.var (.vs (.vs motiveIndex))) (.var (.vs (.vs afterIndex)))) :=
    .application (.var (.vs (.vs motiveIndex))) (.var (.vs (.vs afterIndex)))
  simpa only [afterPredicate, HOL.weaken, HOL.rename, HOL.Rename.weaken] using actual

theorem before_domain : bundleContext.lastPredicate = beforePredicate :=
  Reader.term_unique bundleContext.last_read (.application (.var motiveIndex) (.var beforeIndex))

theorem bundle_domain : afterContext.lastPredicate = HOL.weaken bundlePredicate := by
  have originalRead := NativeVectorAll.Reading.all_reads original pairs witness selection
    elementLevel resultLevel separated (.var familyIndex) (.var motiveIndex) (.var lengthIndex) (.var vectorIndex)
  have raised := originalRead.rename (HOL.Rename.weaken (σ := W)) wk (by intro type index; rfl)
  apply Reader.term_unique afterContext.last_read
  rw [bundle_source]
  have exactSource : (NativeVectorAll.Annotated.Formation.allType resultLevel
      (.var familyIndex.toFin) (.var motiveIndex.toFin) (.var lengthIndex.toFin) (.var vectorIndex.toFin)).rename wk =
      (NativeVectorAll.Annotated.Formation.allType resultLevel (.var 9) (.var 8) (.var 5) (.var 2) : CTm Tower.Head 11) := by
    rw [NativeVectorAll.Annotated.Formation.allType_rename]
    congr 1
  rw [exactSource] at raised
  exact raised

def afterGoal : HOL.Formula Const fieldCarrier := .imp (existsAt afterPredicate) (existsAt resultPredicate)
def bundleGoal : HOL.Formula Const fieldCarrier := .imp (existsAt bundlePredicate) afterGoal
def row : HOL.Formula Const fieldCarrier := .imp (existsAt beforePredicate) bundleGoal

variable (roots : List (HOL.ClosedFormula Const))

def resultWitness : HOL.ProofSyntax Const (IndexedContainerNativeVectorCaseContext.context.hypotheses roots)
    (HOL.weaken (HOL.weaken (HOL.weaken (existsAt resultPredicate)))) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (IndexedContainerNativeVectorCaseApplication.application roots).witness
  rw [IndexedContainerNativeVectorCaseApplication.application_predicate]
  rfl

theorem resultWitness_free : (resultWitness roots).FunctionExtensionalityFree := by
  unfold resultWitness
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedRealizer.witness_free _ (IndexedContainerNativeVectorCaseApplication.application_free roots)

def afterProof : HOL.ProofSyntax Const (afterContext.hypotheses roots) (HOL.weaken (HOL.weaken afterGoal)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (IndexedContainerNativeVectorCaseContext.context.closeLastWitness
      (HOL.weaken (HOL.weaken (existsAt resultPredicate))) (resultWitness roots))
  rw [after_domain]
  change .imp (existsAt (HOL.weaken (HOL.weaken afterPredicate)))
    (HOL.weaken (HOL.weaken (existsAt resultPredicate))) = HOL.weaken (HOL.weaken afterGoal)
  simp only [afterGoal, weaken_imp, existsAt_weaken]

theorem afterProof_free : (afterProof roots).FunctionExtensionalityFree := by
  unfold afterProof
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedContext.closeLastWitness_free _ _ _ (resultWitness_free roots)

def bundleProof : HOL.ProofSyntax Const (bundleContext.hypotheses roots) (HOL.weaken bundleGoal) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (afterContext.closeLastWitness (HOL.weaken afterGoal) (afterProof roots))
  rw [bundle_domain]
  change .imp (existsAt (HOL.weaken bundlePredicate)) (HOL.weaken afterGoal) = HOL.weaken bundleGoal
  simp only [bundleGoal, weaken_imp, existsAt_weaken]

theorem bundleProof_free : (bundleProof roots).FunctionExtensionalityFree := by
  unfold bundleProof
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedContext.closeLastWitness_free _ _ _ (afterProof_free roots)

def rowProof : HOL.ProofSyntax Const (fieldContext.hypotheses roots) row := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (bundleContext.closeLastWitness bundleGoal (bundleProof roots))
  rw [before_domain]
  rfl

theorem rowProof_free : (rowProof roots).FunctionExtensionalityFree := by
  unfold rowProof
  apply (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact GuardedContext.closeLastWitness_free _ _ _ (bundleProof_free roots)

def noAfterField := fieldContext.previous
def noVectorField := noAfterField.previous
def noTagField := noVectorField.previous
def noBeforeField := noTagField.previous
def ambient := noBeforeField.previous

def afterRow := HOL.Term.all (.imp (.app (HOL.weaken fieldContext.lastPredicate) (.var .vz)) row)
def vectorRow := HOL.Term.all (.imp (.app (HOL.weaken noAfterField.lastPredicate) (.var .vz)) afterRow)
def tagRow := HOL.Term.all (.imp (.app (HOL.weaken noVectorField.lastPredicate) (.var .vz)) vectorRow)
def beforeRow := HOL.Term.all (.imp (.app (HOL.weaken noTagField.lastPredicate) (.var .vz)) tagRow)
def closedRow := HOL.Term.all (.imp (.app (HOL.weaken noBeforeField.lastPredicate) (.var .vz)) beforeRow)

def afterRowProof := fieldContext.closeLastGuard row (rowProof roots)
def vectorRowProof := noAfterField.closeLastGuard afterRow (afterRowProof roots)
def tagRowProof := noVectorField.closeLastGuard vectorRow (vectorRowProof roots)
def beforeRowProof := noTagField.closeLastGuard tagRow (tagRowProof roots)
def closedRowProof : HOL.ProofSyntax Const (ambient.hypotheses roots) closedRow :=
  noBeforeField.closeLastGuard beforeRow (beforeRowProof roots)

private def prefixVariable (count : Nat) (type : HOL.Ty Base)
    (position : Fin (fieldCarrier.drop count).length) (same : (fieldCarrier.drop count).get position = type) :
    HOL.Var (fieldCarrier.drop count) type := same ▸ HOL.Var.ofFin _ position
def afterFieldVariable := prefixVariable 1 (E ⇒ .prop) ⟨7, by decide +kernel⟩ (by decide +kernel)
def vectorFamilyVariable := prefixVariable 2 (E ⇒ .prop) ⟨6, by decide +kernel⟩ (by decide +kernel)
def vectorLengthVariable := prefixVariable 2 N ⟨2, by decide +kernel⟩ (by decide +kernel)
def tagFieldVariable := prefixVariable 3 (E ⇒ .prop) ⟨6, by decide +kernel⟩ (by decide +kernel)
def beforeFieldVariable := prefixVariable 4 (E ⇒ .prop) ⟨4, by decide +kernel⟩ (by decide +kernel)

def afterFieldPredicate : HOL.Term Const (fieldCarrier.drop 1) (E ⇒ .prop) := .var afterFieldVariable
def vectorFieldPredicate : HOL.Term Const (fieldCarrier.drop 2) (V ⇒ .prop) :=
  NativeVectorAll.Reading.vectorCode original selection
    (.var vectorFamilyVariable) (.var vectorLengthVariable)
def tagFieldPredicate : HOL.Term Const (fieldCarrier.drop 3) (E ⇒ .prop) :=
  .var tagFieldVariable
def beforeFieldPredicate : HOL.Term Const (fieldCarrier.drop 4) (E ⇒ .prop) :=
  .var beforeFieldVariable
def lengthFieldPredicate : HOL.Term Const (fieldCarrier.drop 5) (N ⇒ .prop) :=
  HOL.weakenCtx _ (HOL.PredicateProducts.full N)

theorem after_field_source : fieldContext.lastType = (.var 7 : CTm Tower.Head 9) := by decide +kernel
theorem vector_field_source : noAfterField.lastType =
    (NativeVectorAll.Annotated.vector (.var 6) (.var 2) : CTm Tower.Head 8) := by decide +kernel
theorem tag_field_source : noVectorField.lastType = (.var 6 : CTm Tower.Head 7) := by decide +kernel
theorem before_field_source : noTagField.lastType = (.var 4 : CTm Tower.Head 6) := by decide +kernel
theorem length_field_source : noBeforeField.lastType =
    (.const NativeNaturalVectorFamilies.natName : CTm Tower.Head 5) := by decide +kernel

theorem after_field_domain : fieldContext.lastPredicate = afterFieldPredicate := by
  apply Reader.term_unique fieldContext.last_read
  rw [after_field_source]
  exact .var afterFieldVariable
theorem vector_field_domain : noAfterField.lastPredicate = vectorFieldPredicate := by
  apply Reader.term_unique noAfterField.last_read
  rw [vector_field_source]
  exact NativeVectorAll.Reading.vector_application original pairs witness selection elementLevel resultLevel
    (.var vectorFamilyVariable) (.var vectorLengthVariable)
theorem tag_field_domain : noVectorField.lastPredicate = tagFieldPredicate := by
  apply Reader.term_unique noVectorField.last_read
  rw [tag_field_source]
  exact .var tagFieldVariable
theorem before_field_domain : noTagField.lastPredicate = beforeFieldPredicate := by
  apply Reader.term_unique noTagField.last_read
  rw [before_field_source]
  exact .var beforeFieldVariable
theorem length_field_domain : noBeforeField.lastPredicate = lengthFieldPredicate := by
  apply Reader.term_unique noBeforeField.last_read
  rw [length_field_source]
  exact NativeVectorAll.Reading.natural_reads original pairs witness selection elementLevel resultLevel

def declaredAfterRow := HOL.Term.all (.imp (.app (HOL.weaken afterFieldPredicate) (.var .vz)) row)
def declaredVectorRow := HOL.Term.all (.imp (.app (HOL.weaken vectorFieldPredicate) (.var .vz)) declaredAfterRow)
def declaredTagRow := HOL.Term.all (.imp (.app (HOL.weaken tagFieldPredicate) (.var .vz)) declaredVectorRow)
def declaredBeforeRow := HOL.Term.all (.imp (.app (HOL.weaken beforeFieldPredicate) (.var .vz)) declaredTagRow)
def declaredClosedRow := HOL.Term.all (.imp (.app (HOL.weaken lengthFieldPredicate) (.var .vz)) declaredBeforeRow)

theorem closedRow_declared : closedRow = declaredClosedRow := by
  simp only [closedRow, beforeRow, tagRow, vectorRow, afterRow, after_field_domain,
    vector_field_domain, tag_field_domain, before_field_domain, length_field_domain]
  rfl

def declaredRowProof : HOL.ProofSyntax Const (ambient.hypotheses roots) declaredClosedRow :=
  HOL.ProofSyntax.castIndices rfl closedRow_declared (closedRowProof roots)

theorem closedRowProof_free : (closedRowProof roots).FunctionExtensionalityFree := by
  apply GuardedContext.closeLastGuard_free
  apply GuardedContext.closeLastGuard_free
  apply GuardedContext.closeLastGuard_free
  apply GuardedContext.closeLastGuard_free
  apply GuardedContext.closeLastGuard_free
  exact rowProof_free roots

theorem declaredRowProof_free : (declaredRowProof roots).FunctionExtensionalityFree :=
  (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (closedRowProof_free roots)

def instantiateRow {Ξ : HOL.Ctx Base} (images : HOL.Subst Const _ Ξ) :=
  HOL.ProofSyntax.subst images (closedRowProof roots)

theorem instantiateRow_free {Ξ : HOL.Ctx Base} (images : HOL.Subst Const _ Ξ) :
    (instantiateRow roots images).FunctionExtensionalityFree :=
  (HOL.ProofSyntax.functionExtensionalityFree_subst _ _).mpr (closedRowProof_free roots)

#print axioms rowProof_free
#print axioms closedRowProof_free
#print axioms instantiateRow_free

end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorLogicalRow
