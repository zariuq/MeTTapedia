import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorLogicalRow
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorSourceGuards

/-!
# Primitive field evidence in the original supplied-case context

Reading coherence identifies the actual payload and vector variable guards.
The retained vector-family beta proof yields least-predicate membership;
the structural source producer supplies the complete allowed condition at
the original zero shape. No extra payload or vector guard is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseFieldEvidence
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedContainerNativeVectorMethodReading (Base Const N E V original pairs witness selection lex elementLevel resultLevel)
open IndexedContainerNativeVectorLogicalRow (fieldCarrier fieldContext variableAt familyIndex lengthIndex tagIndex vectorIndex)

def payloadIndex := variableAt (E ⇒ .prop) 9 (by decide +kernel)
def payload : Term Const fieldCarrier (E ⇒ .prop) := .var payloadIndex
def family : Term Const fieldCarrier (E ⇒ .prop) := .var familyIndex
def length : Term Const fieldCarrier N := .var lengthIndex
def tag : Term Const fieldCarrier E := .var tagIndex
def vector : Term Const fieldCarrier V := .var vectorIndex

theorem tag_source : fieldContext.source.lookup tagIndex.toFin = (.var payloadIndex.toFin : CTm Tower.Head fieldCarrier.length) := by
  decide +kernel

theorem vector_source : fieldContext.source.lookup vectorIndex.toFin =
    (NativeVectorAll.Annotated.vector (.var familyIndex.toFin) (.var lengthIndex.toFin) : CTm Tower.Head fieldCarrier.length) := by
  decide +kernel

theorem tag_domain : fieldContext.telescope.domain tagIndex = payload := by
  have found := fieldContext.reading.lookup tagIndex
  rw [tag_source] at found
  exact Reader.term_unique found (.var payloadIndex)

theorem vector_domain : fieldContext.telescope.domain vectorIndex = NativeVectorAll.Reading.vectorCode original selection family length := by
  have found := fieldContext.reading.lookup vectorIndex
  rw [vector_source] at found
  exact Reader.term_unique found (NativeVectorAll.Reading.vector_application original pairs witness selection
    elementLevel resultLevel (.var familyIndex) (.var lengthIndex))

variable (roots : List (ClosedFormula Const))

def tagMember : ProofSyntax Const (fieldContext.hypotheses roots) (.app payload tag) :=
  ProofSyntax.castIndices rfl (congrArg (fun predicate => Term.app predicate tag) tag_domain)
    (fieldContext.variableProof roots tagIndex)

theorem tagMember_free : (tagMember roots).FunctionExtensionalityFree := by
  unfold tagMember
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (fieldContext.variableProof_free roots tagIndex)

@[irreducible] def vectorGuard : ProofSyntax Const (fieldContext.hypotheses roots)
    (.app (NativeVectorAll.Reading.vectorCode original selection family length) vector) :=
  ProofSyntax.castIndices rfl (congrArg (fun predicate => Term.app predicate vector) vector_domain)
    (fieldContext.variableProof roots vectorIndex)

theorem vectorGuard_free : (vectorGuard roots).FunctionExtensionalityFree := by
  unfold vectorGuard
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (fieldContext.variableProof_free roots vectorIndex)

@[irreducible] def vectorBeta : ProofSyntax Const (fieldContext.hypotheses roots)
    (.eq (.app (NativeVectorAll.Reading.vectorCode original selection family length) vector)
      ((NativeVectorComputationRows.GuardedFamily.algebra original).member family length vector)) :=
  ProofSyntax.castIndices rfl (by
    simp only [NativeVectorAll.Reading.vectorCode, NativeVectorComputationRows.GuardedFamily.weaken_familyCode]
    rfl)
    (NativeVectorComputationRows.GuardedFamily.family_apply (NativeVectorAll.Reading.operations original selection) family length vector)

theorem vectorBeta_free : (vectorBeta roots).FunctionExtensionalityFree := by
  unfold vectorBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact NativeVectorComputationRows.GuardedFamily.family_apply_free _ _ _ _

@[irreducible] def vectorMember : ProofSyntax Const (fieldContext.hypotheses roots)
    ((NativeVectorComputationRows.GuardedFamily.algebra original).member family length vector) :=
  .impE (.eqPropEL (vectorBeta roots)) (vectorGuard roots)

set_option backward.isDefEq.respectTransparency true in
theorem vectorMember_free : (vectorMember roots).FunctionExtensionalityFree := by
  unfold vectorMember
  exact ⟨vectorBeta_free roots, vectorGuard_free roots⟩

def allowed : ProofSyntax Const (fieldContext.hypotheses roots)
    (IndexedContainerNativeVectorPositionReading.sourceAllowed payload length tag (weakenCtx fieldCarrier original.zero)) :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag payload length tag (tagMember roots)

theorem allowed_free : (allowed roots).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorSourceGuards.allowedOfTag_free payload length tag (tagMember roots) (tagMember_free roots)

#print axioms tag_source
#print axioms vector_source
#print axioms allowed_free
#print axioms vectorMember_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseFieldEvidence
