import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildren
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseFieldEvidence

/-!
# Applying the original supplied case to evidence recovered from its children

The original field context supplies the payload and vector guards. The
actual child-array contract produces both scalar IHs and the original All
bundle, which discharge the already-checked logical source row. The source
case function remains an input. Equality between its source constructor and
the recursive-space constructor is a separate representation obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseFromChildren
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original selection)
open IndexedContainerNativeVectorLogicalRow (fieldCarrier fieldContext)
open IndexedContainerNativeVectorCaseFieldEvidence (payload family length tag vector)
open IndexedContainerNativeVectorInactivePadding
open FiniteConstructorEncoding

def before : Term Const fieldCarrier E := .var IndexedContainerNativeVectorLogicalRow.beforeIndex
def after : Term Const fieldCarrier E := .var IndexedContainerNativeVectorLogicalRow.afterIndex
def motive : Term Const fieldCarrier (E ⇒ W ⇒ .prop) := .var IndexedContainerNativeVectorLogicalRow.motiveIndex

theorem hypotheses_readback :
    IndexedContainerNativeVectorAllFromChildren.hypotheses family motive length before vector after =
      .and (IndexedContainerNativeVectorLogicalRow.existsAt IndexedContainerNativeVectorLogicalRow.beforePredicate)
        (.and (IndexedContainerNativeVectorLogicalRow.existsAt IndexedContainerNativeVectorLogicalRow.bundlePredicate)
          (IndexedContainerNativeVectorLogicalRow.existsAt IndexedContainerNativeVectorLogicalRow.afterPredicate)) := rfl

variable (roots : List (ClosedFormula Const)) {Δ : List (Formula Const fieldCarrier)}
    (placement : ProofSyntax.OccurrenceMap (fieldContext.hypotheses roots) Δ)

def resultFromHypotheses
    (given : ProofSyntax Const Δ (IndexedContainerNativeVectorAllFromChildren.hypotheses family motive length before vector after)) :
    ProofSyntax Const Δ (IndexedContainerNativeVectorLogicalRow.existsAt IndexedContainerNativeVectorLogicalRow.resultPredicate) :=
  .impE (.impE (.impE ((IndexedContainerNativeVectorLogicalRow.rowProof roots).mono placement) (.andEL given))
    (.andEL (.andER given))) (.andER (.andER given))

theorem resultFromHypotheses_free
    (given : ProofSyntax Const Δ (IndexedContainerNativeVectorAllFromChildren.hypotheses family motive length before vector after))
    (free : given.FunctionExtensionalityFree) :
    (resultFromHypotheses roots placement given).FunctionExtensionalityFree :=
  ⟨⟨⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr (IndexedContainerNativeVectorLogicalRow.rowProof_free roots),free⟩,free⟩,free⟩

variable (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (construct : Term Const fieldCarrier (N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E))
    (bottom : Term Const fieldCarrier E)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx fieldCarrier original.zero) (weakenCtx fieldCarrier original.successor)))
    (conditions : ProofSyntax Const Δ (IndexedContainerNativeVectorAllFromChildren.contract elementSelection arraySelection
      payload family motive construct length tag before vector after bottom (weakenCtx fieldCarrier original.zero)))
    (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ)

def generatedHypotheses : ProofSyntax Const Δ
    (IndexedContainerNativeVectorAllFromChildren.hypotheses family motive length before vector after) :=
  IndexedContainerNativeVectorAllFromChildren.sourceHypotheses elementSelection arraySelection
    payload family motive construct length tag before vector after bottom (weakenCtx fieldCarrier original.zero)
    ((IndexedContainerNativeVectorCaseFieldEvidence.allowed roots).mono placement) premises induction
    ((IndexedContainerNativeVectorCaseFieldEvidence.vectorMember roots).mono placement) conditions allPremises

theorem generatedHypotheses_free (premisesFree : premises.FunctionExtensionalityFree)
    (inductionFree : induction.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allFree : allPremises.FunctionExtensionalityFree) :
    (generatedHypotheses roots placement elementSelection arraySelection construct bottom premises induction conditions allPremises).FunctionExtensionalityFree :=
  IndexedContainerNativeVectorAllFromChildren.sourceHypotheses_free elementSelection arraySelection
    payload family motive construct length tag before vector after bottom (weakenCtx fieldCarrier original.zero)
    ((IndexedContainerNativeVectorCaseFieldEvidence.allowed roots).mono placement) premises induction
    ((IndexedContainerNativeVectorCaseFieldEvidence.vectorMember roots).mono placement) conditions allPremises
    ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr (IndexedContainerNativeVectorCaseFieldEvidence.allowed_free roots))
    premisesFree inductionFree
    ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr (IndexedContainerNativeVectorCaseFieldEvidence.vectorMember_free roots))
    conditionsFree allFree

def result : ProofSyntax Const Δ
    (IndexedContainerNativeVectorLogicalRow.existsAt IndexedContainerNativeVectorLogicalRow.resultPredicate) :=
  resultFromHypotheses roots placement
    (generatedHypotheses roots placement elementSelection arraySelection construct bottom premises induction conditions allPremises)

theorem result_free (premisesFree : premises.FunctionExtensionalityFree)
    (inductionFree : induction.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (allFree : allPremises.FunctionExtensionalityFree) :
    (result roots placement elementSelection arraySelection construct bottom premises induction conditions allPremises).FunctionExtensionalityFree :=
  resultFromHypotheses_free roots placement _
    (generatedHypotheses_free roots placement elementSelection arraySelection construct bottom premises induction conditions allPremises
      premisesFree inductionFree conditionsFree allFree)

#print axioms hypotheses_readback
#print axioms result_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorCaseFromChildren
