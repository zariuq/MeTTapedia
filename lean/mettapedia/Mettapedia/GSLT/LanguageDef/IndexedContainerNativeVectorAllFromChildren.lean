import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditions
import Mettapedia.Logic.HOL.VectorChildArrayReflection
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence

/-!
# Original source All evidence from the actual child-array contract

The child predicate retains element membership and existential motive
evidence. Reflecting it through the actual mixed array recovers the vector
predicate needed by the original All producer, and both scalar IH premises.
The All recursor and the array recursors keep their distinct computation
profiles. No source case function or constructor representation is assumed
to have been synthesized by this operation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildren
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original pairs witness selection)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorChildGuard
open FiniteConstructorEncoding CurriedPredicates

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (payload family : Term Const Γ (E ⇒ .prop)) (motive : Term Const Γ (E ⇒ W ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E))
    (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape : Term Const Γ N)

def childPredicate := NativeVectorAll.Existence.lifted original family motive

def contract : Formula Const Γ :=
  ((positions payload).contextual bottom construct).childConditions (childPredicate family motive)
    (encoded payload length tag shape) ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom)

variable
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ original.zero) (weakenCtx Γ original.successor)))
    (member : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member family length vector))
    (conditions : ProofSyntax Const Δ (contract elementSelection arraySelection payload family motive construct
      length tag before vector after bottom shape))

@[irreducible] def coverageProgram :
    { covered : SuccessorOrder.MixedCoverage original.successor original.zero (sourceActivity payload length tag shape) length Δ //
      allowed.FunctionExtensionalityFree → induction.FunctionExtensionalityFree → covered.Free } :=
  ⟨sourceCoverage payload length tag shape allowed induction,
    sourceCoverage_free payload length tag shape allowed induction⟩

def coverage : SuccessorOrder.MixedCoverage original.successor original.zero (sourceActivity payload length tag shape) length Δ :=
  (coverageProgram payload length tag shape allowed induction).val

theorem coverage_free (allowedFree : allowed.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree) :
    (coverage payload length tag shape allowed induction).Free :=
  (coverageProgram payload length tag shape allowed induction).property allowedFree inductionFree

@[irreducible] def observations : ProofSyntax Const Δ (ActiveArrayMembership.condition (childPredicate family motive)
    (sourceActivity payload length tag shape) ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom)) :=
  ActiveArrayMembership.fromChildConditions ((positions payload).contextual bottom construct) (childPredicate family motive)
    (encoded payload length tag shape) ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) conditions

theorem observations_free (free : conditions.FunctionExtensionalityFree) :
    (observations elementSelection arraySelection payload family motive construct length tag before vector after bottom shape conditions).FunctionExtensionalityFree := by
  unfold observations
  exact ActiveArrayMembership.fromChildConditions_free _ _ _ _ conditions free

@[irreducible] def liftedVector : ProofSyntax Const Δ
    ((arrayOperations elementSelection arraySelection).toSignature.member (childPredicate family motive) length vector) := by
  let input : Formula Const Γ := .and (SuccessorOrder.interiorCoverage original.successor (sourceActivity payload length tag shape) length)
    (ActiveArrayMembership.condition (childPredicate family motive) (sourceActivity payload length tag shape)
      ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom))
  have supplied : ProofSyntax Const Δ input :=
    .andI (coverage payload length tag shape allowed induction).interior
      (observations elementSelection arraySelection payload family motive construct length tag before vector after bottom shape conditions)
  have body : ProofSyntax Const (input :: Δ)
      ((arrayOperations elementSelection arraySelection).toSignature.member (childPredicate family motive) length vector) :=
    (arrayOperations elementSelection arraySelection).mixedReflectVector family (childPredicate family motive)
      (sourceActivity payload length tag shape) length before vector after bottom
      (premises.prepend input) (induction.prepend input) (.andEL (.hyp 0)) (.andER (.hyp 0)) (member.prepend input)
  exact .impE (.impI body) supplied

set_option backward.isDefEq.respectTransparency true in
theorem liftedVector_free (allowedFree : allowed.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (liftedVector elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction member conditions).FunctionExtensionalityFree := by
  unfold liftedVector
  constructor
  · apply VectorChildArrays.Operations.mixedReflectVector_free
    · exact premises.prepend_free _ premisesFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr inductionFree
    · trivial
    · trivial
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree
  · exact ⟨(coverage payload length tag shape allowed induction).interiorFree
        (coverage_free payload length tag shape allowed induction allowedFree inductionFree),
      observations_free elementSelection arraySelection payload family motive construct
        length tag before vector after bottom shape conditions conditionsFree⟩

def bundle (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ) :
    ProofSyntax Const Δ (NativeVectorAll.Existence.query original pairs witness selection family motive length vector) :=
  NativeVectorAll.Existence.produce original pairs witness selection family motive length vector allPremises
    (liftedVector elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction member conditions)

theorem bundle_free (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ)
    (allowedFree : allowed.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (inductionFree : induction.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) (allFree : allPremises.FunctionExtensionalityFree) :
    (bundle elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction member conditions allPremises).FunctionExtensionalityFree :=
  NativeVectorAll.Existence.produce_free original pairs witness selection family motive length vector allPremises _ allFree
    (liftedVector_free _ _ _ _ _ _ _ _ _ _ _ _ _ allowed premises induction member conditions
      allowedFree premisesFree inductionFree memberFree conditionsFree)

def beforeEvidence : ProofSyntax Const Δ (existsValue [] (.app motive before)) :=
  .andER (.impE (.eqPropEL (NativeVectorAll.Existence.lifted_apply original family motive before))
    ((arrayOperations elementSelection arraySelection).mixedReflectLeading (childPredicate family motive)
      (sourceActivity payload length tag shape) length before vector after bottom premises
      (observations elementSelection arraySelection payload family motive construct length tag before vector after bottom shape conditions)
      (coverage payload length tag shape allowed induction).first))

theorem beforeEvidence_free (allowedFree : allowed.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) :
    (beforeEvidence elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction conditions).FunctionExtensionalityFree :=
  ⟨NativeVectorAll.Existence.lifted_apply_free original family motive before,
    (arrayOperations elementSelection arraySelection).mixedReflectLeading_free _ _ _ _ _ _ _ premises _ _ premisesFree
      (observations_free _ _ _ _ _ _ _ _ _ _ _ _ _ conditions conditionsFree)
      (coverage_free _ _ _ _ allowed induction allowedFree inductionFree).1⟩

def afterEvidence : ProofSyntax Const Δ (existsValue [] (.app motive after)) :=
  .andER (.impE (.eqPropEL (NativeVectorAll.Existence.lifted_apply original family motive after))
    ((arrayOperations elementSelection arraySelection).mixedReflectTrailing family (childPredicate family motive)
      (sourceActivity payload length tag shape) length before vector after bottom premises member
      (observations elementSelection arraySelection payload family motive construct length tag before vector after bottom shape conditions)
      (coverage payload length tag shape allowed induction).last))

theorem afterEvidence_free (allowedFree : allowed.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (afterEvidence elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction member conditions).FunctionExtensionalityFree :=
  ⟨NativeVectorAll.Existence.lifted_apply_free original family motive after,
    (arrayOperations elementSelection arraySelection).mixedReflectTrailing_free _ _ _ _ _ _ _ _ premises member _ _
      premisesFree memberFree (observations_free _ _ _ _ _ _ _ _ _ _ _ _ _ conditions conditionsFree)
      (coverage_free _ _ _ _ allowed induction allowedFree inductionFree).2.2⟩

def hypotheses : Formula Const Γ := .and (existsValue [] (.app motive before))
  (.and (NativeVectorAll.Existence.query original pairs witness selection family motive length vector)
    (existsValue [] (.app motive after)))

def sourceHypotheses (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ) :
    ProofSyntax Const Δ (hypotheses family motive length before vector after) :=
  .andI (beforeEvidence elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
    allowed premises induction conditions)
    (.andI (bundle elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction member conditions allPremises)
      (afterEvidence elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
        allowed premises induction member conditions))

theorem sourceHypotheses_free (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ)
    (allowedFree : allowed.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (inductionFree : induction.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) (allFree : allPremises.FunctionExtensionalityFree) :
    (sourceHypotheses elementSelection arraySelection payload family motive construct length tag before vector after bottom shape
      allowed premises induction member conditions allPremises).FunctionExtensionalityFree :=
  ⟨beforeEvidence_free _ _ _ _ _ _ _ _ _ _ _ _ _ allowed premises induction conditions allowedFree premisesFree inductionFree conditionsFree,
   bundle_free _ _ _ _ _ _ _ _ _ _ _ _ _ allowed premises induction member conditions allPremises
      allowedFree premisesFree inductionFree memberFree conditionsFree allFree,
   afterEvidence_free _ _ _ _ _ _ _ _ _ _ _ _ _ allowed premises induction member conditions
      allowedFree premisesFree inductionFree memberFree conditionsFree⟩

#print axioms sourceHypotheses_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorAllFromChildren
