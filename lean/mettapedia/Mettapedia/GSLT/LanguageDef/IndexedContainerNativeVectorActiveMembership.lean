import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadback
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePadding
import Mettapedia.Logic.HOL.VectorChildArrayMembership

/-!
# Original source activity gives membership of the actual child-array value

The original activity predicate supplies the guarded canonical position
witness. The constructed array then satisfies the supplied recursive-element
predicate at that position. Direct and vector membership, Peano arithmetic,
and the six distinct array computation premises stay explicit. This is the
membership part of childConditions; root-index edges and source installation
remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembership
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding

variable (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def sourceActiveMember (payload elements : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app elements before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member elements length vector))
    (afterMember : ProofSyntax Const Δ (.app elements after))
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot)) :
    ProofSyntax Const Δ (.app elements
      (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot)) :=
  (arrayOperations elementSelection arraySelection).mixedMemberAtActivePlan elements length before vector after bottom slot
    .top .top .top premises arithmetic beforeMember vectorMember afterMember
    (.andER (IndexedContainerNativeVectorActivityReadback.fromActivity payload length tag shape slot active))

theorem sourceActiveMember_free (payload elements : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app elements before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member elements length vector))
    (afterMember : ProofSyntax Const Δ (.app elements after))
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree) :
    (sourceActiveMember elementSelection arraySelection payload elements length tag before vector after bottom shape slot
      premises arithmetic beforeMember vectorMember afterMember active).FunctionExtensionalityFree :=
  (arrayOperations elementSelection arraySelection).mixedMemberAtActivePlan_free _ _ _ _ _ _ _ _ _ _ premises arithmetic
    beforeMember vectorMember afterMember _ premisesFree arithmeticFree beforeFree vectorFree afterFree
    (IndexedContainerNativeVectorActivityReadback.fromActivity_free _ _ _ _ _ active activeFree)

#print axioms sourceActiveMember_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembership
