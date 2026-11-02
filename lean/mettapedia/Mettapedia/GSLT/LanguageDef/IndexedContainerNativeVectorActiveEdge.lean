import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveMembership
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildGuard
import Mettapedia.Logic.HOL.ConstructorEdgeIntroduction
import Mettapedia.Logic.HOL.ConstructorRootSection

/-!
# Root-index edges of the actual mixed child array

Original activity proves the declared child-index guard. Membership of the
source fields in the original root-index section transports that root proof
to the actual array value. Edge introduction then uses both facts at the same
slot and index. Least membership and source constructor installation are not
inferred from root-index membership alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveEdge
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorActiveMembership
open IndexedContainerNativeVectorChildGuard
open FiniteConstructorEncoding

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (payload : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType (constructors payload).fields ⇒ (N ⇒ E) ⇒ E))

def rootPredicate : Term Const Γ (E ⇒ .prop) := (constructors payload).rootAt construct .top

def sourceActiveEdge (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeRoot : ProofSyntax Const Δ (.app (rootPredicate payload construct) before))
    (vectorRoots : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (rootPredicate payload construct) length vector))
    (afterRoot : ProofSyntax Const Δ (.app (rootPredicate payload construct) after))
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (activeFree : active.FunctionExtensionalityFree) :
    ProofSyntax Const Δ (.app (.app (.app ((positions payload).edgeProgram construct)
      (encoded payload length tag shape)) slot)
      (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot)) :=
  (positions payload).edgeProgramFromIndex construct _ slot _ .top
    (childGuardFromActivity payload length tag shape slot active activeFree)
    ((constructors payload).rootAt_elim construct .top _
      (sourceActiveMember elementSelection arraySelection payload (rootPredicate payload construct)
        length tag before vector after bottom shape slot premises arithmetic beforeRoot vectorRoots afterRoot active))

theorem sourceActiveEdge_free (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeRoot : ProofSyntax Const Δ (.app (rootPredicate payload construct) before))
    (vectorRoots : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (rootPredicate payload construct) length vector))
    (afterRoot : ProofSyntax Const Δ (.app (rootPredicate payload construct) after))
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (activeFree : active.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeRoot.FunctionExtensionalityFree) (vectorFree : vectorRoots.FunctionExtensionalityFree)
    (afterFree : afterRoot.FunctionExtensionalityFree) :
    (sourceActiveEdge elementSelection arraySelection payload construct length tag before vector after bottom shape slot
      premises arithmetic beforeRoot vectorRoots afterRoot active activeFree).FunctionExtensionalityFree :=
  (positions payload).edgeProgramFromIndex_free _ _ _ _ _ _ _
    (childGuardFromActivity_free payload length tag shape slot active activeFree)
    ((constructors payload).rootAt_elim_free _ _ _ _
      (sourceActiveMember_free elementSelection arraySelection payload (rootPredicate payload construct)
        length tag before vector after bottom shape slot premises arithmetic beforeRoot vectorRoots afterRoot active
        premisesFree arithmeticFree beforeFree vectorFree afterFree activeFree))

#print axioms sourceActiveEdge_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActiveEdge
