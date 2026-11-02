import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditions
import Mettapedia.Logic.HOL.ConstructorJointEvidence

/-!
# Original child conditions from separately established laws

The assembly consumes the original activity readback, joint array membership,
child-index guard and padding implications. Every law is a retained proof.
The active branch connects membership and root evidence at the same child;
the inactive branch remains the original padding condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildAssembly
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original)
open IndexedContainerNativeVectorPositionReading IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorChildGuard IndexedContainerNativeVectorChildConditions
open IndexedContainerNativeVectorActivityReadback
open FiniteConstructorEncoding

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (payload elements : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E))
    (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)

def fromLaws
    (activity : ProofSyntax Const Δ (.imp (.app (sourceActivity payload length tag shape) slot)
      (.and (sourceAllowed payload length tag shape) (positionWitness length slot))))
    (membership : ProofSyntax Const Δ (.imp (positionWitness length slot)
      (.app (joint payload elements construct)
        (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot))))
    (guard : ProofSyntax Const Δ (.imp (.app (sourceActivity payload length tag shape) slot)
      ((positions payload).childGuard (encoded payload length tag shape) slot .top)))
    (padding : ProofSyntax Const Δ (.imp (.not (.app (sourceActivity payload length tag shape) slot))
      (.eq (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot) bottom))) :
    ProofSyntax Const Δ (slotConditions elementSelection arraySelection payload elements construct
      length tag before vector after bottom shape slot) :=
  .andI (.impI ((positions payload).edgeAndMembership construct elements (encoded payload length tag shape) slot _ .top
    (.impE (guard.prepend _) (.hyp 0))
    (.impE (membership.prepend _) (.andER (.impE (activity.prepend _) (.hyp 0)))))) padding

theorem fromLaws_free
    (activity : ProofSyntax Const Δ (.imp (.app (sourceActivity payload length tag shape) slot)
      (.and (sourceAllowed payload length tag shape) (positionWitness length slot))))
    (membership : ProofSyntax Const Δ (.imp (positionWitness length slot)
      (.app (joint payload elements construct)
        (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot))))
    (guard : ProofSyntax Const Δ (.imp (.app (sourceActivity payload length tag shape) slot)
      ((positions payload).childGuard (encoded payload length tag shape) slot .top)))
    (padding : ProofSyntax Const Δ (.imp (.not (.app (sourceActivity payload length tag shape) slot))
      (.eq (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot) bottom)))
    (activityFree : activity.FunctionExtensionalityFree) (membershipFree : membership.FunctionExtensionalityFree)
    (guardFree : guard.FunctionExtensionalityFree) (paddingFree : padding.FunctionExtensionalityFree) :
    (fromLaws elementSelection arraySelection payload elements construct length tag before vector after bottom shape slot
      activity membership guard padding).FunctionExtensionalityFree := by
  unfold fromLaws
  refine ⟨?_,paddingFree⟩
  apply (positions payload).edgeAndMembership_free
  · exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr guardFree,True.intro⟩
  · exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr membershipFree,
      (ProofSyntax.functionExtensionalityFree_mono _ _).mpr activityFree,True.intro⟩

#print axioms fromLaws_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildAssembly
