import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionReading
import Mettapedia.Logic.HOL.VectorChildArrayInactivePadding

/-!
# Actual source inactivity implies padding of the constructed child array

The source activity predicate is the original constructor compiler's guard.
Its generated count programs provide retained conversion evidence. The address
is derived from that guard, then consumed by the actual array program. Selection
and recursion at the element and array result types remain distinct premises.
This is the inactive branch of childConditions, not its active-edge or complete
membership assembly, and it does not install a new constructor declaration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePadding
open Mettapedia.Logic
open Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original)
open IndexedContainerNativeVectorPositionReading

def arrayOperations
    (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E))) : VectorChildArrays.Operations Const where
  number := N
  element := E
  vector := V
  zero := original.zero
  successor := original.successor
  nil := original.nil
  cons := original.cons
  head := original.head
  tail := original.tail
  elementSelection := elementSelection
  arraySelection := arraySelection

variable (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def sourceInactivePadding (payload elements : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ original.zero) (weakenCtx Γ original.successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation
      (weakenCtx Γ original.zero) (weakenCtx Γ original.successor)))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (member : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member elements length vector))
    (inactive : ProofSyntax Const Δ (.not (.app (sourceActivity payload length tag shape) slot))) :
    ProofSyntax Const Δ (.eq
      (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot) bottom) :=
  (arrayOperations elementSelection arraySelection).paddingFromAddress elements length before vector after bottom slot premises member
    (sourceInactiveAddress payload length tag shape slot allowed principle separate inactive)

theorem sourceInactivePadding_free (payload elements : Term Const Γ (E ⇒ .prop))
    (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ original.zero) (weakenCtx Γ original.successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation
      (weakenCtx Γ original.zero) (weakenCtx Γ original.successor)))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (member : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member elements length vector))
    (inactive : ProofSyntax Const Δ (.not (.app (sourceActivity payload length tag shape) slot)))
    (allowedFree : allowed.FunctionExtensionalityFree) (principleFree : principle.FunctionExtensionalityFree)
    (separateFree : separate.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (sourceInactivePadding elementSelection arraySelection payload elements length tag before vector after bottom shape slot
      allowed principle separate premises member inactive).FunctionExtensionalityFree :=
  (arrayOperations elementSelection arraySelection).paddingFromAddress_free _ _ _ _ _ _ _ premises member _ premisesFree memberFree
    (sourceInactiveAddress_free payload length tag shape slot allowed principle separate inactive
      allowedFree principleFree separateFree inactiveFree)

#print axioms sourceInactivePadding
#print axioms sourceInactivePadding_free
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePadding
