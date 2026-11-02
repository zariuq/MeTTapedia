import Mettapedia.Logic.HOL.VectorChildArraySuffix

/-!
# Trailing fields and padding of constructed mixed child arrays

Vector membership supplies the induction needed for arbitrary open vectors.
The trailing child is at the successor of the vector index. Padding is read
at an explicitly related positive suffix offset; its sum witness retains the
absolute address. This does not silently replace a source inactivity guard by
an assumed arithmetic witness or prove a decoder for arbitrary carriers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.Operations
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (ops : VectorChildArrays.Operations Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def valueAtEnd (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector)) :
    ProofSyntax Const Δ (.eq (.app (ops.suffix index vector rest) index) (.app rest (weakenCtx Γ ops.zero))) :=
  ops.valueAfterVector elements rest index vector (weakenCtx Γ ops.zero) index premises member
    (SuccessorOrder.sumZero ops.successor ops.zero index)

theorem valueAtEnd_free (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (ops.valueAtEnd elements rest index vector premises member).FunctionExtensionalityFree :=
  ops.valueAfterVector_free _ _ _ _ _ _ premises member _ free memberFree (SuccessorOrder.sumZero_free _ _ _)

def mixedLeading (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom) (weakenCtx Γ ops.zero)) before) :=
  ops.prepend_zero _ _ premises.elementChoice premises.elementRecursion

theorem mixedLeading_free (index : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (free : premises.FunctionExtensionalityFree) :
    (ops.mixedLeading index before vector after bottom premises).FunctionExtensionalityFree :=
  ops.prepend_zero_free _ _ _ _ free.1 free.2.1

def mixedTrailing (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector)) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom)
      (.app (weakenCtx Γ ops.successor) index)) after) :=
  .eqTrans (ops.prepend_successor before (ops.suffix index vector (ops.prepend after (ops.padding bottom)))
      index premises.elementChoice premises.elementRecursion)
    (.eqTrans (ops.valueAtEnd elements (ops.prepend after (ops.padding bottom)) index vector premises member)
      (ops.prepend_zero after (ops.padding bottom) premises.elementChoice premises.elementRecursion))

theorem mixedTrailing_free (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (ops.mixedTrailing elements index before vector after bottom premises member).FunctionExtensionalityFree :=
  ⟨ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1,
    ⟨ops.valueAtEnd_free _ _ _ _ premises member free memberFree,
      ops.prepend_zero_free _ _ _ _ free.1 free.2.1⟩⟩

def mixedPadding (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (offset total : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (sum : ProofSyntax Const Δ (ops.sumAt index (.app (weakenCtx Γ ops.successor) offset) total)) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom)
      (.app (weakenCtx Γ ops.successor) total)) bottom) :=
  .eqTrans (ops.prepend_successor before (ops.suffix index vector (ops.prepend after (ops.padding bottom)))
      total premises.elementChoice premises.elementRecursion)
    (.eqTrans (ops.valueAfterVector elements (ops.prepend after (ops.padding bottom)) index vector
        (.app (weakenCtx Γ ops.successor) offset) total premises member sum)
      (.eqTrans (ops.prepend_successor after (ops.padding bottom) offset premises.elementChoice premises.elementRecursion)
        (ops.padding_apply bottom offset)))

theorem mixedPadding_free (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (offset total : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (sum : ProofSyntax Const Δ (ops.sumAt index (.app (weakenCtx Γ ops.successor) offset) total))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (sumFree : sum.FunctionExtensionalityFree) :
    (ops.mixedPadding elements index before vector after bottom offset total premises member sum).FunctionExtensionalityFree :=
  ⟨ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1,
    ⟨ops.valueAfterVector_free _ _ _ _ _ _ premises member sum free memberFree sumFree,
      ⟨ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1,ops.padding_apply_free _ _⟩⟩⟩

#print axioms mixedTrailing_free
#print axioms mixedPadding_free
end Mettapedia.Logic.HOL.VectorChildArrays.Operations
