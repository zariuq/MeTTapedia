import Mettapedia.Logic.HOL.VectorChildArrayBoundary
import Mettapedia.Logic.HOL.MixedPositionCoverage

/-!
# Constructed array padding from a checked inactive-position address

The two existential addresses are opened in their actual scopes. The original
absolute-slot equality then transports the array read back to the caller's
slot. No address witness is selected globally, and no native decoder or
occurrence-preservation theorem is inferred from this logical transport.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.Operations
open SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (ops : VectorChildArrays.Operations Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def paddingAtPredecessor (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot predecessor : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (position : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ ops.successor) predecessor)))
    (sum : ProofSyntax Const Δ (successorOffsetSum ops.successor ops.zero index predecessor)) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom) slot) bottom) := by
  apply ProofSyntax.exE sum
  let body : Formula Const (ops.number :: Γ) :=
    .app (.app (.app (weakenCtx _ (SuccessorOrder.sum ops.zero ops.successor)) (weaken index))
      (.app (weakenCtx _ ops.successor) (.var .vz))) (weaken predecessor)
  let assumptions := body :: weakenHyps Δ
  have present : ProofSyntax Const assumptions body := .hyp 0
  have currentMember : ProofSyntax Const assumptions
      (ops.toSignature.member (weaken elements) (weaken index) (weaken vector)) :=
    ProofSyntax.castIndices rfl (ops.toSignature.rename_member Rename.weaken elements index vector)
      ((member.rename Rename.weaken).prepend body)
  have currentPosition : ProofSyntax Const assumptions
      (.eq (weaken slot) (.app (weakenCtx _ ops.successor) (weaken predecessor))) := by
    apply ProofSyntax.castIndices rfl ?_ ((position.rename Rename.weaken).prepend body)
    simp only [HOL.rename,weaken,rename_weakenCtx]
  have result := ProofSyntax.eqTrans (.eqAppArg (ops.mixed (weaken index) (weaken before) (weaken vector)
      (weaken after) (weaken bottom)) currentPosition)
    (ops.mixedPadding (weaken elements) (weaken index) (weaken before) (weaken vector) (weaken after) (weaken bottom)
      (.var .vz) (weaken predecessor) ((premises.weaken ops.number).prepend body) currentMember present)
  apply ProofSyntax.castIndices rfl ?_ result
  simp only [weaken,HOL.rename,mixed_rename]

theorem paddingAtPredecessor_free (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot predecessor : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (position : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ ops.successor) predecessor)))
    (sum : ProofSyntax Const Δ (successorOffsetSum ops.successor ops.zero index predecessor))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (positionFree : position.FunctionExtensionalityFree) (sumFree : sum.FunctionExtensionalityFree) :
    (ops.paddingAtPredecessor elements index before vector after bottom slot predecessor premises member position sum).FunctionExtensionalityFree := by
  unfold paddingAtPredecessor
  refine ⟨sumFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨?_,?_⟩
  · simpa only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using positionFree
  · apply ops.mixedPadding_free
    · exact (premises.weaken ops.number).prepend_free _ (premises.weaken_free ops.number free)
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using memberFree
    · trivial

def paddingFromAddress (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (address : ProofSyntax Const Δ (paddingAddress ops.successor ops.zero index slot)) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom) slot) bottom) := by
  apply ProofSyntax.exE address
  let body : Formula Const (ops.number :: Γ) :=
    .and (.eq (weaken slot) (.app (weakenCtx _ ops.successor) (.var .vz)))
      (successorOffsetSum ops.successor ops.zero (weaken index) (.var .vz))
  let assumptions := body :: weakenHyps Δ
  have supplied : ProofSyntax Const assumptions body := .hyp 0
  have currentMember : ProofSyntax Const assumptions
      (ops.toSignature.member (weaken elements) (weaken index) (weaken vector)) :=
    ProofSyntax.castIndices rfl (ops.toSignature.rename_member Rename.weaken elements index vector)
      ((member.rename Rename.weaken).prepend body)
  apply ProofSyntax.castIndices rfl ?_
    (ops.paddingAtPredecessor (weaken elements) (weaken index) (weaken before) (weaken vector)
      (weaken after) (weaken bottom) (weaken slot) (.var .vz) ((premises.weaken ops.number).prepend body)
      currentMember (.andEL supplied) (.andER supplied))
  simp only [weaken,HOL.rename,mixed_rename]

theorem paddingFromAddress_free (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (address : ProofSyntax Const Δ (paddingAddress ops.successor ops.zero index slot))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (addressFree : address.FunctionExtensionalityFree) :
    (ops.paddingFromAddress elements index before vector after bottom slot premises member address).FunctionExtensionalityFree := by
  unfold paddingFromAddress
  refine ⟨addressFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ops.paddingAtPredecessor_free
  · exact (premises.weaken ops.number).prepend_free _ (premises.weaken_free ops.number free)
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using memberFree
  · trivial
  · trivial

def paddingAtInactive (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (active : Term Const Γ (ops.number ⇒ .prop)) (coverage : MixedCoverage ops.successor ops.zero active index Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (inactive : ProofSyntax Const Δ (.not (.app active slot))) :
    ProofSyntax Const Δ (.eq (.app (ops.mixed index before vector after bottom) slot) bottom) :=
  ops.paddingFromAddress elements index before vector after bottom slot premises member
    (inactiveAddress ops.successor ops.zero active index slot coverage principle separate inactive)

theorem paddingAtInactive_free (elements : Term Const Γ (ops.element ⇒ .prop)) (index : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (active : Term Const Γ (ops.number ⇒ .prop)) (coverage : MixedCoverage ops.successor ops.zero active index Δ)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (separate : ProofSyntax Const Δ (NaturalNumeralProofs.separation (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (inactive : ProofSyntax Const Δ (.not (.app active slot)))
    (coverageFree : coverage.Free) (principleFree : principle.FunctionExtensionalityFree)
    (separateFree : separate.FunctionExtensionalityFree) (free : premises.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (ops.paddingAtInactive elements index before vector after bottom slot active coverage principle separate premises member inactive).FunctionExtensionalityFree :=
  ops.paddingFromAddress_free _ _ _ _ _ _ _ premises member _ free memberFree
    (inactiveAddress_free _ _ _ _ _ coverage principle separate inactive coverageFree principleFree separateFree inactiveFree)

#print axioms paddingAtInactive
#print axioms paddingAtInactive_free
end Mettapedia.Logic.HOL.VectorChildArrays.Operations
