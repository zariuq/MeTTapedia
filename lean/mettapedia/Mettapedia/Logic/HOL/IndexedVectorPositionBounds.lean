import Mettapedia.Logic.HOL.IndexedVectorPositions
import Mettapedia.Logic.HOL.SuccessorOrderPositionBounds

/-!
# Every lookup position is below its vector index

The least lookup relation is eliminated into the successor-closure order.
Only natural induction is retained as an arithmetic premise. Constructor
injectivity and zero/successor separation are unnecessary for this bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPositionBounds
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

def body : ArgumentBody Const Γ (IndexedVectorPositions.Fields signature) := fun _ fields =>
  .app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) fields.2.2.1) fields.1

theorem body_natural : NaturalBody (body (Γ := Γ) signature) := by
  intro Δ Ω earlier later fields
  simp only [body, HOL.subst, subst_weakenCtx, substituteArguments]

def relation : Term Const Γ (IndexedVectorPositions.Relation signature) :=
  abstractArguments (IndexedVectorPositions.Fields signature) (body signature)

@[simp] theorem relation_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (relation (Γ := Γ) signature) = relation (Γ := Ξ) signature := by
  unfold relation
  rw [abstractArguments_subst _ _ _ (body_natural signature)]
  rfl

variable {Δ : List (Formula Const Γ)}

def relation_apply (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    ProofSyntax Const Δ (.eq (IndexedVectorPositions.holds signature (relation signature) index vector position element)
      (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) index)) :=
  abstractArguments_beta _ _ (body_natural signature) (index, vector, position, element, PUnit.unit)

theorem relation_apply_free (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element) :
    (relation_apply (Δ := Δ) signature index vector position element).FunctionExtensionalityFree :=
  abstractArguments_beta_free _ _ _ _

def headBranch (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) :
    ArgumentProof Δ (IndexedVectorPositions.HeadFields signature)
      (IndexedVectorPositions.headBody signature (relation signature)) := by
  intro Ξ images fields
  have mapped : ProofSyntax Const (Δ.map (HOL.subst images))
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Ξ signature.zero) (weakenCtx Ξ signature.successor)) :=
    ProofSyntax.castIndices rfl (SuccessorOrder.inductionPrinciple_subst signature.successor signature.zero images)
      (principle.subst images)
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (relation_apply signature (.app (weakenCtx Ξ signature.successor) fields.1)
      (signature.consValue fields.1 fields.2.1 fields.2.2.1) (weakenCtx Ξ signature.zero) fields.2.1))
      (SuccessorOrder.zeroLessSuccessor signature.successor signature.zero fields.1 mapped))
  simp only [IndexedVectorPositions.headBody, relation_subst]

theorem headBranch_free (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) (free : principle.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ (IndexedVectorPositions.HeadFields signature)) :
    (headBranch signature principle images fields).FunctionExtensionalityFree := by
  unfold headBranch
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨relation_apply_free signature _ _ _ _, ?_⟩
  apply SuccessorOrder.zeroLessSuccessor_free
  simpa only [ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst] using free

def tailPoint (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element) :
    ProofSyntax Const Δ (.imp (IndexedVectorPositions.holds signature (relation signature) index tail position element)
      (IndexedVectorPositions.holds signature (relation signature) (.app (weakenCtx Γ signature.successor) index)
        (signature.consValue index head tail) (.app (weakenCtx Γ signature.successor) position) element)) :=
  .impI (.impE (.eqPropER (relation_apply signature (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index head tail) (.app (weakenCtx Γ signature.successor) position) element))
    (SuccessorOrder.lessSuccessorMap signature.successor position index
      (.impE (.eqPropEL (relation_apply signature index tail position element)) (.hyp 0))))

theorem tailPoint_free (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element) :
    (tailPoint (Δ := Δ) signature index head tail position element).FunctionExtensionalityFree := by
  unfold tailPoint
  refine ⟨relation_apply_free signature _ _ _ _, ?_⟩
  apply SuccessorOrder.lessSuccessorMap_free
  exact ⟨relation_apply_free signature _ _ _ _, True.intro⟩

def tailBranch : ArgumentProof Δ (IndexedVectorPositions.TailFields signature)
    (IndexedVectorPositions.tailBody signature (relation signature)) := by
  intro Ξ images fields
  apply ProofSyntax.castIndices rfl ?_
    (tailPoint (Δ := Δ.map (HOL.subst images)) signature fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1 fields.2.2.2.2.1)
  simp only [IndexedVectorPositions.tailBody, relation_subst]

theorem tailBranch_free (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ (IndexedVectorPositions.TailFields signature)) :
    (tailBranch (Δ := Δ) signature images fields).FunctionExtensionalityFree := by
  unfold tailBranch
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact tailPoint_free signature _ _ _ _ _

def rules (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) :
    ProofSyntax Const Δ (IndexedVectorPositions.closed signature (relation signature)) :=
  .andI (forallArguments_intro _ _ (headBranch signature principle)) (forallArguments_intro _ _ (tailBranch signature))

theorem rules_free (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
    (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) (free : principle.FunctionExtensionalityFree) :
    (rules signature principle).FunctionExtensionalityFree :=
  ⟨forallArguments_intro_free _ _ _ (headBranch_free signature principle free),
    forallArguments_intro_free _ _ _ (tailBranch_free signature)⟩

def lessOfLookup (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup signature index vector position element)) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) index) :=
  .impE (.eqPropEL (relation_apply signature index vector position element))
    (IndexedVectorPositions.eliminate signature (relation signature) index vector position element present (rules signature principle))

theorem lessOfLookup_free (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup signature index vector position element))
    (principleFree : principle.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (lessOfLookup signature index vector position element principle present).FunctionExtensionalityFree :=
  ⟨relation_apply_free signature index vector position element,
    IndexedVectorPositions.eliminate_free signature _ _ _ _ _ present (rules signature principle)
      presentFree (rules_free signature principle principleFree)⟩

#print axioms lessOfLookup
#print axioms lessOfLookup_free
end Mettapedia.Logic.HOL.IndexedVectorPositionBounds
