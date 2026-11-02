import Mettapedia.Logic.HOL.IndexedVectorPositions
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Scoped vector lookup witnesses retaining element membership

The lookup relation and the element predicate share one existential witness.
Head/tail introductions and position equality transport preserve that scope.
This file does not assume or assert that every bounded position has a witness;
that requires vector induction and the relevant arithmetic premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorLookupWitnesses
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}
    {Δ : List (Formula Const Γ)}

def evidence (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) : Formula Const Γ :=
  .ex (.and (IndexedVectorPositions.lookup signature (weaken index) (weaken vector) (weaken position) (.var .vz))
    (.app (weaken predicate) (.var .vz)))

theorem evidence_subst (images : Subst Const Γ Ξ) (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number) :
    HOL.subst images (evidence signature predicate index vector position) =
      evidence signature (HOL.subst images predicate) (HOL.subst images index) (HOL.subst images vector) (HOL.subst images position) := by
  simp only [evidence,HOL.subst,IndexedVectorPositions.lookup_subst,subst_weaken,Subst.lift]

theorem evidence_rename (rho : Rename Base Γ Ξ) (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number) :
    HOL.rename rho (evidence signature predicate index vector position) =
      evidence signature (HOL.rename rho predicate) (HOL.rename rho index) (HOL.rename rho vector) (HOL.rename rho position) := by
  simpa only [subst_ofRename] using evidence_subst signature (Subst.ofRename rho) predicate index vector position

def introduce (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (lookup : ProofSyntax Const Δ (IndexedVectorPositions.lookup signature index vector position element))
    (member : ProofSyntax Const Δ (.app predicate element)) :
    ProofSyntax Const Δ (evidence signature predicate index vector position) := by
  apply ProofSyntax.exI element
  apply ProofSyntax.castIndices rfl ?_ (.andI lookup member)
  simp only [instantiate,HOL.subst,IndexedVectorPositions.lookup_subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem introduce_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (lookup : ProofSyntax Const Δ (IndexedVectorPositions.lookup signature index vector position element))
    (member : ProofSyntax Const Δ (.app predicate element))
    (lookupFree : lookup.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (introduce signature predicate index vector position element lookup member).FunctionExtensionalityFree := by
  unfold introduce
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr ⟨lookupFree,memberFree⟩

def positionEquation (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (first second : Term Const Γ signature.number) (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (evidence signature predicate index vector first) (evidence signature predicate index vector second)) := by
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.holeCongr
    (evidence signature (weaken predicate) (weaken index) (weaken vector) (.var .vz)) same)
  simp only [instantiate,evidence_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem positionEquation_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (first second : Term Const Γ signature.number) (same : ProofSyntax Const Δ (.eq first second))
    (free : same.FunctionExtensionalityFree) :
    (positionEquation signature predicate index vector first second same).FunctionExtensionalityFree := by
  unfold positionEquation
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ContextualTrinity.holeCongr_free _ _).mpr free

def head (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (element : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (.app predicate element)) :
    ProofSyntax Const Δ (evidence signature predicate (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index element tail) (weakenCtx Γ signature.zero)) :=
  introduce signature predicate _ _ _ element (IndexedVectorPositions.here signature index element tail) member

theorem head_free (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (element : Term Const Γ signature.element) (tail : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (.app predicate element)) (free : member.FunctionExtensionalityFree) :
    (head signature predicate index element tail member).FunctionExtensionalityFree :=
  introduce_free _ _ _ _ _ _ _ _ (IndexedVectorPositions.here_free _ _ _ _) free

def tail (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (present : ProofSyntax Const Δ (evidence signature predicate index vector position)) :
    ProofSyntax Const Δ (evidence signature predicate (.app (weakenCtx Γ signature.successor) index)
      (signature.consValue index first vector) (.app (weakenCtx Γ signature.successor) position)) := by
  apply ProofSyntax.exE present
  apply ProofSyntax.castIndices rfl ?_
    (introduce signature (weaken predicate) (.app (weakenCtx _ signature.successor) (weaken index))
      (signature.consValue (weaken index) (weaken first) (weaken vector))
      (.app (weakenCtx _ signature.successor) (weaken position)) (.var .vz)
      (IndexedVectorPositions.there signature (weaken index) (weaken first) (weaken vector) (weaken position) (.var .vz)
        (.andEL (.hyp 0))) (.andER (.hyp 0)))
  simp only [weaken,evidence_rename,HOL.rename,rename_weakenCtx,IndexedVectorPredicate.Signature.consValue]

theorem tail_free (predicate : Term Const Γ (signature.element ⇒ .prop)) (index : Term Const Γ signature.number)
    (first : Term Const Γ signature.element) (vector : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (present : ProofSyntax Const Δ (evidence signature predicate index vector position))
    (free : present.FunctionExtensionalityFree) :
    (tail signature predicate index first vector position present).FunctionExtensionalityFree := by
  unfold tail
  refine ⟨free,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply introduce_free
  · exact IndexedVectorPositions.there_free _ _ _ _ _ _ _ trivial
  · trivial

#print axioms introduce_free
#print axioms tail_free
end Mettapedia.Logic.HOL.IndexedVectorLookupWitnesses
