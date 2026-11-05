import Mettapedia.Logic.HOL.IndexedVectorPositions
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree

/-!
# Retained equality transport of indexed Vector lookups

Vector, position and element equalities act on the existing lookup formula
through a single typed hole. Array observation transports the position and
its actual selected element together. The recipes preserve the original
ordered hypotheses and introduce neither eta nor function extensionality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPositions
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  (signature : IndexedVectorPredicate.Signature Const) {Γ : Ctx Base}
  {Δ : List (Formula Const Γ)}

def lookup_vec_eq (index : Term Const Γ signature.number)
    (first second : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element) (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (lookup signature index first position element)
      (lookup signature index second position element)) := by
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.holeCongr
    (lookup signature (weaken index) (.var .vz) (weaken position) (weaken element)) same)
  simp only [instantiate,lookup_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem lookup_vec_eq_free (index : Term Const Γ signature.number)
    (first second : Term Const Γ signature.vector) (position : Term Const Γ signature.number)
    (element : Term Const Γ signature.element) (same : ProofSyntax Const Δ (.eq first second))
    (free : same.FunctionExtensionalityFree) :
    (lookup_vec_eq signature index first second position element same).FunctionExtensionalityFree := by
  unfold lookup_vec_eq
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ContextualTrinity.holeCongr_free _ _).mpr free

def lookup_position_eq (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (first second : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (lookup signature index vector first element)
      (lookup signature index vector second element)) := by
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.holeCongr
    (lookup signature (weaken index) (weaken vector) (.var .vz) (weaken element)) same)
  simp only [instantiate,lookup_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem lookup_position_eq_free (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (first second : Term Const Γ signature.number) (element : Term Const Γ signature.element)
    (same : ProofSyntax Const Δ (.eq first second)) (free : same.FunctionExtensionalityFree) :
    (lookup_position_eq signature index vector first second element same).FunctionExtensionalityFree := by
  unfold lookup_position_eq
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ContextualTrinity.holeCongr_free _ _).mpr free

def lookup_element_eq (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (first second : Term Const Γ signature.element)
    (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (lookup signature index vector position first)
      (lookup signature index vector position second)) := by
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.holeCongr
    (lookup signature (weaken index) (weaken vector) (weaken position) (.var .vz)) same)
  simp only [instantiate,lookup_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem lookup_element_eq_free (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (position : Term Const Γ signature.number) (first second : Term Const Γ signature.element)
    (same : ProofSyntax Const Δ (.eq first second)) (free : same.FunctionExtensionalityFree) :
    (lookup_element_eq signature index vector position first second same).FunctionExtensionalityFree := by
  unfold lookup_element_eq
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ContextualTrinity.holeCongr_free _ _).mpr free

def lookup_arrayAt_eq (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (first second : Term Const Γ signature.number) (same : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (lookup signature index vector first (.app array first))
      (lookup signature index vector second (.app array second))) := by
  apply ProofSyntax.castIndices rfl ?_ (ContextualTrinity.holeCongr
    (lookup signature (weaken index) (weaken vector) (.var .vz) (.app (weaken array) (.var .vz))) same)
  simp only [instantiate,lookup_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem lookup_arrayAt_eq_free (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (array : Term Const Γ (signature.number ⇒ signature.element))
    (first second : Term Const Γ signature.number) (same : ProofSyntax Const Δ (.eq first second))
    (free : same.FunctionExtensionalityFree) :
    (lookup_arrayAt_eq signature index vector array first second same).FunctionExtensionalityFree := by
  unfold lookup_arrayAt_eq
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ContextualTrinity.holeCongr_free _ _).mpr free

#print axioms lookup_vec_eq_free
#print axioms lookup_position_eq_free
#print axioms lookup_element_eq_free
#print axioms lookup_arrayAt_eq_free

end Mettapedia.Logic.HOL.IndexedVectorPositions
