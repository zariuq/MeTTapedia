import Mettapedia.Logic.HOL.SuccessorOrderArithmetic

/-!
# Typed substitution of retained successor arithmetic

The closed zero and successor programs are unchanged. All three displayed
Peano premises and their hypothesis occurrences move through the same typed
substitution as the surrounding proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SuccessorOrder.PeanoEvidence
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
  {successor : ClosedTerm Const (number ⇒ number)} {zero : ClosedTerm Const number}
  {assumptions : List (Formula Const Γ)}

def subst (evidence : PeanoEvidence successor zero assumptions) (images : Subst Const Γ Ξ) :
    PeanoEvidence successor zero (assumptions.map (HOL.subst images)) where
  separation := .castIndices rfl (by
    simp only [NaturalNumeralProofs.separation,HOL.subst,Subst.lift,subst_weaken,subst_weakenCtx])
    (evidence.separation.subst images)
  injectivity := .castIndices rfl (by
    simp only [NaturalNumeralProofs.injectivity,HOL.subst,Subst.lift,subst_weaken,subst_weakenCtx,HOL.rename,Rename.weaken])
    (evidence.injectivity.subst images)
  induction := .castIndices rfl (by
    simp only [NaturalRecursionProofs.inductionPrinciple,HOL.subst,Subst.lift,subst_weaken,subst_weakenCtx,HOL.rename,Rename.weaken])
    (evidence.induction.subst images)

theorem subst_free (evidence : PeanoEvidence successor zero assumptions) (images : Subst Const Γ Ξ)
    (free : evidence.Free) : (evidence.subst images).Free := by
  unfold Free subst
  dsimp only
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.1
  · constructor
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.2.1
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free.2.2

#print axioms subst_free
end Mettapedia.Logic.HOL.SuccessorOrder.PeanoEvidence
