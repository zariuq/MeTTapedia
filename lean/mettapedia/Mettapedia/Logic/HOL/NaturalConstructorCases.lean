import Mettapedia.Logic.HOL.SuccessorOrderArithmetic

/-!
# Retained zero-or-successor coverage from natural induction

Natural induction supplies a scoped predecessor witness for every nonzero
point. Coverage alone does not assert disjointness, injectivity or uniqueness.
The retained construction is used when a vector lookup splits its position
into the head case and a successor position in the tail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.NaturalConstructorCases
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {number : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    {Δ : List (Formula Const Γ)}

def casesAt (point : Term Const Γ number) : Formula Const Γ :=
  .or (.eq point (weakenCtx Γ zero))
    (.ex (.eq (weaken point) (.app (weakenCtx _ successor) (.var .vz))))

theorem casesAt_subst (images : Subst Const Γ Ξ) (point : Term Const Γ number) :
    HOL.subst images (casesAt zero successor point) = casesAt zero successor (HOL.subst images point) := by
  simp only [casesAt,HOL.subst,subst_weakenCtx,subst_weaken,Subst.lift]

theorem casesAt_rename (rho : Rename Base Γ Ξ) (point : Term Const Γ number) :
    HOL.rename rho (casesAt zero successor point) = casesAt zero successor (HOL.rename rho point) := by
  simpa only [subst_ofRename] using casesAt_subst zero successor (Subst.ofRename rho) point

def predicate : Term Const Γ (number ⇒ .prop) := .lam (casesAt zero successor (.var .vz))

theorem predicate_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (predicate zero successor) = predicate (Γ := Ξ) zero successor := by
  simp only [predicate,HOL.rename,casesAt_rename,Rename.lift]

def predicate_beta (point : Term Const Γ number) :
    ProofSyntax Const Δ (.eq (.app (predicate zero successor) point) (casesAt zero successor point)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point (casesAt zero successor (.var .vz)))
  simp only [instantiate,casesAt_subst,HOL.subst,Subst.single]
  rfl

theorem predicate_beta_free (point : Term Const Γ number) :
    (predicate_beta (Δ := Δ) zero successor point).FunctionExtensionalityFree := by
  unfold predicate_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def successorCase (point : Term Const Γ number) :
    ProofSyntax Const Δ (casesAt zero successor (.app (weakenCtx Γ successor) point)) := by
  apply ProofSyntax.orIR
  apply ProofSyntax.exI point
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl (.app (weakenCtx Γ successor) point))
  simp only [instantiate,HOL.subst,subst_weakenCtx,PredicateFixedPoint.subst_single_weaken,Subst.single]

theorem successorCase_free (point : Term Const Γ number) :
    (successorCase (Δ := Δ) zero successor point).FunctionExtensionalityFree := by
  unfold successorCase
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def successorClosed : ProofSyntax Const Δ (SuccessorOrder.successorClosed successor (predicate zero successor)) := by
  refine .allI (.impI ?_)
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (predicate_beta zero successor (.app (weakenCtx (number :: Γ) successor) (.var .vz))))
      (successorCase zero successor (.var .vz)))
  simp only [weaken,predicate_rename]

theorem successorClosed_free : (successorClosed (Δ := Δ) zero successor).FunctionExtensionalityFree := by
  unfold successorClosed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨predicate_beta_free _ _ _,successorCase_free _ _ _⟩

def fromInduction (point : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (casesAt zero successor point) :=
  .impE (.eqPropEL (predicate_beta zero successor point))
    (SuccessorOrder.inductionAt successor zero (predicate zero successor) point principle
      (.impE (.eqPropER (predicate_beta zero successor (weakenCtx Γ zero))) (.orIL (.eqRefl _)))
      (successorClosed zero successor))

theorem fromInduction_free (point : Term Const Γ number)
    (principle : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) :
    (fromInduction zero successor point principle).FunctionExtensionalityFree :=
  ⟨predicate_beta_free _ _ _,SuccessorOrder.inductionAt_free _ _ _ _ principle _ _ free
    ⟨predicate_beta_free _ _ _,True.intro⟩ (successorClosed_free _ _)⟩

#print axioms fromInduction_free
end Mettapedia.Logic.HOL.NaturalConstructorCases
