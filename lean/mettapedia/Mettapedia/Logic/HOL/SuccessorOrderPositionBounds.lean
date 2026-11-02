import Mettapedia.Logic.HOL.SuccessorOrderArithmetic

/-!
# Successor bounds used by positional lookup

The successor-closure order transports both endpoints through successor
without injectivity. Zero lies below every successor under the explicit
natural-induction principle. Separation and infinitude are not inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {number : Ty Base} {Γ Ξ : Ctx Base}
    (successor : ClosedTerm Const (number ⇒ number))

def aboveNext (lower : Term Const Γ number) : Term Const Γ (number ⇒ .prop) :=
  .lam (.app (.app (weakenCtx _ (less successor)) (weaken lower))
    (.app (weakenCtx _ successor) (.var .vz)))

@[simp] theorem aboveNext_subst (images : Subst Const Γ Ξ) (lower : Term Const Γ number) :
    HOL.subst images (aboveNext successor lower) = aboveNext successor (HOL.subst images lower) := by
  simp only [aboveNext, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

@[simp] theorem aboveNext_rename (rho : Rename Base Γ Ξ) (lower : Term Const Γ number) :
    HOL.rename rho (aboveNext successor lower) = aboveNext successor (HOL.rename rho lower) := by
  simpa only [subst_ofRename] using aboveNext_subst successor (Subst.ofRename rho) lower

variable {Δ : List (Formula Const Γ)}

def aboveNext_beta (lower upper : Term Const Γ number) : ProofSyntax Const Δ
    (.eq (.app (aboveNext successor lower) upper)
      (.app (.app (weakenCtx Γ (less successor)) lower) (.app (weakenCtx Γ successor) upper))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta upper
    (.app (.app (weakenCtx _ (less successor)) (weaken lower)) (.app (weakenCtx _ successor) (.var .vz))))
  simp only [aboveNext, instantiate, HOL.subst, subst_weakenCtx, Subst.single,
    PredicateFixedPoint.subst_single_weaken]

theorem aboveNext_beta_free (lower upper : Term Const Γ number) :
    (aboveNext_beta (Δ := Δ) successor lower upper).FunctionExtensionalityFree := by
  simp [aboveNext_beta, ProofSyntax.FunctionExtensionalityFree]

def aboveNext_closed (lower : Term Const Γ number) :
    ProofSyntax Const Δ (successorClosed successor (aboveNext successor lower)) := by
  refine .allI (.impI ?_)
  let premise := Term.app (weaken (aboveNext successor lower)) (.var .vz)
  let hypotheses := premise :: weakenHyps Δ
  have previous : ProofSyntax Const hypotheses
      (.app (.app (weakenCtx _ (less successor)) (weaken lower)) (.app (weakenCtx _ successor) (.var .vz))) := by
    apply ProofSyntax.impE (.eqPropEL (aboveNext_beta successor (weaken lower) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypotheses) ⟨0, by simp [hypotheses]⟩)
    change premise = _
    simp only [premise, weaken, aboveNext_rename]
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (aboveNext_beta successor (weaken lower) (.app (weakenCtx _ successor) (.var .vz))))
      (lessStep successor (weaken lower) (.app (weakenCtx _ successor) (.var .vz)) previous))
  simp only [weaken, aboveNext_rename]

theorem aboveNext_closed_free (lower : Term Const Γ number) :
    (aboveNext_closed (Δ := Δ) successor lower).FunctionExtensionalityFree := by
  unfold aboveNext_closed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨aboveNext_beta_free successor _ _, ?_⟩
  apply lessStep_free
  exact ⟨aboveNext_beta_free successor _ _, (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

def lessSuccessorMap (lower upper : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) lower) upper)) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) (.app (weakenCtx Γ successor) lower))
      (.app (weakenCtx Γ successor) upper)) :=
  .impE (.eqPropEL (aboveNext_beta successor (.app (weakenCtx Γ successor) lower) upper))
    (lessEliminate successor lower upper (aboveNext successor (.app (weakenCtx Γ successor) lower)) present
      (.impE (.eqPropER (aboveNext_beta successor (.app (weakenCtx Γ successor) lower)
        (.app (weakenCtx Γ successor) lower))) (lessNext successor (.app (weakenCtx Γ successor) lower)))
      (aboveNext_closed successor (.app (weakenCtx Γ successor) lower)))

theorem lessSuccessorMap_free (lower upper : Term Const Γ number)
    (present : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) lower) upper))
    (free : present.FunctionExtensionalityFree) :
    (lessSuccessorMap successor lower upper present).FunctionExtensionalityFree := by
  unfold lessSuccessorMap
  refine ⟨aboveNext_beta_free successor _ _, ?_⟩
  apply lessEliminate_free
  · exact free
  · exact ⟨aboveNext_beta_free successor _ _, lessNext_free successor _⟩
  · exact aboveNext_closed_free successor _

variable (zero : ClosedTerm Const number)

theorem inductionPrinciple_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)) =
      NaturalRecursionProofs.inductionPrinciple (weakenCtx Ξ zero) (weakenCtx Ξ successor) := by
  simp only [NaturalRecursionProofs.inductionPrinciple, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]
  rfl

def zeroLessSuccessor (index : Term Const Γ number)
    (principle : ProofSyntax Const Δ
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor))) :
    ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less successor)) (weakenCtx Γ zero))
      (.app (weakenCtx Γ successor) index)) :=
  .impE (.eqPropEL (aboveNext_beta successor (weakenCtx Γ zero) index))
    (inductionAt successor zero (aboveNext successor (weakenCtx Γ zero)) index principle
      (.impE (.eqPropER (aboveNext_beta successor (weakenCtx Γ zero) (weakenCtx Γ zero)))
        (lessNext successor (weakenCtx Γ zero)))
      (aboveNext_closed successor (weakenCtx Γ zero)))

theorem zeroLessSuccessor_free (index : Term Const Γ number)
    (principle : ProofSyntax Const Δ
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx Γ zero) (weakenCtx Γ successor)))
    (free : principle.FunctionExtensionalityFree) :
    (zeroLessSuccessor successor zero index principle).FunctionExtensionalityFree := by
  unfold zeroLessSuccessor
  refine ⟨aboveNext_beta_free successor _ _, ?_⟩
  apply inductionAt_free
  · exact free
  · exact ⟨aboveNext_beta_free successor _ _, lessNext_free successor _⟩
  · exact aboveNext_closed_free successor _

#print axioms lessSuccessorMap_free
#print axioms zeroLessSuccessor_free
end Mettapedia.Logic.HOL.SuccessorOrder
