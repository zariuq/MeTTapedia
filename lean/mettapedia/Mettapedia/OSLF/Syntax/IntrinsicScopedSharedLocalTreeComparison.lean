import Mettapedia.OSLF.Syntax.IntrinsicScopedSharedLocalPolynomialComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution

/-!
# Firing histories of the unpruned shared-to-local adapter

The cartesian rule-polynomial comparison acts on the existing indexed W-types.
It retains each complete occurrence and every ordered binder-local child.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalTreeComparison

open Mettapedia.TypeTheory
open IntrinsicScopedSharedLocalPolynomialComparison
open AuthoredPositionedRulePolynomial (Judgment)
open IndexedRulePolynomialMorphisms
open BindingSubstitutionAlgebra
open IntrinsicScopedConditionalSubstitution
  (substJudgment castEnv castEnv_heq heq_transport)

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (IntrinsicScopedConditionalPolynomial.Rule S M))

/-- Interpret the actual shared firing history in the unpruned local rules. -/
noncomputable def toLocalTree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :
    IntrinsicScopedConditionalSubstitution.Tree R A j →
      IntrinsicScopedLocalPolynomial.Tree (localRules R) A j :=
  (toLocalPolynomial R A).mapFix () j

/-- Recover the original shared firing history without deleting assignment data. -/
noncomputable def toSharedTree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :
    IntrinsicScopedLocalPolynomial.Tree (localRules R) A j →
      IntrinsicScopedConditionalSubstitution.Tree R A j :=
  (toSharedPolynomial R A).mapFix () j

@[simp] theorem toShared_toLocal (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A)
    (tree : IntrinsicScopedConditionalSubstitution.Tree R A j) :
    toSharedTree R A j (toLocalTree R A j tree) = tree := by
  change (toSharedPolynomial R A).mapFix () j ((toLocalPolynomial R A).mapFix () j tree) = tree
  have compared := Hom.mapFix_comp (toLocalPolynomial R A) (toSharedPolynomial R A) () j tree
  rw [toLocalPolynomial_toSharedPolynomial] at compared
  exact compared.symm.trans (Hom.mapFix_id (IntrinsicScopedConditionalPolynomial.rules R A) () j tree)

@[simp] theorem toLocal_toShared (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A)
    (tree : IntrinsicScopedLocalPolynomial.Tree (localRules R) A j) :
    toLocalTree R A j (toSharedTree R A j tree) = tree := by
  change (toLocalPolynomial R A).mapFix () j ((toSharedPolynomial R A).mapFix () j tree) = tree
  have compared := Hom.mapFix_comp (toSharedPolynomial R A) (toLocalPolynomial R A) () j tree
  rw [toSharedPolynomial_toLocalPolynomial] at compared
  exact compared.symm.trans (Hom.mapFix_id (IntrinsicScopedLocalPolynomial.rules (localRules R) A) () j tree)

/-- The equivalence is justified by retaining the entire original telescope. -/
noncomputable def treeEquiv (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A) :
    IntrinsicScopedConditionalSubstitution.Tree R A j ≃
      IntrinsicScopedLocalPolynomial.Tree (localRules R) A j where
  toFun := toLocalTree R A j
  invFun := toSharedTree R A j
  left_inv := toShared_toLocal R A j
  right_inv := toLocal_toShared R A j

/-- One constructor is transported with its complete ordered recursive family. -/
theorem toLocalTree_roll (A : BindingCloneAlgebra.Algebra.{u} S) {j : Judgment A}
    (shape : IntrinsicScopedConditionalPolynomial.Shape R A j)
    (children : ∀ p : Fin (R.get shape.1.index).premises.length,
      IntrinsicScopedConditionalSubstitution.Tree R A
        (IntrinsicScopedConditionalPolynomial.childJudgment R A shape.1 p)) :
    toLocalTree R A j (.roll shape children) =
      .roll (toLocalShape R shape) (fun p =>
        (show IntrinsicScopedLocalPolynomial.Tree (localRules R) A
          (IntrinsicScopedLocalPolynomial.childJudgment (localRules R) A (toLocalInstance R shape.1) p) from
          (toLocal_child_positionEquiv R shape.1 p).symm ▸
            toLocalTree R A _ (children ((positionEquiv R shape.1) p)))) := rfl

private theorem liftedEnvironment_heq (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (σ : Environment S A.substitution.Carrier Γ Δ)
    {binders binders' : Ctx S} (same : binders = binders') :
    HEq (A.substitution.liftEnvironment σ binders)
      (A.substitution.liftEnvironment σ binders') := by
  cases same
  rfl

private theorem instance_subst_transport {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ) :
    toLocalInstance R (IntrinsicScopedConditionalSubstitution.Instance.subst R occurrence σ) =
    IntrinsicScopedLocalPolynomial.Instance.subst (localRules R) (toLocalInstance R occurrence)
      (castEnv (toLocal_conclusion R occurrence) σ) := by
  have same : castEnv (toLocal_conclusion R occurrence) σ = σ :=
    eq_of_heq (castEnv_heq _ _)
  rw [same]
  exact toLocal_subst R occurrence σ

private theorem liftedPremiseEnvironment_compare {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (position : Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length) :
    HEq (A.substitution.liftEnvironment σ
      ((R.get occurrence.index).premises.get ((positionEquiv R occurrence) position)).binders)
      (A.substitution.liftEnvironment (castEnv (toLocal_conclusion R occurrence) σ)
        (((localRules R).get (toLocalInstance R occurrence).index).2.premises.get position).binders) := by
  have same : castEnv (toLocal_conclusion R occurrence) σ = σ :=
    eq_of_heq (castEnv_heq _ _)
  rw [same]
  exact liftedEnvironment_heq A σ (toLocal_binders R occurrence position).symm

private theorem substitutedPremise_compare {A : BindingCloneAlgebra.Algebra.{u} S}
    (occurrence : IntrinsicScopedConditionalPolynomial.Instance R A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier occurrence.ambient Δ)
    (position : Fin ((localRules R).get (toLocalInstance R occurrence).index).2.premises.length) :
    IntrinsicScopedConditionalPolynomial.childJudgment R A
      (IntrinsicScopedConditionalSubstitution.Instance.subst R occurrence σ)
        ((positionEquiv R occurrence) position) =
    IntrinsicScopedLocalPolynomial.childJudgment (localRules R) A
      (IntrinsicScopedLocalPolynomial.Instance.subst (localRules R) (toLocalInstance R occurrence)
        (castEnv (toLocal_conclusion R occurrence) σ)) position :=
  (toLocal_child_positionEquiv R
    (IntrinsicScopedConditionalSubstitution.Instance.subst R occurrence σ) position).symm.trans
      (IntrinsicScopedLocalPolynomial.childJudgment_congr (localRules R)
        (instance_subst_transport R occurrence σ) position position HEq.rfl)

private theorem substTree_heq_context (A : BindingCloneAlgebra.Algebra.{u} S)
    {j₁ j₂ : Judgment A} (sameJudgment : j₁ = j₂)
    {tree₁ : IntrinsicScopedLocalPolynomial.Tree (localRules R) A j₁}
    {tree₂ : IntrinsicScopedLocalPolynomial.Tree (localRules R) A j₂} (sameTree : HEq tree₁ tree₂)
    {Δ₁ Δ₂ : Ctx S} (sameContext : Δ₁ = Δ₂)
    {σ₁ : Environment S A.substitution.Carrier j₁.1 Δ₁}
    {σ₂ : Environment S A.substitution.Carrier j₂.1 Δ₂} (sameEnv : HEq σ₁ σ₂)
    {target₁ target₂ : Judgment A} (sameTarget : target₁ = target₂)
    (h₁ : substJudgment j₁ σ₁ = target₁) (h₂ : substJudgment j₂ σ₂ = target₂) :
    HEq (IntrinsicScopedLocalPolynomial.substTree (localRules R) A j₁ tree₁ σ₁ target₁ h₁)
      (IntrinsicScopedLocalPolynomial.substTree (localRules R) A j₂ tree₂ σ₂ target₂ h₂) := by
  cases sameContext
  exact IntrinsicScopedLocalPolynomial.substTree_heq (localRules R) A
    sameJudgment sameTree sameEnv sameTarget h₁ h₂

/-- The actual adapter commutes with ambient substitution on every firing history. -/
theorem toLocalTree_substTree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A)
    (tree : IntrinsicScopedConditionalSubstitution.Tree R A j) :
    ∀ {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (hs : substJudgment j σ = target),
      toLocalTree R A target
        (IntrinsicScopedConditionalSubstitution.substTree R A j tree σ target hs) =
      IntrinsicScopedLocalPolynomial.substTree (localRules R) A j
        (toLocalTree R A j tree) σ target hs := by
  refine IndexedPolynomial.Fix.eliminate (IntrinsicScopedConditionalPolynomial.rules R A)
    (fun _ j tree => ∀ {Δ : Ctx S}
      (σ : Environment S A.substitution.Carrier j.1 Δ)
      (target : Judgment A) (hs : substJudgment j σ = target),
      toLocalTree R A target
        (IntrinsicScopedConditionalSubstitution.substTree R A j tree σ target hs) =
      IntrinsicScopedLocalPolynomial.substTree (localRules R) A j
        (toLocalTree R A j tree) σ target hs) ?_ () j tree
  intro base j shape children ih
  cases base
  obtain ⟨occurrence, hconc⟩ := shape
  subst hconc
  intro Δ σ target hs
  refine IntrinsicScopedLocalPolynomial.roll_congr_instance (localRules R)
    (instance_subst_transport R occurrence σ) _ _ _ _ ?_
  intro position otherPosition samePosition
  cases samePosition
  refine HEq.trans (heq_transport _ _) ?_
  refine HEq.trans (heq_of_eq (ih ((positionEquiv R occurrence) position) _ _ _)) ?_
  exact substTree_heq_context R A
    (toLocal_child_positionEquiv R occurrence position).symm
    (heq_transport _ _).symm
    (congrArg (fun binders => binders ++ Δ) (toLocal_binders R occurrence position).symm)
    (liftedPremiseEnvironment_compare R occurrence σ position)
    (substitutedPremise_compare R occurrence σ position) _ _

/-- The inverse tree adapter also preserves the actual contextual action. -/
theorem toSharedTree_substTree (A : BindingCloneAlgebra.Algebra.{u} S) (j : Judgment A)
    (tree : IntrinsicScopedLocalPolynomial.Tree (localRules R) A j)
    {Δ : Ctx S} (σ : Environment S A.substitution.Carrier j.1 Δ)
    (target : Judgment A) (hs : substJudgment j σ = target) :
    toSharedTree R A target
      (IntrinsicScopedLocalPolynomial.substTree (localRules R) A j tree σ target hs) =
    IntrinsicScopedConditionalSubstitution.substTree R A j (toSharedTree R A j tree) σ target hs := by
  apply (treeEquiv R A target).injective
  change toLocalTree R A target _ = toLocalTree R A target _
  rw [toLocal_toShared, toLocalTree_substTree, toLocal_toShared]

/-- Every clone map commutes with the actual complete-history comparison. -/
theorem toLocalTree_mapTree {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (j : Judgment A)
    (tree : IntrinsicScopedConditionalSubstitution.Tree R A j) :
    toLocalTree R B (AuthoredPositionedRulePolynomial.mapJudgment h j)
      ((IntrinsicScopedConditionalPolynomial.presentationMap R h).rules.mapFix () j tree) =
    IntrinsicScopedLocalPolynomial.mapTree (localRules R) h j (toLocalTree R A j tree) := by
  have first := Hom.mapFix_comp (IntrinsicScopedConditionalPolynomial.presentationMap R h).rules
    (toLocalPolynomial R B) () j tree
  have second := Hom.mapFix_comp (toLocalPolynomial R A)
    (IntrinsicScopedLocalPolynomial.presentationMap (localRules R) h).rules () j tree
  have comparison := congrArg (fun map => map.mapFix () j tree) (toLocalPolynomial_map R h)
  exact first.symm.trans (comparison.trans second)

/-- The inverse comparison is natural on complete firing histories. -/
theorem toSharedTree_mapTree {A B : BindingCloneAlgebra.Algebra.{u} S}
    (h : FreeBindingClone.Hom A B) (j : Judgment A)
    (tree : IntrinsicScopedLocalPolynomial.Tree (localRules R) A j) :
    toSharedTree R B (AuthoredPositionedRulePolynomial.mapJudgment h j)
      (IntrinsicScopedLocalPolynomial.mapTree (localRules R) h j tree) =
    (IntrinsicScopedConditionalPolynomial.presentationMap R h).rules.mapFix () j (toSharedTree R A j tree) := by
  apply (treeEquiv R B (AuthoredPositionedRulePolynomial.mapJudgment h j)).injective
  change toLocalTree R B _ _ = toLocalTree R B _ _
  rw [toLocal_toShared, toLocalTree_mapTree, toLocal_toShared]

end Mettapedia.OSLF.Binding.IntrinsicScopedSharedLocalTreeComparison
