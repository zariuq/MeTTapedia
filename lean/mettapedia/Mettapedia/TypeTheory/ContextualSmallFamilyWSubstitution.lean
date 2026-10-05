import Mettapedia.TypeTheory.ContextualSmallFamilyWCone

/-!
# Actual W substitution over wider contextual parameters

An arbitrary parameter transformation compares the independently formed
small future signatures. Equality elimination supplies actual tree
inverses, while naturality follows from their complete raw-tree readouts.
The comparison retains every arrow and dependent position.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitution

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence ContextualSmallFamilyWTypes
open ContextualWitnessCover
open PowerClassPresheafBaseChange

universe u v w
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

theorem signature_change (point : other.Elements) :
    signature domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) =
      signature (domainUnder change domain) (bodyUnder change domain body) point := by
  apply Sigma.ext (futureDomain_change change domain point).symm
  apply ContextualWReindexing.position_transport_heq (futureDomain_change change domain point).symm
  exact futureBody_change change domain body point

def wComparison (point : other.Elements) :
    WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point) ≃
      WAt (domainUnder change domain) (bodyUnder change domain body) point :=
  ContextualWReindexing.signatureEquiv (signature_change change domain body point) (ContextualSmallFamilyUniverse.root point.1)

theorem wComparison_raw (point : other.Elements)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    HEq (wComparison change domain body point tree).val tree.val :=
  ContextualWReindexing.signatureEquiv_raw _ _ _

theorem wComparison_natural {first second : other.Elements} (step : first ⟶ second)
    (tree : WAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj first)) :
    wComparison change domain body second
      (wMap domain body ((ContextualSmallFamilyUniverse.elementMap change).map step) tree) =
      wMap (domainUnder change domain) (bodyUnder change domain body) step
        (wComparison change domain body first tree) := by
  apply Subtype.ext
  apply eq_of_heq
  have restrictEq := ContextualWReindexing.restrict_signature_heq (signature_change change domain body first)
    (ContextualSmallFamilyUniverse.rootArrow step.1) tree.val (wComparison change domain body first tree).val
    (wComparison_raw change domain body first tree).symm
  have pullEq := ContextualWReindexing.pull_congr (first := ContextualSmallFamilyUniverse.futurePrefix step.1)
    rfl (signature_change change domain body first) rfl _ _ restrictEq
  exact (wComparison_raw change domain body second _).trans
    ((wMap_raw domain body ((ContextualSmallFamilyUniverse.elementMap change).map step) tree).trans
      (pullEq.trans (wMap_raw (domainUnder change domain) (bodyUnder change domain body) step _).symm))

noncomputable def wSubstitution :
    NatTrans (ContextualSmallFamilyUniverse.substitutedFamily (w domain body) change)
      (w (domainUnder change domain) (bodyUnder change domain body)) where
  app point := TypeCat.ofHom (wComparison change domain body point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    exact wComparison_natural change domain body step

noncomputable def wSubstitutionInverse :
    NatTrans (w (domainUnder change domain) (bodyUnder change domain body))
      (ContextualSmallFamilyUniverse.substitutedFamily (w domain body) change) where
  app point := TypeCat.ofHom (wComparison change domain body point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro tree
    apply (wComparison change domain body second).injective
    change wComparison change domain body second
      ((wComparison change domain body second).symm (wMap _ _ step tree)) =
      wComparison change domain body second
        (wMap domain body ((ContextualSmallFamilyUniverse.elementMap change).map step)
          ((wComparison change domain body first).symm tree))
    rw [Equiv.apply_symm_apply, wComparison_natural]
    exact congrArg (wMap (domainUnder change domain) (bodyUnder change domain body) step)
      ((wComparison change domain body first).apply_symm_apply tree).symm

theorem wSubstitution_left :
    composeNat (wSubstitution change domain body) (wSubstitutionInverse change domain body) =
      identityNat (ContextualSmallFamilyUniverse.substitutedFamily (w domain body) change) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (wComparison change domain body point).symm_apply_apply

theorem wSubstitution_right :
    composeNat (wSubstitutionInverse change domain body) (wSubstitution change domain body) =
      identityNat (w (domainUnder change domain) (bodyUnder change domain body)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (wComparison change domain body point).apply_symm_apply

noncomputable def sectionComparison :
    (ContextualSmallFamilyUniverse.substitutedFamily (w domain body) change).sections ≃
      (w (domainUnder change domain) (bodyUnder change domain body)).sections where
  toFun term := ⟨fun point => wComparison change domain body point (term.val point), by
    intro first second step
    exact (wComparison_natural change domain body step (term.val first)).symm.trans
      (congrArg (wComparison change domain body second) (term.property step))⟩
  invFun term := ⟨fun point => (wComparison change domain body point).symm (term.val point), by
    intro first second step
    apply (wComparison change domain body second).injective
    change wComparison change domain body second
      (wMap domain body ((ContextualSmallFamilyUniverse.elementMap change).map step)
        ((wComparison change domain body first).symm (term.val first))) =
      wComparison change domain body second ((wComparison change domain body second).symm (term.val second))
    rw [wComparison_natural]
    exact (congrArg (wMap (domainUnder change domain) (bodyUnder change domain body) step)
      ((wComparison change domain body first).apply_symm_apply (term.val first))).trans
        ((term.property step).trans ((wComparison change domain body second).apply_symm_apply (term.val second)).symm)⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (wComparison change domain body point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (wComparison change domain body point).apply_symm_apply (term.val point)

end Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitution
