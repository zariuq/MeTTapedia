import Mettapedia.CategoryTheory.CanonicalSlicePullbackCoherence
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pullback universal-property comparisons are the adjoint comparisons

The comparisons defined by pullback projections agree with the
comparisons obtained as mates of postcomposition. The proof uses the
complete counit equation and the pullback universal property. Thus the
coherent slice action and its dependent adjunctions share the same
choices of unit and composition comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.CanonicalSlicePullback

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]

theorem identity_eq_adjoint (base : C) : identity base = Over.pullbackId := by
  apply Iso.ext
  apply NatTrans.ext
  funext object
  apply Over.OverMorphism.ext
  change (identityComponent object).hom.left = ((Over.pullbackId).hom.app object).left
  rw [identityComponent_left]
  have law := conjugateEquiv_counit (Over.mapPullbackAdj (𝟙 base))
    (Adjunction.id (C := Over base)) (Over.mapId base).inv object
  have readout := congrArg Over.Hom.left law
  simp [Over.pullbackId, Over.mapId, Adjunction.id,
    Over.mapPullbackAdj_counit_app] at readout ⊢

variable {first middle last : C} (f : first ⟶ middle) (g : middle ⟶ last)

theorem adjointCompositionInverse_fst (object : Over last) :
    ((Over.pullbackComp f g).inv.app object).left ≫
      pullback.fst object.hom (f ≫ g) =
      pullback.fst (pullback.snd object.hom g) f ≫ pullback.fst object.hom g := by
  have law := conjugateEquiv_counit
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom object
  have readout := congrArg Over.Hom.left law
  simpa [Over.pullbackComp, Over.mapComp, Adjunction.comp_counit_app,
    Over.mapPullbackAdj_counit_app, Over.map] using readout

theorem composition_eq_adjoint : composition f g = Over.pullbackComp f g := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext object
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (compositionInverseComponent f g object).hom.left ≫
        pullback.fst object.hom (f ≫ g) = _
    rw [compositionInverseComponent_fst]
    exact (adjointCompositionInverse_fst f g object).symm
  · change (compositionInverseComponent f g object).hom.left ≫
        pullback.snd object.hom (f ≫ g) = _
    rw [compositionInverseComponent_snd]
    exact (Over.w ((Over.pullbackComp f g).inv.app object)).symm

end Mettapedia.CategoryTheory.CanonicalSlicePullback
