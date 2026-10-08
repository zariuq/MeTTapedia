import Mettapedia.CategoryTheory.ElementaryToposStableEpimorphisms
import Mettapedia.CategoryTheory.MonoArrowFibration

/-!
# Image preserves Cartesian arrows in an elementary topos

Pulling back an image inclusion gives a mono factorization of the original
pullback arrow. Its first factor is a pullback of the original image's
epimorphism, so it is again a strong epimorphism. The resulting image
isomorphism identifies the actual image-map square with a pullback.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C] [HasImages C]

def pullbackImageFactor {first second : Arrow C} (square : first ⟶ second) :
    first.left ⟶ pullback (Limits.image.ι second.hom) square.right :=
  pullback.lift (square.left ≫ factorThruImage second.hom) first.hom (by
    rw [Category.assoc, Limits.image.fac]
    exact Arrow.w square)

@[reassoc (attr := simp)] theorem pullbackImageFactor_fst
    {first second : Arrow C} (square : first ⟶ second) :
    pullbackImageFactor square ≫ pullback.fst (Limits.image.ι second.hom) square.right =
      square.left ≫ factorThruImage second.hom := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pullbackImageFactor_snd
    {first second : Arrow C} (square : first ⟶ second) :
    pullbackImageFactor square ≫ pullback.snd (Limits.image.ι second.hom) square.right =
      first.hom := pullback.lift_snd _ _ _

theorem image_factor_pullback {first second : Arrow C} (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    IsPullback square.left (pullbackImageFactor square) (factorThruImage second.hom)
      (pullback.fst (Limits.image.ι second.hom) square.right) := by
  have outer : IsPullback square.left
      (pullbackImageFactor square ≫ pullback.snd (Limits.image.ι second.hom) square.right)
      (factorThruImage second.hom ≫ Limits.image.ι second.hom) square.right := by
    simpa only [pullbackImageFactor_snd, Limits.image.fac] using cartesian
  exact outer.of_bot (pullbackImageFactor_fst square).symm
    (IsPullback.of_hasPullback (Limits.image.ι second.hom) square.right)

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)

def pullbackStrongImageFactorisation {first second : Arrow C} (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    StrongEpiMonoFactorisation first.hom := by
  have : StrongEpiCategory C := ElementaryToposImages.strongEpiCategory classifier
  have : Epi (pullbackImageFactor square) :=
    ElementaryToposStableEpimorphisms.epi_of_pullback classifier
      (image_factor_pullback square cartesian)
  exact {
    I := pullback (Limits.image.ι second.hom) square.right
    m := pullback.snd (Limits.image.ι second.hom) square.right
    e := pullbackImageFactor square
    e_strong_epi := strongEpi_of_epi _
    fac := pullbackImageFactor_snd square }

def imagePullbackIso {first second : Arrow C} (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    Limits.image first.hom ≅ pullback (Limits.image.ι second.hom) square.right :=
  IsImage.isoExt (Image.isImage first.hom)
    (pullbackStrongImageFactorisation classifier square cartesian).toMonoIsImage

@[reassoc (attr := simp)] theorem imagePullbackIso_snd
    {first second : Arrow C} (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    (imagePullbackIso classifier square cartesian).hom ≫
        pullback.snd (Limits.image.ι second.hom) square.right = Limits.image.ι first.hom :=
  IsImage.isoExt_hom_m _ _

variable [HasImageMaps C]

@[reassoc (attr := simp)] theorem imagePullbackIso_fst
    {first second : Arrow C} (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    (imagePullbackIso classifier square cartesian).hom ≫
        pullback.fst (Limits.image.ι second.hom) square.right = Limits.image.map square := by
  apply (cancel_mono (Limits.image.ι second.hom)).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, imagePullbackIso_snd,
    Limits.image.map_ι]

include classifier in
theorem image_square_pullback {first second : Arrow C} (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    IsPullback (Limits.image.map square) (Limits.image.ι first.hom)
      (Limits.image.ι second.hom) square.right := by
  apply (IsPullback.of_hasPullback (Limits.image.ι second.hom) square.right).of_iso'
    (imagePullbackIso classifier square cartesian) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      imagePullbackIso_fst classifier square cartesian
  · simpa only [Iso.refl_hom, Category.comp_id] using
      imagePullbackIso_snd classifier square cartesian
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

include classifier in
theorem image_preserves_cartesian {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsCartesian square.right square] :
    (projection C).IsCartesian square.right ((image (C := C)).map square) := by
  apply (cartesian_iff_pullback ((image (C := C)).map square)).mpr
  exact image_square_pullback classifier square
    ((CodomainComprehension.cartesian_iff_pullback square).mp inferInstance)

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
