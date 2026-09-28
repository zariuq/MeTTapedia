import Mettapedia.OSLF.Syntax.CartesianModelLexYonedaExtension
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Descent of representable presheaf extensions to the target category

The Yoneda-mediated extension has representable values. Full faithfulness
of Yoneda therefore lets its objectwise representation assemble into a
functor in the target category. Its finite-limit preservation and
restriction comparison are established through the Yoneda embedding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D] [HasFiniteLimits D]

/-- Yoneda identifies the target with the full subcategory of its
representable presheaves. -/
noncomputable def targetRepresentableEquivalence :
    D ≌ (RepresentableTargetPresheaves D).FullSubcategory := by
  let Y : D ⥤ Dᵒᵖ ⥤ Type := yoneda
  exact Y.toEssImage.asEquivalence

/-- Descend the representable presheaf extension through the inverse of
Yoneda's equivalence onto its essential image. -/
noncomputable def descendYonedaExtension
    (F : CartesianTargetInterpretations C D) :
    FinitePresentationObjects C ⥤ D :=
  (RepresentableTargetPresheaves D).lift
      (yonedaPresheafExtension C D F).1
      (yonedaPresheafExtension_representable C D F) ⋙
    (targetRepresentableEquivalence D).inverse

/-- The descended target interpretation recovers the canonical presheaf
extension after Yoneda. -/
noncomputable def descendYonedaExtensionCompIso
    (F : CartesianTargetInterpretations C D) :
    descendYonedaExtension C D F ⋙ (yoneda : D ⥤ Dᵒᵖ ⥤ Type) ≅
      (yonedaPresheafExtension C D F).1 := by
  let Q := RepresentableTargetPresheaves D
  let E := yonedaPresheafExtension C D F
  let L : FinitePresentationObjects C ⥤ Q.FullSubcategory :=
    Q.lift E.1 (yonedaPresheafExtension_representable C D F)
  let Y : D ⥤ Q.FullSubcategory := (yoneda : D ⥤ Dᵒᵖ ⥤ Type).toEssImage
  let e := targetRepresentableEquivalence D
  calc
    _ ≅ ((L ⋙ e.inverse) ⋙ Y) ⋙ Q.ι := Iso.refl _
    _ ≅ (L ⋙ (e.inverse ⋙ Y)) ⋙ Q.ι :=
      Functor.isoWhiskerRight (Functor.associator L e.inverse Y) Q.ι
    _ ≅ (L ⋙ 𝟭 Q.FullSubcategory) ⋙ Q.ι :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft L e.counitIso) Q.ι
    _ ≅ L ⋙ Q.ι := Functor.isoWhiskerRight L.rightUnitor Q.ι
    _ ≅ E.1 := Q.liftCompιIso E.1
      (yonedaPresheafExtension_representable C D F)

/-- The target-valued extension preserves finite limits, as reflected by
fully faithful Yoneda from the proved presheaf extension. -/
theorem descendYonedaExtension_preservesFiniteLimits
    (F : CartesianTargetInterpretations C D) :
    PreservesFiniteLimits (descendYonedaExtension C D F) := by
  have hE : PreservesFiniteLimits (yonedaPresheafExtension C D F).1 :=
    (yonedaPresheafExtension C D F).2
  have hcomp : PreservesFiniteLimits
      (descendYonedaExtension C D F ⋙ (yoneda : D ⥤ Dᵒᵖ ⥤ Type)) :=
    preservesFiniteLimits_of_natIso
      (descendYonedaExtensionCompIso C D F).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (descendYonedaExtension C D F) (yoneda : D ⥤ Dᵒᵖ ⥤ Type)

/-- The descended extension, now an object of the target-valued
left-exact interpretation category. -/
noncomputable def extendCartesianTargetModel
    (F : CartesianTargetInterpretations C D) :
    LeftExactTargetInterpretations C D :=
  ⟨descendYonedaExtension C D F,
    descendYonedaExtension_preservesFiniteLimits C D F⟩

/-- Restricting the descended extension recovers the authored model.
The comparison is reflected from the pointwise presheaf comparison by
Yoneda's full faithfulness. -/
noncomputable def extendCartesianTargetModelRestrictionIso
    (F : CartesianTargetInterpretations C D) :
    authoredContext C ⋙ (extendCartesianTargetModel C D F).1 ≅ F.1 := by
  let G := descendYonedaExtension C D F
  let Fp := yonedaOfCartesianTargetModel C D F
  have hY : (authoredContext C ⋙ G) ⋙
        (yoneda : D ⥤ Dᵒᵖ ⥤ Type) ≅
      F.1 ⋙ (yoneda : D ⥤ Dᵒᵖ ⥤ Type) := by
    calc
      _ ≅ authoredContext C ⋙ (G ⋙ (yoneda : D ⥤ Dᵒᵖ ⥤ Type)) :=
        Functor.associator _ _ _
      _ ≅ authoredContext C ⋙ (yonedaPresheafExtension C D F).1 :=
        Functor.isoWhiskerLeft _ (descendYonedaExtensionCompIso C D F)
      _ ≅ Fp.1 :=
        extendPresheafAuthoredModelRestrictionIso C D Fp
      _ ≅ F.1 ⋙ (yoneda : D ⥤ Dᵒᵖ ⥤ Type) := Iso.refl _
  exact Functor.fullyFaithfulCancelRight
    (yoneda : D ⥤ Dᵒᵖ ⥤ Type) hY

/-- Every product-preserving authored interpretation in a small finitely
complete target extends to a left-exact interpretation of the relative
finite-presentation category. Fullness on interpretation maps and the full
equivalence are separate obligations. -/
instance restrictLeftExactTarget_essSurj :
    (restrictLeftExactTarget C D).EssSurj where
  mem_essImage F :=
    ⟨extendCartesianTargetModel C D F,
      ⟨(CartesianTargetInterpretation C D).isoMk
        (extendCartesianTargetModelRestrictionIso C D F)⟩⟩

end Mettapedia.OSLF.CartesianContextModels
