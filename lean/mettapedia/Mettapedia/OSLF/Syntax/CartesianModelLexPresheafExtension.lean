import Mettapedia.OSLF.Syntax.CartesianModelLexRepresentability
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Pointwise extension of presheaf-valued authored models

A product-preserving authored interpretation in a presheaf category is a
natural family of Set-valued authored models. Extending those models by the
proved Set-valued classifying equivalence, then flipping the two functor
arguments, gives a finite-limit-preserving interpretation into presheaves.
The comparison with the input model and the descent to arbitrary targets
are separate coherence results.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D]

/-- A presheaf-valued authored model is a natural family of Set-valued
cartesian models indexed by the opposite target category. -/
noncomputable def presheafAuthoredModelFamily
    (F : CartesianTargetInterpretations C (Dᵒᵖ ⥤ Type)) :
    Dᵒᵖ ⥤ Models C :=
  (ProductModel C).lift F.1.flip (fun d => by
    have hF : PreservesFiniteProducts F.1 := F.2
    change PreservesFiniteProducts
      (F.1 ⋙ (evaluation Dᵒᵖ Type).obj d)
    infer_instance)

/-- The pointwise Set-valued extension, with its variables flipped back to
a functor from relative finite presentations to target presheaves. -/
noncomputable def extendPresheafAuthoredModel
    (F : CartesianTargetInterpretations C (Dᵒᵖ ⥤ Type)) :
    LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type) := by
  let family := presheafAuthoredModelFamily C D F
  let raw : FinitePresentationObjects C ⥤ Dᵒᵖ ⥤ Type :=
    (family ⋙ extendModelToLex C ⋙ (LeftExactSetSemantics C).ι).flip
  have hraw : PreservesFiniteLimits raw := by
    apply preservesFiniteLimits_of_evaluation raw
    intro d
    have hlex : PreservesFiniteLimits
        (((extendModelToLex C).obj (family.obj d)).1) :=
      ((extendModelToLex C).obj (family.obj d)).2
    change PreservesFiniteLimits
      (((extendModelToLex C).obj (family.obj d)).1)
    exact hlex
  exact ⟨raw, hraw⟩

/-- Pointwise reconstruction is naturally isomorphic to the input authored
presheaf model, including maps in the presheaf index. -/
noncomputable def extendPresheafAuthoredModelRestrictionIso
    (F : CartesianTargetInterpretations C (Dᵒᵖ ⥤ Type)) :
    authoredContext C ⋙ (extendPresheafAuthoredModel C D F).1 ≅ F.1 := by
  let family := presheafAuthoredModelFamily C D F
  have hflip :
      (authoredContext C ⋙ (extendPresheafAuthoredModel C D F).1).flip ≅
        F.1.flip := by
    calc
      _ ≅ ((family ⋙ extendModelToLex C ⋙ restrictLexToModel C) ⋙
          (ProductModel C).ι) := Iso.refl _
      _ ≅ (family ⋙ (extendModelToLex C ⋙ restrictLexToModel C)) ⋙
          (ProductModel C).ι :=
        Functor.isoWhiskerRight
          (Functor.associator family (extendModelToLex C) (restrictLexToModel C))
          (ProductModel C).ι
      _ ≅ (family ⋙ 𝟭 (Models C)) ⋙ (ProductModel C).ι :=
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft family (restrictExtendModelIso C))
          (ProductModel C).ι
      _ ≅ family ⋙ (ProductModel C).ι :=
        Functor.isoWhiskerRight family.rightUnitor (ProductModel C).ι
      _ ≅ F.1.flip :=
        (ProductModel C).liftCompιIso F.1.flip (fun d => by
          have hF : PreservesFiniteProducts F.1 := F.2
          change PreservesFiniteProducts
            (F.1 ⋙ (evaluation Dᵒᵖ Type).obj d)
          infer_instance)
  exact (flipFunctor _ _ _).mapIso hflip

/-- Restriction is essentially surjective when the target is a presheaf
category: every product-preserving authored interpretation has the explicit
pointwise left-exact extension above. This does not yet assert fullness of
restriction or arbitrary-target essential surjectivity. -/
instance restrictLeftExactPresheaf_essSurj :
    (restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).EssSurj where
  mem_essImage F :=
    ⟨extendPresheafAuthoredModel C D F,
      ⟨(CartesianTargetInterpretation C (Dᵒᵖ ⥤ Type)).isoMk
        (extendPresheafAuthoredModelRestrictionIso C D F)⟩⟩

end Mettapedia.OSLF.CartesianContextModels
