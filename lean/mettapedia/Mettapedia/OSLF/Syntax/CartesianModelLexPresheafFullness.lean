import Mettapedia.OSLF.Syntax.CartesianModelLexTargetDescent

/-!
# Transformations of presheaf-valued finite-limit interpretations

Evaluating a presheaf-valued interpretation at each stage gives a natural
family of Set-valued interpretations. The existing Set-valued equivalence
lifts transformations of authored models pointwise, with coherence inherited
from full faithfulness. This is the map-level part of the relative
finite-limit universal property for presheaf targets.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D]

/-- Evaluation of a presheaf-valued left-exact interpretation, as a natural
family of Set-valued left-exact interpretations. -/
noncomputable def presheafLexFamily
    (T : LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type)) :
    Dᵒᵖ ⥤ LexSetSemantics C :=
  (LeftExactSetSemantics C).lift T.1.flip (fun d => by
    have hT : PreservesFiniteLimits T.1 := T.2
    change PreservesFiniteLimits
      (T.1 ⋙ (evaluation Dᵒᵖ Type).obj d)
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ T.1 _ hT
      (inferInstance : PreservesFiniteLimits ((evaluation Dᵒᵖ Type).obj d)))

/-- Restriction of each Set-valued stage agrees with evaluation of the
presheaf-valued restriction on authored contexts. -/
noncomputable def presheafLexFamilyRestrictionIso
    (T : LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type)) :
    presheafLexFamily C D T ⋙ restrictLexToModel C ≅
      presheafAuthoredModelFamily C D
        ((restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).obj T) := by
  exact Iso.refl _

/-- A map of presheaf-valued authored interpretations is a natural map
between their families of Set-valued cartesian models. -/
noncomputable def presheafAuthoredModelFamilyMap
    {T U : LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type)}
    (f : (restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).obj T ⟶
      (restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).obj U) :
    presheafAuthoredModelFamily C D
        ((restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).obj T) ⟶
      presheafAuthoredModelFamily C D
        ((restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).obj U) where
  app d := (ProductModel C).homMk ((flipFunctor _ _ _).map f.hom |>.app d)
  naturality d e g := by
    apply ObjectProperty.hom_ext
    exact ((flipFunctor _ _ _).map f.hom).naturality g

/-- The Set-valued restriction equivalence can be used inside every
presheaf-indexed functor category. -/
instance restrictLexToModel_isEquivalence :
    (restrictLexToModel C).IsEquivalence := by
  exact (Functor.isEquivalence_iff_of_iso
    (restrictLexToModelIsoInverse C)).2
      (cartesianModelsEquivLexSetSemantics C).isEquivalence_inverse

instance whiskeringRight_restrictLexToModel_full :
    ((Functor.whiskeringRight Dᵒᵖ _ _).obj
      (restrictLexToModel C)).Full := by
  change ((((restrictLexToModel C).asEquivalence.congrRight).functor)).Full
  infer_instance

/-- Restriction is full for presheaf targets. The Set-valued classifying
equivalence lifts each stage of a transformation, and its full faithfulness
forces those lifts to commute with the presheaf index maps. -/
instance restrictLeftExactPresheaf_full :
    (restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).Full := by
  let R := restrictLexToModel C
  let W := (Functor.whiskeringRight Dᵒᵖ _ _).obj R
  constructor
  intro T U f
  let tFam := presheafLexFamily C D T
  let uFam := presheafLexFamily C D U
  let fFam := presheafAuthoredModelFamilyMap C D f
  let fR : tFam ⋙ R ⟶ uFam ⋙ R :=
    (presheafLexFamilyRestrictionIso C D T).hom ≫ fFam ≫
      (presheafLexFamilyRestrictionIso C D U).inv
  let gFam : tFam ⟶ uFam := W.preimage fR
  let gFlip : T.1.flip ⟶ U.1.flip :=
    ((Functor.whiskeringRight Dᵒᵖ _ _).obj
      (LeftExactSetSemantics C).ι).map gFam
  let gRaw : T.1 ⟶ U.1 := (flipFunctor _ _ _).map gFlip
  refine ⟨(LeftExactTargetInterpretation C (Dᵒᵖ ⥤ Type)).homMk gRaw, ?_⟩
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext d
  have hg : W.map gFam = fR := W.map_preimage fR
  have hgd := congrArg
    (fun a : tFam ⋙ R ⟶ uFam ⋙ R =>
      ((a.app d).hom.app X)) hg
  change (gRaw.app ((authoredContext C).obj X)).app d =
    (f.hom.app X).app d at hgd
  exact hgd

/-- The relative finite-limit universal property for a presheaf target
indexed by a small category. This is an independently useful large target:
the presheaf category itself need not be small. -/
instance restrictLeftExactPresheaf_isEquivalence :
    (restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).IsEquivalence :=
  ⟨restrictLeftExactTarget_faithful C (Dᵒᵖ ⥤ Type),
   restrictLeftExactPresheaf_full C D,
   restrictLeftExactPresheaf_essSurj C D⟩

noncomputable def cartesianPresheafLexEquivalence :
    LeftExactTargetInterpretations C (Dᵒᵖ ⥤ Type) ≌
      CartesianTargetInterpretations C (Dᵒᵖ ⥤ Type) :=
  (restrictLeftExactTarget C (Dᵒᵖ ⥤ Type)).asEquivalence

end Mettapedia.OSLF.CartesianContextModels
