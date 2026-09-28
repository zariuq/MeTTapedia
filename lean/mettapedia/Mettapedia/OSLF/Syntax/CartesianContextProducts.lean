import Mettapedia.OSLF.Syntax.CartesianContextModels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Authored products as coproducts of cartesian models

A product context represents the coproduct of its factor contexts inside the
category of product-preserving models. The proof uses the actual mapped
product cone and covariant Yoneda, so it records which product is preserved.
This is a finite piece of the relative completion, not its full adjunction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type) [SmallCategory C]
variable [HasBinaryProducts C]

/-- The chosen product comparison of a cartesian model, expressed as an
equivalence of its underlying sets. -/
noncomputable def modelProductElements (F : Models C) (X Y : C) :
    F.1.obj (X ⨯ Y) ≃ F.1.obj X × F.1.obj Y := by
  have : PreservesFiniteProducts F.1 := F.property
  have : PreservesLimit (pair X Y) F.1 := inferInstance
  exact (PreservesLimitPair.iso F.1 X Y).toEquiv.trans
    (Types.binaryProductIso (F.1.obj X) (F.1.obj Y)).toEquiv

theorem modelProductElements_fst (F : Models C) (X Y : C)
    (z : F.1.obj (X ⨯ Y)) :
    (modelProductElements C F X Y z).1 = F.1.map prod.fst z := by
  have : PreservesFiniteProducts F.1 := F.property
  have : PreservesLimit (pair X Y) F.1 := inferInstance
  have e : (PreservesLimitPair.iso F.1 X Y).hom ≫
      (Types.binaryProductIso (F.1.obj X) (F.1.obj Y)).hom ≫
      TypeCat.ofHom Prod.fst = F.1.map prod.fst := by
    rw [Types.binaryProductIso_hom_comp_fst,
      PreservesLimitPair.iso_hom]
    exact prodComparison_fst F.1 X Y
  have h := ConcreteCategory.congr_hom e z
  change (modelProductElements C F X Y z).1 = F.1.map prod.fst z at h
  exact h

theorem modelProductElements_snd (F : Models C) (X Y : C)
    (z : F.1.obj (X ⨯ Y)) :
    (modelProductElements C F X Y z).2 = F.1.map prod.snd z := by
  have : PreservesFiniteProducts F.1 := F.property
  have : PreservesLimit (pair X Y) F.1 := inferInstance
  have e : (PreservesLimitPair.iso F.1 X Y).hom ≫
      (Types.binaryProductIso (F.1.obj X) (F.1.obj Y)).hom ≫
      TypeCat.ofHom Prod.snd = F.1.map prod.snd := by
    rw [Types.binaryProductIso_hom_comp_snd,
      PreservesLimitPair.iso_hom]
    exact prodComparison_snd F.1 X Y
  have h := ConcreteCategory.congr_hom e z
  change (modelProductElements C F X Y z).2 = F.1.map prod.snd z at h
  exact h

/-- The two projections of an authored product context, represented as a
cocone in the cartesian model category. -/
noncomputable def representedProductCofan (X Y : C) :
    BinaryCofan ((representedContext C).obj (Opposite.op X))
      ((representedContext C).obj (Opposite.op Y)) :=
  BinaryCofan.mk ((representedContext C).map (prod.fst : X ⨯ Y ⟶ X).op)
    ((representedContext C).map (prod.snd : X ⨯ Y ⟶ Y).op)

/-- The mediating map is determined by the two model elements selected by
the maps from the represented factor contexts. -/
noncomputable def representedProductCofanDesc (X Y : C) (F : Models C)
    (f : (representedContext C).obj (Opposite.op X) ⟶ F)
    (g : (representedContext C).obj (Opposite.op Y) ⟶ F) :
    (representedProductCofan C X Y).pt ⟶ F :=
  ObjectProperty.homMk <|
    coyonedaEquiv.symm
      ((modelProductElements C F X Y).symm
        (coyonedaEquiv f.hom, coyonedaEquiv g.hom))

theorem representedProductCofan_fac_left (X Y : C) (F : Models C)
    (f : (representedContext C).obj (Opposite.op X) ⟶ F)
    (g : (representedContext C).obj (Opposite.op Y) ⟶ F) :
    (representedProductCofan C X Y).inl ≫
      representedProductCofanDesc C X Y F f g = f := by
  apply ObjectProperty.hom_ext
  apply coyonedaEquiv.injective
  dsimp [representedProductCofan, representedProductCofanDesc,
    representedContext, ObjectProperty.lift, ObjectProperty.homMk,
    BinaryCofan.mk]
  rw [← coyonedaEquiv_naturality]
  simp only [Equiv.apply_symm_apply]
  change F.1.map prod.fst
    ((modelProductElements C F X Y).symm
      (coyonedaEquiv f.hom, coyonedaEquiv g.hom)) = coyonedaEquiv f.hom
  rw [← modelProductElements_fst C F X Y, Equiv.apply_symm_apply]

theorem representedProductCofan_fac_right (X Y : C) (F : Models C)
    (f : (representedContext C).obj (Opposite.op X) ⟶ F)
    (g : (representedContext C).obj (Opposite.op Y) ⟶ F) :
    (representedProductCofan C X Y).inr ≫
      representedProductCofanDesc C X Y F f g = g := by
  apply ObjectProperty.hom_ext
  apply coyonedaEquiv.injective
  dsimp [representedProductCofan, representedProductCofanDesc,
    representedContext, ObjectProperty.lift, ObjectProperty.homMk,
    BinaryCofan.mk]
  rw [← coyonedaEquiv_naturality]
  simp only [Equiv.apply_symm_apply]
  change F.1.map prod.snd
    ((modelProductElements C F X Y).symm
      (coyonedaEquiv f.hom, coyonedaEquiv g.hom)) = coyonedaEquiv g.hom
  rw [← modelProductElements_snd C F X Y, Equiv.apply_symm_apply]

/-- An authored product represents an actual coproduct inside the category
of product-preserving models, though its pointwise presheaf coproduct need not
preserve products. -/
noncomputable def representedProductCofan_isColimit (X Y : C) :
    IsColimit (representedProductCofan C X Y) := by
  refine BinaryCofan.IsColimit.mk (representedProductCofan C X Y)
    (fun {F} f g => representedProductCofanDesc C X Y F f g)
    (fun {F} f g => representedProductCofan_fac_left C X Y F f g)
    (fun {F} f g => representedProductCofan_fac_right C X Y F f g)
    ?_
  intro F f g m hm_f hm_g
  apply ObjectProperty.hom_ext
  apply coyonedaEquiv.injective
  apply (modelProductElements C F X Y).injective
  apply Prod.ext
  · rw [modelProductElements_fst]
    have h := congrArg (fun k => coyonedaEquiv k.hom) hm_f
    change coyonedaEquiv (coyoneda.map (prod.fst : X ⨯ Y ⟶ X).op ≫
      m.hom) = coyonedaEquiv f.hom at h
    let m' : coyoneda.obj (Opposite.op (X ⨯ Y)) ⟶ F.1 := m.hom
    have h' : F.1.map prod.fst (coyonedaEquiv m') = coyonedaEquiv f.hom := by
      rw [coyonedaEquiv_naturality m' prod.fst]
      exact h
    simpa [representedProductCofanDesc, ObjectProperty.homMk, m'] using h'
  · rw [modelProductElements_snd]
    have h := congrArg (fun k => coyonedaEquiv k.hom) hm_g
    change coyonedaEquiv (coyoneda.map (prod.snd : X ⨯ Y ⟶ Y).op ≫
      m.hom) = coyonedaEquiv g.hom at h
    let m' : coyoneda.obj (Opposite.op (X ⨯ Y)) ⟶ F.1 := m.hom
    have h' : F.1.map prod.snd (coyonedaEquiv m') = coyonedaEquiv g.hom := by
      rw [coyonedaEquiv_naturality m' prod.snd]
      exact h
    simpa [representedProductCofanDesc, ObjectProperty.homMk, m'] using h'

variable [HasFiniteProducts C]

omit [HasBinaryProducts C] in
/-- The represented terminal context sends the initial object of the
opposite base to an initial cartesian model. -/
theorem represented_preservesInitial :
    PreservesColimit (Functor.empty.{0} Cᵒᵖ) (representedContext C) := by
  apply preservesColimit_of_preserves_colimit_cocone
    (terminalIsTerminal.op : IsInitial (Opposite.op (⊤_ C)))
  exact (isColimitMapCoconeEmptyCoconeEquiv (representedContext C)
    (Opposite.op (⊤_ C))).symm (represented_terminal_is_initial C)

omit [HasFiniteProducts C] in
theorem represented_preservesPair (X Y : C) :
    PreservesColimit (pair (Opposite.op X) (Opposite.op Y))
      (representedContext C) := by
  have source : IsColimit
      (BinaryCofan.mk (prod.fst : X ⨯ Y ⟶ X).op
        (prod.snd : X ⨯ Y ⟶ Y).op) := by
    simpa only [BinaryFan.op_mk] using BinaryFan.IsLimit.op (prodIsProd X Y)
  apply preservesColimit_of_preserves_colimit_cocone source
  exact (isColimitMapCoconeBinaryCofanEquiv
    (representedContext C) (prod.fst : X ⨯ Y ⟶ X).op
    (prod.snd : X ⨯ Y ⟶ Y).op).symm
      (representedProductCofan_isColimit C X Y)

omit [HasFiniteProducts C] in
theorem represented_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (representedContext C) := by
  refine ⟨?_⟩
  intro K
  have : PreservesColimit
      (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩))
      (representedContext C) := by
    exact represented_preservesPair C
      (K.obj ⟨WalkingPair.left⟩).unop
      (K.obj ⟨WalkingPair.right⟩).unop
  exact preservesColimit_of_iso_diagram (representedContext C) (diagramIsoPair K).symm

/-- The Yoneda embedding preserves every finite coproduct that comes from
a finite product of authored contexts. -/
theorem represented_preservesFiniteCoproducts :
    PreservesFiniteCoproducts (representedContext C) := by
  have : PreservesColimitsOfShape (Discrete WalkingPair) (representedContext C) :=
    represented_preservesBinaryCoproducts C
  have : PreservesColimit (Functor.empty.{0} Cᵒᵖ) (representedContext C) :=
    represented_preservesInitial C
  have : PreservesColimitsOfShape (Discrete PEmpty) (representedContext C) :=
    preservesColimitsOfShape_pempty_of_preservesInitial (representedContext C)
  refine ⟨fun n => ?_⟩
  exact PreservesFiniteCoproducts.of_preserves_binary_and_initial
    (representedContext C) (Fin n)

/-- The authored context embedding into the opposite model category
preserves its chosen finite products. -/
theorem representedBase_preservesFiniteProducts :
    PreservesFiniteProducts (representedContext C).rightOp := by
  have : PreservesFiniteCoproducts (representedContext C) :=
    represented_preservesFiniteCoproducts C
  exact preservesFiniteProducts_rightOp (representedContext C)

/-- A cartesian authored context is interpreted by its represented model,
with variance reversed so that substitutions keep their authored direction. -/
def authoredContextModel : C ⥤ (Models C)ᵒᵖ :=
  (representedContext C).rightOp

instance : (authoredContextModel C).Full := by
  dsimp [authoredContextModel]
  infer_instance

instance : (authoredContextModel C).Faithful := by
  dsimp [authoredContextModel]
  infer_instance

theorem authoredContextModel_preservesFiniteProducts :
    PreservesFiniteProducts (authoredContextModel C) :=
  representedBase_preservesFiniteProducts C

end Mettapedia.OSLF.CartesianContextModels
