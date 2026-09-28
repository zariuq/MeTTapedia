import Mettapedia.OSLF.Syntax.CartesianContextProducts
import Mathlib.CategoryTheory.Limits.Sifted
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Sifted colimits of cartesian context models

Sifted colimits commute with finite products in sets. Consequently a sifted
pointwise colimit of product-preserving interpretations is still a model,
and the model-category inclusion creates it. The pointwise binary-coproduct
counterexample shows why the sifted hypothesis matters.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

variable (C : Type) [SmallCategory C]


/-- The pointwise colimit preserves every finite authored context product
when the indexing category is sifted. -/
theorem colimit_preservesFiniteProducts
    (J : Type) [SmallCategory J] [IsSifted J]
    (D : J ⥤ CovariantPresheaf C)
    (h : ∀ j, PreservesFiniteProducts (D.obj j)) :
    PreservesFiniteProducts (colimit D) := by
  have flipped : PreservesFiniteProducts D.flip := by
    refine ⟨fun n => ?_⟩
    apply preservesLimitsOfShape_of_evaluation D.flip (Discrete (Fin n))
    intro j
    exact (h j).preserves n
  have colimPreserves : PreservesFiniteProducts
      (colim : (J ⥤ Type) ⥤ Type) := by
    infer_instance
  have composite : PreservesFiniteProducts (D.flip ⋙ colim) := inferInstance
  refine ⟨fun n => ?_⟩
  exact preservesLimitsOfShape_of_natIso
    (colimitFlipIsoCompColim D.flip).symm

/-- The chosen pointwise sifted colimit is a cartesian model. -/
theorem model_colimit (J : Type) [SmallCategory J] [IsSifted J]
    (D : J ⥤ Models C) :
    ProductModel C (colimit (D ⋙ (ProductModel C).ι)) := by
  apply colimit_preservesFiniteProducts C J
  intro j
  exact (D.obj j).property

instance (J : Type) [SmallCategory J] [IsSifted J] :
    (ProductModel C).IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  intro F h
  cases h with
  | colimit D hD =>
      exact colimit_preservesFiniteProducts C J D hD

noncomputable instance (J : Type) [SmallCategory J] [IsSifted J] :
    CreatesColimitsOfShape J (ProductModel C).ι := by
  infer_instance

instance (J : Type) [SmallCategory J] [IsSifted J] :
    HasColimitsOfShape J (Models C) := by
  infer_instance

/-- The model-category inclusion does not preserve even the coproduct of two
representations of the authored terminal context. Internal model colimits
cannot in general be computed by pointwise functor-category colimits. -/
theorem inclusion_not_preserves_represented_pair [HasFiniteProducts C] :
    ¬ PreservesColimit
      (pair ((representedContext C).obj (Opposite.op (⊤_ C)))
        ((representedContext C).obj (Opposite.op (⊤_ C))))
      (ProductModel C).ι := by
  intro preserves
  let R : CovariantPresheaf C := coyoneda.obj (Opposite.op (⊤_ C))
  let P : CovariantPresheaf C := coyoneda.obj (Opposite.op ((⊤_ C) ⨯ (⊤_ C)))
  let cofan := representedProductCofan C (⊤_ C) (⊤_ C)
  have mapped : IsColimit ((ProductModel C).ι.mapCocone cofan) :=
    isColimitOfPreserves (ProductModel C).ι
      (representedProductCofan_isColimit C _ _)
  have binary : IsColimit (BinaryCofan.mk
      ((ProductModel C).ι.map cofan.inl)
      ((ProductModel C).ι.map cofan.inr)) :=
    (isColimitMapCoconeBinaryCofanEquiv
      (ProductModel C).ι cofan.inl cofan.inr) mapped
  have e : R ⨿ R ≅ P :=
    (coprodIsCoprod R R).coconePointUniqueUpToIso binary
  have hP : ProductModel C P := represented_is_model C _
  have hRR : ProductModel C (R ⨿ R) :=
    (ProductModel C).prop_of_iso e.symm hP
  exact represented_coprod_not_model C hRR

/-- Thus the inclusion cannot preserve binary coproducts as a class, even
though it creates all sifted colimits. -/
theorem inclusion_not_preservesBinaryCoproducts [HasFiniteProducts C] :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (ProductModel C).ι := by
  intro h
  have preserves : PreservesColimit
      (pair ((representedContext C).obj (Opposite.op (⊤_ C)))
        ((representedContext C).obj (Opposite.op (⊤_ C))))
      (ProductModel C).ι := by
        let := h
        infer_instance
  exact inclusion_not_preserves_represented_pair C preserves

end Mettapedia.OSLF.CartesianContextModels
