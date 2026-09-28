import Mettapedia.OSLF.Syntax.FiniteLimitShapes
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Finite-limit-generated Yoneda subcategory of a small category

For any small category, the representables generate an isomorphism-closed
full subcategory of presheaves under terminal objects, binary products and
equalizers. The full subcategory is finitely complete and its inclusion
creates and preserves every finite limit. This applies equally to raw binding
contexts and authored equation-quotient contexts.

The result is an ambient finite-limit realization and a minimal object
property. It does not assert a free-extension hom-set universal property.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.FiniteLimitYoneda

open CategoryTheory
open CategoryTheory.Limits
open Mettapedia.OSLF.Binding

variable (C : Type) [SmallCategory C]

abbrev Presheaf := Cᵒᵖ ⥤ Type

def Representable : ObjectProperty (Presheaf C) := fun F => F.IsRepresentable

def Generated : ObjectProperty (Presheaf C) :=
  (Representable C).limitsClosure finiteLimitDiagram

theorem represented (X : C) : Generated C (yoneda.obj X) := by
  apply ObjectProperty.limitsClosure.of_mem
  change (yoneda.obj X).IsRepresentable
  infer_instance

instance : HasTerminal (Generated C).FullSubcategory := by
  change HasLimitsOfShape (finiteLimitDiagram FiniteLimitShape.terminal)
    (Generated C).FullSubcategory
  have : (Generated C).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.terminal) := by
    unfold Generated
    infer_instance
  apply hasLimitsOfShape_of_closedUnderLimits

instance : HasBinaryProducts (Generated C).FullSubcategory := by
  change HasLimitsOfShape (finiteLimitDiagram FiniteLimitShape.binaryProduct)
    (Generated C).FullSubcategory
  have : (Generated C).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.binaryProduct) := by
    unfold Generated
    infer_instance
  apply hasLimitsOfShape_of_closedUnderLimits

instance : HasEqualizers (Generated C).FullSubcategory := by
  change HasLimitsOfShape (finiteLimitDiagram FiniteLimitShape.equalizer)
    (Generated C).FullSubcategory
  have : (Generated C).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.equalizer) := by
    unfold Generated
    infer_instance
  apply hasLimitsOfShape_of_closedUnderLimits

theorem hasFiniteLimits : HasFiniteLimits (Generated C).FullSubcategory := by
  have : HasFiniteProducts (Generated C).FullSubcategory :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

instance : HasFiniteLimits (Generated C).FullSubcategory := hasFiniteLimits C

theorem closedUnderFiniteProducts :
    (Generated C).IsClosedUnderFiniteProducts := by
  have : (Generated C).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
    change (Generated C).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.terminal)
    unfold Generated
    infer_instance
  have : (Generated C).IsClosedUnderBinaryProducts := by
    change (Generated C).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.binaryProduct)
    unfold Generated
    infer_instance
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

@[instance_reducible]
noncomputable def inclusionCreatesFiniteProducts :
    CreatesFiniteProducts (Generated C).ι := by
  have : (Generated C).IsClosedUnderFiniteProducts := closedUnderFiniteProducts C
  refine ⟨fun J _ => ?_⟩
  exact createsLimitsOfShapeFullSubcategoryInclusion (Discrete J) (Generated C)

@[instance_reducible]
noncomputable def inclusionCreatesFiniteLimits :
    CreatesFiniteLimits (Generated C).ι := by
  have : CreatesFiniteProducts (Generated C).ι := inclusionCreatesFiniteProducts C
  have : CreatesLimitsOfShape WalkingParallelPair (Generated C).ι := by
    have : (Generated C).IsClosedUnderLimitsOfShape WalkingParallelPair := by
      change (Generated C).IsClosedUnderLimitsOfShape
        (finiteLimitDiagram FiniteLimitShape.equalizer)
      unfold Generated
      infer_instance
    infer_instance
  exact createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts (Generated C).ι

theorem inclusionPreservesFiniteLimits : PreservesFiniteLimits (Generated C).ι := by
  have : CreatesFiniteLimits (Generated C).ι := inclusionCreatesFiniteLimits C
  infer_instance

theorem least (Q : ObjectProperty (Presheaf C))
    [Q.IsClosedUnderIsomorphisms]
    [∀ shape, Q.IsClosedUnderLimitsOfShape (finiteLimitDiagram shape)]
    (h : Representable C ≤ Q) : Generated C ≤ Q :=
  ObjectProperty.limitsClosure_le h

/-- The canonical embedding of base objects as generated representables. -/
def intoGenerated : C ⥤ (Generated C).FullSubcategory where
  obj X := ⟨yoneda.obj X, represented C X⟩
  map f := ObjectProperty.homMk (yoneda.map f)
  map_id X := by
    apply ObjectProperty.hom_ext
    change yoneda.map (𝟙 X) = 𝟙 (yoneda.obj X)
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change yoneda.map (f ≫ g) = yoneda.map f ≫ yoneda.map g
    simp

theorem intoGenerated_comp_inclusion :
    intoGenerated C ⋙ (Generated C).ι = yoneda := rfl

instance intoGenerated_faithful : (intoGenerated C).Faithful where
  map_injective := by
    intro X Y f g equal
    apply yoneda.map_injective
    exact congrArg
      (fun h : (intoGenerated C).obj X ⟶ (intoGenerated C).obj Y => h.hom)
      equal

instance intoGenerated_full : (intoGenerated C).Full where
  map_surjective := by
    intro X Y arrow
    obtain ⟨f, hf⟩ := yoneda.map_surjective arrow.hom
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    exact hf

theorem intoGenerated_preservesFiniteProducts :
    PreservesFiniteProducts (intoGenerated C) := by
  have : PreservesFiniteProducts (intoGenerated C ⋙ (Generated C).ι) := by
    rw [intoGenerated_comp_inclusion]
    infer_instance
  exact preservesFiniteProducts_of_reflects_of_preserves
    (intoGenerated C) (Generated C).ι

/-- Yoneda also preserves any finite limit already present in the source
category. A free-completion interpretation must respect all such existing
limits, not only the source's terminal and product contexts. -/
theorem intoGenerated_preservesExistingFiniteLimitsOfShape
    (J : Type) [SmallCategory J] [FinCategory J]
    [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (intoGenerated C) := by
  have : PreservesLimitsOfShape J
      (intoGenerated C ⋙ (Generated C).ι) := by
    rw [intoGenerated_comp_inclusion]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (intoGenerated C) (Generated C).ι

end Mettapedia.OSLF.FiniteLimitYoneda
