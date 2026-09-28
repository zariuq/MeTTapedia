import Mettapedia.OSLF.Syntax.CartesianModelLocalPresentability
import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Finite presentations over authored cartesian contexts

The finitely presentable cartesian models form an essentially small category
closed under finite colimits. Its opposite therefore has finite limits and
contains the authored contexts fully faithfully. This is a concrete relative
finite-limit object category, with the existing context-product equations
already imposed. A universal extension theorem and the operational/logic
generators are further constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits Opposite

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance : IsCardinalLocallyPresentable (Models C) Cardinal.aleph0.{0} :=
  models_locally_finitely_presentable C

/-- Cartesian models with finite presentations. -/
abbrev FinitelyPresentedModels :=
  (isCardinalPresentable (Models C) Cardinal.aleph0.{0}).FullSubcategory

/-- The opposite category has the variance required of formal finite-limit
objects over the authored context category. -/
abbrev FinitePresentationObjects := (FinitelyPresentedModels C)ᵒᵖ

theorem finitelyPresentedModels_essentiallySmall :
    ObjectProperty.EssentiallySmall.{0}
      (isCardinalPresentable (Models C) Cardinal.aleph0.{0}) := by
  infer_instance

instance : HasInitial (FinitelyPresentedModels C) := by
  change HasColimitsOfShape (Discrete PEmpty) (FinitelyPresentedModels C)
  have hJ : HasCardinalLT (Arrow (Discrete PEmpty)) Cardinal.aleph0 :=
    hasCardinalLT_of_finite _ _ (le_refl _)
  have := isClosedUnderColimitsOfShape_isCardinalPresentable
    (Models C) hJ
  exact hasColimitsOfShape_of_closedUnderColimits
    (Discrete PEmpty) (isCardinalPresentable (Models C) Cardinal.aleph0)

instance : HasBinaryCoproducts (FinitelyPresentedModels C) := by
  change HasColimitsOfShape (Discrete WalkingPair) (FinitelyPresentedModels C)
  have hJ : HasCardinalLT (Arrow (Discrete WalkingPair)) Cardinal.aleph0 :=
    hasCardinalLT_of_finite _ _ (le_refl _)
  have := isClosedUnderColimitsOfShape_isCardinalPresentable
    (Models C) hJ
  exact hasColimitsOfShape_of_closedUnderColimits
    (Discrete WalkingPair) (isCardinalPresentable (Models C) Cardinal.aleph0)

instance : HasCoequalizers (FinitelyPresentedModels C) := by
  change HasColimitsOfShape WalkingParallelPair (FinitelyPresentedModels C)
  have hJ : HasCardinalLT (Arrow WalkingParallelPair) Cardinal.aleph0 :=
    hasCardinalLT_of_finite _ _ (le_refl _)
  have := isClosedUnderColimitsOfShape_isCardinalPresentable
    (Models C) hJ
  exact hasColimitsOfShape_of_closedUnderColimits
    WalkingParallelPair (isCardinalPresentable (Models C) Cardinal.aleph0)

instance : HasFiniteColimits (FinitelyPresentedModels C) := by
  have : HasFiniteCoproducts (FinitelyPresentedModels C) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance : HasFiniteLimits (FinitePresentationObjects C) := by
  dsimp [FinitePresentationObjects]
  infer_instance

/-- Each authored context enters through its finitely presentable
representable model. -/
def representedFiniteModel : Cᵒᵖ ⥤ FinitelyPresentedModels C :=
  (isCardinalPresentable (Models C) Cardinal.aleph0).lift
    (representedContext C) (fun X => represented_model_presentable C X)

instance : (representedFiniteModel C).Full := by
  refine ⟨fun {X Y} f => ⟨(representedContext C).preimage f.hom, ?_⟩⟩
  apply ObjectProperty.hom_ext
  exact (representedContext C).map_preimage f.hom

instance : (representedFiniteModel C).Faithful := by
  constructor
  intro X Y f g h
  apply (representedContext C).map_injective
  exact congrArg (fun k : (representedFiniteModel C).obj X ⟶
      (representedFiniteModel C).obj Y => k.hom) h

/-- The finite-presentation embedding retains coproducts represented by
authored context products. The full-subcategory inclusion reflects the
required colimits. -/
theorem representedFiniteModel_preservesFiniteCoproducts :
    PreservesFiniteCoproducts (representedFiniteModel C) := by
  let P := isCardinalPresentable (Models C) Cardinal.aleph0
  have hcomp : PreservesFiniteCoproducts
      (representedFiniteModel C ⋙ P.ι) := by
    have hIso : representedFiniteModel C ⋙ P.ι ≅
        representedContext C := Iso.refl _
    have hrep : PreservesFiniteCoproducts (representedContext C) :=
      represented_preservesFiniteCoproducts C
    refine ⟨fun n => ?_⟩
    exact preservesColimitsOfShape_of_natIso hIso.symm
  have hreflect : ReflectsFiniteCoproducts P.ι := inferInstance
  exact preservesFiniteCoproducts_of_reflects_of_preserves
    (representedFiniteModel C) P.ι

/-- The authored context embedding into the finite-limit object category. -/
abbrev authoredContext : C ⥤ FinitePresentationObjects C :=
  (representedFiniteModel C).rightOp

instance : (authoredContext C).Full := by
  dsimp [authoredContext]
  infer_instance

instance : (authoredContext C).Faithful := by
  dsimp [authoredContext]
  infer_instance

/-- The relative finite-limit embedding preserves the finite products
already declared by the authored context category. -/
theorem authoredContext_preservesFiniteProducts :
    PreservesFiniteProducts (authoredContext C) := by
  have h : PreservesFiniteCoproducts (representedFiniteModel C) :=
    representedFiniteModel_preservesFiniteCoproducts C
  exact preservesFiniteProducts_rightOp (representedFiniteModel C)

end Mettapedia.OSLF.CartesianContextModels
