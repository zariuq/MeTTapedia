import Mettapedia.OSLF.Syntax.CartesianModelFilteredPresentation
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Ind realization of finitely presented cartesian models

The finite-observation nerve is fully faithful and preserves filtered
colimits. Its values have actual small filtered presentations by
representables. Conversely, an Ind object is realized by the colimit of its
finite cartesian models. These constructions give an equivalence between
cartesian models and the Ind category of their finitely presented models.

This realizes the cartesian-model layer. Authored scoped rule actions,
operational events, effective stage selection and compiler preservation are
additional structures, not consequences of this equivalence alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A model is observed by all maps from its finitely presented models.
The harmless lift keeps this definition on Mathlib's dense-nerve interface. -/
def finiteObservationNerve :
    Models C ⥤ (FinitelyPresentedModels C)ᵒᵖ ⥤ Type :=
  Presheaf.restrictedULiftYoneda.{0}
    (isCardinalPresentable (Models C) Cardinal.aleph0).ι

instance : (finiteObservationNerve C).Full := by
  dsimp [finiteObservationNerve]
  infer_instance

instance : (finiteObservationNerve C).Faithful := by
  dsimp [finiteObservationNerve]
  infer_instance

/-- Compactness makes finite observations commute with filtered growth. -/
instance {J : Type} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (finiteObservationNerve C) := by
  apply preservesColimitsOfShape_of_evaluation
  intro A
  have : IsFinitelyPresentable.{0} A.unop.obj := A.unop.property
  change PreservesColimitsOfShape J
    (coyoneda.obj (op A.unop.obj) ⋙ uliftFunctor.{0})
  infer_instance

/-- Restricting the nerve to finite models gives their ordinary Yoneda
embedding, via the actual full-subcategory hom equivalence. -/
noncomputable def finiteObservationNerve_on_finite :
    (isCardinalPresentable (Models C) Cardinal.aleph0).ι ⋙
      finiteObservationNerve C ≅ yoneda :=
  (Functor.FullyFaithful.ofFullyFaithful
      (isCardinalPresentable (Models C) Cardinal.aleph0).ι).compUliftYonedaCompWhiskeringLeft ≪≫
    uliftYonedaIsoYoneda

namespace FilteredModelPresentation

variable {C} {X : Models C} (P : FilteredModelPresentation X)

/-- The retained finite-model diagram, observed by its nerve, is the
diagram of representables used in this Ind presentation. -/
noncomputable def nerveDiagramIso :
    P.finiteDiagram ⋙ yoneda ≅
      P.presentation.diag ⋙ finiteObservationNerve C :=
  (isoWhiskerLeft P.finiteDiagram (finiteObservationNerve_on_finite C)).symm

/-- Construct an Ind presentation from the actual filtered realization. -/
noncomputable def indPresentation :
    IndObjectPresentation ((finiteObservationNerve C).obj X) :=
  let observed := P.presentation.map (finiteObservationNerve C)
  let represented := observed.changeDiag P.nerveDiagramIso
  { I := P.Stage
    F := P.finiteDiagram
    ι := represented.ι
    isColimit := represented.isColimit }

end FilteredModelPresentation

/-- Every model's nerve is an Ind object; the filtered presentation and
its universal property have been constructed, rather than hypothesized. -/
theorem finiteObservationNerve_isIndObject (X : Models C) :
    IsIndObject ((finiteObservationNerve C).obj X) :=
  IsIndObject.mk (filteredModelPresentation X).indPresentation

/-- The nerve takes values in the full category of genuine Ind objects. -/
noncomputable def modelIndObjects :
    Models C ⥤ ObjectProperty.FullSubcategory
      (IsIndObject (C := FinitelyPresentedModels C)) :=
  ObjectProperty.lift _ (finiteObservationNerve C)
    (finiteObservationNerve_isIndObject C)

instance : (modelIndObjects C).Full := by
  dsimp [modelIndObjects]
  infer_instance

instance : (modelIndObjects C).Faithful := by
  dsimp [modelIndObjects]
  infer_instance

/-- Realize an arbitrary Ind presentation by the colimit of its actual
finite models. Nerve preservation supplies the comparison isomorphism. -/
noncomputable def realizeIndPresentation
    {A : (FinitelyPresentedModels C)ᵒᵖ ⥤ Type}
    (P : IndObjectPresentation A) :
    (finiteObservationNerve C).obj
      (colimit (P.F ⋙ (isCardinalPresentable (Models C) Cardinal.aleph0).ι)) ≅ A := by
  let diagram := P.F ⋙ (isCardinalPresentable (Models C) Cardinal.aleph0).ι
  let comparison : diagram ⋙ finiteObservationNerve C ≅ P.F ⋙ yoneda :=
    isoWhiskerLeft P.F (finiteObservationNerve_on_finite C)
  exact IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves (finiteObservationNerve C) (colimit.isColimit diagram))
    P.isColimit comparison

noncomputable instance : (modelIndObjects C).EssSurj :=
  Functor.EssSurj.mk fun A =>
    let presentation := A.property.presentation
    ⟨colimit (presentation.F ⋙ (isCardinalPresentable (Models C) Cardinal.aleph0).ι),
      ⟨ObjectProperty.isoMk _ (realizeIndPresentation C presentation)⟩⟩

noncomputable instance : (modelIndObjects C).IsEquivalence where

/-- Ind completion of the genuine finitely presented cartesian models,
with both object realization and all model maps. -/
noncomputable def cartesianModelIndEquivalence :
    Models C ≌ Ind (FinitelyPresentedModels C) :=
  (modelIndObjects C).asEquivalence.trans
    (Ind.equivalence (FinitelyPresentedModels C)).symm

#print axioms FilteredModelPresentation.indPresentation
#print axioms finiteObservationNerve_isIndObject
#print axioms realizeIndPresentation
#print axioms cartesianModelIndEquivalence

end Mettapedia.OSLF.CartesianContextModels
