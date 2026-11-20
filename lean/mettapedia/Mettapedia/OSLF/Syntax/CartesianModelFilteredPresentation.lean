import Mettapedia.OSLF.Syntax.CartesianModelFinitePresentations
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Filtered presentations of cartesian models

Every cartesian model has a small filtered presentation by genuinely finitely
presentable cartesian models. The stage diagram, its maps, its cocone and its
universal property are retained as data. The construction uses the proved
local finite presentability of the model category, without assuming that an
arbitrary finite authored program is a compact object.

Finite observations factor through stages. Equal observations become equal
after transport, including along one common route from a named stage. These
positive laws do not reflect absence or terminality at an earlier snapshot.
This is the cartesian-model layer; operational event interpretations and
compiler preservation require their own constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type} [SmallCategory C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- An actual filtered realization, with compactness proved in the cartesian
model category rather than supplied as an external presentation hypothesis. -/
structure FilteredModelPresentation (X : Models C) where
  Stage : Type
  category : SmallCategory Stage
  filtered : @IsFiltered Stage category
  presentation : @ColimitPresentation (Models C) _ Stage category X
  compact : ∀ stage, IsFinitelyPresentable.{0} (presentation.diag.obj stage)

attribute [instance] FilteredModelPresentation.category
  FilteredModelPresentation.filtered

/-- The established cartesian-model generator supplies the stages and their
colimit, not merely a hypothetical cocone. -/
theorem exists_filteredModelPresentation [HasFiniteProducts C] (X : Models C) :
    Nonempty (FilteredModelPresentation X) := by
  obtain ⟨P, _, generator⟩ :=
    HasCardinalFilteredGenerator.exists_generator (Models C) Cardinal.aleph0
  obtain ⟨J, _, _, ⟨presentation⟩⟩ := generator.exists_colimitsOfShape X
  exact ⟨{
    Stage := J
    category := inferInstance
    filtered := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
    presentation := presentation.toColimitPresentation
    compact := fun stage =>
      generator.le_isCardinalPresentable _ (presentation.prop_diag_obj stage)
  }⟩

/-- Choose a proved filtered presentation. No effective stage selector is
asserted by this mathematical choice. -/
noncomputable def filteredModelPresentation [HasFiniteProducts C] (X : Models C) :
    FilteredModelPresentation X :=
  Classical.choice (exists_filteredModelPresentation X)

namespace FilteredModelPresentation

variable {X : Models C} (P : FilteredModelPresentation X)

/-- The same stage maps land in the full category of finitely presented
models; no new morphism or interpretation is introduced. -/
def finiteDiagram : P.Stage ⥤ FinitelyPresentedModels C :=
  (isCardinalPresentable (Models C) Cardinal.aleph0).lift
    P.presentation.diag P.compact

/-- The finite diagram realizes exactly the retained cartesian-model
diagram when its compactness certificates are forgotten. -/
theorem finiteDiagram_comp_inclusion :
    P.finiteDiagram ⋙ (isCardinalPresentable (Models C) Cardinal.aleph0).ι =
      P.presentation.diag := rfl

/-- Every map from a finitely presented model factors through an actual
stage of this realization. -/
theorem observation_factors (A : FinitelyPresentedModels C) (f : A.obj ⟶ X) :
    ∃ (stage : P.Stage) (g : A.obj ⟶ P.presentation.diag.obj stage),
      g ≫ P.presentation.ι.app stage = f := by
  have : IsFinitelyPresentable.{0} A.obj := A.property
  exact IsFinitelyPresentable.exists_hom_of_isColimit P.presentation.isColimit f

/-- Two finite observations which agree in the model agree at a common
stage. The two transport routes are part of the witness. -/
theorem observations_equal_eventually (A : FinitelyPresentedModels C)
    {first second : P.Stage}
    (f : A.obj ⟶ P.presentation.diag.obj first)
    (g : A.obj ⟶ P.presentation.diag.obj second)
    (same : f ≫ P.presentation.ι.app first = g ≫ P.presentation.ι.app second) :
    ∃ (stage : P.Stage) (left : first ⟶ stage) (right : second ⟶ stage),
      f ≫ P.presentation.diag.map left = g ≫ P.presentation.diag.map right := by
  have : IsFinitelyPresentable.{0} A.obj := A.property
  exact IsFinitelyPresentable.exists_eq_of_isColimit P.presentation.isColimit f g same

/-- Agreement of two observations from one stage is witnessed by a single
later route, rather than by unrelated transport maps. -/
theorem observations_equal_from_stage (A : FinitelyPresentedModels C)
    {original : P.Stage}
    (f g : A.obj ⟶ P.presentation.diag.obj original)
    (same : f ≫ P.presentation.ι.app original = g ≫ P.presentation.ι.app original) :
    ∃ (stage : P.Stage) (route : original ⟶ stage),
      f ≫ P.presentation.diag.map route = g ≫ P.presentation.diag.map route := by
  have : IsFinitelyPresentable.{0} A.obj := A.property
  have : IsCardinalFiltered P.Stage Cardinal.aleph0 :=
    (isCardinalFiltered_aleph0_iff P.Stage).2 inferInstance
  exact IsCardinalPresentable.exists_eq_of_isColimit' Cardinal.aleph0
    P.presentation.isColimit f g same

/-- Finitely many observations, possibly from different finite models,
can be realized together without changing their order or domains. -/
theorem observations_factor_together (n : Nat)
    (A : Fin n → FinitelyPresentedModels C) (f : ∀ i, (A i).obj ⟶ X) :
    ∃ (stage : P.Stage) (g : ∀ i, (A i).obj ⟶ P.presentation.diag.obj stage),
      ∀ i, g i ≫ P.presentation.ι.app stage = f i := by
  induction n with
  | zero =>
      obtain ⟨stage⟩ := IsFiltered.nonempty (C := P.Stage)
      exact ⟨stage, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n induction =>
      obtain ⟨first, gs, hs⟩ := induction (fun i => A i.castSucc) (fun i => f i.castSucc)
      obtain ⟨last, g, hg⟩ := P.observation_factors (A (Fin.last n)) (f (Fin.last n))
      let stage := IsFiltered.max first last
      let left : first ⟶ stage := IsFiltered.leftToMax first last
      let right : last ⟶ stage := IsFiltered.rightToMax first last
      refine ⟨stage, Fin.lastCases (g ≫ P.presentation.diag.map right)
        (fun i => gs i ≫ P.presentation.diag.map left), ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.lastCases_last, Category.assoc, P.presentation.w right] using hg
      · simpa only [Fin.lastCases_castSucc, Category.assoc, P.presentation.w left] using hs j

end FilteredModelPresentation

#print axioms exists_filteredModelPresentation
#print axioms FilteredModelPresentation.observation_factors
#print axioms FilteredModelPresentation.observations_equal_from_stage
#print axioms FilteredModelPresentation.observations_factor_together

end Mettapedia.OSLF.CartesianContextModels
