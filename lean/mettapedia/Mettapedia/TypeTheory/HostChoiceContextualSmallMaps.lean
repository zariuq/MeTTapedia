import Mettapedia.TypeTheory.ContextualEnumerationCovers

/-!
# Optional host-choice comparison for contextual small maps

The explicitly named factory selects actual fibre enumerations from the
pointwise small-fibre predicate with `Classical.choice`. The independent core
constructs composition from those data. It also constructs the future-data
parameter family, literal pullback, small fibre enumerations and all triangle
maps. This module supplies the generic data-selection step and proves the
resulting covering properties.

These are metatheoretic host-choice comparisons. They do not install native
choice, identify pointwise covers with natural small carrier diagrams, prove
internal Collection, or assert a complete constructive model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualSmallMaps

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualSmallMapConstructions ContextualEnumerationCovers

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {C : D ⥤ Type z}

/-- The only enumeration factory here selects with host choice. -/
noncomputable def selectedEnumerations (operation : NaturalHom A B) (small : SmallFibres operation) :
    UniformEnumerations operation := fun point value => Classical.choice (small point value)

theorem smallFibres_compose (first : NaturalHom A B) (second : NaturalHom B C)
    (inner : SmallFibres first) (outer : SmallFibres second) : SmallFibres (first.comp second) :=
  smallFibres_compose_of_enumerations first second (selectedEnumerations first inner) outer

noncomputable def selectedFutureEnumerations (operation : NaturalHom A B) (small : SmallFibres operation)
    (point : D) (value : B.obj point) : FutureEnumerations operation point value :=
  fun future => selectedEnumerations operation small future.1 (B.map future.2 value)

theorem futureData_exists (operation : NaturalHom A B) (small : SmallFibres operation) :
    ∀ point value, Nonempty (FutureEnumerations operation point value) :=
  fun point value => ⟨selectedFutureEnumerations operation small point value⟩

theorem futureParameter_cover (operation : NaturalHom A B) (small : SmallFibres operation) (point : D) :
    Function.Surjective ((futureProjection operation).app point) :=
  futureProjection_surjective operation (futureData_exists operation small) point

theorem futureTop_cover (operation : NaturalHom A B) (small : SmallFibres operation) (point : D) :
    Function.Surjective ((pullbackFirst operation (futureProjection operation)).app point) :=
  futureTop_surjective operation (futureData_exists operation small) point

/-- Both covering properties come from the named selection factory. The
uniform fibre enumeration of the constructed pullback is choice-free core
data carried by its actual future-data parameters. -/
theorem constructed_covering_diagram (operation : NaturalHom A B) (small : SmallFibres operation) :
    (∀ point, Function.Surjective ((futureProjection operation).app point)) ∧
      (∀ point, Function.Surjective ((pullbackFirst operation (futureProjection operation)).app point)) ∧
        SmallFibres (pullbackSecond operation (futureProjection operation)) :=
  ⟨futureParameter_cover operation small, futureTop_cover operation small, futurePullback_smallFibres operation⟩

#print axioms selectedEnumerations
#print axioms smallFibres_compose
#print axioms selectedFutureEnumerations
#print axioms futureData_exists
#print axioms futureParameter_cover
#print axioms futureTop_cover
#print axioms constructed_covering_diagram

end Mettapedia.TypeTheory.HostChoiceContextualSmallMaps
