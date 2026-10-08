import Mettapedia.CategoryTheory.FibrationTwoCategory

/-!
# Generic objects in general fibrations

Genericity requires a unique base classifier for each total object, with
an actual Cartesian arrow over that classifier. Its total Cartesian arrow
need not be unique. Classification commutes with Cartesian substitution by
composition and uniqueness of the base map. No preorder or predicate
presentation is required of the total category.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FibrationGenericObject

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open Mettapedia.CategoryTheory.FibrationTwoCategory

universe u v

structure Generic (projection : Fibration.{u,v}) where
  object : projection.Total
  classifies : ∀ source : projection.Total,
    ∃! route : projection.functor.obj source ⟶ projection.functor.obj object,
      ∃ arrow : source ⟶ object, projection.functor.IsCartesian route arrow

namespace Generic

variable {projection : Fibration.{u,v}} (generic : Generic projection)

def characteristic (source : projection.Total) :
    projection.functor.obj source ⟶ projection.functor.obj generic.object :=
  Classical.choose (generic.classifies source)

def classify (source : projection.Total) : source ⟶ generic.object :=
  Classical.choose (Classical.choose_spec (generic.classifies source)).1

theorem classify_cartesian (source : projection.Total) :
    projection.functor.IsCartesian (generic.characteristic source) (generic.classify source) :=
  Classical.choose_spec (Classical.choose_spec (generic.classifies source)).1

theorem classify_base (source : projection.Total) :
    projection.functor.map (generic.classify source) = generic.characteristic source := by
  let := generic.classify_cartesian source
  exact (IsHomLift.eq_of_isHomLift projection.functor
    (generic.characteristic source) (generic.classify source)).symm

theorem unique (source : projection.Total)
    (route : projection.functor.obj source ⟶ projection.functor.obj generic.object)
    (arrow : source ⟶ generic.object)
    (cartesian : projection.functor.IsCartesian route arrow) :
    route = generic.characteristic source :=
  (Classical.choose_spec (generic.classifies source)).2 route ⟨arrow, cartesian⟩

/-- Only the base map is forced by genericity. -/
theorem characteristic_substitution {source target : projection.Total}
    (arrow : source ⟶ target)
    (cartesian : projection.functor.IsCartesian (projection.functor.map arrow) arrow) :
    generic.characteristic source =
      projection.functor.map arrow ≫ generic.characteristic target := by
  let := cartesian
  let := generic.classify_cartesian target
  apply Eq.symm
  apply generic.unique source _ (arrow ≫ generic.classify target)
  infer_instance

theorem characteristic_self :
    generic.characteristic generic.object = 𝟙 (projection.functor.obj generic.object) := by
  apply Eq.symm
  apply generic.unique generic.object _ (𝟙 generic.object)
  infer_instance

end Generic

end Mettapedia.CategoryTheory.FibrationGenericObject
