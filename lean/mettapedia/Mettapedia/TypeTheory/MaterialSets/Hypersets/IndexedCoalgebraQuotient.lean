import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraBisimulation

/-!
# Constructed indexed behavioral quotient

The actual quotient retains both complete contextual behavior and its
base parameter. Its descended parameter, small-covered coalgebra and
indexed transition are constructed by kernel quotient elimination.
The projection satisfies the whole indexed coalgebra equation, including
the base coordinate and every admitted future argument.

Behavioral equality within a fixed base fibre is equality in the quotient.
Across distinct base fibres no identification is forced. This does not
construct a final indexed object for all possible source coalgebras.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotient

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open IndexedCoalgebraBisimulation (original Related observation)

universe u v w z
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w}
variable (parameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family parameter))
variable (parameterSquare : transition.comp (IndexedCoveredPower.projection parameter) = parameter)

abbrev family := Mettapedia.TypeTheory.ContextualKernelQuotients.quotient (observation parameter transition)
abbrev projection := Mettapedia.TypeTheory.ContextualKernelQuotients.projection (observation parameter transition)

theorem projection_eq_iff (point : D) (left right : A.obj point) :
    (projection parameter transition).app point left = (projection parameter transition).app point right ↔
      Related parameter transition point left right :=
  (Mettapedia.TypeTheory.ContextualKernelQuotients.projection_eq_iff (observation parameter transition)
    point left right).trans (IndexedCoalgebraBisimulation.observation_eq_iff parameter transition point left right)

theorem parameter_respects : Mettapedia.TypeTheory.ContextualKernelQuotients.Respects
    (observation parameter transition) parameter :=
  fun _ _ _ same => congrArg Prod.fst same

def quotientParameter : NaturalHom (family parameter transition) B :=
  Mettapedia.TypeTheory.ContextualKernelQuotients.descend
    (observation parameter transition) parameter (parameter_respects parameter transition)

theorem parameter_beta (point : D) (argument : A.obj point) :
    (quotientParameter parameter transition).app point ((projection parameter transition).app point argument) =
      parameter.app point argument := rfl

theorem parameter_square :
    (projection parameter transition).comp (quotientParameter parameter transition) = parameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

include parameterSquare in
theorem projected_power_eq {point : D} {left right : A.obj point}
    (related : Related parameter transition point left right) :
    imagePower (projection parameter transition) point ((original parameter transition).app point left) =
      imagePower (projection parameter transition) point ((original parameter transition).app point right) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨child, same, admitted⟩
    obtain ⟨matching, matched, children⟩ :=
      (IndexedCoalgebraBisimulation.related_isBisimulation parameter transition parameterSquare).forth
        related argument.1 admitted
    exact ⟨matching, ((projection_eq_iff parameter transition argument.1.1 child matching).mpr children).symm.trans same,
      matched⟩
  · rintro ⟨child, same, admitted⟩
    obtain ⟨matching, matched, children⟩ :=
      (IndexedCoalgebraBisimulation.related_isBisimulation parameter transition parameterSquare).back
        related argument.1 admitted
    exact ⟨matching, ((projection_eq_iff parameter transition argument.1.1 matching child).mpr children).trans same,
      matched⟩

def coalgebra : NaturalHom (family parameter transition) (CoveredFuturePowerFamilies.family (family parameter transition)) where
  app point := Quotient.lift
    (fun argument => imagePower (projection parameter transition) point ((original parameter transition).app point argument))
    (fun first second same => projected_power_eq parameter transition parameterSquare
      ((IndexedCoalgebraBisimulation.observation_eq_iff parameter transition point first second).mp same))
  naturality {first second} step value := by
    refine Quotient.inductionOn value fun argument => ?_
    exact (imagePower_restrict (projection parameter transition) step
      ((original parameter transition).app first argument)).trans
        (congrArg (imagePower (projection parameter transition) second)
          ((original parameter transition).naturality step argument))

theorem coalgebra_square :
    (original parameter transition).comp (imageHom (projection parameter transition)) =
      (projection parameter transition).comp (coalgebra parameter transition parameterSquare) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem quotient_support (point : D) (value : (family parameter transition).obj point) :
    IndexedCoveredPower.Supports (quotientParameter parameter transition) point
      ((quotientParameter parameter transition).app point value)
      ((coalgebra parameter transition parameterSquare).app point value) := by
  refine Quotient.inductionOn value fun argument future admitted => ?_
  obtain ⟨child, same, childAdmitted⟩ := admitted
  rw [← same]
  exact IndexedCoalgebraBisimulation.future_support parameter transition parameterSquare
    point argument ⟨future.1, child⟩ childAdmitted

def indexedCoalgebra : NaturalHom (family parameter transition)
    (IndexedCoveredPower.family (quotientParameter parameter transition)) where
  app point value := ⟨((quotientParameter parameter transition).app point value,
    (coalgebra parameter transition parameterSquare).app point value),
      quotient_support parameter transition parameterSquare point value⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext ((quotientParameter parameter transition).naturality step value)
      ((coalgebra parameter transition parameterSquare).naturality step value)

theorem indexed_parameter_square :
    (indexedCoalgebra parameter transition parameterSquare).comp
      (IndexedCoveredPower.projection (quotientParameter parameter transition)) =
        quotientParameter parameter transition := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem indexed_projection_square :
    transition.comp (IndexedCoveredPower.image parameter (quotientParameter parameter transition)
      (projection parameter transition) (parameter_square parameter transition)) =
    (projection parameter transition).comp (indexedCoalgebra parameter transition parameterSquare) := by
  apply NaturalHom.ext
  intro point argument
  apply Subtype.ext
  exact Prod.ext (congrArg (fun operation : NaturalHom A B => operation.app point argument) parameterSquare) rfl

theorem relative_bisimilar_iff_eq (point : D) (left right : (family parameter transition).obj point) :
    (ContextualCoalgebraBisimulation.Bisimilar (coalgebra parameter transition parameterSquare) point left right ∧
      (quotientParameter parameter transition).app point left =
        (quotientParameter parameter transition).app point right) ↔ left = right := by
  constructor
  · refine Quotient.inductionOn₂ left right fun first second related => ?_
    exact (projection_eq_iff parameter transition point first second).mpr
      ⟨ContextualCoalgebraBisimulation.bisimilar_reflected (original parameter transition)
        (projection parameter transition) (coalgebra parameter transition parameterSquare)
        (coalgebra_square parameter transition parameterSquare) related.1, related.2⟩
  · intro same
    cases same
    exact ⟨ContextualCoalgebraBisimulation.bisimilar_refl (coalgebra parameter transition parameterSquare) point left, rfl⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotient
