import Mettapedia.TypeTheory.PresheafDependentAdjunction
import Mettapedia.TypeTheory.SliceBeckChevalley

/-!
# Dependent-product base change on presheaf slices

For any pullback square of small presheaves, dependent product commutes
with substitution. The comparison is obtained by conjugating the
dependent-sum pullback-pasting isomorphism across the existing adjunctions.
Its evaluation and abstraction laws retain entire slice morphisms.

This is change of context within one presheaf model. It does not assert
that an arbitrary change of the underlying syntax category preserves Pi.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafDependentBaseChange

open CategoryTheory CategoryTheory.Limits
open Mettapedia.Computability.ComputationalTrinity
open PresheafDependentAdjunction SliceBeckChevalley

universe u
variable {C : Type u} [Category.{u} C]
variable {A B D E : Face.{u, u, u} C}
variable {top : D ⟶ A} {left : D ⟶ E}
variable {right : A ⟶ B} {bottom : E ⟶ B}

/-- Dependent products commute with substitution around every pullback
square, as a natural isomorphism of functors on actual slice categories. -/
noncomputable def piBaseChange
    (square : IsPullback top left right bottom) :
    dependentProduct right ⋙ Over.pullback bottom ≅
      Over.pullback top ⋙ dependentProduct left :=
  conjugateIsoEquiv
    ((Over.mapPullbackAdj bottom).comp (dependentAdjunction right))
    ((dependentAdjunction left).comp (Over.mapPullbackAdj top))
    (sigmaBaseChange square.flip)

/-- Evaluation determines the base-change comparison through the
composite adjunctions. This is the counit law of the conjugate, not just
an objectwise isomorphism of function spaces. -/
theorem piBaseChange_evaluation
    (square : IsPullback top left right bottom) (Y : Over A) :
    (Over.pullback left ⋙ Over.map top).map
        ((piBaseChange square).hom.app Y) ≫
      ((dependentAdjunction left).comp (Over.mapPullbackAdj top)).counit.app Y =
    (sigmaBaseChange square.flip).hom.app
        ((dependentProduct right ⋙ Over.pullback bottom).obj Y) ≫
      ((Over.mapPullbackAdj bottom).comp (dependentAdjunction right)).counit.app Y :=
  conjugateEquiv_counit _ _ (sigmaBaseChange square.flip).hom Y

/-- Abstraction followed by context change agrees with context change
of the body followed by abstraction. -/
theorem piBaseChange_transpose
    (square : IsPullback top left right bottom)
    (X : Over E) (Y : Over A)
    (body : (Over.map bottom ⋙ Over.pullback right).obj X ⟶ Y) :
    ((Over.mapPullbackAdj bottom).comp (dependentAdjunction right)).homEquiv X Y body ≫
        (piBaseChange square).hom.app Y =
      ((dependentAdjunction left).comp (Over.mapPullbackAdj top)).homEquiv X Y
        ((sigmaBaseChange square.flip).hom.app X ≫ body) := by
  let first := (Over.mapPullbackAdj bottom).comp (dependentAdjunction right)
  let second := (dependentAdjunction left).comp (Over.mapPullbackAdj top)
  let comparison := (sigmaBaseChange square.flip).hom
  apply (second.homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, piBaseChange_evaluation]
  rw [← Category.assoc, comparison.naturality]
  rw [Category.assoc, ← Adjunction.homEquiv_counit]
  exact congrArg (fun k => comparison.app X ≫ k)
    ((first.homEquiv X Y).symm_apply_apply body)

end Mettapedia.TypeTheory.PresheafDependentBaseChange
