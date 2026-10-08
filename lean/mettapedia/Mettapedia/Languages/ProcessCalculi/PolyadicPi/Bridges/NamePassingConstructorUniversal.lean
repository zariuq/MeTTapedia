import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorClassifying
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Coherent uniqueness of the continuation-constructor interpretation

An independently supplied closed finite-limit map compares just the two
primitive objects and the five constructor arrows with the continuation
algebra. Complete expression reconstruction then earns a unique admitted
natural isomorphism to the constructed interpretation. The admission of a
cell fixes its two primitive object components; no whole-expression or
universal-property law is supplied as input.

This is the relative classifying property of the constructor completion.
Operational-edge/internal-category generators and extra process equations
are not part of this presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorUniversal

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open NamePassingContinuationOperations NamePassingConstructorClassifying

universe u v

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable (operations : Operations C)
variable (candidate : GeneratedCategory.Object signature.{v} ⥤ C)
variable [PreservesFiniteLimits candidate] [MonoidalClosedFunctor candidate]

/-- Independent comparisons at the two fresh object declarations. -/
structure ObjectImages where
  names : candidate.obj nameObject ≅ operations.names
  terms : candidate.obj termObject ≅ operations.termObject

private def emptyBaseComparison :
    GeneratedCategory.baseFunctor signature.{v} ⋙ candidate ≅
      (NamePassingConstructorClassifying.assignment operations).base :=
  NatIso.ofComponents (fun object => isEmptyElim object) (by
    intro source target arrow
    exact False.elim (isEmptyElim source : False))

def primitiveImages (images : ObjectImages operations candidate) :
    AtomicPresentation.PrimitiveImages candidate
      (NamePassingConstructorClassifying.assignment operations) where
  base := emptyBaseComparison operations candidate
  object origin := by
    cases origin with
    | up origin =>
      cases origin with
      | names => exact images.names
      | terms => exact images.terms

/-- A single constructor's image, with its product/function header
comparison earned from the supplied map and the two object comparisons. -/
def normalizedConstructor (images : ObjectImages operations candidate)
    (constructor : Constructor) : Interpretation.ArrowValue C :=
  (FunctorNormalization.assignment
    (AtomicPresentation.functor candidate
      (NamePassingConstructorClassifying.assignment operations)
      (primitiveImages operations candidate images)) headers).arrow (ULift.up constructor)

structure ConstructorImages (images : ObjectImages operations candidate) : Prop where
  constructor (origin : Constructor) :
    normalizedConstructor operations candidate images origin = constructorValue operations origin

theorem arrowImages (images : ObjectImages operations candidate)
    (supplied : ConstructorImages operations candidate images) :
    CoherentExtension.ArrowImages candidate
      (NamePassingConstructorClassifying.assignment operations)
      (primitiveImages operations candidate images) headers where
  arrow origin := supplied.constructor origin.down

def comparison (images : ObjectImages operations candidate)
    (supplied : ConstructorImages operations candidate images) :
    candidate ≅ (constructorMap operations).functor :=
  CoherentExtension.comparison candidate
    (NamePassingConstructorClassifying.assignment operations)
    (primitiveImages operations candidate images) headers
    (arrowImages operations candidate images supplied) (realization operations)

abbrev CellAdmission (images : ObjectImages operations candidate)
    (cell : candidate ⟶ (constructorMap operations).functor) : Prop :=
  CoherentExtension.CellAdmission candidate
    (NamePassingConstructorClassifying.assignment operations)
    (primitiveImages operations candidate images) (realization operations) cell

theorem comparison_admitted (images : ObjectImages operations candidate)
    (supplied : ConstructorImages operations candidate images) :
    CellAdmission operations candidate images
      (comparison operations candidate images supplied).hom :=
  CoherentExtension.comparison_admitted candidate
    (NamePassingConstructorClassifying.assignment operations)
    (primitiveImages operations candidate images) headers
    (arrowImages operations candidate images supplied) (realization operations)

theorem admitted_cell_unique (images : ObjectImages operations candidate)
    (supplied : ConstructorImages operations candidate images)
    (cell : candidate ⟶ (constructorMap operations).functor)
    (admitted : CellAdmission operations candidate images cell) :
    cell = (comparison operations candidate images supplied).hom :=
  CoherentExtension.admitted_cell_unique candidate
    (NamePassingConstructorClassifying.assignment operations)
    (primitiveImages operations candidate images) headers
    (arrowImages operations candidate images supplied) (realization operations) cell admitted

/-- Complete uniqueness is propagated from primitive object and constructor
readings by the generated finite-limit and closed rules. -/
@[instance_reducible] def admittedIsoUnique (images : ObjectImages operations candidate)
    (supplied : ConstructorImages operations candidate images) :
    Unique {iso : candidate ≅ (constructorMap operations).functor //
      CellAdmission operations candidate images iso.hom} :=
  CoherentExtension.admittedIsoUnique candidate
    (NamePassingConstructorClassifying.assignment operations)
    (primitiveImages operations candidate images) (realization operations) headers
    (arrowImages operations candidate images supplied)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorUniversal
