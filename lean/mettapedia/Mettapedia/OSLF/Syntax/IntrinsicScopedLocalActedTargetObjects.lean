import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetPostcomposition

/-!
# Actual image objects for a change of operational target

The recovered interpretation of a postcomposed classifier has canonical
comparisons with the images of the original program and event objects.
The endpoint comparisons use the original endpoints, rather than only the
existence of an abstract equivalence of models.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace CategoricalModel

variable (M : CategoricalModel R equations (D := D))

/-- The existing satisfying program interpretation on actual image sorts. -/
abbrev imageProgram : SatisfyingInterpretation (D := D')
    (authoredEquationPresentation S equations) :=
  (mapSatisfyingInterpretations H (authoredEquationPresentation S equations)).obj M.program

/-- The actual image event objects with their mapped endpoint arrows. -/
def imageEvents : EventObjects (M.imageProgram H).interpretation.model where
  event Γ s := H.obj (M.objects.event Γ s)
  source Γ s := H.map (M.objects.source Γ s)
  target Γ s := H.map (M.objects.target Γ s)

/-- Recovering the postcomposed program classifier gives the image program
interpretation through the mapped original program-unit isomorphism. -/
def imageProgramIso : M.imageProgram H ≅ (M.structured.postcompose H).programInterpretation :=
  (mapSatisfyingInterpretations H (authoredEquationPresentation S equations)).mapIso M.programUnitIso

/-- The generic event comparison is the image of the original event
comparison, and commutes with both actual image endpoints. -/
def imageEventsHom : (M.imageEvents H).Hom
    (M.structured.postcompose H).eventModel.objects (M.imageProgramIso H).hom where
  event Γ s := H.map (M.eventIso Γ s).hom
  source Γ s := by
    change H.map (M.eventIso Γ s).hom ≫
      (M.structured.postcompose H).eventModel.objects.source Γ s =
        H.map (M.objects.source Γ s) ≫ H.map (M.programUnit.underlying.power Γ s)
    have original : (M.eventIso Γ s).hom ≫ M.structured.eventModel.objects.source Γ s =
        M.objects.source Γ s ≫ M.programUnit.underlying.power Γ s := M.eventUnit.source Γ s
    exact (congrArg (H.map (M.eventIso Γ s).hom ≫ ·)
      (M.structured.postcompose_source H Γ s)).trans
        ((H.map_comp _ _).symm.trans ((congrArg H.map original).trans (H.map_comp _ _)))
  target Γ s := by
    change H.map (M.eventIso Γ s).hom ≫
      (M.structured.postcompose H).eventModel.objects.target Γ s =
        H.map (M.objects.target Γ s) ≫ H.map (M.programUnit.underlying.power Γ s)
    have original : (M.eventIso Γ s).hom ≫ M.structured.eventModel.objects.target Γ s =
        M.objects.target Γ s ≫ M.programUnit.underlying.power Γ s := M.eventUnit.target Γ s
    exact (congrArg (H.map (M.eventIso Γ s).hom ≫ ·)
      (M.structured.postcompose_target H Γ s)).trans
        ((H.map_comp _ _).symm.trans ((congrArg H.map original).trans (H.map_comp _ _)))

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
