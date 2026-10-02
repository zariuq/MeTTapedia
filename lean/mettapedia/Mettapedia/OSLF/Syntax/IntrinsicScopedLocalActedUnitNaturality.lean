import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedUniversalProperty
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedCounitNaturality

/-!
# Naturality of the recovered program and event components

The classifying transformation of a model map moves represented valuations
by that map. Its program projections and generic event projections therefore
give the naturality squares of the recovered program and event components.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (mapJudgment)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace CategoricalModel

variable {M N : CategoricalModel R equations (D := D)}

/-- The classifying transformation moves each program point by the model's
program component. -/
theorem classifyingMap_programProjection (f : M ⟶ N) (a : Classifier R equations) :
    (classifyingMap f).app a ≫ N.programProjection a =
      M.programProjection a ≫ Model.familyMap f.program.underlying.power a.base.as.arities := by
  have points := congrArg (fun value : N.StageValuation (M.classifyingObject a) a => value.point)
    (homEquiv_classifyingMap f a (𝟙 (M.classifyingObject a)))
  change (𝟙 _ ≫ (classifyingMap f).app a) ≫ N.programProjection a =
    (𝟙 _ ≫ M.programProjection a) ≫ Model.familyMap f.program.underlying.power a.base.as.arities
      at points
  simpa only [Category.id_comp] using points

/-- On event-free objects the classifying transformation is the contextual
product of the original model's program components. -/
theorem classifyingMap_programSection (f : M ⟶ N) (X : Base equations) :
    (classifyingMap f).app ((programSection R equations).obj X) =
      Model.familyMap f.program.underlying.power X.as.arities := by
  have projection := classifyingMap_programProjection f ((programSection R equations).obj X)
  change (classifyingMap f).app ((programSection R equations).obj X) ≫ 𝟙 _ =
    𝟙 _ ≫ Model.familyMap f.program.underlying.power X.as.arities at projection
  simpa only [Category.comp_id, Category.id_comp] using projection

/-- The program comparison is natural on contextual products. -/
theorem familyMap_programUnit_naturality (f : M ⟶ N) (X : Base equations) :
    Model.familyMap f.program.underlying.power X.as.arities ≫
        Model.familyMap N.programUnit.underlying.power X.as.arities =
      Model.familyMap M.programUnit.underlying.power X.as.arities ≫
        Model.familyMap (StructuredFunctor.modelHom (F := M.structured) (G := N.structured) (classifyingMap f)).program.underlying.power
          X.as.arities := by
  have natural := StructuredFunctor.programIso_naturality
    (F := M.structured) (G := N.structured) (classifyingMap f) X
  have point : Model.familyMap f.program.underlying.power X.as.arities ≫
      (N.structured.programIso X).hom =
      (M.structured.programIso X).hom ≫
        Model.familyMap (StructuredFunctor.programHom (F := M.structured) (G := N.structured)
          (classifyingMap f)).underlying.power X.as.arities :=
    (congrArg (· ≫ (N.structured.programIso X).hom)
      (classifyingMap_programSection f X)).symm.trans natural
  exact (congrArg (Model.familyMap f.program.underlying.power X.as.arities ≫ ·)
    (N.familyMap_programUnit X)).trans
      (point.trans (congrArg (· ≫ _) (M.familyMap_programUnit X).symm))

/-- The program components of the unit are natural on every model map. -/
theorem programUnit_naturality (f : M ⟶ N) :
    f.program ≫ N.programUnit =
      M.programUnit ≫ (StructuredFunctor.modelHom (F := M.structured) (G := N.structured) (classifyingMap f)).program := by
  apply (CategoricalBindingInterpretationMaps.interpretationHomEquiv
    M.programModel N.structured.programModel).injective
  apply NatTrans.ext
  funext X
  change Model.familyMap (fun Γ s => f.program.underlying.power Γ s ≫
      N.programUnit.underlying.power Γ s) X.arities =
    Model.familyMap (fun Γ s => M.programUnit.underlying.power Γ s ≫
      (StructuredFunctor.modelHom (F := M.structured) (G := N.structured) (classifyingMap f)).program.underlying.power Γ s) X.arities
  exact (Model.familyMap_comp f.program.underlying.power N.programUnit.underlying.power X.arities).trans
    ((familyMap_programUnit_naturality f ⟨X⟩).trans
      (Model.familyMap_comp M.programUnit.underlying.power
        (StructuredFunctor.modelHom (F := M.structured) (G := N.structured)
          (classifyingMap f)).program.underlying.power X.arities).symm)

/-- The generic event projection moves by the event component of a model
map. -/
theorem classifyingMap_eventIso_inv (f : M ⟶ N) (Γ : Ctx S) (s : S.Srt) :
    (classifyingMap f).app (eventObject R equations Γ s) ≫ (N.eventIso Γ s).inv =
      (M.eventIso Γ s).inv ≫ f.events.event Γ s := by
  let a := eventObject R equations Γ s
  let position := first R (pairJudgment equations Γ s) (Context.empty R _)
  let value := M.genericValuation a
  have moved := homEquiv_classifyingMap f a (𝟙 (M.classifyingObject a))
  have eventEq := congr_arg_heq (fun value : N.StageValuation (M.classifyingObject a) a =>
    value.event position) moved
  have judgmentEq : mapJudgment ((N.stageTarget (M.classifyingObject a)).program
      ((N.valuationsRepresentableBy a).homEquiv
        (𝟙 (M.classifyingObject a) ≫ (classifyingMap f).app a)).point)
      ((events R equations a).listed.label position) =
      mapJudgment (stageMap f.program (M.classifyingObject a))
        (mapJudgment ((M.stageTarget (M.classifyingObject a)).program value.point)
          ((events R equations a).listed.label position)) :=
    (congrArg (fun value : N.StageValuation (M.classifyingObject a) a =>
      mapJudgment ((N.stageTarget (M.classifyingObject a)).program value.point)
        ((events R equations a).listed.label position)) moved).trans
      ((congrArg (fun φ => mapJudgment φ ((events R equations a).listed.label position))
        ((f.targetHom (M.classifyingObject a)).program_point value.point)).trans
        (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ _))
  have maps := N.objects.stageEvent_val_heq judgmentEq
    (eventEq.trans (f.valuation_event value position))
  change HEq ((𝟙 _ ≫ (classifyingMap f).app a) ≫ (N.eventIso Γ s).inv)
    ((𝟙 _ ≫ (M.eventIso Γ s).inv) ≫ f.events.event Γ s) at maps
  simpa only [Category.id_comp] using eq_of_heq maps

/-- The event components of the unit are natural on every model map. -/
theorem eventUnit_naturality (f : M ⟶ N) (Γ : Ctx S) (s : S.Srt) :
    f.events.event Γ s ≫ (N.eventIso Γ s).hom =
      (M.eventIso Γ s).hom ≫ (classifyingMap f).app (eventObject R equations Γ s) := by
  have inverse := classifyingMap_eventIso_inv f Γ s
  have moved := congrArg (fun g => (M.eventIso Γ s).hom ≫ g ≫ (N.eventIso Γ s).hom) inverse
  have left : (M.eventIso Γ s).hom ≫
      ((classifyingMap f).app (eventObject R equations Γ s) ≫ (N.eventIso Γ s).inv) ≫
      (N.eventIso Γ s).hom =
      (M.eventIso Γ s).hom ≫ (classifyingMap f).app (eventObject R equations Γ s) :=
    congrArg ((M.eventIso Γ s).hom ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (N.eventIso Γ s).inv_hom_id).trans
        (Category.comp_id _)))
  have right : (M.eventIso Γ s).hom ≫
      ((M.eventIso Γ s).inv ≫ f.events.event Γ s) ≫ (N.eventIso Γ s).hom =
      f.events.event Γ s ≫ (N.eventIso Γ s).hom := by
    rw [← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (right.symm.trans moved.symm).trans left

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
