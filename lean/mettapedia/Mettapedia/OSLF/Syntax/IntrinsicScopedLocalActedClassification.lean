import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFunctorModelLaws
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelMaps

/-!
# Models are the structure-preserving functors out of the classifier

The classifying functor of a model preserves the structure. Conversely, the
values of a structure-preserving functor represent the valuations of its
model, compatibly with arrows: evaluating a firing tree at the valuation of a
map into a value is the functor's value at the tree's arrow. So every
structure-preserving functor is the classifying functor of its model.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree freeModel)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

/-! ## The classifying functor of a model preserves the structure -/

namespace CategoricalModel

variable [HasPullbacks D] (model : CategoricalModel R equations (D := D))

/-- On event-free objects the classifying functor is the classifying functor
of the program model. -/
theorem quotient_programSection_classifyingFunctor :
    (authoredEquationPresentation S equations).quotientFunctor ⋙ programSection R equations ⋙
      model.classifyingFunctor = model.programModel.classifyingFunctor :=
  (congrArg ((authoredEquationPresentation S equations).quotientFunctor ⋙ ·)
    model.programSection_classifyingFunctor).trans
    (model.programModel.quotient_comp_equationClassifyingFunctor _ model.program.satisfies)

/-- **The classifying functor of a model is structure-preserving.** -/
noncomputable def structured : StructuredFunctor R equations (D := D) where
  carrier := model.classifyingFunctor
  program := model.quotient_programSection_classifyingFunctor.symm ▸
    model.programModel.classifyingPreserving
  pullback f j := model.classifyingFunctor_isPullback_reindex f j

end CategoricalModel

/-- **Classifying functors of models, on all maps of models.** -/
noncomputable def classifyFunctor [HasPullbacks D] :
    CategoricalModel R equations (D := D) ⥤ StructuredFunctor R equations (D := D) where
  obj model := model.structured
  map f := CategoricalModel.classifyingMap f
  map_id model := CategoricalModel.classifyingMap_id model
  map_comp f g := CategoricalModel.classifyingMap_comp f g

/-! ## A structure-preserving functor is the classifying functor of its model -/

namespace StructuredFunctor

variable (F : StructuredFunctor R equations (D := D))

/-- **The values of a structure-preserving functor represent the valuations of
its model.** -/
noncomputable def valuationsRepresentableBy (a : Classifier R equations) :
    (F.model.valuations a).RepresentableBy (F.carrier.obj a) :=
  F.model.valuationsRepresentableByCones F.contextCones a

/-- The valuation of a map into a value: its program point, and the value at
each variable. -/
def valuation {a : Classifier R equations} {Z : D} (g : Z ⟶ F.carrier.obj a) :
    F.model.StageValuation Z a :=
  ⟨g ≫ F.programPoint a, fun position => F.treeEvent _ (leaf R (events R equations a) position) g⟩

theorem homEquiv_eq_valuation {a : Classifier R equations} {Z : D} (g : Z ⟶ F.carrier.obj a) :
    (F.valuationsRepresentableBy a).homEquiv g = F.valuation g :=
  rfl

/-- **Evaluating a firing tree at the valuation of a map into a value is the
value at the tree's arrow.** -/
theorem evaluate_valuation {a : Classifier R equations} {Z : D} (g : Z ⟶ F.carrier.obj a)
    (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    (F.valuation g).evaluate J tree = F.treeEvent J tree g := by
  have acts : ActsAlong ((F.model.stageTarget Z).program (F.valuation g).point)
      (freeModel R _ (seeds R _ (events R equations a))) (F.model.stageTarget Z).model.act
      (treeImage g) :=
    actsAlong g
  have rulesAlong' : RulesAlong ((F.model.stageTarget Z).program (F.valuation g).point)
      (freeModel R _ (seeds R _ (events R equations a))) (F.model.stageTarget Z).model.rules
      (treeImage g) :=
    rulesAlong g
  exact interpret_eq_of_variables R (events R equations a) _ (F.valuation g).assignment
    (treeImage g) (isHom_of_along acts rulesAlong')
    (fun position => (F.valuation g).evaluate_leaf position) J tree

/-- **Arrows move the valuations of maps into values as they move
valuations.** -/
theorem homEquiv_map {a b : Classifier R equations} (arrow : a ⟶ b) {Z : D}
    (g : Z ⟶ F.carrier.obj a) :
    (F.valuationsRepresentableBy b).homEquiv (g ≫ F.carrier.map arrow) =
      ((F.valuationsRepresentableBy a).homEquiv g).transport arrow := by
  have point : (g ≫ F.carrier.map arrow) ≫ F.programPoint b =
      (g ≫ F.programPoint a) ≫ F.eventModel.programFunctor.map arrow.base :=
    (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (F.map_programPoint arrow)).trans
      (Category.assoc _ _ _).symm)
  apply ClassifierTarget.Valuation.ext' point
  intro position
  refine HEq.trans ?_ (((F.valuationsRepresentableBy a).homEquiv g).transport_event arrow
    position).symm
  refine HEq.trans ?_ (heq_of_eq (F.evaluate_valuation g _ _)).symm
  have judgmentEq : mapJudgment (F.pointProgram ((g ≫ F.carrier.map arrow) ≫ F.programPoint b))
      ((events R equations b).listed.label position) =
        mapJudgment (valuePoint g) (mapJudgment (modelMap equations arrow.base)
          ((events R equations b).listed.label position)) :=
    (congrArg (fun y => mapJudgment (F.pointProgram y) ((events R equations b).listed.label position))
      point).trans ((congrArg (fun h => mapJudgment h ((events R equations b).listed.label position))
        ((F.model.stageTarget Z).program_move arrow.base (g ≫ F.programPoint a))).trans
        (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ _))
  exact F.eventModel.objects.stageEvent_heq judgmentEq (heq_of_eq ((Category.assoc _ _ _).trans
    (congrArg (g ≫ ·) ((F.carrier.map_comp _ _).symm.trans
      (congrArg F.carrier.map (comp_rep_leaf R equations arrow position))))))

variable [HasPullbacks D]

/-- **A structure-preserving functor is the classifying functor of its model.** -/
noncomputable def counitIso : F.model.classifyingFunctor ≅ F.carrier :=
  (Mettapedia.CategoryTheory.RepresentableLift.isoLift F.model.valuationFunctor
    F.model.classifyingObject F.model.valuationsRepresentableBy F.carrier
    F.valuationsRepresentableBy (fun arrow _ g => F.homEquiv_map arrow g)).symm

/-- The comparison keeps valuations. -/
theorem homEquiv_counitIso_inv (a : Classifier R equations) {Z : D} (g : Z ⟶ F.carrier.obj a) :
    (F.model.valuationsRepresentableBy a).homEquiv (g ≫ F.counitIso.inv.app a) =
      (F.valuationsRepresentableBy a).homEquiv g :=
  Mettapedia.CategoryTheory.RepresentableLift.homEquiv_isoLift F.model.valuationFunctor
    F.model.classifyingObject F.model.valuationsRepresentableBy F.carrier
    F.valuationsRepresentableBy (fun arrow _ g => F.homEquiv_map arrow g) a g

end StructuredFunctor

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
