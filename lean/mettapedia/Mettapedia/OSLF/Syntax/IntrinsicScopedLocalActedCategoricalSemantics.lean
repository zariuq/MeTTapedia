import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedCategoricalModels

/-!
# The classifying functor of a model in a category

At a stage `Z`, a valuation of a classifier object is a generalized element of
its program object together with a generalized event at each of its event
variables. Classifier arrows transport valuations by evaluating their firing
trees; restaging along a map of stages commutes with this transport. The
valuations therefore form a functor from the classifier to presheaves on `D`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree interpret NaturalAssignment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace CategoricalModel

variable (model : CategoricalModel R equations (D := D))

/-- Valuations at a stage. -/
abbrev StageValuation (Z : D) (a : Classifier R equations) : Type v :=
  (model.stageTarget Z).Valuation a

/-- The model read along a restaged point is the restaged model read along
the point. -/
theorem pointModel_restage {Z Z' : D} (h : Z' ⟶ Z) {X : Base equations}
    (x : Z ⟶ model.programModel.family X.as.arities) :
    (model.stageTarget Z').pointModel (h ≫ x) =
      ((model.stageModel Z').pullback (model.programModel.stageRestage h)).pullback
        (model.programModel.pointProgram _ model.program.satisfies _ x) := by
  change (model.stageModel Z').pullback
      (model.programModel.pointProgram _ model.program.satisfies _ (h ≫ x)) = _
  rw [model.programModel.pointProgram_restage]
  exact SubstitutionModel.pullback_comp _ _ _

/-- **Restaging is a map of targets.** -/
noncomputable def restageTargetHom {Z Z' : D} (h : Z' ⟶ Z) :
    (model.stageTarget Z).Hom (model.stageTarget Z') where
  base := model.programModel.stageRestage h
  evidence := model.restageHom h
  point x := h ≫ x
  point_move _ _ := (Category.assoc _ _ _).symm
  program_point x := model.programModel.pointProgram_restage _ model.program.satisfies _ h x

/-- Restage a valuation along a map of stages. -/
noncomputable def restageValuation {Z Z' : D} (h : Z' ⟶ Z) {a : Classifier R equations}
    (value : model.StageValuation Z a) : model.StageValuation Z' a :=
  value.map (model.restageTargetHom h)

theorem restageValuation_event {Z Z' : D} (h : Z' ⟶ Z) {a : Classifier R equations}
    (value : model.StageValuation Z a) (position : Fin (events R equations a).listed.length) :
    HEq ((model.restageValuation h value).event position)
      (model.objects.restage h (value.event position)) :=
  cast_heq _ _

/-- **Transport along classifier arrows is natural in the stage.** -/
theorem transport_restage {Z Z' : D} (h : Z' ⟶ Z) {a b : Classifier R equations}
    (value : model.StageValuation Z a) (arrow : a ⟶ b) :
    model.restageValuation h (value.transport arrow) =
      (model.restageValuation h value).transport arrow :=
  ClassifierTarget.Valuation.transport_map _ value arrow

theorem restageValuation_id {Z : D} {a : Classifier R equations}
    (value : model.StageValuation Z a) : model.restageValuation (𝟙 Z) value = value := by
  apply ClassifierTarget.Valuation.ext' (Category.id_comp _)
  intro position
  refine (model.restageValuation_event _ value position).trans ?_
  refine model.objects.stageEvent_heq ?_ (heq_of_eq (Category.id_comp _))
  exact (congrArg (fun h => mapJudgment h _) (model.programModel.stageRestage_id Z)).trans
    (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)

theorem restageValuation_comp {Z Z' Z'' : D} (h : Z' ⟶ Z) (k : Z'' ⟶ Z')
    {a : Classifier R equations} (value : model.StageValuation Z a) :
    model.restageValuation (k ≫ h) value =
      model.restageValuation k (model.restageValuation h value) := by
  apply ClassifierTarget.Valuation.ext' (Category.assoc _ _ _)
  intro position
  refine (model.restageValuation_event _ value position).trans ?_
  refine HEq.trans ?_ (model.restageValuation_event k _ position).symm
  refine HEq.trans ?_ (model.objects.restage_heq k ?_ (model.restageValuation_event h value
    position)).symm
  · refine model.objects.stageEvent_heq ?_ (heq_of_eq (Category.assoc _ _ _))
    exact (congrArg (fun p => mapJudgment p _) (model.programModel.stageRestage_comp h k)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ _)
  · exact congrArg (fun p => mapJudgment p ((events R equations a).listed.label position))
      (model.programModel.pointProgram_restage _ model.program.satisfies _ h value.point)

/-- The valuations of a classifier object at every stage. -/
noncomputable def valuations (a : Classifier R equations) : Dᵒᵖ ⥤ Type v where
  obj Z := model.StageValuation Z.unop a
  map h := TypeCat.ofHom (fun value => model.restageValuation h.unop value)
  map_id Z := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact model.restageValuation_id value
  map_comp h k := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact model.restageValuation_comp h.unop k.unop value

/-- **The valuation functor of a model**: each classifier object goes to the
presheaf of its valuations, each arrow to evaluation of its firing trees. -/
noncomputable def valuationFunctor : Classifier R equations ⥤ (Dᵒᵖ ⥤ Type v) where
  obj a := model.valuations a
  map arrow :=
    { app := fun Z => TypeCat.ofHom (fun value => value.transport arrow)
      naturality := by
        intro Z Z' h
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext value
        exact (model.transport_restage h.unop value arrow).symm }
  map_id a := by
    apply NatTrans.ext
    funext Z
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact value.transport_id
  map_comp first second := by
    apply NatTrans.ext
    funext Z
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact value.transport_comp first second

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
