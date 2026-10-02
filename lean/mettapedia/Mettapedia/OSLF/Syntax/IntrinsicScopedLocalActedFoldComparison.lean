import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence

/-!
# Classification agrees with the free operational fold

The classifying interpretation of an arbitrary firing-tree arrow, evaluated
at any generalized valuation and read back into the model's event object,
is the independently constructed universal fold of the free operational
model. Program points and endpoints agree as well. The comparison preserves
substitution on event uses and ordered binder-local rule premises, and is
natural along all maps of models.
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
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree
  (Tree Holes freeModel freeModelUniversal interpret foldHom substitute)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra (Environment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution (substJudgment)

universe u v

section TargetFold

universe w p

variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable {target : ClassifierTarget.{u, w, p} R equations}

/-- The target valuation uses the pre-existing universal operational fold. -/
theorem _root_.Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics.ClassifierTarget.Valuation.evaluate_eq_freeFold
    {a : Classifier R equations} (value : target.Valuation a)
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    value.evaluate j tree =
      (((freeModelUniversal R _ _ (target.pointModel value.point))
        value.assignment).evidence.toFun () j tree) := rfl

/-- The evaluation of a node uses the rule algebra read along its point and
one recursively evaluated witness at each premise position. -/
theorem _root_.Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics.ClassifierTarget.Valuation.evaluate_node
    {a : Classifier R equations} (value : target.Valuation a)
    {j : Judgment (modelAt equations a.base)} (shape : Shape R _ j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ shape.1 position)) :
    value.evaluate j (Mettapedia.TypeTheory.IndexedPolynomial.Free.node
      (IntrinsicScopedLocalPolynomial.rules R _) shape children) =
      (target.pointModel value.point).rules.act () j
        ⟨shape, fun position => value.evaluate _ (children position)⟩ :=
  IntrinsicScopedLocalActedFree.interpret_node R _ _
    (target.pointModel value.point) value.assignment shape children

end TargetFold

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace CategoricalModel

variable (model : CategoricalModel R equations (D := D))

/-- At every generalized element the actual classification map of a firing
tree is the universal free-operational-model fold, read into its event object. -/
theorem classification_rep_freeFold {a : Classifier R equations} {Z : D}
    (g : Z ⟶ model.classifyingObject a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (g ≫ ((classificationEquivalence (R := R) (equations := equations) (D := D)).functor.obj
        model).carrier.map (rep R equations j tree)) ≫ (model.eventIso j.1 j.2.1).inv =
      (((freeModelUniversal R _ _ ((model.stageTarget Z).pointModel
        ((model.valuationsRepresentableBy a).homEquiv g).point))
        ((model.valuationsRepresentableBy a).homEquiv g).assignment).evidence.toFun () j tree).1 :=
  model.comp_rep_eventIso_inv g j tree

/-- Reading the classification arrow at the representation of a valuation
evaluates that valuation, including its actual program point. -/
theorem classification_rep_evaluate {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map (rep R equations j tree)) ≫ (model.eventIso j.1 j.2.1).inv =
      (value.evaluate j tree).1 := by
  have compared := model.comp_rep_eventIso_inv
    ((model.valuationsRepresentableBy a).homEquiv.symm value) j tree
  have same := (model.valuationsRepresentableBy a).homEquiv.apply_symm_apply value
  have judgment := congrArg (fun valuation : model.StageValuation Z a =>
    mapJudgment ((model.stageTarget Z).program valuation.point) j) same
  have evaluated := congr_arg_heq (fun valuation : model.StageValuation Z a =>
    valuation.evaluate j tree) same
  have events := model.objects.stageEvent_val_heq judgment evaluated
  exact compared.trans (eq_of_heq events)

/-- Every ordered program/event valuation is covered by the fold comparison,
not only the canonical generalized element. -/
theorem classification_rep_freeFold_valuation {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map (rep R equations j tree)) ≫ (model.eventIso j.1 j.2.1).inv =
      (((freeModelUniversal R _ _ ((model.stageTarget Z).pointModel value.point))
        value.assignment).evidence.toFun () j tree).1 := by
  exact (model.classification_rep_evaluate value j tree).trans
    (congrArg Subtype.val (value.evaluate_eq_freeFold j tree))

/-- The represented tree's program point is exactly the interpreted pair of
its endpoints, independent of its derivation. -/
theorem classification_rep_program_point {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map (rep R equations j tree)) ≫
        model.programProjection (eventObject R equations j.1 j.2.1) =
      value.point ≫ model.programFunctor.map (judgmentBase equations j) := by
  have point : (model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.programProjection a = value.point :=
    congrArg ClassifierTarget.Valuation.point
      ((model.valuationsRepresentableBy a).homEquiv.apply_symm_apply value)
  exact (Category.assoc _ _ _).trans
    ((congrArg (((model.valuationsRepresentableBy a).homEquiv.symm value) ≫ ·)
      (model.map_programProjection (rep R equations j tree))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ model.programFunctor.map (judgmentBase equations j)) point)))

/-- The fold comparison preserves the source endpoint. -/
theorem classification_rep_source {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map (rep R equations j tree)) ≫ (model.eventIso j.1 j.2.1).inv) ≫
        model.objects.source j.1 j.2.1 =
      model.programModel.elemEquiv (((model.stageTarget Z).program value.point).raw.map j.2.2.1) := by
  rw [model.classification_rep_freeFold_valuation value j tree]
  exact (((freeModelUniversal R _ _ ((model.stageTarget Z).pointModel value.point))
    value.assignment).evidence.toFun () j tree).2.1

/-- The fold comparison preserves the target endpoint. -/
theorem classification_rep_target {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map (rep R equations j tree)) ≫ (model.eventIso j.1 j.2.1).inv) ≫
        model.objects.target j.1 j.2.1 =
      model.programModel.elemEquiv (((model.stageTarget Z).program value.point).raw.map j.2.2.2) := by
  rw [model.classification_rep_freeFold_valuation value j tree]
  exact (((freeModelUniversal R _ _ ((model.stageTarget Z).pointModel value.point))
    value.assignment).evidence.toFun () j tree).2.2

/-- Substitution of an arbitrary firing tree, including substituted variable
uses and binder-local nodes, is interpreted by the target's actual action. -/
theorem classification_rep_substitute {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) {Δ : Ctx S}
    (σ : Environment S (modelAt equations a.base).substitution.Carrier j.1 Δ)
    (target : Judgment (modelAt equations a.base)) (same : substJudgment j σ = target) :
    ((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map
        (rep R equations target (substitute R _ _ j tree σ target same))) ≫
        (model.eventIso target.1 target.2.1).inv =
      (((model.stageTarget Z).pointModel value.point).act j
        (((freeModelUniversal R _ _ ((model.stageTarget Z).pointModel value.point))
          value.assignment).evidence.toFun () j tree) σ target same).1 := by
  rw [model.classification_rep_freeFold_valuation value target]
  exact congrArg Subtype.val
    (((freeModelUniversal R _ _ ((model.stageTarget Z).pointModel value.point))
      value.assignment).preserves j tree σ target same)

/-- A substituted event-variable leaf is interpreted from its retained
natural assignment; no rule constructor is added. -/
theorem classification_rep_leaf {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (hole : Holes _ (seeds R _ (events R equations a)) j) :
    ((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map
        (rep R equations j (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure
          (IntrinsicScopedLocalPolynomial.rules R _) hole))) ≫
        (model.eventIso j.1 j.2.1).inv = (value.assignment.value j hole).1 := by
  rw [model.classification_rep_freeFold_valuation]
  exact congrArg Subtype.val (IntrinsicScopedLocalActedFree.interpret_pure R _ _
    ((model.stageTarget Z).pointModel value.point) value.assignment j hole)

/-- An authored node uses the target's own rule action at the same occurrence,
with recursively folded inputs at every ordered binder-local premise. -/
theorem classification_rep_node {a : Classifier R equations} {Z : D}
    (value : model.StageValuation Z a) {j : Judgment (modelAt equations a.base)}
    (shape : Shape R _ j)
    (children : ∀ p : Fin (R.get shape.1.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ shape.1 p)) :
    ((model.valuationsRepresentableBy a).homEquiv.symm value ≫
      model.classifyingFunctor.map
        (rep R equations j (Mettapedia.TypeTheory.IndexedPolynomial.Free.node
          (IntrinsicScopedLocalPolynomial.rules R _) shape children))) ≫ (model.eventIso j.1 j.2.1).inv =
      (((model.stageTarget Z).pointModel value.point).rules.act () j
        ⟨shape, fun p => value.evaluate _ (children p)⟩).1 := by
  have compared := model.classification_rep_evaluate value j
    (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (IntrinsicScopedLocalPolynomial.rules R _)
      shape children)
  have evaluated := ClassifierTarget.Valuation.evaluate_node
    (target := model.stageTarget Z) (a := a) (j := j) value shape children
  have read := congrArg (fun e : (model.stageTarget Z).model.carrier
    (mapJudgment ((model.stageTarget Z).program value.point) j) => e.1) evaluated
  exact compared.trans read

/-- Classification and the free fold commute with every model map. No
injectivity or coverage of the target events is required. -/
theorem classification_rep_map {M N : CategoricalModel R equations (D := D)} (f : M ⟶ N)
    {a : Classifier R equations} {Z : D} (g : Z ⟶ M.classifyingObject a)
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((g ≫ (classifyingMap f).app a) ≫
      N.classifyingFunctor.map (rep R equations j tree)) ≫ (N.eventIso j.1 j.2.1).inv =
      ((g ≫ M.classifyingFunctor.map (rep R equations j tree)) ≫
        (M.eventIso j.1 j.2.1).inv) ≫ f.events.event j.1 j.2.1 := by
  have natural := congrArg
    (fun k => (g ≫ k) ≫ (N.eventIso j.1 j.2.1).inv)
    ((classifyingMap f).naturality (rep R equations j tree)).symm
  have component := congrArg
    (fun k => (g ≫ M.classifyingFunctor.map (rep R equations j tree)) ≫ k)
    (classifyingMap_eventIso_inv f j.1 j.2.1)
  exact (congrArg (· ≫ (N.eventIso j.1 j.2.1).inv) (Category.assoc _ _ _)).trans
    (natural.trans ((congrArg (· ≫ (N.eventIso j.1 j.2.1).inv)
      (Category.assoc _ _ _).symm).trans ((Category.assoc _ _ _).trans
        (component.trans (Category.assoc _ _ _).symm))))

omit [HasPullbacks D] in
/-- The independent free-model fold fuses with the stage map of any model
map, at arbitrary generalized valuations and for arbitrary firing trees. -/
theorem freeFold_map {M N : CategoricalModel R equations (D := D)} (f : M ⟶ N)
    {a : Classifier R equations} {Z : D} (value : M.StageValuation Z a)
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    HEq (((freeModelUniversal R _ _ ((N.stageTarget Z).pointModel (f.valuation value).point))
      (f.valuation value).assignment).evidence.toFun () j tree)
      (f.events.stage Z _ (((freeModelUniversal R _ _ ((M.stageTarget Z).pointModel value.point))
        value.assignment).evidence.toFun () j tree)) :=
  ClassifierTarget.Valuation.evaluate_map (f.targetHom Z) value j tree

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
