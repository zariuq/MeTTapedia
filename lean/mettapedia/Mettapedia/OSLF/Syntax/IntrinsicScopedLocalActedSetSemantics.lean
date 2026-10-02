import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedClassifier

/-!
# Semantics of the rule-local classifier in a target

A target supplies a binding algebra with a substitution model of the
rule-local presentation over it, and program points at every equation
context. A point interprets the context's equation-class binding model in the
target algebra; reindexing a point along a class of contextual assignments
composes with the assignment's model map.

A valuation of a classifier object is a program point together with one
witness at each listed event variable; distinct positions keep distinct
witnesses even when their endpoints coincide. Along a classifier arrow a
valuation evaluates each assigned firing tree in the target model read along
its point: rule nodes by the model's rule actions, event leaves by its
substitution action on the assigned witnesses.

Points may be the interpretations themselves (Set-valued semantics) or
generalized elements of a program object at a stage (semantics in a category).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics

open _root_.CategoryTheory
open _root_.CategoryTheory.Pseudofunctor
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree
  (Tree interpret freeModel NaturalAssignment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange (pushTree pushHole)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCoherence (interpret_pushTree)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u u' u'' w p

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

set_option linter.checkUnivs false in
/-- A target of the classifier: a substitution model over a binding algebra,
with program points at every equation context, each interpreting that
context's equation-class model, stable under reindexing. -/
structure ClassifierTarget where
  algebra : BindingCloneAlgebra.Algebra.{u} S
  model : SubstitutionModel.{u, w} R algebra
  Point : Base equations → Type p
  program : ∀ {X : Base equations}, Point X →
    FreeBindingClone.Hom (modelAt equations X) algebra
  move : ∀ {X Y : Base equations}, (X ⟶ Y) → Point X → Point Y
  move_id : ∀ {X : Base equations} (point : Point X), move (𝟙 X) point = point
  move_comp : ∀ {X Y Z : Base equations} (first : X ⟶ Y) (second : Y ⟶ Z) (point : Point X),
    move (first ≫ second) point = move second (move first point)
  program_move : ∀ {X Y : Base equations} (assignment : X ⟶ Y) (point : Point X),
    program (move assignment point) =
      FreeBindingClone.Hom.comp (modelMap equations assignment) (program point)

variable {R equations}

namespace ClassifierTarget

variable (target : ClassifierTarget.{u, w, p} R equations)

/-- The target model read along a program point. -/
noncomputable abbrev pointModel {X : Base equations} (point : target.Point X) :
    SubstitutionModel.{0, w} R (modelAt equations X) :=
  target.model.pullback (target.program point)

/-- Reindexing a point reads its model along the assignment's model map. -/
theorem pointModel_move {X Y : Base equations} (assignment : X ⟶ Y) (point : target.Point X) :
    target.pointModel (target.move assignment point) =
      (target.pointModel point).pullback (modelMap equations assignment) := by
  unfold pointModel
  rw [target.program_move]
  exact SubstitutionModel.pullback_comp (modelMap equations assignment) (target.program point)
    target.model

/-- A valuation interprets the program metavariables of a classifier object
and gives one witness at each of its event variables. -/
structure Valuation (a : Classifier R equations) where
  point : target.Point a.base
  event : ∀ position : Fin (events R equations a).listed.length,
    target.model.carrier
      (mapJudgment (target.program point) ((events R equations a).listed.label position))

variable {target}

theorem Valuation.ext' {a : Classifier R equations} {first second : target.Valuation a}
    (point : first.point = second.point)
    (event : ∀ position, HEq (first.event position) (second.event position)) :
    first = second := by
  obtain ⟨firstPoint, firstEvent⟩ := first
  obtain ⟨secondPoint, secondEvent⟩ := second
  change firstPoint = secondPoint at point
  subst point
  congr
  funext position
  exact eq_of_heq (event position)

/-- The witnesses of a valuation, as an interpretation of every use of its
event variables. -/
noncomputable def Valuation.assignment {a : Classifier R equations} (value : target.Valuation a) :
    NaturalAssignment R _ (seeds R _ (events R equations a)) (target.pointModel value.point) :=
  ofSlotValues R _ (target.pointModel value.point) (events R equations a) value.event

/-- Evaluate a firing tree over the event variables of a classifier object. -/
noncomputable def Valuation.evaluate {a : Classifier R equations} (value : target.Valuation a)
    (judgment : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) judgment) :
    target.model.carrier (mapJudgment (target.program value.point) judgment) :=
  interpret R _ _ (target.pointModel value.point) value.assignment judgment tree

/-- A bare event variable evaluates to its witness. -/
theorem Valuation.evaluate_leaf {a : Classifier R equations} (value : target.Valuation a)
    (position : Fin (events R equations a).listed.length) :
    value.evaluate _ (leaf R (events R equations a) position) = value.event position :=
  value_ofSlotValues R _ (target.pointModel value.point) (events R equations a) value.event position

theorem Valuation.evaluate_heq {a : Classifier R equations} (value : target.Valuation a)
    {first second : Judgment (modelAt equations a.base)} (same : first = second)
    {one : Tree R _ (seeds R _ (events R equations a)) first}
    {two : Tree R _ (seeds R _ (events R equations a)) second} (sameTree : HEq one two) :
    HEq (value.evaluate first one) (value.evaluate second two) := by
  subst same
  cases sameTree
  rfl

/-- Transport a valuation along a classifier arrow: reindex the point, and
evaluate each assigned tree. -/
noncomputable def Valuation.transport {a b : Classifier R equations} (value : target.Valuation a)
    (arrow : a ⟶ b) : target.Valuation b where
  point := target.move arrow.base value.point
  event position := cast (congrArg (fun h => target.model.carrier
      (mapJudgment h ((events R equations b).listed.label position)))
      (target.program_move arrow.base value.point).symm)
    (value.evaluate _ (atSlot R _ arrow.fiber position))

theorem Valuation.transport_event {a b : Classifier R equations} (value : target.Valuation a)
    (arrow : a ⟶ b) (position : Fin (events R equations b).listed.length) :
    HEq ((value.transport arrow).event position)
      (value.evaluate _ (atSlot R _ arrow.fiber position)) :=
  cast_heq _ _

/-- Evaluating the trees an arrow substitutes is evaluating in the transported
valuation. -/
theorem Valuation.evaluate_interpret {a b : Classifier R equations} (value : target.Valuation a)
    (arrow : a ⟶ b) (judgment : Judgment (modelAt equations b.base))
    (tree : Tree R _ (seeds R _ (events R equations b)) judgment) :
    HEq (value.evaluate _ (interpret R _ _ _ arrow.fiber _
        (pushTree R (modelMap equations arrow.base)
          (pushSeed R (modelMap equations arrow.base) (events R equations b)) judgment tree)))
      ((value.transport arrow).evaluate judgment tree) := by
  refine (heq_of_eq ((IntrinsicScopedLocalActedFibres.interpret_composeAssignment R _ _
    arrow.fiber value.assignment _ _).symm.trans
    (interpret_pushTree R _ _ _ judgment tree))).trans ?_
  refine interpret_heq_of_slots R (target.pointModel_move arrow.base value.point).symm _ _
    (fun position => ?_) judgment tree
  change HEq ((IntrinsicScopedLocalActedFibres.composeAssignment R _ _ arrow.fiber
      value.assignment).value _ (pushHole (modelMap equations arrow.base)
        (pushSeed R (modelMap equations arrow.base) (events R equations b)) _
        (exactHole R _ (events R equations b) ⟨position, ⟨rfl⟩⟩))) _
  rw [pushHole_exactHole]
  refine HEq.trans ?_ (heq_of_eq (value_ofSlotValues R _
    (target.pointModel (value.transport arrow).point) (events R equations b)
    (value.transport arrow).event position)).symm
  exact (value.transport_event arrow position).symm

theorem Valuation.transport_id {a : Classifier R equations} (value : target.Valuation a) :
    value.transport (𝟙 a) = value := by
  apply Valuation.ext' (target.move_id value.point)
  intro position
  have judgmentEq : mapJudgment (modelMap equations (𝟙 a.base))
      ((events R equations a).listed.label position) =
        (events R equations a).listed.label position :=
    (congrArg (fun h => mapJudgment h ((events R equations a).listed.label position))
      (modelMap_id equations a.base)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)
  exact (value.transport_event _ position).trans
    ((value.evaluate_heq judgmentEq (atSlot_id_heq R equations a position)).trans
      (heq_of_eq (value.evaluate_leaf position)))

theorem Valuation.transport_comp {a b c : Classifier R equations} (value : target.Valuation a)
    (first : a ⟶ b) (second : b ⟶ c) :
    value.transport (first ≫ second) = (value.transport first).transport second := by
  apply Valuation.ext' (target.move_comp first.base second.base value.point)
  intro position
  have judgmentEq : mapJudgment (modelMap equations (first.base ≫ second.base))
      ((events R equations c).listed.label position) =
        mapJudgment (modelMap equations first.base)
          (mapJudgment (modelMap equations second.base)
            ((events R equations c).listed.label position)) :=
    (congrArg (fun h => mapJudgment h ((events R equations c).listed.label position))
      (modelMap_comp equations first.base second.base)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ _)
  refine (value.transport_event _ position).trans ?_
  refine (value.evaluate_heq judgmentEq (atSlot_comp R equations first second position)).trans ?_
  exact (value.evaluate_interpret first _ (atSlot R _ second.fiber position)).trans
    ((value.transport first).transport_event second position).symm

variable (target)

/-- **Semantics of the classifier in a target.** Objects go to their
valuations, arrows to evaluation of their firing trees, keeping individual
witnesses. -/
noncomputable def semantics : Classifier R equations ⥤ Type (max p w) where
  obj a := target.Valuation a
  map arrow := TypeCat.ofHom (fun value => value.transport arrow)
  map_id a := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact value.transport_id
  map_comp first second := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact value.transport_comp first second

/-! ## Maps of targets -/

set_option linter.checkUnivs false in
/-- A map of targets: a binding-clone map of the base algebras, a map of
substitution models into the second model read along it, and a map of
program points compatible with reindexing and with the interpretations. -/
structure Hom (target : ClassifierTarget.{u, w, p} R equations)
    (target' : ClassifierTarget.{u', w, p} R equations) where
  base : FreeBindingClone.Hom target.algebra target'.algebra
  evidence : SubstitutionModel.Hom R _ target.model (target'.model.pullback base)
  point : ∀ {X : Base equations}, target.Point X → target'.Point X
  point_move : ∀ {X Y : Base equations} (assignment : X ⟶ Y) (x : target.Point X),
    point (target.move assignment x) = target'.move assignment (point x)
  program_point : ∀ {X : Base equations} (x : target.Point X),
    target'.program (point x) = FreeBindingClone.Hom.comp (target.program x) base

variable {target} {target' : ClassifierTarget.{u', w, p} R equations}

/-- The model at a moved point is the second model read along the map and
then along the point. -/
theorem Hom.pointModel_point (f : Hom target target') {X : Base equations}
    (x : target.Point X) :
    target'.pointModel (f.point x) =
      (target'.model.pullback f.base).pullback (target.program x) := by
  unfold pointModel
  rw [f.program_point]
  exact SubstitutionModel.pullback_comp _ _ _

theorem Hom.evidence_heq (f : Hom target target') {first second : Judgment target.algebra}
    (same : first = second) {one : target.model.carrier first}
    {two : target.model.carrier second} (sameValue : HEq one two) :
    HEq (f.evidence.evidence.toFun () first one) (f.evidence.evidence.toFun () second two) := by
  subst same
  cases sameValue
  rfl

/-- Move a valuation along a map of targets. -/
noncomputable def Valuation.map (f : Hom target target') {a : Classifier R equations}
    (value : target.Valuation a) : target'.Valuation a where
  point := f.point value.point
  event position := cast (congrArg (fun h => target'.model.carrier
      (mapJudgment h ((events R equations a).listed.label position)))
      (f.program_point value.point).symm)
    (f.evidence.evidence.toFun () _ (value.event position))

theorem Valuation.map_event (f : Hom target target') {a : Classifier R equations}
    (value : target.Valuation a) (position : Fin (events R equations a).listed.length) :
    HEq ((value.map f).event position) (f.evidence.evidence.toFun () _ (value.event position)) :=
  cast_heq _ _

/-- Moving a valuation twice applies both evidence maps. -/
theorem Valuation.map_map_event {target'' : ClassifierTarget.{u'', w, p} R equations}
    (f : Hom target target') (g : Hom target' target'') {a : Classifier R equations}
    (value : target.Valuation a) (position : Fin (events R equations a).listed.length) :
    HEq (((value.map f).map g).event position)
      (g.evidence.evidence.toFun () _ (f.evidence.evidence.toFun () _ (value.event position))) :=
  (Valuation.map_event g _ position).trans (g.evidence_heq
    (congrArg (fun h => mapJudgment h ((events R equations a).listed.label position))
      (f.program_point value.point)) (Valuation.map_event f value position))

/-- **Maps of targets commute with evaluating firing trees.** -/
theorem Valuation.evaluate_map (f : Hom target target') {a : Classifier R equations}
    (value : target.Valuation a) (judgment : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) judgment) :
    HEq ((value.map f).evaluate judgment tree)
      (f.evidence.evidence.toFun () _ (value.evaluate judgment tree)) := by
  refine HEq.trans ?_ (heq_of_eq (IntrinsicScopedLocalActedFree.interpret_mapHom R _ _
    value.assignment (f.evidence.pullback (target.program value.point)) judgment tree))
  refine interpret_heq_of_slots R (f.pointModel_point value.point) _ _
    (fun position => ?_) judgment tree
  refine (heq_of_eq (value_ofSlotValues R _ (target'.pointModel (f.point value.point))
    (events R equations a) (value.map f).event position)).trans ?_
  refine (value.map_event f position).trans ?_
  exact heq_of_eq (congrArg (f.evidence.evidence.toFun () _)
    (value_ofSlotValues R _ (target.pointModel value.point) (events R equations a)
      value.event position)).symm

/-- **Transport along classifier arrows commutes with maps of targets.** -/
theorem Valuation.transport_map (f : Hom target target') {a b : Classifier R equations}
    (value : target.Valuation a) (arrow : a ⟶ b) :
    (value.transport arrow).map f = (value.map f).transport arrow := by
  apply Valuation.ext' (f.point_move arrow.base value.point)
  intro position
  refine (Valuation.map_event f _ position).trans ?_
  refine (f.evidence_heq ?_ (value.transport_event arrow position)).trans ?_
  · exact congrArg (fun h => mapJudgment h ((events R equations b).listed.label position))
      (target.program_move arrow.base value.point)
  refine (Valuation.evaluate_map f value _ _).symm.trans ?_
  exact ((value.map f).transport_event arrow position).symm

variable (target)

/-- **A map of targets is a natural transformation of semantics.** -/
noncomputable def semanticsMap (f : Hom target target') : target.semantics ⟶ target'.semantics where
  app a := TypeCat.ofHom (fun value => value.map f)
  naturality a b arrow := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact Valuation.transport_map f value arrow

end ClassifierTarget

/-! ## Set-valued semantics -/

variable (R equations)

set_option linter.checkUnivs false in
/-- A model of the authored equations with a substitution model of the
rule-local presentation over it. -/
structure OperationalModel where
  base : FreeBindingEquationModel.Model.{u} equations
  model : SubstitutionModel.{u, w} R base.algebra

variable {R equations}

/-- An operational model is a target whose points are the interpretations of
the equation-class models themselves. -/
noncomputable def OperationalModel.toTarget (operational : OperationalModel.{u, w} R equations) :
    ClassifierTarget.{u, w, u} R equations where
  algebra := operational.base.algebra
  model := operational.model
  Point X := FreeBindingClone.Hom (modelAt equations X) operational.base.algebra
  program h := h
  move assignment h := FreeBindingClone.Hom.comp (modelMap equations assignment) h
  move_id {X} h := by
    rw [modelMap_id]
    rfl
  move_comp first second h := by
    rw [modelMap_comp]
    rfl
  program_move _ _ := rfl

/-- **Set semantics of the classifier.** An operational model interprets
every classifier object by its valuations and every classifier arrow by
evaluating its firing trees, keeping individual witnesses. -/
noncomputable def combinedSetSemantics (operational : OperationalModel.{u, w} R equations) :
    Classifier R equations ⥤ Type (max u w) :=
  operational.toTarget.semantics

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
