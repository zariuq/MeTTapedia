import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedCategoricalSemantics
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mettapedia.CategoryTheory.RepresentableLift

/-!
# Valuations are represented by iterated pullbacks

Over the program object of an equation context, each listed event variable
adds a pullback of its event object's endpoints along the endpoints its
judgment names. Maps into the resulting object are exactly valuations: a
generalized element of the program object and a generalized event at each
variable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres (atSlot atSlot_weaken first)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace EventModel

variable (model : EventModel equations (D := D))

/-- The generic point of a program object. -/
noncomputable abbrev genericProgram (X : Base equations) :=
  model.programModel.pointProgram _ model.program.satisfies X.as
    (𝟙 (model.programModel.family X.as.arities))

/-- The endpoints of an event object. -/
def eventEndpoints (Γ : Ctx S) (s : S.Srt) :
    model.objects.event Γ s ⟶ model.programModel.power Γ s ⊗ model.programModel.power Γ s :=
  lift (model.objects.source Γ s) (model.objects.target Γ s)

/-- The endpoints a judgment of the equation-class model names, at the
generic point of the program object. -/
noncomputable def judgmentEndpoints (X : Base equations) (j : Judgment (modelAt equations X)) :
    model.programModel.family X.as.arities ⟶
      model.programModel.power j.1 j.2.1 ⊗ model.programModel.power j.1 j.2.1 :=
  lift (model.programModel.elemEquiv ((model.genericProgram X).raw.map j.2.2.1))
    (model.programModel.elemEquiv ((model.genericProgram X).raw.map j.2.2.2))

/-- The endpoint of a term at a point is the point followed by the endpoint at
the generic point. -/
theorem elemEquiv_pointProgram (X : Base equations) {Z : D}
    (x : Z ⟶ model.programModel.family X.as.arities) {Γ : Ctx S} {s : S.Srt}
    (term : (modelAt equations X).substitution.Carrier Γ s) :
    model.programModel.elemEquiv
        ((model.programModel.pointProgram _ model.program.satisfies X.as x).raw.map term) =
      x ≫ model.programModel.elemEquiv ((model.genericProgram X).raw.map term) := by
  have point := model.programModel.pointProgram_restage _ model.program.satisfies X.as x
    (𝟙 (model.programModel.family X.as.arities))
  rw [Category.comp_id] at point
  rw [point]
  exact model.programModel.elemEquiv_restage x _

/-- The events of a valuation over a generalized element of the program
object. -/
abbrev PointEvents (X : Base equations) (n : ℕ) (label : Fin n → Judgment (modelAt equations X))
    {Z : D} (x : Z ⟶ model.programModel.family X.as.arities) : Type v :=
  ∀ position : Fin n, model.objects.StageEvent Z
    (mapJudgment (model.programModel.pointProgram _ model.program.satisfies X.as x)
      (label position))

theorem source_eventEndpoints (Γ : Ctx S) (s : S.Srt) :
    model.eventEndpoints Γ s ≫ fst _ _ = model.objects.source Γ s :=
  lift_fst _ _

theorem target_eventEndpoints (Γ : Ctx S) (s : S.Srt) :
    model.eventEndpoints Γ s ≫ snd _ _ = model.objects.target Γ s :=
  lift_snd _ _

/-- A generalized event over a point has the endpoints its judgment names at
that point. -/
theorem pointEvent_endpoints (X : Base equations) {Z : D}
    (x : Z ⟶ model.programModel.family X.as.arities) (j : Judgment (modelAt equations X))
    (event : model.objects.StageEvent Z
      (mapJudgment (model.programModel.pointProgram _ model.program.satisfies X.as x) j)) :
    event.1 ≫ model.eventEndpoints j.1 j.2.1 = x ≫ model.judgmentEndpoints X j := by
  apply hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (event.1 ≫ ·)
      (model.source_eventEndpoints j.1 j.2.1)).trans (event.2.1.trans
        ((model.elemEquiv_pointProgram X x _).trans
          ((congrArg (x ≫ ·) (lift_fst _ _)).symm.trans (Category.assoc _ _ _).symm))))
  · exact (Category.assoc _ _ _).trans ((congrArg (event.1 ≫ ·)
      (model.target_eventEndpoints j.1 j.2.1)).trans (event.2.2.trans
        ((model.elemEquiv_pointProgram X x _).trans
          ((congrArg (x ≫ ·) (lift_snd _ _)).symm.trans (Category.assoc _ _ _).symm))))

/-- **A map into an event object is a generalized event over a point** as soon
as its endpoints are those the judgment names at the point. -/
def pointEvent (X : Base equations) {Z : D} (x : Z ⟶ model.programModel.family X.as.arities)
    (j : Judgment (modelAt equations X)) (e : Z ⟶ model.objects.event j.1 j.2.1)
    (endpoints : e ≫ model.eventEndpoints j.1 j.2.1 = x ≫ model.judgmentEndpoints X j) :
    model.objects.StageEvent Z
      (mapJudgment (model.programModel.pointProgram _ model.program.satisfies X.as x) j) :=
  ⟨e,
    by
      have square := congrArg (· ≫ fst _ _) endpoints
      simp only [Category.assoc, source_eventEndpoints, judgmentEndpoints, lift_fst] at square
      exact square.trans (model.elemEquiv_pointProgram X x _).symm,
    by
      have square := congrArg (· ≫ snd _ _) endpoints
      simp only [Category.assoc, target_eventEndpoints, judgmentEndpoints, lift_snd] at square
      exact square.trans (model.elemEquiv_pointProgram X x _).symm⟩

theorem pointEvent_val (X : Base equations) {Z : D} (x : Z ⟶ model.programModel.family X.as.arities)
    (j : Judgment (modelAt equations X)) (e : Z ⟶ model.objects.event j.1 j.2.1)
    (endpoints : e ≫ model.eventEndpoints j.1 j.2.1 = x ≫ model.judgmentEndpoints X j) :
    (model.pointEvent X x j e endpoints).1 = e :=
  rfl

/-! ## Objects of valuations -/

/-- **Objects of valuations over a program context.** For each ordered list
of event variables, an object with a program point and an event at each
variable. The first variable's event and forgetting that variable form a
pullback of its event object's endpoints along the endpoints its judgment
names; with no variables, the program point is an isomorphism. -/
structure ContextCones (X : Base equations) where
  obj : ∀ n : ℕ, (Fin n → Judgment (modelAt equations X)) → D
  program : ∀ n label, obj n label ⟶ model.programModel.family X.as.arities
  event : ∀ n label (position : Fin n),
    obj n label ⟶ model.objects.event (label position).1 (label position).2.1
  forget : ∀ n label, obj (n + 1) label ⟶ obj n (Fin.tail label)
  forget_program : ∀ n label,
    forget n label ≫ program n (Fin.tail label) = program (n + 1) label
  forget_event : ∀ n label (position : Fin n),
    forget n label ≫ event n (Fin.tail label) position = event (n + 1) label position.succ
  isPullback : ∀ n label, IsPullback (event (n + 1) label 0) (forget n label)
    (model.eventEndpoints (label 0).1 (label 0).2.1)
    (program n (Fin.tail label) ≫ model.judgmentEndpoints X (label 0))
  program_zero : ∀ label, IsIso (program 0 label)

namespace ContextCones

variable {model} {X : Base equations} (cones : model.ContextCones X)

/-- Each listed event has the endpoints its judgment names. -/
theorem event_endpoints :
    ∀ (n : ℕ) (label : Fin n → Judgment (modelAt equations X)) (position : Fin n),
      cones.event n label position ≫ model.eventEndpoints (label position).1 (label position).2.1 =
        cones.program n label ≫ model.judgmentEndpoints X (label position)
  | n + 1, label, position => by
      cases position using Fin.cases with
      | zero =>
          rw [(cones.isPullback n label).w, ← cones.forget_program, Category.assoc]
      | succ rest =>
          exact (congrArg (· ≫ model.eventEndpoints _ _) (cones.forget_event n label rest)).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (cones.forget n label ≫ ·)
                (event_endpoints n (Fin.tail label) rest)).trans
                ((Category.assoc _ _ _).symm.trans
                  (congrArg (· ≫ model.judgmentEndpoints X _) (cones.forget_program n label)))))

/-- A map into a cone gives a generalized event at each variable. -/
def events {n : ℕ} {label : Fin n → Judgment (modelAt equations X)} {Z : D}
    (g : Z ⟶ cones.obj n label) : model.PointEvents X n label (g ≫ cones.program n label) :=
  fun position => model.pointEvent X (g ≫ cones.program n label) (label position)
    (g ≫ cones.event n label position)
    ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (cones.event_endpoints n label position)).trans
      (Category.assoc _ _ _).symm))

/-- A point with events lifts to a map into the cone over the point. -/
noncomputable def lift :
    ∀ (n : ℕ) (label : Fin n → Judgment (modelAt equations X)) {Z : D}
      (x : Z ⟶ model.programModel.family X.as.arities) (_ : model.PointEvents X n label x),
      {g : Z ⟶ cones.obj n label // g ≫ cones.program n label = x}
  | 0, label, _, x, _ =>
      haveI := cones.program_zero label
      ⟨x ≫ inv (cones.program 0 label), by simp⟩
  | n + 1, label, _, x, events =>
      let rest := lift n (Fin.tail label) x (fun position => events position.succ)
      ⟨(cones.isPullback n label).lift (events 0).1 rest.1
          ((model.pointEvent_endpoints X x (label 0) (events 0)).trans
            ((congrArg (· ≫ model.judgmentEndpoints X (label 0)) rest.2).symm.trans
              (Category.assoc _ _ _))),
        ((congrArg (_ ≫ ·) (cones.forget_program n label)).symm.trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ cones.program n (Fin.tail label))
              ((cones.isPullback n label).lift_snd _ _ _)))).trans rest.2⟩

theorem lift_event :
    ∀ (n : ℕ) (label : Fin n → Judgment (modelAt equations X)) {Z : D}
      (x : Z ⟶ model.programModel.family X.as.arities) (events : model.PointEvents X n label x)
      (position : Fin n),
      (cones.lift n label x events).1 ≫ cones.event n label position = (events position).1
  | n + 1, label, _, x, events, position => by
      cases position using Fin.cases with
      | zero => exact (cones.isPullback n label).lift_fst _ _ _
      | succ rest =>
          exact (congrArg (_ ≫ ·) (cones.forget_event n label rest)).symm.trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ cones.event n (Fin.tail label) rest)
                ((cones.isPullback n label).lift_snd _ _ _)).trans
                (lift_event n (Fin.tail label) x (fun position => events position.succ) rest)))

/-- Maps into a cone agreeing on the program point and on every event are
equal. -/
theorem hom_ext :
    ∀ (n : ℕ) (label : Fin n → Judgment (modelAt equations X)) {Z : D}
      {g g' : Z ⟶ cones.obj n label},
      g ≫ cones.program n label = g' ≫ cones.program n label →
      (∀ position, g ≫ cones.event n label position = g' ≫ cones.event n label position) →
      g = g'
  | 0, label, _, g, g', program, _ => by
      have := cones.program_zero label
      exact (cancel_mono (cones.program 0 label)).mp program
  | n + 1, label, _, g, g', program, events => by
      apply (cones.isPullback n label).hom_ext
      · exact events 0
      · refine hom_ext n (Fin.tail label) ?_ (fun rest => ?_)
        · rw [Category.assoc, Category.assoc, cones.forget_program]
          exact program
        · rw [Category.assoc, Category.assoc, cones.forget_event]
          exact events rest.succ

/-- **Maps into a cone are points with events.** -/
noncomputable def homEquiv (n : ℕ) (label : Fin n → Judgment (modelAt equations X)) (Z : D) :
    (Z ⟶ cones.obj n label) ≃
      Σ x : Z ⟶ model.programModel.family X.as.arities, model.PointEvents X n label x where
  toFun g := ⟨g ≫ cones.program n label, cones.events g⟩
  invFun data := (cones.lift n label data.1 data.2).1
  left_inv g := cones.hom_ext n label (cones.lift n label _ _).2
    (fun position => cones.lift_event n label _ _ position)
  right_inv data := by
    obtain ⟨x, events⟩ := data
    have point := (cones.lift n label x events).2
    refine Sigma.ext point ?_
    refine Function.hfunext rfl (fun position position' same => ?_)
    cases same
    refine model.objects.stageEvent_heq ?_ (heq_of_eq (cones.lift_event n label x events position))
    exact congrArg (fun y => mapJudgment
      (model.programModel.pointProgram _ model.program.satisfies X.as y) (label position)) point

end ContextCones

/-- Judgment endpoints are natural in the equation context. -/
theorem judgmentEndpoints_map {X Y : Base equations} (assignment : Y ⟶ X)
    (j : Judgment (modelAt equations X)) :
    model.programFunctor.map assignment ≫ model.judgmentEndpoints X j =
      model.judgmentEndpoints Y (mapJudgment (modelMap equations assignment) j) := by
  have moved := (congrArg (model.programModel.pointProgram _ model.program.satisfies X.as)
    (Category.id_comp (model.programFunctor.map assignment)).symm).trans
    (model.programModel.pointProgram_move equations model.program.satisfies assignment
      (𝟙 (model.programModel.family Y.as.arities)))
  apply hom_ext
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (lift_fst _ _)).trans ?_)
    refine (model.elemEquiv_pointProgram X _ _).symm.trans ?_
    refine Eq.trans ?_ (lift_fst _ _).symm
    exact congrArg (fun h => model.programModel.elemEquiv (h.raw.map j.2.2.1)) moved
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (lift_snd _ _)).trans ?_)
    refine (model.elemEquiv_pointProgram X _ _).symm.trans ?_
    refine Eq.trans ?_ (lift_snd _ _).symm
    exact congrArg (fun h => model.programModel.elemEquiv (h.raw.map j.2.2.2)) moved

variable [HasPullbacks D]

/-- Adding one event variable: the pullback of its event object's endpoints
along the endpoints its judgment names. -/
noncomputable def extendData (X : Base equations)
    (base : Σ C : D, C ⟶ model.programModel.family X.as.arities)
    (j : Judgment (modelAt equations X)) :
    Σ C : D, C ⟶ model.programModel.family X.as.arities :=
  ⟨pullback (model.eventEndpoints j.1 j.2.1) (base.2 ≫ model.judgmentEndpoints X j),
    pullback.snd _ _ ≫ base.2⟩

/-- The object of valuations of a list of event variables over a program
context, with its projection to the program object. -/
noncomputable def contextData (X : Base equations) :
    ∀ (n : ℕ) (_ : Fin n → Judgment (modelAt equations X)),
      Σ C : D, C ⟶ model.programModel.family X.as.arities
  | 0, _ => ⟨model.programModel.family X.as.arities, 𝟙 _⟩
  | n + 1, label => model.extendData X (contextData X n (Fin.tail label)) (label 0)

theorem contextData_succ (X : Base equations) (n : ℕ)
    (label : Fin (n + 1) → Judgment (modelAt equations X)) :
    model.contextData X (n + 1) label =
      model.extendData X (model.contextData X n (Fin.tail label)) (label 0) :=
  rfl

/-- The new variable's event. -/
noncomputable def extendEvent (X : Base equations)
    (base : Σ C : D, C ⟶ model.programModel.family X.as.arities)
    (j : Judgment (modelAt equations X)) :
    (model.extendData X base j).1 ⟶ model.objects.event j.1 j.2.1 :=
  pullback.fst (model.eventEndpoints j.1 j.2.1) (base.2 ≫ model.judgmentEndpoints X j)

/-- Forget the new variable. -/
noncomputable def extendBase (X : Base equations)
    (base : Σ C : D, C ⟶ model.programModel.family X.as.arities)
    (j : Judgment (modelAt equations X)) :
    (model.extendData X base j).1 ⟶ base.1 :=
  pullback.snd (model.eventEndpoints j.1 j.2.1) (base.2 ≫ model.judgmentEndpoints X j)

/-- The event at one listed variable. -/
noncomputable def eventProjection (X : Base equations) :
    ∀ (n : ℕ) (label : Fin n → Judgment (modelAt equations X)) (position : Fin n),
      (model.contextData X n label).1 ⟶ model.objects.event (label position).1 (label position).2.1
  | n + 1, label, position =>
      Fin.cases (motive := fun position =>
          (model.contextData X (n + 1) label).1 ⟶
            model.objects.event (label position).1 (label position).2.1)
        (model.extendEvent X (model.contextData X n (Fin.tail label)) (label 0))
        (fun rest => model.extendBase X (model.contextData X n (Fin.tail label)) (label 0) ≫
          eventProjection X n (Fin.tail label) rest) position

/-- **The chosen objects of valuations**: iterated pullbacks. -/
noncomputable def contextCones (X : Base equations) : model.ContextCones X where
  obj n label := (model.contextData X n label).1
  program n label := (model.contextData X n label).2
  event := model.eventProjection X
  forget n label := model.extendBase X (model.contextData X n (Fin.tail label)) (label 0)
  forget_program _ _ := rfl
  forget_event _ _ _ := rfl
  isPullback _ _ := IsPullback.of_hasPullback _ _
  program_zero _ := inferInstanceAs (IsIso (𝟙 _))

end EventModel

namespace CategoricalModel

variable (model : CategoricalModel R equations (D := D))

/-- **Valuations are represented by objects of valuations.** -/
noncomputable def valuationsRepresentableByCones (cones : ∀ X, model.toEventModel.ContextCones X)
    (a : Classifier R equations) :
    (model.valuations a).RepresentableBy
      ((cones a.base).obj (events R equations a).listed.length (events R equations a).listed.label) where
  homEquiv {Z} :=
    { toFun := fun g => ⟨g ≫ (cones a.base).program _ _, (cones a.base).events g⟩
      invFun := fun value => ((cones a.base).lift _ _ value.point value.event).1
      left_inv := fun g => (cones a.base).hom_ext _ _ ((cones a.base).lift _ _ _ _).2
        (fun position => (cones a.base).lift_event _ _ _ _ position)
      right_inv := fun value => by
        apply ClassifierTarget.Valuation.ext' ((cones a.base).lift _ _ value.point value.event).2
        intro position
        refine model.objects.stageEvent_heq ?_
          (heq_of_eq ((cones a.base).lift_event _ _ value.point value.event position))
        exact congrArg (fun x => mapJudgment
          (model.programModel.pointProgram _ model.program.satisfies _ x)
          ((events R equations a).listed.label position))
          ((cones a.base).lift _ _ value.point value.event).2 }
  homEquiv_comp {Z Z'} f g := by
    apply ClassifierTarget.Valuation.ext' (Category.assoc _ _ _)
    intro position
    refine HEq.trans ?_ (model.restageValuation_event f _ position).symm
    refine model.objects.stageEvent_heq ?_ (heq_of_eq (Category.assoc _ _ _))
    refine (congrArg (fun x => mapJudgment
      (model.programModel.pointProgram _ model.program.satisfies _ x)
      ((events R equations a).listed.label position)) (Category.assoc f g _)).trans ?_
    exact (congrArg (fun p => mapJudgment p ((events R equations a).listed.label position))
      (model.programModel.pointProgram_restage _ model.program.satisfies _ f _)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ _)

variable [HasPullbacks D]

/-- **Valuations are represented by the context object.** -/
noncomputable def valuationsRepresentableBy (a : Classifier R equations) :
    (model.valuations a).RepresentableBy
      (model.toEventModel.contextData a.base (events R equations a).listed.length
        (events R equations a).listed.label).1 :=
  model.valuationsRepresentableByCones model.toEventModel.contextCones a

/-- The object classifying valuations of a classifier object. -/
noncomputable abbrev classifyingObject (a : Classifier R equations) : D :=
  (model.toEventModel.contextData a.base (events R equations a).listed.length
    (events R equations a).listed.label).1

/-- **The classifying functor of a model.** A classifier object goes to the
object of its valuations; an arrow acts on generalized elements by evaluating
its firing trees. -/
noncomputable def classifyingFunctor : Classifier R equations ⥤ D :=
  Mettapedia.CategoryTheory.RepresentableLift.lift model.valuationFunctor
    model.classifyingObject model.valuationsRepresentableBy

/-- Generalized elements of the classifying functor's values are valuations,
and arrows act on them by transport. -/
theorem classifyingFunctor_homEquiv {a b : Classifier R equations} (arrow : a ⟶ b) {Z : D}
    (point : Z ⟶ model.classifyingObject a) :
    (model.valuationsRepresentableBy b).homEquiv (point ≫ model.classifyingFunctor.map arrow) =
      ((model.valuationsRepresentableBy a).homEquiv point).transport arrow :=
  Mettapedia.CategoryTheory.RepresentableLift.homEquiv_map model.valuationFunctor
    model.classifyingObject model.valuationsRepresentableBy arrow point

/-- **On event-free objects the classifying functor is the program
classifier of the model.** -/
theorem programSection_classifyingFunctor :
    programSection R equations ⋙ model.classifyingFunctor = model.programFunctor := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) (fun X Y assignment => heq_of_eq ?_)
  change model.classifyingFunctor.map ((programSection R equations).map assignment) =
    model.programFunctor.map assignment
  apply (model.valuationsRepresentableBy ((programSection R equations).obj Y)).homEquiv.injective
  have acted := model.classifyingFunctor_homEquiv ((programSection R equations).map assignment)
    (𝟙 (model.classifyingObject ((programSection R equations).obj X)))
  refine (congrArg (model.valuationsRepresentableBy ((programSection R equations).obj Y)).homEquiv
    (Category.id_comp _).symm).trans (acted.trans ?_)
  apply ClassifierTarget.Valuation.ext'
  · change (𝟙 _ ≫ 𝟙 _) ≫ model.programFunctor.map assignment = model.programFunctor.map assignment ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · intro position
    exact Fin.elim0 position

/-- The projection of a classifying object to the program object. -/
noncomputable abbrev programProjection (a : Classifier R equations) :
    model.classifyingObject a ⟶ model.programModel.family a.base.as.arities :=
  (model.toEventModel.contextData a.base _ _).2

/-- The classifying functor acts on program objects as the program
classifier. -/
theorem map_programProjection {a b : Classifier R equations} (arrow : a ⟶ b) :
    model.classifyingFunctor.map arrow ≫ model.programProjection b =
      model.programProjection a ≫ model.programFunctor.map arrow.base := by
  have acted := congrArg ClassifierTarget.Valuation.point
    (model.classifyingFunctor_homEquiv arrow (𝟙 (model.classifyingObject a)))
  change (𝟙 _ ≫ model.classifyingFunctor.map arrow) ≫ model.programProjection b =
    (𝟙 _ ≫ model.programProjection a) ≫ model.programFunctor.map arrow.base at acted
  simpa only [Category.id_comp] using acted

/-- The classifying functor acts on events by evaluating the arrow's firing
trees at the generic valuation. -/
theorem map_eventProjection {a b : Classifier R equations} (arrow : a ⟶ b)
    (position : Fin (events R equations b).listed.length) :
    HEq (model.classifyingFunctor.map arrow ≫ model.toEventModel.eventProjection b.base _ _ position)
      (((model.valuationsRepresentableBy a).homEquiv (𝟙 (model.classifyingObject a))).evaluate _
        (atSlot R _ arrow.fiber position)).1 := by
  have acted := model.classifyingFunctor_homEquiv arrow (𝟙 (model.classifyingObject a))
  have eventsEq := congr_arg_heq (fun value : model.StageValuation (model.classifyingObject a) b =>
    (value.event position).1) acted
  refine HEq.trans ?_ (eventsEq.trans ?_)
  · exact heq_of_eq (congrArg (· ≫ model.toEventModel.eventProjection b.base _ _ position)
      (Category.id_comp _).symm)
  · refine model.objects.stageEvent_val_heq ?_ (ClassifierTarget.Valuation.transport_event _ arrow position)
    exact congrArg (fun p => mapJudgment p ((events R equations b).listed.label position))
      ((model.stageTarget _).program_move arrow.base _)

/-- The generic valuation of a classifying object. -/
noncomputable abbrev genericValuation (a : Classifier R equations) :
    model.StageValuation (model.classifyingObject a) a :=
  (model.valuationsRepresentableBy a).homEquiv (𝟙 (model.classifyingObject a))

/-- **The event-variable projection goes to the pullback projection.** -/
theorem map_projection (a : Classifier R equations) (j : Judgment (modelAt equations a.base)) :
    model.classifyingFunctor.map (projection R equations a j) =
      model.toEventModel.extendBase a.base
        (model.toEventModel.contextData a.base _ (events R equations a).listed.label) j := by
  apply (model.toEventModel.contextCones a.base).hom_ext _ (events R equations a).listed.label
  · refine (model.map_programProjection (projection R equations a j)).trans ?_
    change _ ≫ model.programFunctor.map (𝟙 a.base) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  · intro position
    refine eq_of_heq ((model.map_eventProjection (projection R equations a j) position).trans ?_)
    have judgmentEq : mapJudgment (modelMap equations (𝟙 a.base))
        ((events R equations a).listed.label position) =
          (events R equations a).listed.label position :=
      (congrArg (fun h => mapJudgment h ((events R equations a).listed.label position))
        (modelMap_id equations a.base)).trans
        (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)
    have slotEq : HEq (atSlot R _ (projection R equations a j).fiber position)
        (IntrinsicScopedLocalActedFibres.leaf R ((events R equations a).cons R _ j)
          position.succ) :=
      (atSlot_inclusion R equations a.base
        (IntrinsicScopedLocalActedFibres.weaken R j (events R equations a)) position).trans
        (heq_of_eq (atSlot_weaken R j (events R equations a) position))
    refine (model.objects.stageEvent_val_heq ?_ ((model.genericValuation (object R equations a.base ((events R equations a).cons R _ j))).evaluate_heq judgmentEq
      slotEq)).trans ?_
    · exact congrArg (mapJudgment _) judgmentEq
    refine heq_of_eq ((congrArg Subtype.val
      ((model.genericValuation (object R equations a.base ((events R equations a).cons R _ j))).evaluate_leaf position.succ)).trans ?_)
    exact Category.id_comp _

/-- **Reindexing keeps the new variable's event.** -/
theorem map_reindex_first {a b : Classifier R equations} (f : b ⟶ a)
    (j : Judgment (modelAt equations a.base)) :
    model.classifyingFunctor.map (reindex R equations f j) ≫
        model.toEventModel.eventProjection a.base _ (Fin.cons j (events R equations a).listed.label) 0 =
      model.toEventModel.eventProjection b.base _
        (Fin.cons (mapJudgment (modelMap equations f.base) j) (events R equations b).listed.label) 0 := by
  refine eq_of_heq ((model.map_eventProjection (reindex R equations f j)
    (first R j (events R equations a))).trans ?_)
  refine (model.objects.stageEvent_val_heq rfl (heq_of_eq (congrArg
    ((model.genericValuation (object R equations b.base ((events R equations b).cons R _
      (mapJudgment (modelMap equations f.base) j)))).evaluate _)
    (atSlot_reindexEvents_first R equations f j)))).trans ?_
  refine heq_of_eq ((congrArg Subtype.val
    ((model.genericValuation (object R equations b.base ((events R equations b).cons R _
      (mapJudgment (modelMap equations f.base) j)))).evaluate_leaf _)).trans ?_)
  exact Category.id_comp _

omit [CartesianMonoidalCategory D] [HasPullbacks D] in
private theorem isPullback_of_eq {P X Y W : D} {fst fst' : P ⟶ X} {snd snd' : P ⟶ Y}
    {f : X ⟶ W} {g g' : Y ⟶ W} (sameFst : fst = fst') (sameSnd : snd = snd') (sameG : g = g')
    (pullbackSquare : IsPullback fst' snd' f g') : IsPullback fst snd f g := by
  subst sameFst sameSnd sameG
  exact pullbackSquare

/-- **The classifying functor preserves the pullbacks of event-variable
projections along every arrow.** -/
theorem classifyingFunctor_isPullback_reindex {a b : Classifier R equations} (f : b ⟶ a)
    (j : Judgment (modelAt equations a.base)) :
    IsPullback (model.classifyingFunctor.map (reindex R equations f j))
      (model.classifyingFunctor.map
        (projection R equations b (mapJudgment (modelMap equations f.base) j)))
      (model.classifyingFunctor.map (projection R equations a j))
      (model.classifyingFunctor.map f) := by
  have endpoints : model.classifyingFunctor.map f ≫ model.programProjection a ≫
      model.toEventModel.judgmentEndpoints a.base j =
        model.programProjection b ≫
          model.toEventModel.judgmentEndpoints b.base (mapJudgment (modelMap equations f.base) j) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ model.toEventModel.judgmentEndpoints a.base j) (model.map_programProjection f)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (model.programProjection b ≫ ·) (model.toEventModel.judgmentEndpoints_map f.base j))))
  refine IsPullback.of_right
    (h₁₂ := model.toEventModel.eventProjection a.base _ (Fin.cons j (events R equations a).listed.label) 0)
    (h₂₂ := model.programProjection a ≫ model.toEventModel.judgmentEndpoints a.base j)
    (v₁₃ := model.toEventModel.eventEndpoints j.1 j.2.1) ?_ ?_ ?_
  · exact isPullback_of_eq (model.map_reindex_first f j) (model.map_projection b _) endpoints
      (IsPullback.of_hasPullback _ _)
  · exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg model.classifyingFunctor.map (reindex_comm R equations f j)).trans
        (CategoryTheory.Functor.map_comp _ _ _))
  · exact isPullback_of_eq rfl (model.map_projection a j) rfl (IsPullback.of_hasPullback _ _)

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
