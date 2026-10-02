import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedStructuredFunctors
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericFactor
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# The model of a structure-preserving functor

A structure-preserving functor out of the classifier gives a model: its
binding model and event objects are its values on event-free and generic
event objects. At a stage, a generalized event substituted along an
environment is the functor's value at the generic substitution, applied to the
point of the event and environment; a rule applied to generalized premises is
the functor's value at the rule's generic occurrence, applied to the point of
the occurrence and premises. The value of the functor at the arrow of any
firing tree is the fold of the tree with these actions, and the laws of a
model follow from the laws of the free model of trees.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (ActionOn)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel (substJudgment_congr)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment mapJudgment_substJudgment heq_transport)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree Holes)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace StructuredFunctor

variable (F : StructuredFunctor R equations (D := D))

/-- The program point of a value of the functor. -/
abbrev programPoint (a : Classifier R equations) :
    F.carrier.obj a ⟶ F.programModel.family a.base.as.arities :=
  F.carrier.map (toProgram R equations a) ≫ (F.programIso a.base).hom

/-- The interpretation of equation classes at a generalized element of a
program object. -/
abbrev pointProgram {X : Base equations} {Z : D} (x : Z ⟶ F.programModel.family X.as.arities) :=
  F.programModel.pointProgram _ F.programInterpretation.satisfies X.as x

/-- The value of the functor at the arrow of a tree has the endpoints its
judgment names. -/
theorem rep_endpoints {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : IntrinsicScopedLocalActedFree.Tree R _ (seeds R _ (events R equations a)) J) :
    F.carrier.map (rep R equations J tree) ≫ F.eventModel.eventEndpoints J.1 J.2.1 =
      F.programPoint a ≫ F.eventModel.judgmentEndpoints a.base J := by
  have toProgramSquare : F.carrier.map (rep R equations J tree) ≫
      F.carrier.map (toProgram R equations (eventObject R equations J.1 J.2.1)) =
        F.carrier.map (toProgram R equations a) ≫
          F.carrier.map ((programSection R equations).map (judgmentBase equations J)) :=
    (F.carrier.map_comp _ _).symm.trans
      ((congrArg F.carrier.map (rep_toProgram R equations J tree)).trans (F.carrier.map_comp _ _))
  have natural := F.programIso_natural (judgmentBase equations J)
  have endpoints := F.eventModel.programFunctor_judgmentBase J
  refine (congrArg (F.carrier.map (rep R equations J tree) ≫ ·)
    (F.eventEndpoints_eventModel J.1 J.2.1)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((F.programIso (pairBase equations J.1 J.2.1)).hom ≫
      F.programModel.pairComponents J.1 J.2.1)) toProgramSquare).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (F.carrier.map (toProgram R equations a) ≫ ·)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ F.programModel.pairComponents J.1 J.2.1) natural).trans
              ((Category.assoc _ _ _).trans
                (congrArg ((F.programIso a.base).hom ≫ ·) endpoints))))).trans
          (Category.assoc _ _ _).symm)))

/-- **The value of the functor at the arrow of a tree** is a generalized event
over the judgment read at the point. -/
def treeEvent {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : IntrinsicScopedLocalActedFree.Tree R _ (seeds R _ (events R equations a)) J) {Z : D}
    (g : Z ⟶ F.carrier.obj a) :
    F.eventModel.objects.StageEvent Z (mapJudgment (F.pointProgram (g ≫ F.programPoint a)) J) :=
  F.eventModel.pointEvent a.base (g ≫ F.programPoint a) J (g ≫ F.carrier.map (rep R equations J tree))
    ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (F.rep_endpoints J tree)).trans
      (Category.assoc _ _ _).symm))

theorem treeEvent_val {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : IntrinsicScopedLocalActedFree.Tree R _ (seeds R _ (events R equations a)) J) {Z : D}
    (g : Z ⟶ F.carrier.obj a) :
    (F.treeEvent J tree g).1 = g ≫ F.carrier.map (rep R equations J tree) :=
  rfl

/-! ## Maps into values at finite contexts -/

section Lifts

variable {X : Base equations} {Z : D}

/-- **The value at a listed variable of a lift is the lifted event.** -/
theorem treeEvent_leaf_lift {n : ℕ} {label : Fin n → Judgment (modelAt equations X)}
    (x : Z ⟶ F.programModel.family X.as.arities) (events : F.eventModel.PointEvents X n label x)
    (position : Fin n) :
    HEq (F.treeEvent (a := object R equations X ⟨⟨n, label⟩⟩) (label position)
        (leaf R ⟨⟨n, label⟩⟩ position) ((F.contextCones X).lift n label x events).1)
      (events position) :=
  F.eventModel.objects.stageEvent_heq
    (congrArg (fun y => mapJudgment (F.pointProgram y) (label position))
      ((F.contextCones X).lift n label x events).2)
    (heq_of_eq ((F.contextCones X).lift_event n label x events position))

/-- **A map into a value at a finite context is the lift of a point and
events** as soon as it has that point and those events. -/
theorem eq_lift {n : ℕ} {label : Fin n → Judgment (modelAt equations X)}
    (x : Z ⟶ F.programModel.family X.as.arities) (events : F.eventModel.PointEvents X n label x)
    (g : Z ⟶ F.carrier.obj (object R equations X ⟨⟨n, label⟩⟩))
    (point : g ≫ F.programPoint _ = x)
    (premises : ∀ position, HEq (g ≫ F.carrier.map (rep R equations
        (a := object R equations X ⟨⟨n, label⟩⟩) (label position) (leaf R ⟨⟨n, label⟩⟩ position)))
      (events position).1) :
    g = ((F.contextCones X).lift n label x events).1 :=
  (F.contextCones X).hom_ext n label (point.trans ((F.contextCones X).lift n label x events).2.symm)
    (fun position => eq_of_heq ((premises position).trans
      (heq_of_eq ((F.contextCones X).lift_event n label x events position)).symm))

variable (J : Judgment (modelAt equations X)) (x : Z ⟶ F.programModel.family X.as.arities)

/-- A generalized event as the events of a one-variable context. -/
def singleEvents (e : F.eventModel.objects.StageEvent Z (mapJudgment (F.pointProgram x) J)) :
    F.eventModel.PointEvents X 1 (Fin.cons J Fin.elim0) x :=
  fun position => Fin.cases (motive := fun position => F.eventModel.objects.StageEvent Z
      (mapJudgment (F.pointProgram x)
        (Fin.cons (α := fun _ => Judgment (modelAt equations X)) J Fin.elim0 position)))
    e (fun i => i.elim0) position

/-- The map into the value at a one-variable context given by a point and an
event. -/
def singleLift (e : F.eventModel.objects.StageEvent Z (mapJudgment (F.pointProgram x) J)) :
    Z ⟶ F.carrier.obj (object R equations X ((Context.empty R _).cons R _ J)) :=
  ((F.contextCones X).lift 1 _ x (F.singleEvents J x e)).1

theorem singleLift_point
    (e : F.eventModel.objects.StageEvent Z (mapJudgment (F.pointProgram x) J)) :
    F.singleLift J x e ≫ F.programPoint _ = x :=
  ((F.contextCones X).lift 1 _ x (F.singleEvents J x e)).2

/-- The value at the variable of a one-variable lift is its event. -/
theorem treeEvent_singleLift
    (e : F.eventModel.objects.StageEvent Z (mapJudgment (F.pointProgram x) J)) :
    HEq (F.treeEvent J (leaf R ((Context.empty R _).cons R _ J) (first R J (Context.empty R _)))
      (F.singleLift J x e)) e :=
  F.treeEvent_leaf_lift x (F.singleEvents J x e) 0

theorem eq_singleLift (e : F.eventModel.objects.StageEvent Z (mapJudgment (F.pointProgram x) J))
    (g : Z ⟶ F.carrier.obj (object R equations X ((Context.empty R _).cons R _ J)))
    (point : g ≫ F.programPoint _ = x)
    (event : HEq (g ≫ F.carrier.map (rep R equations
        (a := object R equations X ((Context.empty R _).cons R _ J)) J
        (leaf R ((Context.empty R _).cons R _ J) (first R J (Context.empty R _))))) e.1) :
    g = F.singleLift J x e :=
  F.eq_lift x (F.singleEvents J x e) g point (fun position => by
    refine Fin.cases ?_ (fun i => i.elim0) position
    exact event)

variable (I : Instance R (modelAt equations X))

/-- Generalized premises of the occurrence an instance reads as, as the events
of the instance's premises. -/
def premiseEvents (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position)) :
    F.eventModel.PointEvents X _ (childJudgment R _ I) x :=
  fun position => cast (congrArg (F.eventModel.objects.StageEvent Z)
    (mapInstance_child R (F.pointProgram x) I position)) (children position)

/-- The map into the value at the premises of an instance given by a point
and generalized premises. -/
def premiseLift (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position)) :
    Z ⟶ F.carrier.obj (object R equations X ⟨⟨_, childJudgment R _ I⟩⟩) :=
  ((F.contextCones X).lift _ _ x (F.premiseEvents x I children)).1

theorem premiseLift_point (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position)) :
    F.premiseLift x I children ≫ F.programPoint _ = x :=
  ((F.contextCones X).lift _ _ x (F.premiseEvents x I children)).2

/-- The value at a premise of a lift is the given premise. -/
theorem treeEvent_premiseLift (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position))
    (position : Fin (R.get I.index).2.premises.length) :
    HEq (F.treeEvent (childJudgment R _ I position) (leaf R ⟨⟨_, childJudgment R _ I⟩⟩ position)
      (F.premiseLift x I children)) (children position) :=
  (F.treeEvent_leaf_lift x (F.premiseEvents x I children) position).trans (cast_heq _ _)

theorem eq_premiseLift (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position))
    (g : Z ⟶ F.carrier.obj (object R equations X ⟨⟨_, childJudgment R _ I⟩⟩))
    (point : g ≫ F.programPoint _ = x)
    (premises : ∀ position, HEq (g ≫ F.carrier.map (rep R equations
        (a := object R equations X ⟨⟨_, childJudgment R _ I⟩⟩) (childJudgment R _ I position)
        (leaf R ⟨⟨_, childJudgment R _ I⟩⟩ position))) (children position).1) :
    g = F.premiseLift x I children :=
  F.eq_lift x _ g point (fun position => (premises position).trans
    (F.eventModel.objects.stageEvent_val_heq (mapInstance_child R (F.pointProgram x) I position)
      (cast_heq _ _).symm))

end Lifts

/-! ## The substitution action -/

/-- The map into the value at the generic substitution. -/
def substitutionLift {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ) :
    Z ⟶ F.carrier.obj (substitutionObject R equations j.1 Δ j.2.1) :=
  F.singleLift (substitutionJudgment equations j.1 Δ j.2.1)
    (F.programModel.substitutionPoint j.2.2.1 j.2.2.2 σ)
    (cast (congrArg (F.eventModel.objects.StageEvent Z)
      (F.programModel.mapJudgment_substitutionPoint equations F.programInterpretation.satisfies
        j.2.2.1 j.2.2.2 σ).symm) e)

theorem substitutionLift_point {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ) :
    F.substitutionLift j e σ ≫ F.programPoint _ = F.programModel.substitutionPoint j.2.2.1 j.2.2.2 σ :=
  F.singleLift_point _ _ _

/-- **A map into the value at the generic substitution is the lift of an
event and an environment** as soon as it has their point and their event. -/
theorem eq_substitutionLift {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ)
    (x : Z ⟶ F.carrier.obj (substitutionObject R equations j.1 Δ j.2.1))
    (point : x ≫ F.programPoint _ = F.programModel.substitutionPoint j.2.2.1 j.2.2.2 σ)
    (event : HEq (x ≫ F.carrier.map (rep R equations
        (a := substitutionObject R equations j.1 Δ j.2.1) (substitutionJudgment equations j.1 Δ j.2.1)
        (leaf R ((Context.empty R _).cons R _ (substitutionJudgment equations j.1 Δ j.2.1))
          (first R _ (Context.empty R _))))) e.1) :
    x = F.substitutionLift j e σ :=
  F.eq_singleLift _ _ _ x point (event.trans (F.eventModel.objects.stageEvent_val_heq
    (F.programModel.mapJudgment_substitutionPoint equations F.programInterpretation.satisfies
      j.2.2.1 j.2.2.2 σ).symm (cast_heq _ e).symm))

/-- The substituted generic judgment read at the point of an event and an
environment is the substituted judgment. -/
theorem substitutionLift_judgment {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ) :
    mapJudgment (F.pointProgram (F.substitutionLift j e σ ≫ F.programPoint _))
        (substJudgment (substitutionJudgment equations j.1 Δ j.2.1)
          (substitutionEnv equations j.1 Δ j.2.1)) =
      substJudgment j σ := by
  rw [F.substitutionLift_point]
  refine (mapJudgment_substJudgment _ _ _).trans ?_
  have environment : (fun t w => (F.pointProgram
      (F.programModel.substitutionPoint j.2.2.1 j.2.2.2 σ)).raw.map
        (substitutionEnv equations j.1 Δ j.2.1 t w)) = σ := by
    funext t w
    exact F.programModel.substitutionPoint_env equations F.programInterpretation.satisfies
      j.2.2.1 j.2.2.2 σ w
  exact substJudgment_congr (F.programModel.mapJudgment_substitutionPoint equations
    F.programInterpretation.satisfies j.2.2.1 j.2.2.2 σ) (heq_of_eq environment)

/-- **The substitution action of the functor at a stage.** -/
def act (Z : D) : ActionOn (F.programModel.stage Z) (F.eventModel.objects.StageEvent Z) :=
  fun j e _ σ _ same =>
    cast (congrArg (F.eventModel.objects.StageEvent Z)
        ((F.substitutionLift_judgment j e σ).trans same))
      (F.treeEvent _ (substitutionTree R equations j.1 _ j.2.1) (F.substitutionLift j e σ))

/-- The substitution action is the value at the generic substitution. -/
theorem act_val_heq {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ)
    (target : Judgment (F.programModel.stage Z)) (same : substJudgment j σ = target) :
    HEq (F.act Z j e σ target same).1
      (F.treeEvent _ (substitutionTree R equations j.1 Δ j.2.1) (F.substitutionLift j e σ)).1 :=
  F.eventModel.objects.stageEvent_val_heq ((F.substitutionLift_judgment j e σ).trans same).symm
    (cast_heq _ _)

/-- The substitution action agrees on equal inputs. -/
theorem act_heq {Z : D} {j j' : Judgment (F.programModel.stage Z)} (same : j = j')
    {e : F.eventModel.objects.StageEvent Z j} {e' : F.eventModel.objects.StageEvent Z j'}
    (sameEvent : HEq e e') {Δ : Ctx S}
    {σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ}
    {σ' : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j'.1 Δ}
    (sameEnv : HEq σ σ') {target target' : Judgment (F.programModel.stage Z)}
    (sameTarget : target = target') (h : substJudgment j σ = target)
    (h' : substJudgment j' σ' = target') :
    HEq (F.act Z j e σ target h) (F.act Z j' e' σ' target' h') := by
  subst same
  cases sameEvent
  cases sameEnv
  subst sameTarget
  rfl

/-! ## The rule actions -/

/-- The premises of an occurrence, at the premises of the generic occurrence
read at the occurrence's point. -/
def rulePremises {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    F.eventModel.objects.StageEvent Z (childJudgment R _ (mapInstance R
      (F.pointProgram (F.programModel.rulePoint R occurrence))
      (ruleInstance R equations occurrence.index occurrence.ambient)) position) :=
  cast (congrArg (F.eventModel.objects.StageEvent Z)
    (childJudgment_congr R (F.programModel.mapInstance_rulePoint R equations
      F.programInterpretation.satisfies occurrence).symm position position HEq.rfl))
    (children position)

/-- The map into the value at the generic occurrence. -/
def ruleLift {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    Z ⟶ F.carrier.obj (ruleObject R equations occurrence.index occurrence.ambient) :=
  F.premiseLift (F.programModel.rulePoint R occurrence)
    (ruleInstance R equations occurrence.index occurrence.ambient) (F.rulePremises occurrence children)

theorem ruleLift_point {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    F.ruleLift occurrence children ≫ F.programPoint _ = F.programModel.rulePoint R occurrence :=
  F.premiseLift_point _ _ _

/-- **A map into the value at the generic occurrence of a rule is the lift of
an occurrence and premises** as soon as it has their point and their events. -/
theorem eq_ruleLift {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position))
    (x : Z ⟶ F.carrier.obj (ruleObject R equations occurrence.index occurrence.ambient))
    (point : x ≫ F.programPoint _ = F.programModel.rulePoint R occurrence)
    (premises : ∀ position, HEq (x ≫ F.carrier.map (rep R equations
        (a := ruleObject R equations occurrence.index occurrence.ambient)
        (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position)
        (leaf R (events R equations (ruleObject R equations occurrence.index occurrence.ambient))
          position))) (children position).1) :
    x = F.ruleLift occurrence children :=
  F.eq_premiseLift _ _ _ x point (fun position => (premises position).trans
    (F.eventModel.objects.stageEvent_val_heq
      (childJudgment_congr R (F.programModel.mapInstance_rulePoint R equations
        F.programInterpretation.satisfies occurrence).symm position position HEq.rfl)
      (cast_heq _ _).symm))

theorem ruleLift_judgment {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    mapJudgment (F.pointProgram (F.ruleLift occurrence children ≫ F.programPoint _))
        (conclusionJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient)) =
      conclusionJudgment R _ occurrence := by
  rw [F.ruleLift_point]
  exact (mapInstance_conclusion R _ _).symm.trans
    (congrArg (conclusionJudgment R _) (F.programModel.mapInstance_rulePoint R equations
      F.programInterpretation.satisfies occurrence))

/-- **The rule actions of the functor at a stage.** -/
def rulesAlgebra (Z : D) :
    (rules R (F.programModel.stage Z)).Algebra
      (fun _ j => F.eventModel.objects.StageEvent Z j) where
  act _ _ layer :=
    cast (congrArg (F.eventModel.objects.StageEvent Z)
        ((F.ruleLift_judgment layer.1.1 layer.2).trans layer.1.2))
      (F.treeEvent _ (ruleTree R equations layer.1.1.index layer.1.1.ambient)
        (F.ruleLift layer.1.1 layer.2))

/-- The rule actions are the values at the generic occurrences. -/
theorem rulesAlgebra_val_heq {Z : D} (j : Judgment (F.programModel.stage Z))
    (layer : (rules R (F.programModel.stage Z)).Extension
      (fun _ j => F.eventModel.objects.StageEvent Z j) () j) :
    HEq ((F.rulesAlgebra Z).act () j layer).1
      (F.treeEvent _ (ruleTree R equations layer.1.1.index layer.1.1.ambient)
        (F.ruleLift layer.1.1 layer.2)).1 :=
  F.eventModel.objects.stageEvent_val_heq
    ((F.ruleLift_judgment layer.1.1 layer.2).trans layer.1.2).symm (cast_heq _ _)

/-! ## The fold of trees is the value at their arrows -/

/-- The program point of a value moves along an arrow by the program
classifier. -/
theorem map_programPoint {a b : Classifier R equations} (w : a ⟶ b) :
    F.carrier.map w ≫ F.programPoint b =
      F.programPoint a ≫ F.eventModel.programFunctor.map w.base := by
  have square := (F.carrier.map_comp _ _).symm.trans
    ((congrArg F.carrier.map (comp_toProgram R equations w)).trans (F.carrier.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (F.programIso b.base).hom) square).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (F.carrier.map (toProgram R equations a) ≫ ·)
          (F.programIso_natural w.base)).trans (Category.assoc _ _ _).symm)))

section Fold

variable {F} {a : Classifier R equations} {Z : D} (g : Z ⟶ F.carrier.obj a)

/-- The interpretation of equation classes at the point of a value. -/
abbrev valuePoint :=
  F.pointProgram (g ≫ F.programPoint a)

/-- The event at a listed variable of a value. -/
def valueEvent (position : Fin (events R equations a).listed.length) :
    F.eventModel.objects.StageEvent Z
      (mapJudgment (valuePoint g) ((events R equations a).listed.label position)) :=
  F.treeEvent _ (leaf R (events R equations a) position) g

/-- The value of a leaf: the event at its variable, substituted along the
environment it records. -/
def leafValue (J : Judgment (modelAt equations a.base))
    (hole : Holes _ (seeds R _ (events R equations a)) J) :
    F.eventModel.objects.StageEvent Z (mapJudgment (valuePoint g) J) :=
  F.act Z (mapJudgment (valuePoint g) (hole.original.asJudgment _))
    (cast (congrArg (fun j => F.eventModel.objects.StageEvent Z (mapJudgment (valuePoint g) j))
      hole.seed.2.down) (valueEvent g hole.seed.1))
    (fun t v => (valuePoint g).raw.map (hole.arrow.environment t v))
    (mapJudgment (valuePoint g) J)
    ((mapJudgment_substJudgment _ _ _).symm.trans
      (congrArg (mapJudgment (valuePoint g)) (Map.as_substitution _ hole.arrow)))

/-- **The fold of the trees over a value**, with the functor's substitution
and rule actions. -/
def foldValue : ∀ J : Judgment (modelAt equations a.base),
    Tree R _ (seeds R _ (events R equations a)) J →
      F.eventModel.objects.StageEvent Z (mapJudgment (valuePoint g) J) :=
  Mettapedia.TypeTheory.IndexedPolynomial.Free.fold (rules R _)
    (fun _ J hole => leafValue g J hole)
    (IndexedRuleAlgebraPullback.pullback (rulesMap R (valuePoint g)) (F.rulesAlgebra Z)) ()

/-- Values at the arrows of equal trees agree. -/
theorem treeEvent_heq {J J' : Judgment (modelAt equations a.base)} (same : J = J')
    {tree : Tree R _ (seeds R _ (events R equations a)) J}
    {tree' : Tree R _ (seeds R _ (events R equations a)) J'} (sameTree : HEq tree tree') :
    HEq (F.treeEvent J tree g) (F.treeEvent J' tree' g) := by
  subst same
  cases sameTree
  rfl

/-- The arrow of a tree into the generic substitution. -/
abbrev treeArrow (j : Judgment (modelAt equations a.base)) {Δ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S
      (modelAt equations a.base).substitution.Carrier j.1 Δ)
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    a ⟶ substitutionObject R equations j.1 Δ j.2.1 :=
  singleArrow R equations (substitutionBaseOf equations j environment)
    (substitutionJudgment equations j.1 Δ j.2.1)
    (cast (congrArg (Tree R _ (seeds R _ (events R equations a)))
      (mapJudgment_substitutionBaseOf equations j environment).symm) tree)

/-- **The value at the arrow of a tree into the generic substitution is the
lift of the value at the tree and the environment.** -/
theorem treeArrow_lift (j : Judgment (modelAt equations a.base)) {Δ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S
      (modelAt equations a.base).substitution.Carrier j.1 Δ)
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    g ≫ F.carrier.map (treeArrow j environment tree) =
      F.substitutionLift (mapJudgment (valuePoint g) j) (F.treeEvent j tree g)
        (fun t v => (valuePoint g).raw.map (environment t v)) := by
  have readLabel : mapJudgment (modelMap equations (substitutionBaseOf equations j environment))
      (substitutionJudgment equations j.1 Δ j.2.1) = j :=
    mapJudgment_substitutionBaseOf equations j environment
  refine F.eq_substitutionLift (mapJudgment (valuePoint g) j) (F.treeEvent j tree g)
    (fun t v => (valuePoint g).raw.map (environment t v))
    (g ≫ F.carrier.map (treeArrow j environment tree)) ?_ ?_
  · have natural := F.map_programPoint (treeArrow j environment tree)
    have points := F.programModel.comp_substitutionBaseOf equations F.programInterpretation.satisfies
      (g ≫ F.programPoint a) j environment
    exact (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) natural).trans
      ((Category.assoc _ _ _).symm.trans points))
  · have reading := singleArrow_comp_rep_leaf R equations
      (substitutionBaseOf equations j environment) (substitutionJudgment equations j.1 Δ j.2.1)
      (cast (congrArg (Tree R _ (seeds R _ (events R equations a))) readLabel.symm) tree)
    have arrows := rep_heq R equations (X := a.base) (Γ := events R equations a)
      (Γ' := events R equations a) rfl readLabel
      (cast_heq (congrArg (Tree R _ (seeds R _ (events R equations a))) readLabel.symm) tree)
    have mapped := Mettapedia.CategoryTheory.Functor.map_heq F.carrier rfl
      (congrArg (fun j : Judgment (modelAt equations a.base) =>
        eventObject R equations j.1 j.2.1) readLabel) arrows
    have composed := Mettapedia.CategoryTheory.comp_heq g
      (congrArg (fun j : Judgment (modelAt equations a.base) =>
        F.carrier.obj (eventObject R equations j.1 j.2.1)) readLabel) mapped
    exact HEq.trans (heq_of_eq ((Category.assoc _ _ _).trans (congrArg (g ≫ ·)
      ((F.carrier.map_comp _ _).symm.trans (congrArg F.carrier.map reading))))) composed

/-- **The value at a substituted tree is the substitution action on the value
at the tree.** -/
theorem treeEvent_substitute (j : Judgment (modelAt equations a.base)) {Δ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S
      (modelAt equations a.base).substitution.Carrier j.1 Δ)
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    F.treeEvent (substJudgment j environment)
        (IntrinsicScopedLocalActedFree.substitute R _ _ j tree environment _ rfl) g =
      F.act Z (mapJudgment (valuePoint g) j) (F.treeEvent j tree g)
        (fun t v => (valuePoint g).raw.map (environment t v))
        (mapJudgment (valuePoint g) (substJudgment j environment))
        (mapJudgment_substJudgment _ _ _).symm := by
  apply Subtype.ext
  refine eq_of_heq (HEq.trans ?_ (F.act_val_heq _ _ _ _ _).symm)
  have factored := singleArrow_comp_substitutionRep R equations j environment tree
  refine heq_of_eq ((congrArg (fun x => g ≫ F.carrier.map x) factored.symm).trans ?_)
  refine (congrArg (g ≫ ·) (F.carrier.map_comp _ _)).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (treeArrow_lift g j environment tree))

/-- **At a leaf, the value at the tree's arrow is the substituted event.** -/
theorem treeEvent_pure (J : Judgment (modelAt equations a.base))
    (hole : Holes _ (seeds R _ (events R equations a)) J) :
    F.treeEvent J (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R _) hole) g =
      leafValue g J hole := by
  have sameLabel : (events R equations a).listed.label hole.seed.1 = hole.original.asJudgment _ :=
    hole.seed.2.down
  let variable_ : Tree R _ (seeds R _ (events R equations a)) (hole.original.asJudgment _) :=
    Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R _)
      (exactHole R _ _ ⟨hole.seed.1, ⟨sameLabel⟩⟩)
  have substituted := (pure_heq_substitute R _ J hole).trans
    (IntrinsicScopedLocalActedFree.substitute_congr R _ _ variable_ rfl
      (Map.as_substitution _ hole.arrow).symm _ rfl)
  have first := treeEvent_heq g (Map.as_substitution _ hole.arrow).symm substituted
  have second := treeEvent_substitute g _ hole.arrow.environment variable_
  have atVariable : HEq (F.treeEvent _ variable_ g)
      (cast (congrArg (fun j => F.eventModel.objects.StageEvent Z (mapJudgment (valuePoint g) j))
        sameLabel) (valueEvent g hole.seed.1)) :=
    (treeEvent_heq g sameLabel.symm (pure_heq R sameLabel.symm
      (exactHole_heq R _ hole.seed.1 sameLabel rfl))).trans (cast_heq _ _).symm
  have third := F.act_heq rfl atVariable HEq.rfl (congrArg (mapJudgment (valuePoint g))
    (Map.as_substitution _ hole.arrow))
    (mapJudgment_substJudgment _ _ _).symm
    ((mapJudgment_substJudgment _ _ _).symm.trans
      (congrArg (mapJudgment (valuePoint g)) (Map.as_substitution _ hole.arrow)))
  exact eq_of_heq ((first.trans (heq_of_eq second)).trans third)

/-- **The value at the arrow of an occurrence into the rule's generic
occurrence is the lift of the occurrence and the values at the premises.** -/
theorem ruleArrow_lift (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position)) :
    g ≫ F.carrier.map (ruleArrow R equations occurrence children) =
      F.ruleLift (mapInstance R (valuePoint g) occurrence)
        (fun position => (mapInstance_child R (valuePoint g) occurrence position).symm ▸
          F.treeEvent _ (children position) g) := by
  refine F.eq_ruleLift (mapInstance R (valuePoint g) occurrence)
    (fun position => (mapInstance_child R (valuePoint g) occurrence position).symm ▸
      F.treeEvent _ (children position) g)
    (g ≫ F.carrier.map (ruleArrow R equations occurrence children)) ?_ ?_
  · have natural := F.map_programPoint (ruleArrow R equations occurrence children)
    have points := F.programModel.comp_ruleBaseOf R equations F.programInterpretation.satisfies
      (g ≫ F.programPoint a) occurrence
    exact (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) natural).trans
      ((Category.assoc _ _ _).symm.trans points))
  · intro position
    have reading := ruleArrow_comp_rep_leaf R equations occurrence children position
    have mapped := Mettapedia.CategoryTheory.Functor.map_heq F.carrier rfl rfl reading
    have composed := Mettapedia.CategoryTheory.comp_heq g rfl mapped
    have toPremise := F.eventModel.objects.stageEvent_val_heq
      (mapInstance_child R (valuePoint g) occurrence position).symm
      (heq_transport (mapInstance_child R (valuePoint g) occurrence position).symm
        (F.treeEvent _ (children position) g)).symm
    refine HEq.trans (heq_of_eq ((Category.assoc _ _ _).trans
      (congrArg (g ≫ ·) (F.carrier.map_comp _ _).symm))) ?_
    exact composed.trans toPremise

/-- **At a rule node, the value at the tree's arrow is the rule action on the
values at the children.** -/
theorem treeEvent_node {J : Judgment (modelAt equations a.base)} (shape : Shape R _ J)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ shape.1 position)) :
    F.treeEvent J (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R _) shape children) g =
      (F.rulesAlgebra Z).act () (mapJudgment (valuePoint g) J)
        ⟨mapShape R (valuePoint g) shape, fun position =>
          ((mapInstance_child R (valuePoint g) shape.1 position).symm ▸
            F.treeEvent _ (children position) g :
              F.eventModel.objects.StageEvent Z
                (childJudgment R _ (mapInstance R (valuePoint g) shape.1) position))⟩ := by
  obtain ⟨occurrence, rfl⟩ := shape
  apply Subtype.ext
  have action := F.rulesAlgebra_val_heq
    (mapJudgment (valuePoint g) (conclusionJudgment R _ occurrence))
    ⟨mapShape R (valuePoint g) ⟨occurrence, rfl⟩, fun position =>
      ((mapInstance_child R (valuePoint g) occurrence position).symm ▸
        F.treeEvent _ (children position) g :
          F.eventModel.objects.StageEvent Z
            (childJudgment R _ (mapInstance R (valuePoint g) occurrence) position))⟩
  have factored := eq_of_heq (ruleArrow_comp_ruleRep R equations occurrence children)
  have lifted := ruleArrow_lift g occurrence children
  have valueEq : (F.treeEvent _ (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R _)
      ⟨occurrence, rfl⟩ children) g).1 =
        (F.treeEvent _ (ruleTree R equations occurrence.index occurrence.ambient)
          (F.ruleLift (mapInstance R (valuePoint g) occurrence) (fun position =>
            (mapInstance_child R (valuePoint g) occurrence position).symm ▸
              F.treeEvent _ (children position) g))).1 :=
    (congrArg (fun x => g ≫ F.carrier.map x) factored.symm).trans
      ((congrArg (g ≫ ·) (F.carrier.map_comp _ _)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) lifted)))
  exact eq_of_heq ((heq_of_eq valueEq).trans action.symm)

/-- **The fold of a tree over a value is the value at the tree's arrow.** -/
theorem foldValue_eq (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    foldValue g J tree = F.treeEvent J tree g :=
  (IntrinsicScopedLocalSubstitutionModel.fold_unique_rulesMap (valuePoint g)
    (holes := fun _ J => Holes _ (seeds R _ (events R equations a)) J) (F.rulesAlgebra Z)
    (leafValue g) (fun J tree => F.treeEvent J tree g) (treeEvent_pure g)
    (fun _ shape children => treeEvent_node g shape children) J tree).symm

end Fold

/-! ## Restaging -/

/-- The substitution action is the value at the generic substitution. -/
theorem act_heq_treeEvent {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ)
    (target : Judgment (F.programModel.stage Z)) (same : substJudgment j σ = target) :
    HEq (F.act Z j e σ target same)
      (F.treeEvent _ (substitutionTree R equations j.1 Δ j.2.1) (F.substitutionLift j e σ)) :=
  cast_heq _ _

/-- The rule actions are the values at the generic occurrences. -/
theorem rulesAlgebra_heq_treeEvent {Z : D} (j : Judgment (F.programModel.stage Z))
    (layer : (rules R (F.programModel.stage Z)).Extension
      (fun _ j => F.eventModel.objects.StageEvent Z j) () j) :
    HEq ((F.rulesAlgebra Z).act () j layer)
      (F.treeEvent _ (ruleTree R equations layer.1.1.index layer.1.1.ambient)
        (F.ruleLift layer.1.1 layer.2)) :=
  cast_heq _ _

/-- **The value at a tree moves along a map of stages by restaging.** -/
theorem treeEvent_comp {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) {Z Z' : D} (k : Z' ⟶ Z)
    (g : Z ⟶ F.carrier.obj a) :
    HEq (F.treeEvent J tree (k ≫ g)) (F.eventModel.objects.restage k (F.treeEvent J tree g)) :=
  F.eventModel.objects.stageEvent_heq
    ((congrArg (fun y => mapJudgment (F.pointProgram y) J) (Category.assoc k g _)).trans
      (congrArg (fun hom => mapJudgment hom J)
        (F.programModel.pointProgram_restage _ F.programInterpretation.satisfies a.base.as k _)))
    (heq_of_eq (Category.assoc _ _ _))

/-- The lift of an event and an environment reads the event at the generic
variable. -/
theorem substitutionLift_event {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ) :
    F.substitutionLift j e σ ≫ F.carrier.map (rep R equations
        (a := substitutionObject R equations j.1 Δ j.2.1) (substitutionJudgment equations j.1 Δ j.2.1)
        (leaf R ((Context.empty R _).cons R _ (substitutionJudgment equations j.1 Δ j.2.1))
          (first R _ (Context.empty R _)))) = e.1 :=
  eq_of_heq (F.eventModel.objects.stageEvent_val_heq
    ((congrArg (fun y => mapJudgment (F.pointProgram y) (substitutionJudgment equations j.1 Δ j.2.1))
      (F.substitutionLift_point j e σ)).trans
      (F.programModel.mapJudgment_substitutionPoint equations F.programInterpretation.satisfies
        j.2.2.1 j.2.2.2 σ))
    ((F.treeEvent_singleLift _ _ _).trans (cast_heq _ e)))

/-- **Lifts of events and environments move along maps of stages.** -/
theorem comp_substitutionLift {Z Z' : D} (k : Z' ⟶ Z) (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ) :
    k ≫ F.substitutionLift j e σ =
      F.substitutionLift (mapJudgment (F.programModel.stageRestage k) j)
        (F.eventModel.objects.restage k e)
        (fun t v => (F.programModel.stageRestage k).raw.map (σ t v)) :=
  F.eq_substitutionLift (mapJudgment (F.programModel.stageRestage k) j)
    (F.eventModel.objects.restage k e) (fun t v => (F.programModel.stageRestage k).raw.map (σ t v))
    (k ≫ F.substitutionLift j e σ)
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (F.substitutionLift_point j e σ)).trans
      (F.programModel.comp_substitutionPoint k _ _ σ)))
    (heq_of_eq ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (F.substitutionLift_event j e σ))))

/-- **Lifts of points and premises move along maps of stages.** -/
theorem comp_premiseLift {X : Base equations} {Z Z' : D} (k : Z' ⟶ Z)
    (x : Z ⟶ F.programModel.family X.as.arities) {x' : Z' ⟶ F.programModel.family X.as.arities}
    (point : k ≫ x = x') (I : Instance R (modelAt equations X))
    (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position))
    (restaged : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z'
        (childJudgment R _ (mapInstance R (F.pointProgram x') I) position))
    (same : ∀ position, HEq (restaged position) (F.eventModel.objects.restage k (children position))) :
    k ≫ F.premiseLift x I children = F.premiseLift x' I restaged := by
  subst point
  refine F.eq_premiseLift (k ≫ x) I restaged (k ≫ F.premiseLift x I children)
    ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (F.premiseLift_point x I children))) ?_
  intro position
  have read : F.premiseLift x I children ≫ F.carrier.map (rep R equations
      (a := object R equations X ⟨⟨_, childJudgment R _ I⟩⟩) (childJudgment R _ I position)
      (leaf R ⟨⟨_, childJudgment R _ I⟩⟩ position)) = (F.premiseEvents x I children position).1 :=
    (F.contextCones X).lift_event _ _ x (F.premiseEvents x I children) position
  have moved : HEq (F.eventModel.objects.restage k (F.premiseEvents x I children position))
      (restaged position) :=
    (F.eventModel.objects.restage_heq k (mapInstance_child R (F.pointProgram x) I position).symm
      (cast_heq _ _)).trans (same position).symm
  have judgmentEq : mapJudgment (F.programModel.stageRestage k)
      (mapJudgment (F.pointProgram x) (childJudgment R _ I position)) =
        childJudgment R _ (mapInstance R (F.pointProgram (k ≫ x)) I) position :=
    (congrArg (fun hom => mapJudgment hom (childJudgment R _ I position))
      (F.programModel.pointProgram_restage _ F.programInterpretation.satisfies X.as k x).symm).trans
      (mapInstance_child R (F.pointProgram (k ≫ x)) I position).symm
  exact HEq.trans (heq_of_eq ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) read)))
    (F.eventModel.objects.stageEvent_val_heq judgmentEq moved)

theorem rulePremises_heq {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq (F.rulePremises occurrence children position) (children position) := by
  unfold rulePremises
  exact cast_heq _ _

/-- **Lifts of occurrences and premises move along maps of stages.** -/
theorem comp_ruleLift {Z Z' : D} (k : Z' ⟶ Z) (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position))
    (restaged : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z'
        (childJudgment R _ (mapInstance R (F.programModel.stageRestage k) occurrence) position))
    (same : ∀ position, HEq (restaged position) (F.eventModel.objects.restage k (children position))) :
    k ≫ F.ruleLift occurrence children =
      F.ruleLift (mapInstance R (F.programModel.stageRestage k) occurrence) restaged := by
  have moved : ∀ position, HEq
      (F.rulePremises (mapInstance R (F.programModel.stageRestage k) occurrence) restaged position)
      (F.eventModel.objects.restage k (F.rulePremises occurrence children position)) := by
    intro position
    have one := F.rulePremises_heq (mapInstance R (F.programModel.stageRestage k) occurrence)
      restaged position
    have two := F.rulePremises_heq occurrence children position
    have judgmentEq : childJudgment R _ occurrence position = childJudgment R _ (mapInstance R
        (F.pointProgram (F.programModel.rulePoint R occurrence))
        (ruleInstance R equations occurrence.index occurrence.ambient)) position :=
      childJudgment_congr R (F.programModel.mapInstance_rulePoint R equations
          F.programInterpretation.satisfies occurrence).symm position position HEq.rfl
    have three := F.eventModel.objects.restage_heq k judgmentEq two.symm
    exact one.trans ((same position).trans three)
  exact F.comp_premiseLift k (F.programModel.rulePoint R occurrence)
    (F.programModel.comp_rulePoint R k occurrence)
    (ruleInstance R equations occurrence.index occurrence.ambient) (F.rulePremises occurrence children)
    (F.rulePremises (mapInstance R (F.programModel.stageRestage k) occurrence) restaged) moved

end StructuredFunctor

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
