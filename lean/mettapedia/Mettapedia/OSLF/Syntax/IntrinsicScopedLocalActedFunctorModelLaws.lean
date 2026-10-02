import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFunctorModels
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericLaws
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# The laws of the model of a structure-preserving functor

Over a map into a value of a structure-preserving functor, the values at the
arrows of firing trees commute with substitution and with the rule actions,
along the interpretation of equation classes at the map's point. Every input
of a law at a stage is the image of the generic data of a context under a map
into the functor's value at that context, so the laws of the free model of
trees hold for the functor's actions.
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
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (ActionOn)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment substJudgment_identity castEnv castEnv_heq heq_transport mapJudgment_substJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree freeModel)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace StructuredFunctor

variable (F : StructuredFunctor R equations (D := D))

/-! ## Trees over a value map onto the functor's actions -/

section Along

variable {F} {a : Classifier R equations} {Z : D} (g : Z ⟶ F.carrier.obj a)

/-- The values at the arrows of the trees over a value. -/
abbrev treeImage :
    ∀ J : Judgment (modelAt equations a.base),
      (freeModel R _ (seeds R _ (events R equations a))).carrier J →
        F.eventModel.objects.StageEvent Z (mapJudgment (valuePoint g) J) :=
  fun J tree => F.treeEvent J tree g

theorem actsAlong :
    ActsAlong (valuePoint g) (freeModel R _ (seeds R _ (events R equations a))) (F.act Z)
      (treeImage g) :=
  fun j tree _ σ => treeEvent_substitute g j σ tree

theorem rulesAlong :
    RulesAlong (valuePoint g) (freeModel R _ (seeds R _ (events R equations a))) (F.rulesAlgebra Z)
      (treeImage g) :=
  fun _ shape children => treeEvent_node g shape children

end Along

/-! ## The laws -/

/-- **The identity environment fixes generalized events.** -/
theorem act_identity (Z : D) : ActionOn.IdentityLaw (F.act Z) := by
  intro j e same
  let σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier
      j.1 j.1 := fun _ v => (F.programModel.stage Z).substitution.injectVar v
  let J := substitutionJudgment equations j.1 j.1 j.2.1
  have atLeaf : HEq (F.treeEvent J (leaf R ((Context.empty R _).cons R _ J)
      (first R J (Context.empty R _))) (F.substitutionLift j e σ)) e :=
    (F.treeEvent_singleLift _ _ _).trans (cast_heq _ _)
  have reading : mapJudgment (valuePoint (F.substitutionLift j e σ)) J = j :=
    (congrArg (fun y => mapJudgment (F.pointProgram y) J) (F.substitutionLift_point j e σ)).trans
      (F.programModel.mapJudgment_substitutionPoint equations F.programInterpretation.satisfies
        j.2.2.1 j.2.2.2 σ)
  have fixed := identity_along (actsAlong (F.substitutionLift j e σ)) J
    (leaf R ((Context.empty R _).cons R _ J) (first R J (Context.empty R _)))
    (substJudgment_identity _)
  exact eq_of_heq ((F.act_heq reading.symm atLeaf.symm HEq.rfl reading.symm same _).trans
    ((heq_of_eq fixed).trans atLeaf))

/-- **Acting twice is acting along the composite environment.** -/
theorem act_comp (Z : D) : ActionOn.CompLaw (F.act Z) := by
  intro j e Δ Θ σ τ target second direct
  let J := doubleSubstitutionJudgment equations j.1 Δ Θ j.2.1
  let p := F.programModel.doubleSubstitutionPoint j.2.2.1 j.2.2.2 σ τ
  have readAt := F.programModel.mapJudgment_doubleSubstitutionPoint equations
    F.programInterpretation.satisfies j.2.2.1 j.2.2.2 σ τ
  let x := F.singleLift J p (cast (congrArg (F.eventModel.objects.StageEvent Z) readAt.symm) e)
  have point : x ≫ F.programPoint _ = p := F.singleLift_point _ _ _
  let leaf₀ := leaf R ((Context.empty R _).cons R _ J) (first R J (Context.empty R _))
  have atLeaf : HEq (F.treeEvent J leaf₀ x) e := (F.treeEvent_singleLift _ _ _).trans (cast_heq _ _)
  have reading : mapJudgment (valuePoint x) J = j :=
    (congrArg (fun y => mapJudgment (F.pointProgram y) J) point).trans readAt
  have firstEnv : (fun t v => (valuePoint x).raw.map
      (doubleSubstitutionFirst equations j.1 Δ Θ j.2.1 t v)) = σ :=
    funext fun _ => funext fun v =>
      (congrArg (fun y => (F.pointProgram y).raw.map
        (doubleSubstitutionFirst equations j.1 Δ Θ j.2.1 _ v)) point).trans
      (F.programModel.doubleSubstitutionPoint_first equations F.programInterpretation.satisfies
        j.2.2.1 j.2.2.2 σ τ v)
  have secondEnv : (fun t v => (valuePoint x).raw.map
      (doubleSubstitutionSecond equations j.1 Δ Θ j.2.1 t v)) = τ :=
    funext fun _ => funext fun v =>
      (congrArg (fun y => (F.pointProgram y).raw.map
        (doubleSubstitutionSecond equations j.1 Δ Θ j.2.1 _ v)) point).trans
      (F.programModel.doubleSubstitutionPoint_second equations F.programInterpretation.satisfies
        j.2.2.1 j.2.2.2 σ τ v)
  have compositeEnv : (fun t v => (F.programModel.stage Z).substitution.substitute
      (fun r w => (valuePoint x).raw.map (doubleSubstitutionSecond equations j.1 Δ Θ j.2.1 r w))
      ((valuePoint x).raw.map (doubleSubstitutionFirst equations j.1 Δ Θ j.2.1 t v))) =
        fun t v => (F.programModel.stage Z).substitution.substitute τ (σ t v) :=
    funext fun t => funext fun v =>
      congrArg₂ (fun τ' s' => (F.programModel.stage Z).substitution.substitute τ' s') secondEnv
        (congrFun (congrFun firstEnv t) v)
  have middle := substJudgment_congr reading (heq_of_eq firstEnv)
  have law := comp_along (actsAlong x) J leaf₀ (doubleSubstitutionFirst equations j.1 Δ Θ j.2.1)
    (doubleSubstitutionSecond equations j.1 Δ Θ j.2.1) target
    ((substJudgment_congr middle (heq_of_eq secondEnv)).trans second)
    ((substJudgment_congr reading (heq_of_eq compositeEnv)).trans direct)
  have inner := F.act_heq reading.symm atLeaf.symm (heq_of_eq firstEnv.symm) middle.symm
    (rfl : substJudgment j σ = substJudgment j σ) rfl
  exact eq_of_heq ((F.act_heq middle.symm inner (heq_of_eq secondEnv.symm) rfl second _).trans
    ((heq_of_eq law).trans (F.act_heq reading atLeaf (heq_of_eq compositeEnv) rfl _ direct)))

/-- **Substitution passes beneath the functor's rule actions.** -/
theorem act_rules (Z : D) : RulesLaw R _ (F.act Z) (F.rulesAlgebra Z) := by
  intro j shape children Δ σ target same
  let I := ruleSubstitutionInstance R equations shape.1.index shape.1.ambient Δ
  let p := F.programModel.ruleSubstitutionPoint R shape.1 (castEnv shape.2 σ)
  have readAt := F.programModel.mapInstance_ruleSubstitutionPoint equations
    F.programInterpretation.satisfies R shape.1 (castEnv shape.2 σ)
  let premises : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram p) I) position) :=
    fun position => cast (congrArg (F.eventModel.objects.StageEvent Z)
      (childJudgment_congr R readAt.symm position position HEq.rfl)) (children position)
  have lifted := F.treeEvent_premiseLift p I premises
  have point := F.premiseLift_point p I premises
  generalize F.premiseLift p I premises = x at lifted point
  have reading : mapInstance R (valuePoint x) I = shape.1 :=
    (congrArg (fun y => mapInstance R (F.pointProgram y) I) point).trans readAt
  have env : (fun t v => (valuePoint x).raw.map
      (ruleSubstitutionEnv R equations shape.1.index shape.1.ambient Δ t v)) = castEnv shape.2 σ :=
    funext fun _ => funext fun v =>
      (congrArg (fun y => (F.pointProgram y).raw.map
        (ruleSubstitutionEnv R equations shape.1.index shape.1.ambient Δ _ v)) point).trans
      (F.programModel.ruleSubstitutionPoint_env equations F.programInterpretation.satisfies R
        shape.1 (castEnv shape.2 σ) v)
  exact rulesLaw_along (actsAlong x) (rulesAlong x) I
    (fun position => leaf R ⟨⟨_, childJudgment R _ I⟩⟩ position)
    (ruleSubstitutionEnv R equations shape.1.index shape.1.ambient Δ) shape reading children
    (fun position position' samePosition => by
      cases samePosition
      exact (cast_heq _ _).symm.trans (lifted position).symm)
    σ ((heq_of_eq env).trans (castEnv_heq _ _)) target same

/-- **Restaging commutes with the substitution action.** -/
theorem act_restage {Z Z' : D} (k : Z' ⟶ Z) (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ)
    (target : Judgment (F.programModel.stage Z)) (same : substJudgment j σ = target) :
    F.eventModel.objects.restage k (F.act Z j e σ target same) =
      F.act Z' (mapJudgment (F.programModel.stageRestage k) j) (F.eventModel.objects.restage k e)
        (fun t w => (F.programModel.stageRestage k).raw.map (σ t w))
        (mapJudgment (F.programModel.stageRestage k) target)
        ((mapJudgment_substJudgment _ j σ).symm.trans (congrArg _ same)) := by
  have atTarget : target = mapJudgment (valuePoint (F.substitutionLift j e σ))
      (substJudgment (substitutionJudgment equations j.1 Δ j.2.1)
        (substitutionEnv equations j.1 Δ j.2.1)) :=
    ((F.substitutionLift_judgment j e σ).trans same).symm
  have one := F.eventModel.objects.restage_heq k atTarget (F.act_heq_treeEvent j e σ target same)
  have two := (F.treeEvent_comp _ (substitutionTree R equations j.1 Δ j.2.1) k
    (F.substitutionLift j e σ)).symm
  have three := congr_arg_heq (fun g => F.treeEvent _ (substitutionTree R equations j.1 Δ j.2.1) g)
    (F.comp_substitutionLift k j e σ)
  have four := (F.act_heq_treeEvent (mapJudgment (F.programModel.stageRestage k) j)
    (F.eventModel.objects.restage k e) (fun t w => (F.programModel.stageRestage k).raw.map (σ t w))
    (mapJudgment (F.programModel.stageRestage k) target)
    ((mapJudgment_substJudgment _ j σ).symm.trans (congrArg _ same))).symm
  exact eq_of_heq (one.trans (two.trans (three.trans four)))

/-- **Restaging commutes with the rule actions.** -/
theorem rules_restage {Z Z' : D} (k : Z' ⟶ Z) {j : Judgment (F.programModel.stage Z)}
    (shape : Shape R (F.programModel.stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ shape.1 position)) :
    F.eventModel.objects.restage k ((F.rulesAlgebra Z).act () j ⟨shape, children⟩) =
      (F.rulesAlgebra Z').act () (mapJudgment (F.programModel.stageRestage k) j)
        ⟨mapShape R (F.programModel.stageRestage k) shape, fun position =>
          ((mapInstance_child R (F.programModel.stageRestage k) shape.1 position).symm ▸
            F.eventModel.objects.restage k (children position) :
              F.eventModel.objects.StageEvent Z' (childJudgment R _
                (mapInstance R (F.programModel.stageRestage k) shape.1) position))⟩ := by
  have atTarget : j = mapJudgment (valuePoint (F.ruleLift shape.1 children))
      (conclusionJudgment R _ (ruleInstance R equations shape.1.index shape.1.ambient)) :=
    ((F.ruleLift_judgment shape.1 children).trans shape.2).symm
  have one := F.eventModel.objects.restage_heq k atTarget
    (F.rulesAlgebra_heq_treeEvent j ⟨shape, children⟩)
  have two := (F.treeEvent_comp _ (ruleTree R equations shape.1.index shape.1.ambient) k
    (F.ruleLift shape.1 children)).symm
  let premises : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      F.eventModel.objects.StageEvent Z' (childJudgment R _
        (mapInstance R (F.programModel.stageRestage k) shape.1) position) := fun position =>
    ((mapInstance_child R (F.programModel.stageRestage k) shape.1 position).symm ▸
      F.eventModel.objects.restage k (children position) :
        F.eventModel.objects.StageEvent Z' (childJudgment R _
          (mapInstance R (F.programModel.stageRestage k) shape.1) position))
  have three := congr_arg_heq (fun g => F.treeEvent _ (ruleTree R equations shape.1.index
    shape.1.ambient) g) (F.comp_ruleLift k shape.1 children premises
      (fun position => heq_transport _ _))
  have four := (F.rulesAlgebra_heq_treeEvent (mapJudgment (F.programModel.stageRestage k) j)
    ⟨mapShape R (F.programModel.stageRestage k) shape, premises⟩).symm
  exact eq_of_heq (one.trans (two.trans (three.trans four)))

/-- **The model of a structure-preserving functor**: its values on event-free
and generic event objects, with substitution and rule actions given by its
values at the generic substitutions and generic occurrences. -/
noncomputable def model : CategoricalModel R equations (D := D) where
  program := F.programInterpretation
  objects := F.eventModel.objects
  act := F.act
  act_identity := F.act_identity
  act_comp := F.act_comp
  rules := F.rulesAlgebra
  act_rules := F.act_rules
  act_restage := F.act_restage
  rules_restage := F.rules_restage

end StructuredFunctor

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
