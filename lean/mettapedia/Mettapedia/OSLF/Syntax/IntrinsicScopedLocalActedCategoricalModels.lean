import Mettapedia.OSLF.Syntax.CategoricalBindingStage
import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedSetSemantics
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# Models of a rule-local operational presentation in a category

A model interprets the authored binding signature and equations, and gives,
for each context `Γ` and sort `s`, an object `E(Γ,s)` of individual events with
source and target in the function object `P(Γ,s)`. A generalized event at a
stage `Z` over a judgment is a map `Z ⟶ E(Γ,s)` whose source and target are the
judgment's endpoints.

At every stage the model substitutes generalized events along environments and
applies each authored rule to generalized witnesses of its ordered, binder-local
premises, with the laws of a substitution model. Restaging along a map of
stages preserves both actions. Nothing requires events to cover the endpoints,
to be determined by them, or to reflect reductions.

Each stage is a target of the classifier: its points are the generalized
elements of the program objects.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (JudgmentAction ActionOn)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier (Base modelAt)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution (mapJudgment_substJudgment)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature}

/-! ## Event objects and generalized events -/

section Objects

variable (M : Model S D)

/-- For each context and sort, an object of individual events with source and
target in the function object. -/
structure EventObjects where
  event : Ctx S → S.Srt → D
  source : ∀ Γ s, event Γ s ⟶ M.power Γ s
  target : ∀ Γ s, event Γ s ⟶ M.power Γ s

variable {M}

/-- Generalized events at a stage whose endpoints are a judgment's endpoints. -/
def EventObjects.StageEvent (E : EventObjects M) (Z : D) (j : Judgment (M.stage Z)) : Type v :=
  {e : Z ⟶ E.event j.1 j.2.1 //
    e ≫ E.source j.1 j.2.1 = M.elemEquiv j.2.2.1 ∧ e ≫ E.target j.1 j.2.1 = M.elemEquiv j.2.2.2}

/-- Restage a generalized event along a map of stages. -/
def EventObjects.restage (E : EventObjects M) {Z Z' : D} (h : Z' ⟶ Z)
    {j : Judgment (M.stage Z)} (e : E.StageEvent Z j) :
    E.StageEvent Z' (mapJudgment (M.stageRestage h) j) :=
  ⟨h ≫ e.1,
    (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) e.2.1).trans
      (M.elemEquiv_restage h (j.2.2.1 : M.ElemOver Z j.1 j.2.1)).symm),
    (Category.assoc _ _ _).trans ((congrArg (h ≫ ·) e.2.2).trans
      (M.elemEquiv_restage h (j.2.2.2 : M.ElemOver Z j.1 j.2.1)).symm)⟩

theorem EventObjects.restage_heq (E : EventObjects M) {Z Z' : D} (h : Z' ⟶ Z)
    {first second : Judgment (M.stage Z)} (same : first = second)
    {one : E.StageEvent Z first} {two : E.StageEvent Z second} (sameEvent : HEq one two) :
    HEq (E.restage h one) (E.restage h two) := by
  subst same
  cases sameEvent
  rfl

/-- Generalized events at equal judgments with equal maps are equal. -/
theorem EventObjects.stageEvent_heq (E : EventObjects M) {Z : D}
    {first second : Judgment (M.stage Z)} (same : first = second)
    {one : E.StageEvent Z first} {two : E.StageEvent Z second} (sameMap : HEq one.1 two.1) :
    HEq one two := by
  subst same
  exact heq_of_eq (Subtype.ext (eq_of_heq sameMap))

/-- Equal generalized events at equal judgments have equal maps. -/
theorem EventObjects.stageEvent_val_heq (E : EventObjects M) {Z : D}
    {first second : Judgment (M.stage Z)} (same : first = second)
    {one : E.StageEvent Z first} {two : E.StageEvent Z second} (sameEvent : HEq one two) :
    HEq one.1 two.1 := by
  subst same
  cases sameEvent
  rfl

theorem EventObjects.restage_val (E : EventObjects M) {Z Z' : D} (h : Z' ⟶ Z)
    {j : Judgment (M.stage Z)} (e : E.StageEvent Z j) : (E.restage h e).1 = h ≫ e.1 :=
  rfl

end Objects

/-! ## Models -/

variable (R : List (LocalRule S))
variable {M' : List (MetaArity S)} (equations : List (EqAxiom S M'))

/-- A binding model of the authored equations, with event objects: the data
from which the objects of valuations are built. -/
structure EventModel where
  program : SatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)
  objects : EventObjects program.interpretation.model

namespace EventModel

variable {equations}
variable (model : EventModel equations (D := D))

/-- The binding model of programs. -/
abbrev programModel : Model S D :=
  model.program.interpretation.model

/-- The program classifier of the model. -/
noncomputable abbrev programFunctor : Base equations ⥤ D :=
  model.programModel.equationClassifyingFunctor _ model.program.satisfies

end EventModel

/-- **A model of the rule-local operational presentation in `D`.** -/
structure CategoricalModel where
  program : SatisfyingInterpretation (D := D) (authoredEquationPresentation S equations)
  objects : EventObjects program.interpretation.model
  act : ∀ Z : D, ActionOn (program.interpretation.model.stage Z) (objects.StageEvent Z)
  act_identity : ∀ Z : D, ActionOn.IdentityLaw (act Z)
  act_comp : ∀ Z : D, ActionOn.CompLaw (act Z)
  rules : ∀ Z : D, (IntrinsicScopedLocalPolynomial.rules R
    (program.interpretation.model.stage Z)).Algebra (fun _ j => objects.StageEvent Z j)
  act_rules : ∀ Z : D, RulesLaw R _ (act Z) (rules Z)
  act_restage : ∀ {Z Z' : D} (h : Z' ⟶ Z) (j : Judgment (program.interpretation.model.stage Z))
    (e : objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      (program.interpretation.model.stage Z).substitution.Carrier j.1 Δ)
    (target : Judgment (program.interpretation.model.stage Z))
    (same : IntrinsicScopedConditionalSubstitution.substJudgment j σ = target),
    objects.restage h (act Z j e σ target same) =
      act Z' (mapJudgment (program.interpretation.model.stageRestage h) j) (objects.restage h e)
        (fun t w => (program.interpretation.model.stageRestage h).raw.map (σ t w))
        (mapJudgment (program.interpretation.model.stageRestage h) target)
        ((mapJudgment_substJudgment _ j σ).symm.trans (congrArg _ same))
  rules_restage : ∀ {Z Z' : D} (h : Z' ⟶ Z) {j : Judgment (program.interpretation.model.stage Z)}
    (shape : Shape R (program.interpretation.model.stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      objects.StageEvent Z (childJudgment R _ shape.1 position)),
    objects.restage h ((rules Z).act () j ⟨shape, children⟩) =
      (rules Z').act () (mapJudgment (program.interpretation.model.stageRestage h) j)
        ⟨mapShape R (program.interpretation.model.stageRestage h) shape, fun position =>
          ((mapInstance_child R (program.interpretation.model.stageRestage h) shape.1 position).symm ▸
            objects.restage h (children position) :
              objects.StageEvent Z' (childJudgment R _
                (mapInstance R (program.interpretation.model.stageRestage h) shape.1) position))⟩

namespace CategoricalModel

variable {R equations}
variable (model : CategoricalModel R equations (D := D))

/-- The binding model and event objects of a model. -/
abbrev toEventModel : EventModel equations (D := D) :=
  ⟨model.program, model.objects⟩

/-- The binding model of programs. -/
abbrev programModel : Model S D :=
  model.program.interpretation.model

/-- The generalized events of the model at a stage, as a substitution model
over the stage clone. -/
def stageModel (Z : D) : SubstitutionModel R (model.programModel.stage Z) where
  carrier := model.objects.StageEvent Z
  act := model.act Z
  act_identity := model.act_identity Z
  act_comp := model.act_comp Z
  rules := model.rules Z
  act_rules := model.act_rules Z

/-- Restaging along a map of stages is a map of stage models. -/
def restageHom {Z Z' : D} (h : Z' ⟶ Z) :
    SubstitutionModel.Hom R _ (model.stageModel Z)
      ((model.stageModel Z').pullback (model.programModel.stageRestage h)) where
  evidence :=
    { toFun := fun _ _ event => model.objects.restage h event
      commutes := fun base j layer => by
        cases base
        obtain ⟨shape, children⟩ := layer
        exact (model.rules_restage h shape children).trans
          (pullback_rulesMap_act_map (model.programModel.stageRestage h) (model.rules Z')
            (fun _ event => model.objects.restage h event) shape children).symm }
  preserves := fun j e _ σ target same => model.act_restage h j e σ target same

/-- The program classifier of the model. -/
noncomputable abbrev programFunctor : Base equations ⥤ D :=
  model.programModel.equationClassifyingFunctor _ model.program.satisfies

/-- **Each stage is a target of the classifier**: its points are the
generalized elements of the program objects. -/
noncomputable def stageTarget (Z : D) : ClassifierTarget.{max u v, v, v} R equations where
  algebra := model.programModel.stage Z
  model := model.stageModel Z
  Point X := Z ⟶ model.programModel.family X.as.arities
  program x := model.programModel.pointProgram _ model.program.satisfies _ x
  move assignment x := x ≫ (model.programFunctor).map assignment
  move_id x := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  move_comp first second x := by
    rw [CategoryTheory.Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  program_move assignment x :=
    model.programModel.pointProgram_move equations model.program.satisfies assignment x

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
