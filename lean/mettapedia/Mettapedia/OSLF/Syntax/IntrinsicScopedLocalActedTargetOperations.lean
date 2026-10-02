import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetFold
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetTransport

/-!
# Actual operation arrows under change of target

Generalized events and occurrences at any stage of the new target have
representable substitution and rule domains. Their lifts use the specified
comparisons for program and event objects. Evaluating the corresponding
generic trees is precomposition with the image of the original operation
arrow, defined by the independent free firing-tree fold.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment mapJudgment_substJudgment)

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace CategoricalModel

variable (M : CategoricalModel R equations (D := D))

/-- The program comparison acts on natural families at every new stage. -/
abbrev imageStageMap (Z : D') := stageMap (M.imageProgramIso H).hom Z

/-- A substitution domain at an arbitrary new stage, with its actual
image program values and its individual image event. -/
def imageActLift {Z : D'} (j : Judgment ((M.imageProgram H).interpretation.model.stage Z))
    (e : (M.imageEvents H).StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      ((M.imageProgram H).interpretation.model.stage Z).substitution.Carrier j.1 Δ) :
    Z ⟶ H.obj (M.classifyingObject (substitutionObject R equations j.1 Δ j.2.1)) :=
  (M.structured.postcompose H).substitutionLift
    (mapJudgment (M.imageStageMap H Z) j) ((M.imageEventsHom H).stage Z j e)
    (fun t w => (M.imageStageMap H Z).raw.map (σ t w))

theorem imageActLift_point {Z : D'}
    (j : Judgment ((M.imageProgram H).interpretation.model.stage Z))
    (e : (M.imageEvents H).StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      ((M.imageProgram H).interpretation.model.stage Z).substitution.Carrier j.1 Δ) :
    M.imageActLift H j e σ ≫ (M.structured.postcompose H).programPoint
      (substitutionObject R equations j.1 Δ j.2.1) =
      (M.structured.postcompose H).programModel.substitutionPoint
        ((M.imageStageMap H Z).raw.map j.2.2.1) ((M.imageStageMap H Z).raw.map j.2.2.2)
        (fun t w => (M.imageStageMap H Z).raw.map (σ t w)) :=
  (M.structured.postcompose H).substitutionLift_point _ _ _

/-- Each ordered premise is moved through the actual event comparison,
retaining its own declared binder extension. -/
def imageRuleChildren {Z : D'}
    (occurrence : Instance R ((M.imageProgram H).interpretation.model.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (M.imageEvents H).StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    (M.structured.postcompose H).eventModel.objects.StageEvent Z
      (childJudgment R _ (mapInstance R (M.imageStageMap H Z) occurrence) position) :=
  (mapInstance_child R (M.imageStageMap H Z) occurrence position).symm ▸
    (M.imageEventsHom H).stage Z _ (children position)

/-- The image premise is the specified map of the actual individual event,
including premises whose endpoints live under additional binders. -/
theorem imageRuleChildren_val {Z : D'}
    (occurrence : Instance R ((M.imageProgram H).interpretation.model.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (M.imageEvents H).StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq (M.imageRuleChildren H occurrence children position).1
      ((children position).1 ≫ H.map
        (M.eventIso (childJudgment R _ occurrence position).1
          (childJudgment R _ occurrence position).2.1).hom) :=
  (M.structured.postcompose H).eventModel.objects.stageEvent_val_heq
    (mapInstance_child R (M.imageStageMap H Z) occurrence position)
    (IntrinsicScopedConditionalSubstitution.heq_transport _ _)

/-- The representable domain of a rule occurrence and its ordered,
binder-local premises at any new target stage. -/
def imageRuleLift {Z : D'}
    (occurrence : Instance R ((M.imageProgram H).interpretation.model.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (M.imageEvents H).StageEvent Z (childJudgment R _ occurrence position)) :
    Z ⟶ H.obj (M.classifyingObject (ruleObject R equations occurrence.index occurrence.ambient)) :=
  (M.structured.postcompose H).ruleLift
    (mapInstance R (M.imageStageMap H Z) occurrence) (M.imageRuleChildren H occurrence children)

theorem imageRuleLift_point {Z : D'}
    (occurrence : Instance R ((M.imageProgram H).interpretation.model.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (M.imageEvents H).StageEvent Z (childJudgment R _ occurrence position)) :
    M.imageRuleLift H occurrence children ≫ (M.structured.postcompose H).programPoint
      (ruleObject R equations occurrence.index occurrence.ambient) =
      (M.structured.postcompose H).programModel.rulePoint R
        (mapInstance R (M.imageStageMap H Z) occurrence) :=
  (M.structured.postcompose H).ruleLift_point _ _

/-- Recovered substitution on actual image inputs is the original
operation arrow mapped by the target functor, at every new target stage. -/
theorem postcompose_act_freeFold {Z : D'}
    (j : Judgment ((M.imageProgram H).interpretation.model.stage Z))
    (e : (M.imageEvents H).StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      ((M.imageProgram H).interpretation.model.stage Z).substitution.Carrier j.1 Δ) :
    ((M.structured.postcompose H).act Z (mapJudgment (M.imageStageMap H Z) j)
      ((M.imageEventsHom H).stage Z j e)
      (fun t w => (M.imageStageMap H Z).raw.map (σ t w))
      (substJudgment (mapJudgment (M.imageStageMap H Z) j)
        (fun t w => (M.imageStageMap H Z).raw.map (σ t w))) rfl).1 ≫
        H.map (M.eventIso Δ j.2.1).inv =
      M.imageActLift H j e σ ≫ H.map (M.foldOperation _
        (substitutionTree R equations j.1 Δ j.2.1)) := by
  have action := eq_of_heq ((M.structured.postcompose H).act_val_heq
    (mapJudgment (M.imageStageMap H Z) j) ((M.imageEventsHom H).stage Z j e)
    (fun t w => (M.imageStageMap H Z).raw.map (σ t w)) _ rfl)
  exact (congrArg (· ≫ H.map (M.eventIso Δ j.2.1).inv) action).trans
    (M.postcompose_tree_freeFold H (M.imageActLift H j e σ) _
      (substitutionTree R equations j.1 Δ j.2.1))

/-- Recovered rule action on actual image inputs is the mapped source
rule-operation arrow. Its domain retains all ordered local premises. -/
theorem postcompose_rule_freeFold {Z : D'}
    (occurrence : Instance R ((M.imageProgram H).interpretation.model.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (M.imageEvents H).StageEvent Z (childJudgment R _ occurrence position)) :
    (((M.structured.postcompose H).rulesAlgebra Z).act ()
      (conclusionJudgment R _ (mapInstance R (M.imageStageMap H Z) occurrence))
      ⟨⟨mapInstance R (M.imageStageMap H Z) occurrence, rfl⟩,
        M.imageRuleChildren H occurrence children⟩).1 ≫
          H.map (M.eventIso occurrence.ambient (R.get occurrence.index).2.conclusion.sort).inv =
      M.imageRuleLift H occurrence children ≫ H.map (M.foldOperation _
        (ruleTree R equations occurrence.index occurrence.ambient)) := by
  have action := eq_of_heq ((M.structured.postcompose H).rulesAlgebra_val_heq
    (conclusionJudgment R _ (mapInstance R (M.imageStageMap H Z) occurrence))
    ⟨⟨mapInstance R (M.imageStageMap H Z) occurrence, rfl⟩,
      M.imageRuleChildren H occurrence children⟩)
  exact (congrArg
    (· ≫ H.map (M.eventIso occurrence.ambient (R.get occurrence.index).2.conclusion.sort).inv)
    action).trans (M.postcompose_tree_freeFold H (M.imageRuleLift H occurrence children) _
      (ruleTree R equations occurrence.index occurrence.ambient))

section MapOperations

variable {K L : CategoricalModel R equations (D := D')}

/-- A model map carries the underlying arrow of contextual substitution
to the action at the image judgment, without any restriction on the stage. -/
theorem Hom.act_value (f : K ⟶ L) {Z : D'} (j : Judgment (K.programModel.stage Z))
    (e : K.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      (K.programModel.stage Z).substitution.Carrier j.1 Δ) :
    (K.act Z j e σ (substJudgment j σ) rfl).1 ≫ f.events.event Δ j.2.1 =
      (L.act Z (mapJudgment (stageMap f.program Z) j) (f.events.stage Z j e)
        (fun t w => (stageMap f.program Z).raw.map (σ t w))
        (substJudgment (mapJudgment (stageMap f.program Z) j)
          (fun t w => (stageMap f.program Z).raw.map (σ t w))) rfl).1 := by
  have law := (f.stage Z).act j e σ (substJudgment j σ) rfl
  have values := congrArg Subtype.val law
  have same := mapJudgment_substJudgment (stageMap f.program Z) j σ
  have moved := (L.stageModel Z).toAction.act_heq
    (value₁ := f.events.stage Z j e) rfl HEq.rfl HEq.rfl same
    ((mapJudgment_substJudgment (stageMap f.program Z) j σ).symm.trans rfl) rfl
  exact values.trans (eq_of_heq (L.objects.stageEvent_val_heq same moved))

/-- A model map retains the ordered declaration addresses when it maps
the witnesses of the rule's binder-local premises. -/
def Hom.ruleChildren (f : K ⟶ L) {Z : D'}
    (occurrence : Instance R (K.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      K.objects.StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    L.objects.StageEvent Z
      (childJudgment R _ (mapInstance R (stageMap f.program Z) occurrence) position) :=
  (mapInstance_child R (stageMap f.program Z) occurrence position).symm ▸
    f.events.stage Z _ (children position)

/-- The underlying rule-action arrow commutes with every model map.
The equality of conclusion indices transports only the endpoint fiber. -/
theorem Hom.rule_value (f : K ⟶ L) {Z : D'}
    (occurrence : Instance R (K.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      K.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    ((K.rules Z).act () (conclusionJudgment R _ occurrence)
      ⟨⟨occurrence, rfl⟩, children⟩).1 ≫
        f.events.event occurrence.ambient (R.get occurrence.index).2.conclusion.sort =
      ((L.rules Z).act ()
        (conclusionJudgment R _ (mapInstance R (stageMap f.program Z) occurrence))
        ⟨⟨mapInstance R (stageMap f.program Z) occurrence, rfl⟩,
          f.ruleChildren occurrence children⟩).1 := by
  let shape : Shape R (K.programModel.stage Z) (conclusionJudgment R _ occurrence) :=
    ⟨occurrence, rfl⟩
  have law := ((f.stage Z).rules _ ⟨shape, children⟩).trans
    (pullback_rulesMap_act_map (stageMap f.program Z) (L.rules Z)
      (fun j e => f.events.stage Z j e) shape children)
  have same := (mapInstance_conclusion R (stageMap f.program Z) occurrence).symm
  have moved := rulesAct_heq R (L.rules Z) same rfl
    (mapShape R (stageMap f.program Z) shape).2 rfl
    (f.ruleChildren occurrence children) (f.ruleChildren occurrence children)
    (fun p q h => by cases h; rfl)
  exact (congrArg Subtype.val law).trans
    (eq_of_heq (L.objects.stageEvent_val_heq same moved))

end MapOperations

section ActualImageOperations

/-- An arbitrary generalized value of the postcomposed source classifier
gives a valuation on the actual image program and event objects. -/
def imageValuation {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ H.obj (M.classifyingObject a)) : (M.targetModel H).StageValuation Z a :=
  (M.targetModelIso H).inv.valuation ((M.structured.postcompose H).valuation g)

/-- Interpretation of every firing tree on actual image objects agrees
with the mapped independent source fold, including substituted event leaves. -/
theorem targetModel_tree_evaluate {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ H.obj (M.classifyingObject a)) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((M.imageValuation H g).evaluate j tree).1 = g ≫ H.map (M.foldOperation j tree) := by
  let value := (M.structured.postcompose H).valuation g
  let f := (M.targetModelIso H).inv
  have fusion := ClassifierTarget.Valuation.evaluate_map (f.targetHom Z) value j tree
  have same := (congrArg (fun φ => mapJudgment φ j)
    ((f.targetHom Z).program_point value.point)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ j)
  have values := eq_of_heq ((M.targetModel H).objects.stageEvent_val_heq same fusion)
  have event := M.targetModelIso_inv_event H j.1 j.2.1
  have read := congrArg Subtype.val ((M.structured.postcompose H).evaluate_valuation g j tree)
  exact values.trans
    ((congrArg (((value.evaluate j tree).1) ≫ ·) event).trans
      ((congrArg (· ≫ H.map (M.eventIso j.1 j.2.1).inv) read).trans
        (M.postcompose_tree_freeFold H g j tree)))

/-- The preceding comparison identifies the existing freeModelUniversal
fold at the actual image valuation, rather than introducing another fold. -/
theorem targetModel_tree_freeFold {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ H.obj (M.classifyingObject a)) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (((IntrinsicScopedLocalActedFree.freeModelUniversal R _ _
      (((M.targetModel H).stageTarget Z).pointModel (M.imageValuation H g).point))
        (M.imageValuation H g).assignment).evidence.toFun () j tree).1 =
      g ≫ H.map (M.foldOperation j tree) := by
  exact (congrArg Subtype.val ((M.imageValuation H g).evaluate_eq_freeFold j tree)).symm.trans
    (M.targetModel_tree_evaluate H g j tree)

/-- Changing an arbitrary target stage precomposes the same mapped fold
operation; this includes the substitution stored in event-variable leaves. -/
theorem targetModel_tree_restage {a : Classifier R equations} {Z Z' : D'}
    (k : Z' ⟶ Z) (g : Z ⟶ H.obj (M.classifyingObject a))
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((M.imageValuation H (k ≫ g)).evaluate j tree).1 =
      k ≫ ((M.imageValuation H g).evaluate j tree).1 :=
  (M.targetModel_tree_evaluate H (k ≫ g) j tree).trans
    ((Category.assoc _ _ _).trans
      (congrArg (k ≫ ·) (M.targetModel_tree_evaluate H g j tree).symm))

variable {M} {N : CategoricalModel R equations (D := D)}

/-- The original operational fold arrows commute with every model map. -/
theorem foldOperation_map (f : M ⟶ N) {a : Classifier R equations}
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    (classifyingMap f).app a ≫ N.foldOperation j tree =
      M.foldOperation j tree ≫ f.events.event j.1 j.2.1 := by
  have natural := (classifyingMap f).naturality (rep R equations j tree)
  have event := classifyingMap_eventIso_inv f j.1 j.2.1
  exact (congrArg ((classifyingMap f).app a ≫ ·) (N.foldOperation_rep j tree).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (N.eventIso j.1 j.2.1).inv) natural.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (M.classifyingFunctor.map (rep R equations j tree) ≫ ·) event).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ f.events.event j.1 j.2.1) (M.foldOperation_rep j tree)))))))

/-- The actual image fold fuses with all transported model maps, including
maps that merge events. The new-stage value moves by the mapped original
classifying component. -/
theorem targetModel_tree_map (f : M ⟶ N) {a : Classifier R equations} {Z : D'}
    (g : Z ⟶ H.obj (M.classifyingObject a)) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    ((M.imageValuation H g).evaluate j tree).1 ≫
        ((transportModels H).map f).events.event j.1 j.2.1 =
      ((N.imageValuation H (g ≫ H.map ((classifyingMap f).app a))).evaluate j tree).1 := by
  have image := (H.map_comp (M.foldOperation j tree) (f.events.event j.1 j.2.1)).symm.trans
    ((congrArg H.map (foldOperation_map f j tree).symm).trans
      (H.map_comp ((classifyingMap f).app a) (N.foldOperation j tree)))
  exact (congrArg₂ (· ≫ ·) (M.targetModel_tree_evaluate H g j tree)
    (transportModels_map_event H f j.1 j.2.1)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (g ≫ ·) image).trans
          ((Category.assoc _ _ _).symm.trans
            (N.targetModel_tree_evaluate H (g ≫ H.map ((classifyingMap f).app a)) j tree).symm)))

variable (M)

/-- Contextual substitution on the actual image event object is
precomposition of the mapped original substitution-operation arrow.
The input stage is an arbitrary object of the new target. -/
theorem targetModel_act_freeFold {Z : D'}
    (j : Judgment ((M.imageProgram H).interpretation.model.stage Z))
    (e : (M.imageEvents H).StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      ((M.imageProgram H).interpretation.model.stage Z).substitution.Carrier j.1 Δ) :
    ((M.targetModel H).act Z j e σ (substJudgment j σ) rfl).1 =
      M.imageActLift H j e σ ≫ H.map (M.foldOperation _
        (substitutionTree R equations j.1 Δ j.2.1)) := by
  have forward := Hom.act_value (M.targetModelIso H).hom j e σ
  rw [M.targetModelIso_hom_event H] at forward
  have cancellation :
      (((M.targetModel H).act Z j e σ (substJudgment j σ) rfl).1 ≫
        H.map (M.eventIso Δ j.2.1).hom) ≫ H.map (M.eventIso Δ j.2.1).inv =
        ((M.targetModel H).act Z j e σ (substJudgment j σ) rfl).1 :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (H.mapIso (M.eventIso Δ j.2.1)).hom_inv_id).trans
        (Category.comp_id _))
  exact cancellation.symm.trans
    ((congrArg (· ≫ H.map (M.eventIso Δ j.2.1).inv) forward).trans
      (M.postcompose_act_freeFold H j e σ))

/-- The substitution comparison also permits any equal target judgment,
transporting its context and endpoint fiber explicitly. -/
theorem targetModel_act_freeFold_target {Z : D'}
    (j : Judgment ((M.imageProgram H).interpretation.model.stage Z))
    (e : (M.imageEvents H).StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      ((M.imageProgram H).interpretation.model.stage Z).substitution.Carrier j.1 Δ)
    (target : Judgment ((M.imageProgram H).interpretation.model.stage Z))
    (same : substJudgment j σ = target) :
    HEq ((M.targetModel H).act Z j e σ target same).1
      (M.imageActLift H j e σ ≫ H.map (M.foldOperation _
        (substitutionTree R equations j.1 Δ j.2.1))) := by
  have changed := ((M.targetModel H).stageModel Z).toAction.act_heq
    (value₁ := e) (σ₁ := σ) rfl HEq.rfl HEq.rfl same rfl same
  exact ((M.targetModel H).objects.stageEvent_val_heq same changed).symm.trans
    (heq_of_eq (M.targetModel_act_freeFold H j e σ))

/-- Every authored rule action on actual image events is the mapped
original rule-operation arrow applied to the new-stage occurrence and its
ordered binder-local premises. -/
theorem targetModel_rule_freeFold {Z : D'}
    (occurrence : Instance R ((M.imageProgram H).interpretation.model.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (M.imageEvents H).StageEvent Z (childJudgment R _ occurrence position)) :
    (((M.targetModel H).rules Z).act () (conclusionJudgment R _ occurrence)
      ⟨⟨occurrence, rfl⟩, children⟩).1 =
      M.imageRuleLift H occurrence children ≫ H.map (M.foldOperation _
        (ruleTree R equations occurrence.index occurrence.ambient)) := by
  have forward := Hom.rule_value (M.targetModelIso H).hom occurrence children
  rw [M.targetModelIso_hom_event H] at forward
  have cancellation :
      ((((M.targetModel H).rules Z).act () (conclusionJudgment R _ occurrence)
        ⟨⟨occurrence, rfl⟩, children⟩).1 ≫
          H.map (M.eventIso occurrence.ambient (R.get occurrence.index).2.conclusion.sort).hom) ≫
            H.map (M.eventIso occurrence.ambient (R.get occurrence.index).2.conclusion.sort).inv =
        (((M.targetModel H).rules Z).act () (conclusionJudgment R _ occurrence)
          ⟨⟨occurrence, rfl⟩, children⟩).1 :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·)
        (H.mapIso (M.eventIso occurrence.ambient (R.get occurrence.index).2.conclusion.sort)).hom_inv_id).trans
          (Category.comp_id _))
  exact cancellation.symm.trans
    ((congrArg
      (· ≫ H.map (M.eventIso occurrence.ambient (R.get occurrence.index).2.conclusion.sort).inv)
      forward).trans (M.postcompose_rule_freeFold H occurrence children))

end ActualImageOperations

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
