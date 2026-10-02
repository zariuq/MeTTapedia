import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafInterpretation

/-!
# The actual extension evaluates retained operational trees

The generic occurrence is valued by an actual occurrence and each original
ordered premise witness. Its extension evaluates to the implemented rule
action. In clone presheaves that action is the pointwise original local firing.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafFoldComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open IntrinsicScopedLocalPolynomial
open IntrinsicScopedLocalActedClassifier
open IntrinsicScopedLocalActedCategoricalModels
open IntrinsicScopedLocalActedFree (Tree)
open IntrinsicScopedLocalActedFiniteContext (seeds)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.CategoryTheory.PresheafStructuredExtension

universe w u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {R : List (LocalRule S)} {equations : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

section RuleValuation

variable (M : CategoricalModel R equations (D := D))

/-- Reading a generic premise at the actual rule point gives that same ordered premise. -/
theorem rulePoint_child {Z : D} (occurrence : Instance R (M.programModel.stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    mapJudgment ((M.stageTarget Z).program (M.programModel.rulePoint R occurrence))
        (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position) =
      childJudgment R _ occurrence position :=
  (mapInstance_child R _ (ruleInstance R equations occurrence.index occurrence.ambient) position).symm.trans
    (childJudgment_congr R
      (M.programModel.mapInstance_rulePoint R equations M.program.satisfies occurrence)
      position position HEq.rfl)

/-- The actual occurrence and all its ordered retained children value the generic rule object. -/
def ruleValuation {Z : D} (occurrence : Instance R (M.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      M.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    M.StageValuation Z (ruleObject R equations occurrence.index occurrence.ambient) where
  point := M.programModel.rulePoint R occurrence
  event position := (rulePoint_child M occurrence position).symm ▸ children position

/-- Each generic input keeps the original individual ordered event. -/
theorem ruleValuation_event {Z : D} (occurrence : Instance R (M.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      M.objects.StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq ((ruleValuation M occurrence children).event position) (children position) :=
  eqRec_heq _ _

/-- The original free fold at that valuation applies the actual rule algebra. -/
theorem ruleValuation_evaluate {Z : D} (occurrence : Instance R (M.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      M.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    HEq ((ruleValuation M occurrence children).evaluate _
      (ruleTree R equations occurrence.index occurrence.ambient))
      ((M.rules Z).act () (conclusionJudgment R _ occurrence) ⟨⟨occurrence, rfl⟩, children⟩) := by
  apply (ruleValuation M occurrence children).evaluate_ruleTree_of_instance occurrence
    (M.programModel.mapInstance_rulePoint R equations M.program.satisfies occurrence) children
  intro p q same
  cases eq_of_heq same
  exact (ruleValuation_event M occurrence children p).symm

end RuleValuation

section Extension

variable [HasPullbacks D] [HasColimitsOfSize.{0, max w v} D]
variable (M : CategoricalModel R equations (D := D))

/-- The actual Kan extension of a tree representative, read in its retained event object. -/
def extensionEvent {a : Classifier R equations} {Z : D} (value : M.StageValuation Z a)
    (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    Z ⟶ M.objects.event j.1 j.2.1 :=
  ((M.valuationsRepresentableBy a).homEquiv.symm value ≫
    ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.app a) ≫
    (IntrinsicScopedLocalActedPresheaf.modelPresheafExtension.{w} M).map
      (embedding.{w, 0, 0, v}.map (rep R equations j tree)) ≫
    ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).inv.app
      (eventObject R equations j.1 j.2.1) ≫ (M.eventIso j.1 j.2.1).inv

/-- At every semantic stage, the extension is the existing retained-event free fold. -/
theorem extensionEvent_evaluate {a : Classifier R equations} {Z : D}
    (value : M.StageValuation Z a) (j : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    extensionEvent.{w} M value j tree = (value.evaluate j tree).val := by
  have extension := CocontinuousInterpretation.extension_freeFold_stage.{w} M
    ((M.valuationsRepresentableBy a).homEquiv.symm value) j tree
  have folded : (M.valuationsRepresentableBy a).homEquiv.symm value ≫
      M.foldOperation j tree = (value.evaluate j tree).val := by
    rw [← M.foldOperation_rep]
    exact (Category.assoc _ _ _).symm.trans (M.classification_rep_evaluate value j tree)
  exact extension.trans folded

/-- The extension of the actual generic rule representative at an occurrence and its children. -/
def extensionRuleEvent {Z : D} (occurrence : Instance R (M.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      M.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    Z ⟶ M.objects.event occurrence.ambient (R.get occurrence.index).2.conclusion.sort :=
  extensionEvent.{w} M (ruleValuation M occurrence children) _
    (ruleTree R equations occurrence.index occurrence.ambient)

/-- The generic extension uses the actual rule action and the same ordered premise witnesses. -/
theorem extension_rule_action {Z : D} (occurrence : Instance R (M.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      M.objects.StageEvent Z (childJudgment R _ occurrence position)) :
    extensionRuleEvent.{w} M occurrence children =
      ((M.rules Z).act () (conclusionJudgment R _ occurrence) ⟨⟨occurrence, rfl⟩, children⟩).val := by
  have folded := ruleValuation_evaluate M occurrence children
  have endpoints : mapJudgment
      ((M.stageTarget Z).program (ruleValuation M occurrence children).point)
      (conclusionJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient)) =
      conclusionJudgment R _ occurrence :=
    (mapInstance_conclusion R _ (ruleInstance R equations occurrence.index occurrence.ambient)).symm.trans
      (congrArg (conclusionJudgment R _)
        (M.programModel.mapInstance_rulePoint R equations M.program.satisfies occurrence))
  exact (extensionEvent_evaluate.{w} M (ruleValuation M occurrence children) _ _).trans
    (eq_of_heq (M.objects.stageEvent_val_heq endpoints folded))

end Extension

section OperationalPresheaf

open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafCategoricalModel (categoricalModel)
open IntrinsicScopedOperationalPresheafEventFunctions (stageEventEquiv eventFunctionEquiv)
open IntrinsicScopedOperationalPresheafRuleFirings (ruleEvidence pointFire)

variable {A : BindingCloneAlgebra.Algebra.{v} S}
variable (Y : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.{v,v} R A)
variable (satisfies : BindingEquationInterpretation.Satisfies A equations)

/-- Every generalized categorical rule action is the original local model's
pointwise firing with every ordered retained premise. -/
theorem rule_action_at_point {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (categoricalModel R Y equations satisfies).objects.StageEvent Z
        (childJudgment R _ occurrence position))
    (X : IntrinsicScopedConditionalPresheaf.Base A)
    (point : (IntrinsicScopedOperationalPresheafRulePoints.occurrenceStage R occurrence).obj X) :
    (stageEventEquiv Y.toAction Z _
      (((categoricalModel R Y equations satisfies).rules Z).act ()
        (conclusionJudgment R _ occurrence) ⟨⟨occurrence, rfl⟩, children⟩)).val.app X point =
      pointFire R Y occurrence
        (fun position => stageEventEquiv Y.toAction Z _ (children position)) X point :=
  congrArg (fun value => value.val.app X point)
    (IntrinsicScopedOperationalPresheafCategoricalModel.actualStage_rules_comparison
      R Y Z _ ⟨occurrence, rfl⟩ children)

/-- Reading the genuinely extended generic rule uses that same pointwise
original firing, at every clone stage and every ordinary assignment. -/
theorem extension_rule_at_point {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      (categoricalModel R Y equations satisfies).objects.StageEvent Z
        (childJudgment R _ occurrence position))
    (X : IntrinsicScopedConditionalPresheaf.Base A)
    (point : (IntrinsicScopedOperationalPresheafRulePoints.occurrenceStage R occurrence).obj X) :
    (eventFunctionEquiv Y.toAction occurrence.ambient (R.get occurrence.index).2.conclusion.sort Z
      (extensionRuleEvent.{0} (categoricalModel R Y equations satisfies) occurrence children)).app X point =
        pointFire R Y occurrence
          (fun position => stageEventEquiv Y.toAction Z _ (children position)) X point := by
  exact (congrArg (fun event =>
    (eventFunctionEquiv Y.toAction occurrence.ambient (R.get occurrence.index).2.conclusion.sort Z event).app X point)
      (extension_rule_action.{0} (categoricalModel R Y equations satisfies) occurrence children)).trans
    (rule_action_at_point Y satisfies occurrence children X point)

end OperationalPresheaf

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafFoldComparison
