import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafExtensionFold
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonControls

/-!
# An authored binder-local Lambda firing in the presheaf extension

The extension is evaluated at the actual Boolean model's ordered LamCong
valuation. Its recursive input is an event between two functions of the
lambda-bound variable. The transported constructor returns the model's
original rule action, whose two endpoints remain distinct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (seeds)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.CategoryTheory.PresheafStructuredExtension

universe w u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {R : List (LocalRule S)} {equationsList : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable [HasColimitsOfSize.{0, max w v} D]

namespace CocontinuousInterpretation

/-- Extension at any represented valuation agrees with that valuation's
original event fold, including its individual ordered event inputs. -/
theorem extension_evaluate (M : CategoricalModel R equationsList (D := D))
    {a : Classifier R equationsList} {Z : D} (value : M.StageValuation Z a)
    (j : Judgment (modelAt equationsList a.base))
    (tree : Tree R _ (seeds R _ (events R equationsList a)) j) :
    ((M.valuationsRepresentableBy a).homEquiv.symm value ≫
      ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).hom.app a) ≫
      ((classificationEquivalence.{w, u, v}).functor.obj M).carrier.map
        (embedding.{w, 0, 0, v}.map (rep R equationsList j tree)) ≫
      ((unitIso.{w, 0, 0, v, u}).app M.classifyingFunctor).inv.app
        (eventObject R equationsList j.1 j.2.1) ≫
      (M.eventIso j.1 j.2.1).inv = (value.evaluate j tree).1 := by
  have extension := extension_freeFold_stage M
    ((M.valuationsRepresentableBy a).homEquiv.symm value) j tree
  have folded : (M.valuationsRepresentableBy a).homEquiv.symm value ≫
      M.foldOperation j tree = (value.evaluate j tree).1 := by
    rw [← M.foldOperation_rep]
    simpa only [Category.assoc] using M.classification_rep_evaluate value j tree
  exact extension.trans folded

end CocontinuousInterpretation

namespace PresheafLambdaControl

open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparisonControls
open Mettapedia.OSLF.Binding.LambdaContextualRung (Srt)

/-- The actual presheaf-extension result, read back into the model's
event object through the proved Kan-unit and generic-event isomorphisms. -/
def extensionLamEvent : PUnit ⟶ boolModel.objects.event [] Srt.term :=
  ((boolModel.valuationsRepresentableBy lamObject).homEquiv.symm lamValuation ≫
    ((unitIso.{0, 0, 0, 0, 1}).app boolModel.classifyingFunctor).hom.app lamObject) ≫
    ((CocontinuousInterpretation.classificationEquivalence.{0, 1, 0}).functor.obj
      boolModel).carrier.map (embedding.{0, 0, 0, 0}.map
        (ruleRep lambdaRules noEquations lamIndex [])) ≫
    ((unitIso.{0, 0, 0, 0, 1}).app boolModel.classifyingFunctor).inv.app
      (eventObject lambdaRules noEquations [] Srt.term) ≫
    (boolModel.eventIso [] Srt.term).inv

/-- The authored constructor still requests its premise under one local
binder; the extension does not replace it by a closed event. -/
theorem premise_has_local_binder :
    (childJudgment lambdaRules _ lamOccurrence ⟨0, by decide⟩).1 = [Srt.term] :=
  lam_firing_child_context

/-- The actual extension uses the existing fold at the ordered valuation. -/
theorem extension_lam_evaluate :
    extensionLamEvent =
      (lamValuation.evaluate _ (ruleTree lambdaRules noEquations lamIndex [])).1 := by
  exact CocontinuousInterpretation.extension_evaluate boolModel lamValuation _
    (ruleTree lambdaRules noEquations lamIndex [])

/-- Reading the actual extension returns the original LamCong action,
with the same ordered event under its one local binder. -/
theorem extension_lam_rule_action :
    extensionLamEvent =
      ((boolModel.rules PUnit).act () (conclusionJudgment lambdaRules _ lamOccurrence)
        ⟨⟨lamOccurrence, rfl⟩, lamChildren⟩).1 := by
  rw [extension_lam_evaluate]
  have judgment :
      AuthoredPositionedRulePolynomial.mapJudgment
        ((boolModel.stageTarget PUnit).program lamValuation.point)
        (conclusionJudgment lambdaRules _
          (ruleInstance lambdaRules noEquations lamIndex [])) =
        conclusionJudgment lambdaRules _ lamOccurrence :=
    (mapInstance_conclusion lambdaRules
      ((boolModel.stageTarget PUnit).program lamValuation.point)
      (ruleInstance lambdaRules noEquations lamIndex [])).symm.trans
        (congrArg (conclusionJudgment lambdaRules _) lam_program_occurrence_comparison)
  exact eq_of_heq (boolModel.objects.stageEvent_val_heq judgment lam_rule_firing_comparison)

/-- The extension preserves this firing's concrete, unequal endpoints. -/
theorem extension_lam_endpoint_pair :
    extensionLamEvent PUnit.unit = ((fun _ => false), (fun _ => true)) := by
  rw [extension_lam_rule_action]
  exact lam_firing_endpoint_pair

/-- An operational beta/congruence witness remains an event; the extension
does not turn its two program endpoints into an equation. -/
theorem extension_lam_not_diagonal :
    (extensionLamEvent PUnit.unit).1 ≠ (extensionLamEvent PUnit.unit).2 := by
  rw [extension_lam_rule_action]
  exact lam_firing_not_diagonal

end PresheafLambdaControl
end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
