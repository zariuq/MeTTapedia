import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

/-!
# The exact physical selection retained by request activation

Successful activation of an actual source receipt validates that receipt's
own take/read/output lists. This strengthens the existing existential step
interface without selecting a different firing or introducing an evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MatchingReceiptSelection

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open RequestActivation

variable {V Head P : Type} {O : Type*} [DecidableEq O]

theorem valid (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead) (width : Nat)
    (recipe : Recipe V Head P) (label : O → Term Head) (before : Configuration (Term Head) O)
    (receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head))
    (qualified : receipt.ValidAt layer recipe.matchingRule label before.present)
    (background : (ABTProtectedParameters.action width).Consistent before.equations)
    {rule : RuleInstance (Term Head)}
    (computed : activate layer falseHead trueHead recipe receipt.assignment = some rule) :
    (physicalSelection receipt).Valid (ABTProtectedParameters.action width) label rule before := by
  obtain ⟨request, premises, conclusion, requestInstance, readInstances, outputInstance, rfl⟩ :=
    (activate_iff layer falseHead trueHead recipe receipt.assignment rule).mp computed
  have takeMatch := instTemplate_of_matches layer structural receipt.assignment qualified.takesMatch
  have takeValues : [request] = receipt.takes.map label := by
    simpa [Recipe.matchingRule, GuardedMultisetRewriting.requestRule, instTemplate, requestInstance] using takeMatch
  have readMatch := instTemplate_of_matches layer structural receipt.assignment qualified.readsMatch
  have readValues : premises = receipt.reads.map label := Option.some.inj (readInstances.symm.trans readMatch)
  have outputValues : [conclusion] = receipt.outputs.map label := by
    simpa [Recipe.matchingRule, GuardedMultisetRewriting.requestRule, instTemplate, outputInstance] using qualified.makes
  have checked : recipe.dataCondition receipt.assignment = true :=
    qualified.checks_hold ⟨recipe.request, fun assignment _ => recipe.dataCondition assignment = true⟩
      (by simp [Recipe.matchingRule, GuardedMultisetRewriting.requestRule])
  refine ⟨qualified.uniqueTakes, qualified.uniqueOutputs, ?_, ?_, outputValues.symm,
    ⟨qualified.takesPresent, qualified.readsPresent, qualified.apart, qualified.fresh,
      by simp [Selection.commit]⟩, ?_, ?_⟩
  · simpa [fromValues, physicalSelection, Recipe.matchingRule,
      GuardedMultisetRewriting.requestRule] using qualified.takesMatch.length_eq
  · simpa [fromValues, physicalSelection] using congrArg List.length readValues
  · obtain ⟨candidate, models⟩ := background
    refine ⟨candidate, ?_⟩
    change (ABTProtectedParameters.action width).Models candidate
      (before.equations ++ Selection.equations label [request] receipt.takes ++
        Selection.equations label premises receipt.reads ++ [])
    simp only [SubstitutionAction.models_append, SubstitutionAction.models_nil, and_true]
    rw [takeValues, readValues]
    exact ⟨⟨models, self_equations _ candidate label receipt.takes⟩,
      self_equations _ candidate label receipt.reads⟩
  · intro query member candidate _
    have same : query = ABTDataChecks.check falseHead trueHead (recipe.dataCondition receipt.assignment) := by
      simpa [fromValues] using member
    subst query
    exact (ABTDataChecks.holds_iff falseHead trueHead distinct width _ candidate label before.present).mpr checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MatchingReceiptSelection
