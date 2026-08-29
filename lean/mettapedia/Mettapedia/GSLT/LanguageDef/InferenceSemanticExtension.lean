import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Semantic validation of inference-definition extensions

Structural validation says that a learned rule is a well-formed rule schema.
It does not say that the rule is true in an independently chosen semantics.
This module supplies the missing compositional boundary.

A `SemanticExtension` contains soundness for the base definition and a
separate proof for every genuinely added rule.  The generic derivation checker
then inherits soundness for the composite definition.  Old derivations still
transport through the ordinary definition-extension theorem; no learned
rule can create semantic truth merely by being syntactically admissible.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-- Independent semantic validation of a structurally validated extension.

The new-rule field exposes the exact stored schema and every premise needed
to establish its instantiated conclusion.  Consequently its proof cannot be
obtained merely from the target checker's acceptance result. -/
structure SemanticExtension (base : ValidatedCalculusLanguageDef)
    (extension : ValidatedCalculusLanguageExtension base) (meaning : Pattern → Prop) where
  baseRuleSound : ∀ ruleInstance premises conclusion,
    RuleApplication base ruleInstance premises conclusion →
      (∀ premise ∈ premises, meaning premise) → meaning conclusion
  addedRuleSound : ∀ (rule : RuleSchema),
    rule ∈ extension.extension.newRules →
      ∀ (ruleInstance : RuleInstance) (premises : List Pattern)
        (conclusion : Pattern),
        extension.target.1.lookupRule? ruleInstance.ruleId = some rule →
        argumentsValidAt rule.metavariables ruleInstance.arguments = true →
        RuleSchema.sideConditionsHold rule ruleInstance.arguments = true →
        InstantiatesList rule.metavariables ruleInstance.arguments
          rule.premises premises →
        Instantiates rule.metavariables ruleInstance.arguments
          rule.conclusion conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion

namespace SemanticExtension

variable {base : ValidatedCalculusLanguageDef}
variable {extension : ValidatedCalculusLanguageExtension base}
variable {meaning : Pattern → Prop}

/-- Every rule used by the target definition is either an exact base rule
or an exact member of the extension delta. -/
theorem target_application_classifies
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application :
      RuleApplication extension.target ruleInstance premises conclusion) :
    RuleApplication base ruleInstance premises conclusion ∨
      ∃ rule,
        rule ∈ extension.extension.newRules ∧
          extension.target.1.lookupRule? ruleInstance.ruleId = some rule := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have memberTarget : rule ∈ extension.target.1.rules :=
        List.mem_of_find?_eq_some lookup
      have memberComposite :
          rule ∈ base.1.rules ++ extension.extension.newRules := by
        simpa [ValidatedCalculusLanguageExtension.target, CalculusLanguageExtension.apply] using
          memberTarget
      rcases List.mem_append.mp memberComposite with memberBase | memberAdded
      · left
        have ruleIdEq : rule.id = ruleInstance.ruleId := by
          apply of_decide_eq_true
          exact List.find?_some
            (p := fun candidate : RuleSchema =>
              decide (candidate.id = ruleInstance.ruleId))
            (a := rule) (l := extension.target.1.rules) (by
              simpa only [CalculusLanguageDef.lookupRule?] using lookup)
        exact .intro rule (by
          simpa only [← ruleIdEq] using
            lookupRule?_eq_some_of_mem base memberBase)
          argumentsValid sideConditionsValid premisesInstantiate
          conclusionInstantiates
      · right
        exact ⟨rule, memberAdded, lookup⟩

/-- The independent base and learned-rule proofs combine into one local
soundness theorem for the composite definition. -/
theorem targetRuleSound (self : SemanticExtension base extension meaning) :
    ∀ ruleInstance premises conclusion,
      RuleApplication extension.target ruleInstance premises conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion := by
  intro ruleInstance premises conclusion application premisesMeaning
  rcases target_application_classifies application with baseApplication |
      ⟨rule, memberAdded, lookup⟩
  · exact self.baseRuleSound ruleInstance premises conclusion
      baseApplication premisesMeaning
  · cases application with
    | intro actualRule actualLookup argumentsValid sideConditionsValid
        premisesInstantiate conclusionInstantiates =>
        have ruleEq : actualRule = rule := by
          rw [actualLookup] at lookup
          exact Option.some.inj lookup
        subst rule
        exact self.addedRuleSound actualRule memberAdded ruleInstance
          premises conclusion actualLookup argumentsValid sideConditionsValid
          premisesInstantiate conclusionInstantiates premisesMeaning

/-- A checked proof in the learned definition has the independently stated
meaning.  This is the theorem that turns structural replay plus per-rule
semantics into a sound learned theory. -/
theorem derivation_sound (self : SemanticExtension base extension meaning)
    {goal : Pattern} (derivation : Derivation extension.target goal) :
    meaning goal :=
  derivation.sound_of_ruleApplications meaning self.targetRuleSound

/-- Positive control: old proofs preserve both their exact derivation and
their independent meaning after learning. -/
theorem transported_derivation_sound
    (self : SemanticExtension base extension meaning)
    {goal : Pattern} (derivation : Derivation base goal) :
    meaning goal :=
  self.derivation_sound (extension.transport derivation)

/-- Negative control: if a structurally checked target proof concludes a
semantic counterexample, no `SemanticExtension` can exist for that proposed
delta.  Structural validation therefore cannot launder a false learned rule. -/
theorem no_semantic_extension_of_counterexample
    {goal : Pattern} (derivation : Derivation extension.target goal)
    (counterexample : ¬ meaning goal) :
    ¬ Nonempty (SemanticExtension base extension meaning) := by
  rintro ⟨semanticExtension⟩
  exact counterexample (semanticExtension.derivation_sound derivation)

end SemanticExtension

end Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension
