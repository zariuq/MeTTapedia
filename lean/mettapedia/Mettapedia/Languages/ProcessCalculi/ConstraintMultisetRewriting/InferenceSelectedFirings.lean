import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceRequestExecution

/-!
# Selected occurrences and source origins of actual inference firings

`SelectedFiring` retains the witnesses already present in the installed
request system's ordinary step: installed schema, supplied inputs, computed
activation, selected physical occurrences, qualification and authority.
It adds no execution rule. Its source origin is recovered from that actual
activation, rather than supplied as an independent logical certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open InferenceSchemaActivation (Tm judgment)
open InferenceSchemaKernel (Space Value locatedAction SourceSchema Inputs)
open InferenceRequestExecution (Occurrence label location payload system postRule)

/-- The occurrence-addressed evidence of one existing native step. -/
structure SelectedFiring (definition : ValidatedCalculusLanguageDef) (actor : Bool)
    (before after : Configuration Value Occurrence) where
  source : SourceSchema Unit
  installed : source ∈ ((system definition).authority.process actor).schemas
  inputs : Inputs Tm
  rule : RuleInstance Value
  computed : (system definition).activate source inputs = some rule
  picked : Selection Occurrence
  qualified : picked.Valid locatedAction label rule before
  formed : PublicationAuthority.Formed
    ((system definition).authority.process actor).rights location picked
  destination : after = picked.result label rule before

namespace SelectedFiring

variable {definition : ValidatedCalculusLanguageDef} {actor : Bool}
  {before after : Configuration Value Occurrence}

/-- Forgetting retained witnesses recovers precisely the original step. -/
theorem ordinary (firing : SelectedFiring definition actor before after) :
    (system definition).Step payload actor before after :=
  ⟨firing.source, firing.installed, firing.inputs, firing.rule, firing.computed,
    firing.picked, firing.qualified, firing.formed, firing.destination⟩

/-- Every actual step has occurrence-addressed evidence. -/
theorem of_step (stepped : (system definition).Step payload actor before after) :
    Nonempty (SelectedFiring definition actor before after) := by
  obtain ⟨source, installed, inputs, rule, computed, picked, qualified,
    formed, destination⟩ := stepped
  exact ⟨⟨source, installed, inputs, rule, computed, picked, qualified,
    formed, destination⟩⟩

/-- An actual server activation retains its ordered source application. -/
structure KernelOrigin (firing : SelectedFiring definition true before after) where
  instance_ : InferenceChecker.RuleInstance
  sourceRule : RuleSchema
  premises : List Pattern
  conclusion : Pattern
  source_eq : firing.source = .inl instance_.ruleId
  inputs_eq : firing.inputs = .inl instance_.arguments
  lookup : definition.1.lookupRule? instance_.ruleId = some sourceRule
  instantiated : instantiateRule? definition instance_ = some (premises, conclusion)
  rule_eq : firing.rule = InferenceSchemaKernel.locate
    (InferenceSchemaActivation.fromResult instance_.ruleId sourceRule
      instance_.arguments premises conclusion)

theorem kernel_origin (firing : SelectedFiring definition true before after) :
    Nonempty firing.KernelOrigin := by
  have installed := firing.installed
  change firing.source ∈ definition.1.rules.map
    (fun rule => (Sum.inl rule.id : SourceSchema Unit)) at installed
  obtain ⟨sourceRule, _, sourceEq⟩ := List.mem_map.mp installed
  have computed := firing.computed
  rw [← sourceEq] at computed
  cases inputsEq : firing.inputs with
  | inr client =>
      simp [InferenceSchemaKernel.System.activate, InferenceSchemaKernel.activation,
        inputsEq] at computed
  | inl arguments =>
      rw [inputsEq] at computed
      change (InferenceSchemaActivation.activate definition sourceRule.id arguments).map
        InferenceSchemaKernel.locate = some firing.rule at computed
      obtain ⟨raw, activated, same⟩ := Option.map_eq_some_iff.mp computed
      obtain ⟨rule, premises, conclusion, lookup, instantiated, rawEq⟩ :=
        InferenceSchemaActivation.origin definition sourceRule.id arguments activated
      exact ⟨⟨⟨sourceRule.id, arguments⟩, rule, premises, conclusion,
        sourceEq.symm, inputsEq, lookup, instantiated,
        same.symm.trans (congrArg InferenceSchemaKernel.locate rawEq)⟩⟩

/-- The generating logical rule is justified by the activation computation. -/
theorem KernelOrigin.application {firing : SelectedFiring definition true before after}
    (origin : firing.KernelOrigin) :
    RuleApplication definition origin.instance_ origin.premises origin.conclusion :=
  instantiateRule?_eq_some_iff_application.mp origin.instantiated

/-- The private client actor posts data; it installs no logical rule. -/
structure ClientOrigin (firing : SelectedFiring definition false before after) where
  value : Tm
  source_eq : firing.source = .inr ()
  inputs_eq : firing.inputs = .inr value
  rule_eq : firing.rule = postRule value

theorem client_origin (firing : SelectedFiring definition false before after) :
    Nonempty firing.ClientOrigin := by
  have sourceEq : firing.source = .inr () := by
    simpa [system] using firing.installed
  have computed := firing.computed
  rw [sourceEq] at computed
  cases inputsEq : firing.inputs with
  | inl arguments =>
      simp [InferenceSchemaKernel.System.activate, InferenceSchemaKernel.activation,
        inputsEq] at computed
  | inr value =>
      have ruleEq : postRule value = firing.rule := by
        simpa [InferenceSchemaKernel.System.activate, InferenceSchemaKernel.activation,
          system, inputsEq] using computed
      exact ⟨⟨value, sourceEq, inputsEq, ruleEq.symm⟩⟩

/-- The native inference package's checks are local source admission data;
its activated physical step has no world-dependent guard. -/
theorem checks_empty (firing : SelectedFiring definition actor before after) :
    firing.rule.checks = [] := by
  cases actor with
  | false =>
      obtain ⟨origin⟩ := firing.client_origin
      rw [origin.rule_eq]
      rfl
  | true =>
      obtain ⟨origin⟩ := firing.kernel_origin
      rw [origin.rule_eq]
      rfl

end SelectedFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedFirings
