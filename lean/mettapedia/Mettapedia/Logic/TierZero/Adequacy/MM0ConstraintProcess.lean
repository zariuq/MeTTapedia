import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintCatalog

/-!
# Actual MM0 catalog firings on the two-sided constraint step

A firing selects an installed rule key, obtains its source metadata, supplies
a finite argument tuple, and activates an ordinary constraint rule instance.
Its definition contains neither a source rewriting step nor MM0 derivability.

Any finite run resolves at one model of its final retained equation store to
an actual source-catalog run. Therefore it preserves independent MM0 validity
at that observation. This is the soundness direction of a compatibility
profile; occurrence-complete run construction and authority-preserving schema
installation are not established here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintProcess

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog
open MM0ConstraintTheoremApplication (falseHead trueHead boolean_heads_distinct)

variable {O : Type*} [DecidableEq O]

def Fires (theory : Theory) (target : Context) (keys : List RuleKey)
    (label : O → Tm) (before after : Configuration Tm O) : Prop :=
  ∃ key ∈ keys, ∃ schema, schemaFor theory target key = some schema ∧
    ∃ values rule, RequestActivation.activate ContextualPatterns.layer falseHead trueHead
        (schema.requestRecipe target key.name)
        (RequestActivation.boundedAssignment schema.arity values) = some rule ∧
      Step (MM0ConstraintParameters.action target) label rule before after

theorem firing_refines {theory : Theory} {target : Context} {keys : List RuleKey}
    {label : O → Tm} {before after : Configuration Tm O}
    (fired : Fires theory target keys label before after) :
    (MM0ConstraintParameters.action target).Refines after.equations before.equations := by
  obtain ⟨_, _, _, _, _, _, _, stepped⟩ := fired
  exact stepped.refines

theorem firing_consistent {theory : Theory} {target : Context} {keys : List RuleKey}
    {label : O → Tm} {before after : Configuration Tm O}
    (fired : Fires theory target keys label before after) :
    (MM0ConstraintParameters.action target).Consistent after.equations := by
  obtain ⟨_, _, _, _, _, _, _, stepped⟩ := fired
  exact stepped.consistent

theorem firing_resolves {theory : Theory} {target : Context} {keys : List RuleKey}
    {label : O → Tm} {before after : Configuration Tm O}
    (fired : Fires theory target keys label before after)
    (candidate : ABTProtectedParameters.Assignment Head target.length)
    (models : (MM0ConstraintParameters.action target).Models candidate after.equations) :
    (process theory target keys).Step
      (labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present)
      (labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) after.present) := by
  obtain ⟨key, installed, schema, compiled, values, rule, computed, picked, valid, rfl⟩ := fired
  apply process_step_of_key theory target keys installed (compiled_schema_origin theory target key compiled)
  exact RequestResolution.resolved_step_of_valid ContextualPatterns.layer rfl falseHead trueHead
    boolean_heads_distinct target.length (schema.requestRecipe target key.name)
    (RequestActivation.boundedAssignment schema.arity values) computed
    (bounded_arguments_bind_only_the_request target key.name schema values)
    (templates_fixed theory target key compiled _) valid candidate models

theorem firing_preserves {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm)
    {keys : List RuleKey} {label : O → Tm} {before after : Configuration Tm O}
    (fired : Fires theory target keys label before after)
    (candidate : ABTProtectedParameters.Assignment Head target.length)
    (models : (MM0ConstraintParameters.action target).Models candidate after.equations)
    (incoming : ∀ value ∈ labels (fun occurrence =>
      (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value) :
    ∀ value ∈ labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) after.present,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value :=
  process_step_preserves wellFormed formed hypotheses keys incoming (firing_resolves fired candidate models)

theorem run_refines {theory : Theory} {target : Context} {keys : List RuleKey}
    {label : O → Tm} {before after : Configuration Tm O}
    (run : Relation.ReflTransGen (Fires theory target keys label) before after) :
    (MM0ConstraintParameters.action target).Refines after.equations before.equations := by
  induction run with
  | refl => exact (MM0ConstraintParameters.action target).refines_refl _
  | tail prior fired earlier =>
      exact (MM0ConstraintParameters.action target).refines_trans (firing_refines fired) earlier

/-- The one final model interprets every earlier state through refinement;
the observation is not changed independently at each step. -/
theorem run_resolves {theory : Theory} {target : Context} {keys : List RuleKey}
    {label : O → Tm} {before after : Configuration Tm O}
    (run : Relation.ReflTransGen (Fires theory target keys label) before after) :
    ∀ candidate : ABTProtectedParameters.Assignment Head target.length,
      (MM0ConstraintParameters.action target).Models candidate after.equations →
      Relation.ReflTransGen (process theory target keys).Step
        (labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present)
        (labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) after.present) := by
  induction run with
  | refl => intro _ _; exact .refl
  | tail prior fired earlier =>
      intro candidate models
      exact (earlier candidate (firing_refines fired candidate models)).tail
        (firing_resolves fired candidate models)

theorem run_preserves {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm)
    {keys : List RuleKey} {label : O → Tm} {before after : Configuration Tm O}
    (run : Relation.ReflTransGen (Fires theory target keys label) before after)
    (candidate : ABTProtectedParameters.Assignment Head target.length)
    (models : (MM0ConstraintParameters.action target).Models candidate after.equations)
    (incoming : ∀ value ∈ labels (fun occurrence =>
      (MM0ConstraintParameters.action target).apply candidate (label occurrence)) before.present,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value) :
    ∀ value ∈ labels (fun occurrence => (MM0ConstraintParameters.action target).apply candidate (label occurrence)) after.present,
      ValidValue theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses value :=
  process_run_preserves wellFormed formed hypotheses keys incoming (run_resolves run candidate models)

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintProcess
