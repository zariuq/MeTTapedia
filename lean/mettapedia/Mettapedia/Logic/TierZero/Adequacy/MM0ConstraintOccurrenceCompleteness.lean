import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintInputNormalization
import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintProcess
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestOccurrenceLifting

/-!
# Constructing actual constraint firings from the source MM0 catalog

The source bag step supplies its own matcher/template evidence and original
data check. Physical occurrence choices are reconstructed, and the actual
source assignment is recovered as a finite argument tuple from admitted
declaration metadata. The resulting firing uses the ordinary two-sided step.

The construction lifts whole finite source runs while retaining the equation
store and reusing a single, fresh-supplying occurrence label map. It does not
derive authority for installing or publishing a rule from this simulation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintOccurrenceCompleteness

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog
open MM0ConstraintInputNormalization
open MM0ConstraintProcess
open MM0ConstraintTheoremApplication (falseHead trueHead boolean_heads_distinct)

variable {O : Type*} [DecidableEq O]

theorem source_firing_lifts {theory : Theory} (wellFormed : theory.WellFormed)
    {target : Context} {keys : List RuleKey} (label : O → Tm) (before : Configuration Tm O)
    (supply : ∀ value : Tm, ∃ occurrence, occurrence ∉ before.present ∧ label occurrence = value)
    (background : (MM0ConstraintParameters.action target).Consistent before.equations)
    {after : Multiset Tm}
    (stepped : (process theory target keys).Step (labels label before.present) after) :
    ∃ final : Configuration Tm O, Fires theory target keys label before final ∧
      labels label final.present = after := by
  obtain ⟨installed, member, sourceStep⟩ := stepped
  obtain ⟨key, keyInstalled, rule, sourceRule, rfl⟩ := (compileRules_member _ _ _ _).mp member
  obtain ⟨schema, compiled, origin⟩ := source_rule_has_schema theory target key sourceRule
  rw [← origin] at sourceStep
  obtain ⟨receipt, valid, destination⟩ := RequestOccurrenceLifting.receipt_of_step ContextualPatterns.layer
    (schema.requestRecipe target key.name) label before.present supply sourceStep
  have accepted : schema.dataCondition receipt.assignment = true :=
    valid.checks_hold ⟨(schema.requestRecipe target key.name).request,
      fun assignment _ => schema.dataCondition assignment = true⟩ (by
        simp [RequestActivation.Recipe.matchingRule, Schema.requestRecipe, GuardedMultisetRewriting.requestRule])
  obtain ⟨values, normal⟩ := assignment_is_finite_input wellFormed target key compiled receipt.assignment accepted valid.binds
  obtain ⟨activated, computed, fired⟩ := RequestActivation.step_of_matching_receipt ContextualPatterns.layer rfl
    falseHead trueHead boolean_heads_distinct target.length (schema.requestRecipe target key.name)
    label before receipt valid background
  refine ⟨(RequestActivation.physicalSelection receipt).result label activated before, ?_, ?_⟩
  · refine ⟨key, keyInstalled, schema, compiled, values, activated, ?_, fired⟩
    rw [← normal]
    exact computed
  · simpa only [Selection.result, RequestActivation.physicalSelection, Selection.commit,
      GuardedMultisetRewriting.FiringReceipt.commit, fire] using destination

theorem run_consistent {theory : Theory} {target : Context} {keys : List RuleKey}
    {label : O → Tm} {before after : Configuration Tm O}
    (run : Relation.ReflTransGen (Fires theory target keys label) before after)
    (background : (MM0ConstraintParameters.action target).Consistent before.equations) :
    (MM0ConstraintParameters.action target).Consistent after.equations := by
  induction run with
  | refl => exact background
  | tail prior fired earlier => exact firing_consistent fired

theorem source_run_lifts {theory : Theory} (wellFormed : theory.WellFormed)
    {target : Context} {keys : List RuleKey} (label : O → Tm)
    (supply : ∀ (world : Finset O) (value : Tm), ∃ occurrence, occurrence ∉ world ∧ label occurrence = value)
    {source destination : Multiset Tm}
    (run : Relation.ReflTransGen (process theory target keys).Step source destination) :
    ∀ before : Configuration Tm O, labels label before.present = source →
      (MM0ConstraintParameters.action target).Consistent before.equations →
      ∃ final : Configuration Tm O, Relation.ReflTransGen (Fires theory target keys label) before final ∧
        labels label final.present = destination := by
  induction run with
  | refl =>
      intro before same _
      exact ⟨before, .refl, same⟩
  | tail prior stepped earlier =>
      intro before same background
      obtain ⟨middle, preceding, middleBag⟩ := earlier before same background
      rw [← middleBag] at stepped
      obtain ⟨final, fired, finalBag⟩ := source_firing_lifts wellFormed label middle (supply middle.present)
        (run_consistent preceding background) stepped
      exact ⟨final, preceding.tail fired, finalBag⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintOccurrenceCompleteness
