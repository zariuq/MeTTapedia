import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedCatalogActivation
import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintReaches

/-!
# Natural scoped MM0 requests execute on ordinary constraint steps

The runtime firing relation selects an installed catalog key and executes
its natural activation with decoded finite argument expressions. Theorem and
basic-conversion activation actually constructs restricted contextual bodies.
The original constructor, definition and dummy checks remain in their own
schemes.

Valid firings coincide with the qualified compatibility profile, retaining
the entire ordinary rule instance, physical step and equation store. This
transports full-catalog reachability adequacy to natural scoped activation.
Publication authority and executable/native refinement remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedProcess

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog
open MM0ConstraintInputNormalization
open MM0ScopedCatalogActivation
open MM0ConstraintTheoremApplication (falseHead trueHead boolean_heads_distinct)

variable {O : Type*} [DecidableEq O]

def Fires (theory : Theory) (target : Context) (keys : List RuleKey)
    (label : O → Tm) (before after : Configuration Tm O) : Prop :=
  ∃ key ∈ keys, ∃ expressions rule, activate theory target key expressions = some rule ∧
    Step (MM0ConstraintParameters.action target) label rule before after

theorem firing_to_compatibility {sorts : SortSignature} {theory : Theory} {target : Context}
    (formed : Context.WellFormed sorts target) {keys : List RuleKey} {label : O → Tm}
    {before after : Configuration Tm O} (fired : Fires theory target keys label before after) :
    MM0ConstraintProcess.Fires theory target keys label before after := by
  obtain ⟨key, installed, expressions, rule, computed, stepped⟩ := fired
  have compatible := natural_reflects_compatibility theory target formed key expressions computed
  cases compiled : schemaFor theory target key with
  | none => simp [compatibilityActivate, compiled] at compatible
  | some schema =>
      simp only [compatibilityActivate, compiled, Option.bind_eq_bind, Option.bind_some] at compatible
      split at compatible
      · rename_i count
        refine ⟨key, installed, schema, compiled, expressions.map (encode target), rule, ?_, stepped⟩
        rw [← count, bounded_encoded_assignment]
        exact compatible
      · cases compatible

theorem compatibility_to_firing {sorts : SortSignature} {theory : Theory} {target : Context}
    (formed : Context.WellFormed sorts target) {keys : List RuleKey} {label : O → Tm}
    {before after : Configuration Tm O}
    (fired : MM0ConstraintProcess.Fires theory target keys label before after) :
    Fires theory target keys label before after := by
  obtain ⟨key, installed, schema, compiled, values, rule, computed, picked, valid, destination⟩ := fired
  have accepted := RequestActivation.condition_of_valid ContextualPatterns.layer falseHead trueHead boolean_heads_distinct
    target.length (schema.requestRecipe target key.name) (RequestActivation.boundedAssignment schema.arity values) computed valid
  obtain ⟨expressions, count, columns⟩ := data_arguments theory target key compiled
    (RequestActivation.boundedAssignment schema.arity values) accepted
  have assignmentEqual : RequestActivation.boundedAssignment schema.arity values = expressionAssignment target expressions := by
    funext index
    by_cases inside : index < schema.arity
    · exact columns index inside
    · simp [RequestActivation.boundedAssignment, inside, expressionAssignment,
        List.getElem?_eq_none (by omega : expressions.length ≤ index)]
  have compatible : compatibilityActivate theory target key expressions = some rule := by
    simp only [compatibilityActivate, compiled, Option.bind_eq_bind, Option.bind_some]
    rw [if_pos count, ← assignmentEqual]
    exact computed
  exact ⟨key, installed, expressions, rule,
    valid_compatibility_has_natural_activation theory target formed key expressions compatible valid,
    picked, valid, destination⟩

theorem fires_iff_compatibility {sorts : SortSignature} {theory : Theory} {target : Context}
    (formed : Context.WellFormed sorts target) {keys : List RuleKey} {label : O → Tm}
    {before after : Configuration Tm O} :
    Fires theory target keys label before after ↔ MM0ConstraintProcess.Fires theory target keys label before after :=
  ⟨firing_to_compatibility formed, compatibility_to_firing formed⟩

theorem run_iff_compatibility {sorts : SortSignature} {theory : Theory} {target : Context}
    (formed : Context.WellFormed sorts target) {keys : List RuleKey} {label : O → Tm}
    {before after : Configuration Tm O} :
    Relation.ReflTransGen (Fires theory target keys label) before after ↔
      Relation.ReflTransGen (MM0ConstraintProcess.Fires theory target keys label) before after := by
  constructor
  · intro run
    induction run with
    | refl => exact .refl
    | tail prior fired earlier => exact earlier.tail (firing_to_compatibility formed fired)
  · intro run
    induction run with
    | refl => exact .refl
    | tail prior fired earlier => exact earlier.tail (compatibility_to_firing formed fired)

/-- The acceptance relation executes natural activation, not the compatibility
relation or independent derivability in disguise. -/
def Reaches (theory : Theory) (target : Context) (hypotheses : List Preterm) (expression : Preterm) : Prop :=
  ∃ (requests : List RequestPacket) (before after : Configuration Tm MM0ConstraintReaches.Occurrence),
    before.equations = [] ∧
    labels MM0ConstraintReaches.label before.present = requestBag requests + hypothesisBag target hypotheses ∧
    Relation.ReflTransGen (Fires theory target (catalog theory) MM0ConstraintReaches.label) before after ∧
    proofValue target expression ∈ labels MM0ConstraintReaches.label after.present

theorem reaches_iff_compatibility {sorts : SortSignature} {theory : Theory} {target : Context}
    (formed : Context.WellFormed sorts target) (hypotheses : List Preterm) (expression : Preterm) :
    Reaches theory target hypotheses expression ↔ MM0ConstraintReaches.Reaches theory target hypotheses expression := by
  constructor
  · rintro ⟨requests, before, after, emptyEquations, initial, run, published⟩
    exact ⟨requests, before, after, emptyEquations, initial, (run_iff_compatibility formed).mp run, published⟩
  · rintro ⟨requests, before, after, emptyEquations, initial, run, published⟩
    exact ⟨requests, before, after, emptyEquations, initial, (run_iff_compatibility formed).mpr run, published⟩

theorem scoped_reaches_iff_derives {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    Reaches theory target hypotheses expression ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression :=
  (reaches_iff_compatibility formed hypotheses expression).trans
    (MM0ConstraintReaches.constraint_reaches_iff_derives wellFormed formed hypotheses expression)

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedProcess
