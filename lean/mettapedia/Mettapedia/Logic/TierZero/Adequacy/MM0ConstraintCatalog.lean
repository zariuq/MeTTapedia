import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintTheoremApplication

/-!
# Source-origin activation of the complete MM0 rule-key catalog

Every rule key produces finite request metadata from the same admitted theory
as the source catalog: theorem application, the four basic conversion schemes,
constructor congruence and definition unfolding. Their actual data computations
are retained. Activation forms ordinary constraint rule instances.

This module supplies the catalog and its exact source origin. It does not
identify source matching with raw constraint states, prove search completeness,
or grant theorem-space publication authority.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintCatalog

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting

structure Schema where
  arity : Nat
  premises : List Pat
  conclusion : Pat
  dataCondition : Subst Nat Tm → Bool

def Schema.requestRecipe (schema : Schema) (target : Context) (name : String) :
    RequestActivation.Recipe Nat Head Pat where
  request := theoremRequest target.length schema.arity name
  premises := schema.premises
  conclusion := schema.conclusion
  dataCondition := schema.dataCondition

def argumentSchema (signature : TermSignature) (target formal : Context)
    (premises : List Pat) (conclusion : Pat) : Schema :=
  ⟨formal.length, premises, conclusion, fun assignment => (admitArguments signature formal target assignment).isSome⟩

def guardedSchema (target : Context) (arity : Nat) (check : List Preterm → Bool)
    (premises : List Pat) (conclusion : Pat) : Schema :=
  ⟨arity, premises, conclusion, fun assignment => (checkedArguments target arity check assignment).isSome⟩

def theoremSchema (signature : TermSignature) (target : Context) (declaration : TheoremDecl) : Schema :=
  argumentSchema signature target declaration.arguments
    (declaration.hypotheses.map (proofPattern target.length)) (proofPattern target.length declaration.conclusion)

def basicSchema (signature : TermSignature) (target : Context) (kind : BasicConversion) (sort : Nat) : Schema :=
  argumentSchema signature target (regularFormals kind.arity sort)
    (kind.premises target.length sort) (kind.conclusion target.length sort)

def congruenceSchema (signature : TermSignature) (target : Context) (symbol : Nat) (declaration : TermDecl) : Schema :=
  guardedSchema target (declaration.arguments.length + declaration.arguments.length)
    (congruenceCheck signature target declaration)
    (congruencePremises target.length 0 declaration.arguments.length declaration.arguments)
    (conversionPattern target.length declaration.resultSort
      (Preterm.applyArgs (.term symbol) (argumentSpine 0 declaration.arguments.length))
      (Preterm.applyArgs (.term symbol) (argumentSpine declaration.arguments.length declaration.arguments.length)))

def unfoldingSchema (signature : TermSignature) (target : Context) (symbol : Nat)
    (declaration : TermDecl) (body : Definition.Body) : Schema :=
  guardedSchema target (declaration.arguments.length + body.dummies.length)
    (unfoldingCheck signature target declaration body) []
    (conversionPattern target.length declaration.resultSort
      (Preterm.applyArgs (.term symbol) (argumentSpine 0 declaration.arguments.length)) body.expression)

def schemaFor (theory : Theory) (target : Context) (key : RuleKey) : Option Schema :=
  match key with
  | .theorem_ index => (theory.theoremSignature index).map (theoremSchema theory.termSignature target)
  | .basic kind sort => some (basicSchema theory.termSignature target kind sort)
  | .congruence symbol => (theory.termSignature symbol).map (congruenceSchema theory.termSignature target symbol)
  | .unfolding symbol => do
      let declaration ← theory.termSignature symbol
      let body ← theory.definitionSignature symbol
      return unfoldingSchema theory.termSignature target symbol declaration body

/-- The origin equation checks the actual executable catalog constructors;
it is not an independent assertion that a supplied instance was admitted. -/
theorem schemaFor_origin (theory : Theory) (target : Context) (key : RuleKey) :
    (schemaFor theory target key).map (fun schema => (schema.requestRecipe target key.name).matchingRule) =
      ruleFor theory target key := by
  cases key with
  | theorem_ index =>
      cases known : theory.theoremSignature index <;> simp only [schemaFor, ruleFor, known] <;> rfl
  | basic kind sort => rfl
  | congruence symbol =>
      cases known : theory.termSignature symbol <;> simp only [schemaFor, ruleFor, known] <;> rfl
  | unfolding symbol =>
      cases known : theory.termSignature symbol <;> cases defined : theory.definitionSignature symbol <;>
        simp only [schemaFor, ruleFor, known, defined] <;> rfl

theorem compiled_schema_origin (theory : Theory) (target : Context) (key : RuleKey)
    {schema : Schema} (compiled : schemaFor theory target key = some schema) :
    ruleFor theory target key = some (schema.requestRecipe target key.name).matchingRule := by
  rw [← schemaFor_origin theory target key, compiled]
  rfl

theorem source_rule_has_schema (theory : Theory) (target : Context) (key : RuleKey)
    {rule : GuardedMultisetRewriting.Rule Nat Tm Pat} (compiled : ruleFor theory target key = some rule) :
    ∃ schema, schemaFor theory target key = some schema ∧
      (schema.requestRecipe target key.name).matchingRule = rule := by
  rw [← schemaFor_origin theory target key] at compiled
  exact Option.map_eq_some_iff.mp compiled

def Schema.Scoped (schema : Schema) (width : Nat) : Prop :=
  (∀ pattern ∈ schema.premises, pattern.scope = width) ∧ schema.conclusion.scope = width

private theorem congruencePremises_scoped (width : Nat) (binders : Context) :
    ∀ left right pattern, pattern ∈ congruencePremises width left right binders → pattern.scope = width := by
  induction binders with
  | nil => simp [congruencePremises]
  | cons binder binders earlier =>
      intro left right pattern member
      rcases (show pattern = conversionPattern width binder.sort (.var left) (.var right) ∨
          pattern ∈ congruencePremises width (left + 1) (right + 1) binders from by
        simpa [congruencePremises] using member) with rfl | member
      · rfl
      · exact earlier (left + 1) (right + 1) pattern member

theorem schemaFor_scoped (theory : Theory) (target : Context) (key : RuleKey)
    {schema : Schema} (compiled : schemaFor theory target key = some schema) :
    schema.Scoped target.length := by
  cases key with
  | theorem_ index =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      refine ⟨?_, rfl⟩
      intro pattern member
      obtain ⟨expression, _, rfl⟩ := List.mem_map.mp member
      rfl
  | basic kind sort =>
      have same : basicSchema theory.termSignature target kind sort = schema := Option.some.inj compiled
      subst schema
      cases kind <;> constructor
      all_goals first | rfl | intro pattern member
      all_goals simp only [basicSchema, argumentSchema, BasicConversion.premises, List.mem_cons,
        List.not_mem_nil, or_false] at member
      all_goals rcases member with rfl | rfl <;> rfl
  | congruence symbol =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact ⟨congruencePremises_scoped target.length declaration.arguments 0 declaration.arguments.length, rfl⟩
  | unfolding symbol =>
      cases known : theory.termSignature symbol with
      | none => simp [schemaFor, known] at compiled
      | some declaration =>
          cases defined : theory.definitionSignature symbol with
          | none => simp [schemaFor, known, defined] at compiled
          | some body =>
              have same : unfoldingSchema theory.termSignature target symbol declaration body = schema := by
                simpa [schemaFor, known, defined] using compiled
              subst schema
              exact ⟨by simp [unfoldingSchema, guardedSchema], rfl⟩

theorem templates_fixed (theory : Theory) (target : Context) (key : RuleKey)
    {schema : Schema} (compiled : schemaFor theory target key = some schema) (assignment : Subst Nat Tm) :
    ∀ pattern ∈ (schema.requestRecipe target key.name).request ::
      (schema.requestRecipe target key.name).premises ++ [(schema.requestRecipe target key.name).conclusion],
      ∀ value, ContextualPatterns.layer.inst assignment pattern = some value →
        FixedMatching.Fixed (MM0ConstraintParameters.action target) value := by
  have scopedSchema := schemaFor_scoped theory target key compiled
  intro pattern member value instantiated
  have scope : pattern.scope = target.length := by
    simp only [Schema.requestRecipe, List.mem_cons, List.mem_append] at member
    rcases member with (rfl | member) | (rfl | impossible)
    · rfl
    · exact scopedSchema.1 pattern member
    · exact scopedSchema.2
    · cases impossible
  apply ABTProtectedParameters.fixed_of_supported
  have supported := ContextualPatterns.Pattern.inst_supported instantiated
  rw [scope] at supported
  exact supported

theorem bounded_arguments_bind_only_the_request (target : Context) (name : String)
    (schema : Schema) (values : List Tm) :
    GuardedMultisetRewriting.BindsOnlyGathers ContextualPatterns.layer
      (schema.requestRecipe target name).matchingRule
      (RequestActivation.boundedAssignment schema.arity values) := by
  apply RequestActivation.boundedAssignment_binds
  intro index inside
  exact theoremRequest_contains_formal target.length schema.arity name index inside

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintCatalog
