import Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintCatalog

/-!
# Finite source inputs are recovered from actual MM0 catalog metadata

An accepted source data condition recovers the original argument expressions
and their encoded columns. Admitted declarations bound every gathered
pattern variable by the request arity. The source binding discipline therefore
forces every other assignment slot to be empty.

Consequently the actual source assignment is exactly a finite supplied tuple,
not merely an assignment agreeing on a convenient subset. Sorting and the
constructor-specific data checks are retained in the recovery argument.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintInputNormalization

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport
open MM0Rewriting
open MM0ConstraintCatalog

theorem bounded_encoded_assignment (target : Context) (arguments : List Preterm) :
    RequestActivation.boundedAssignment arguments.length (arguments.map (encode target)) =
      expressionAssignment target arguments := by
  funext index
  by_cases inside : index < arguments.length
  · simp [RequestActivation.boundedAssignment, inside, expressionAssignment]
  · simp [RequestActivation.boundedAssignment, inside, expressionAssignment]

private theorem formals_bounded (arity : Nat) :
    ∀ expression ∈ formals arity, expression.VarsBelow arity := by
  intro expression member
  obtain ⟨index, inside, rfl⟩ := List.mem_map.mp member
  exact List.mem_range.mp inside

theorem request_bounded (width arity : Nat) (name : String) :
    ∀ index ∈ (theoremRequest width arity name).vars, index < arity :=
  judgmentPattern_vars_below width arity (requestTag name) (formals arity) (formals_bounded arity)

theorem premises_bounded {theory : Theory} (wellFormed : theory.WellFormed)
    (target : Context) (key : RuleKey) {schema : Schema}
    (compiled : schemaFor theory target key = some schema) :
    ∀ pattern ∈ schema.premises, ∀ index ∈ pattern.vars, index < schema.arity := by
  cases key with
  | theorem_ index =>
      obtain ⟨declaration, known, rfl⟩ := Option.map_eq_some_iff.mp compiled
      intro pattern member
      obtain ⟨expression, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨_, _, typed, _, _⟩ := (wellFormed.theorems _ _ known).hypotheses expression present
      exact judgmentPattern_vars_below target.length declaration.arguments.length "pf" [expression]
        (by simpa using typed.varsBelow)
  | basic kind sort =>
      have same : basicSchema theory.termSignature target kind sort = schema := Option.some.inj compiled
      subst schema
      simpa [basicSchema, argumentSchema, regularFormals] using kind.premises_bounded target.length sort
  | congruence symbol =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact congruencePremises_bounded target.length
        (declaration.arguments.length + declaration.arguments.length) declaration.arguments
        0 declaration.arguments.length (by omega) (by omega)
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
              simp [unfoldingSchema, guardedSchema]

theorem gathers_bounded {theory : Theory} (wellFormed : theory.WellFormed)
    (target : Context) (key : RuleKey) {schema : Schema}
    (compiled : schemaFor theory target key = some schema) :
    ∀ pattern ∈ (schema.requestRecipe target key.name).matchingRule.take ++
      (schema.requestRecipe target key.name).matchingRule.read,
      ∀ index ∈ pattern.vars, index < schema.arity := by
  intro pattern member
  rcases (show pattern = theoremRequest target.length schema.arity key.name ∨ pattern ∈ schema.premises from by
    simpa [Schema.requestRecipe, RequestActivation.Recipe.matchingRule,
      GuardedMultisetRewriting.requestRule] using member) with rfl | member
  · exact request_bounded target.length schema.arity key.name
  · exact premises_bounded wellFormed target key compiled pattern member

private theorem admitted_columns (signature : TermSignature) (formal target : Context)
    (assignment : Subst Nat Tm) (accepted : (admitArguments signature formal target assignment).isSome = true) :
    ∃ arguments, arguments.length = formal.length ∧
      ∀ index < formal.length, assignment index = expressionAssignment target arguments index := by
  obtain ⟨arguments, recovered⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨admissible, columns⟩ := (admitArguments_iff _ _ _ _ _).mp recovered
  exact ⟨arguments, admissible.length_eq, columns⟩

private theorem checked_columns (target : Context) (arity : Nat) (check : List Preterm → Bool)
    (assignment : Subst Nat Tm) (accepted : (checkedArguments target arity check assignment).isSome = true) :
    ∃ arguments, arguments.length = arity ∧
      ∀ index < arity, assignment index = expressionAssignment target arguments index := by
  obtain ⟨arguments, recovered⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨count, _, columns⟩ := (checkedArguments_iff _ _ _ _ _).mp recovered
  exact ⟨arguments, count, columns⟩

theorem data_arguments (theory : Theory) (target : Context) (key : RuleKey) {schema : Schema}
    (compiled : schemaFor theory target key = some schema) (assignment : Subst Nat Tm)
    (accepted : schema.dataCondition assignment = true) :
    ∃ arguments, arguments.length = schema.arity ∧
      ∀ index < schema.arity, assignment index = expressionAssignment target arguments index := by
  cases key with
  | theorem_ index =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact admitted_columns theory.termSignature declaration.arguments target assignment accepted
  | basic kind sort =>
      have same : basicSchema theory.termSignature target kind sort = schema := Option.some.inj compiled
      subst schema
      exact admitted_columns theory.termSignature (regularFormals kind.arity sort) target assignment accepted
  | congruence symbol =>
      obtain ⟨declaration, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
      exact checked_columns target (declaration.arguments.length + declaration.arguments.length)
        (congruenceCheck theory.termSignature target declaration) assignment accepted
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
              exact checked_columns target (declaration.arguments.length + body.dummies.length)
                (unfoldingCheck theory.termSignature target declaration body) assignment accepted

/-- The exact finite input tuple is derived from data admission and the
real source gather-variable bounds, including emptiness outside its arity. -/
theorem assignment_is_finite_input {theory : Theory} (wellFormed : theory.WellFormed)
    (target : Context) (key : RuleKey) {schema : Schema}
    (compiled : schemaFor theory target key = some schema) (assignment : Subst Nat Tm)
    (accepted : schema.dataCondition assignment = true)
    (bindings : GuardedMultisetRewriting.BindsOnlyGathers ContextualPatterns.layer
      (schema.requestRecipe target key.name).matchingRule assignment) :
    ∃ values, assignment = RequestActivation.boundedAssignment schema.arity values := by
  obtain ⟨arguments, count, columns⟩ := data_arguments theory target key compiled assignment accepted
  refine ⟨arguments.map (encode target), ?_⟩
  rw [← count, bounded_encoded_assignment]
  funext index
  by_cases inside : index < schema.arity
  · exact columns index inside
  · have unbound : assignment index = none := bindings index (by
      intro pattern member occurs
      exact inside (gathers_bounded wellFormed target key compiled pattern member index occurs))
    rw [unbound]
    simp [expressionAssignment, List.getElem?_eq_none (by omega : arguments.length ≤ index)]

end Mettapedia.Logic.TierZero.Adequacy.MM0ConstraintInputNormalization
