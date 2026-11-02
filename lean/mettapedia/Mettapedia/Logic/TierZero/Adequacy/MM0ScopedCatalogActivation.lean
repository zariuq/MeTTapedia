import Mettapedia.Logic.TierZero.Adequacy.MM0ScopedRequestActivation

/-!
# Natural contextual activation in the complete MM0 catalog

Theorem application and basic conversion construct restricted argument bodies
and activate reinterfaced source templates. Congruence and unfolding retain
their distinct original constructor/dummy data conditions; theorem-substitution
independence is not imposed on ordinary constructor application.

Successful natural activation produces the exact ordinary rule instance of
the compatibility profile. Every valid compatibility firing has a natural
activation with that same instance. False data checks do not count as firings.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0ScopedCatalogActivation

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open MM0ContextualSupport
open MM0Rewriting
open MM0ScopedPatterns
open MM0ConstraintCatalog
open MM0ConstraintTheoremApplication (falseHead trueHead boolean_heads_distinct)

def compatibilityActivate (theory : Theory) (target : Context) (key : RuleKey) (expressions : List Preterm) :
    Option (RuleInstance Tm) := do
  let schema ← schemaFor theory target key
  if expressions.length = schema.arity then
    RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      (schema.requestRecipe target key.name) (expressionAssignment target expressions)
  else none

def activate (theory : Theory) (target : Context) (key : RuleKey) (expressions : List Preterm) :
    Option (RuleInstance Tm) :=
  match key with
  | .theorem_ index => do
      let declaration ← theory.theoremSignature index
      MM0ScopedRequestActivation.activate theory.termSignature declaration.arguments target key.name
        (declaration.hypotheses.map (proofPattern target.length))
        (proofPattern target.length declaration.conclusion) expressions
  | .basic kind sort =>
      MM0ScopedRequestActivation.activate theory.termSignature (regularFormals kind.arity sort) target key.name
        (kind.premises target.length sort) (kind.conclusion target.length sort) expressions
  | .congruence _ | .unfolding _ => compatibilityActivate theory target key expressions

private theorem theorem_premises_original (width : Nat) (declaration : TheoremDecl) :
    ∀ pattern ∈ declaration.hypotheses.map (proofPattern width), Ambient width pattern := by
  intro pattern member
  obtain ⟨expression, _, rfl⟩ := List.mem_map.mp member
  exact judgmentPattern_ambient width "pf" [expression]

private theorem basic_premises_original (width sort : Nat) (kind : BasicConversion) :
    ∀ pattern ∈ kind.premises width sort, Ambient width pattern := by
  intro pattern member
  cases kind <;> simp only [BasicConversion.premises, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl <;> exact judgmentPattern_ambient _ _ _

private theorem basic_conclusion_original (width sort : Nat) (kind : BasicConversion) :
    Ambient width (kind.conclusion width sort) := by
  cases kind <;> exact judgmentPattern_ambient _ _ _

theorem natural_reflects_compatibility {sorts : SortSignature} (theory : Theory) (target : Context)
    (formed : Context.WellFormed sorts target) (key : RuleKey) (expressions : List Preterm) {rule : RuleInstance Tm}
    (computed : activate theory target key expressions = some rule) :
    compatibilityActivate theory target key expressions = some rule := by
  cases key with
  | theorem_ index =>
      cases known : theory.theoremSignature index with
      | none => simp [activate, known] at computed
      | some declaration =>
          have natural : MM0ScopedRequestActivation.activate theory.termSignature declaration.arguments target
              (RuleKey.theorem_ index).name (declaration.hypotheses.map (proofPattern target.length))
              (proofPattern target.length declaration.conclusion) expressions = some rule := by
            simpa [activate, known] using computed
          have admitted := MM0ScopedRequestActivation.successful_arguments theory.termSignature declaration.arguments target
            formed _ _ _ expressions natural
          simp only [compatibilityActivate, schemaFor, known, Option.map_some, Option.bind_eq_bind, Option.bind_some]
          rw [if_pos (show expressions.length = (theoremSchema theory.termSignature target declaration).arity from admitted.length_eq)]
          exact MM0ScopedRequestActivation.activate_reflects_source theory.termSignature declaration.arguments target formed _ _ _
            expressions (theorem_premises_original target.length declaration) (judgmentPattern_ambient _ _ _) natural
  | basic kind sort =>
      have natural : MM0ScopedRequestActivation.activate theory.termSignature (regularFormals kind.arity sort) target
          (RuleKey.basic kind sort).name (kind.premises target.length sort) (kind.conclusion target.length sort)
          expressions = some rule := computed
      have admitted := MM0ScopedRequestActivation.successful_arguments theory.termSignature (regularFormals kind.arity sort) target
        formed _ _ _ expressions natural
      simp only [compatibilityActivate, schemaFor, Option.bind_eq_bind, Option.bind_some]
      rw [if_pos (show expressions.length = (basicSchema theory.termSignature target kind sort).arity from admitted.length_eq)]
      exact MM0ScopedRequestActivation.activate_reflects_source theory.termSignature (regularFormals kind.arity sort) target formed _ _ _
        expressions (basic_premises_original target.length sort kind) (basic_conclusion_original target.length sort kind) natural
  | congruence symbol => exact computed
  | unfolding symbol => exact computed

private theorem encoded_admission (signature : TermSignature) (formal target : Context) (expressions : List Preterm)
    (count : expressions.length = formal.length)
    (accepted : (admitArguments signature formal target (expressionAssignment target expressions)).isSome = true) :
    Substitution.Admissible signature formal target expressions := by
  obtain ⟨arguments, recovered⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨admissible, columns⟩ := (admitArguments_iff _ _ _ _ _).mp recovered
  have recoveredRead := (readArguments_iff target formal.length (expressionAssignment target expressions) arguments).mpr
    ⟨admissible.length_eq, columns⟩
  have originalRead : readArguments target formal.length (expressionAssignment target expressions) = some expressions := by
    rw [← count]
    exact readArguments_encoded target expressions
  have same := Option.some.inj (recoveredRead.symm.trans originalRead)
  subst arguments
  exact admissible

private theorem source_arguments_admissible {O : Type*} [DecidableEq O]
    (signature : TermSignature) (formal target : Context) (name : String)
    (premises : List Pat) (conclusion : Pat) (expressions : List Preterm) (count : expressions.length = formal.length)
    {rule : RuleInstance Tm} {picked : Selection O} {label : O → Tm} {before : Configuration Tm O}
    (computed : RequestActivation.activate ContextualPatterns.layer falseHead trueHead
      ((argumentSchema signature target formal premises conclusion).requestRecipe target name)
      (expressionAssignment target expressions) = some rule)
    (valid : picked.Valid (MM0ConstraintParameters.action target) label rule before) :
    Substitution.Admissible signature formal target expressions := by
  have accepted := RequestActivation.condition_of_valid ContextualPatterns.layer falseHead trueHead boolean_heads_distinct
    target.length ((argumentSchema signature target formal premises conclusion).requestRecipe target name)
    (expressionAssignment target expressions) computed valid
  exact encoded_admission signature formal target expressions count accepted

theorem valid_compatibility_has_natural_activation {O : Type*} [DecidableEq O] {sorts : SortSignature}
    (theory : Theory) (target : Context) (formed : Context.WellFormed sorts target) (key : RuleKey)
    (expressions : List Preterm) {rule : RuleInstance Tm} {picked : Selection O}
    {label : O → Tm} {before : Configuration Tm O}
    (computed : compatibilityActivate theory target key expressions = some rule)
    (valid : picked.Valid (MM0ConstraintParameters.action target) label rule before) :
    activate theory target key expressions = some rule := by
  cases key with
  | theorem_ index =>
      cases known : theory.theoremSignature index with
      | none => simp [compatibilityActivate, schemaFor, known] at computed
      | some declaration =>
          simp only [compatibilityActivate, schemaFor, known, Option.map_some, Option.bind_eq_bind, Option.bind_some] at computed
          split at computed
          · rename_i count
            have admitted := source_arguments_admissible theory.termSignature declaration.arguments target
              (RuleKey.theorem_ index).name _ _ expressions count computed valid
            simp only [activate, known, Option.bind_eq_bind, Option.bind_some]
            rw [MM0ScopedRequestActivation.activate_eq_source_of_admissible theory.termSignature declaration.arguments target formed
              (RuleKey.theorem_ index).name (declaration.hypotheses.map (proofPattern target.length))
              (proofPattern target.length declaration.conclusion) expressions admitted
              (theorem_premises_original target.length declaration) (judgmentPattern_ambient target.length "pf" [declaration.conclusion])]
            exact computed
          · cases computed
  | basic kind sort =>
      simp only [compatibilityActivate, schemaFor, Option.bind_eq_bind, Option.bind_some] at computed
      split at computed
      · rename_i count
        have admitted := source_arguments_admissible theory.termSignature (regularFormals kind.arity sort) target
          (RuleKey.basic kind sort).name _ _ expressions count computed valid
        change MM0ScopedRequestActivation.activate theory.termSignature (regularFormals kind.arity sort) target _ _ _ expressions = _
        rw [MM0ScopedRequestActivation.activate_eq_source_of_admissible theory.termSignature (regularFormals kind.arity sort) target formed
          _ _ _ expressions admitted (basic_premises_original target.length sort kind) (basic_conclusion_original target.length sort kind)]
        exact computed
      · cases computed
  | congruence symbol => exact computed
  | unfolding symbol => exact computed

end Mettapedia.Logic.TierZero.Adequacy.MM0ScopedCatalogActivation
