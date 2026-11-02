import Mettapedia.GSLT.LanguageDef.PatternABTCarrier
import Mettapedia.GSLT.LanguageDef.ABTHeadMapping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ABTProtectedParameters

/-!
# Existing inference schemas activate as ordinary constraint rules

The installed source definition supplies actual rule lookup, ordered argument
admission, side conditions and schema instantiation. These are local data
operations; activation never traverses a proof object or tests derivability.
Its output consumes one request, reads its ordered premise judgments and
produces its conclusion through the existing occurrence step.

Arguments retain their declared binder depths in the request's physical ABT
fields. Premise and conclusion judgments use the established injective raw
Pattern carrier. No guest syntax, logic or proof interpreter enters this
generic boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaActivation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering (PatternABTHead)
open Mettapedia.GSLT.LanguageDef.PatternABTCarrier (lowerRaw lowerRaw_scope lowerRaw_injective)

abbrev Head := PatternABTHead ⊕ String
abbrev Tm := Term Head
abbrev action := ABTProtectedParameters.action (Head := Head) 0

def lowerPattern (pattern : Pattern) : Tm := mapHeads Sum.inl (lowerRaw pattern)

theorem lowerPattern_injective : Function.Injective lowerPattern := by
  intro first second same
  exact lowerRaw_injective (mapHeads_injective Sum.inl Sum.inl_injective _ _ same)

theorem lowerPattern_scope (depth : Nat) (pattern : Pattern) :
    Term.supportedAt depth (lowerPattern pattern) = pattern.isWellScopedAt depth := by
  rw [lowerPattern, mapHeads_scope, lowerRaw_scope]

def judgment (pattern : Pattern) : Tm :=
  .node (.inr "judgment") (.cons 0 (lowerPattern pattern) .nil)

theorem judgment_injective : Function.Injective judgment := by
  intro first second same
  exact lowerPattern_injective (Fields.cons.inj (Term.node.inj same).2).2.1

def requestFields : List (String × Nat) → List Pattern → Fields Head
  | (_, depth) :: formals, argument :: arguments => .cons depth (lowerPattern argument) (requestFields formals arguments)
  | _, _ => .nil

def request (id : RuleId) (rule : RuleSchema) (arguments : List Pattern) : Tm :=
  .node (.inl (.apply id.value)) (requestFields rule.metavariables arguments)

theorem request_ne_judgment (id : RuleId) (rule : RuleSchema) (arguments : List Pattern) (pattern : Pattern) :
    request id rule arguments ≠ judgment pattern := by
  intro same
  cases (Term.node.inj same).1

def fromResult (id : RuleId) (rule : RuleSchema) (arguments : List Pattern)
    (premises : List Pattern) (conclusion : Pattern) : RuleInstance Tm where
  take := [request id rule arguments]
  read := premises.map judgment
  tell := []
  checks := []
  produce := [judgment conclusion]

def activate (definition : ValidatedCalculusLanguageDef) (id : RuleId) (arguments : List Pattern) :
    Option (RuleInstance Tm) := do
  let rule ← definition.1.lookupRule? id
  let result ← InferenceChecker.instantiateRule? definition ⟨id, arguments⟩
  return fromResult id rule arguments result.1 result.2

theorem origin (definition : ValidatedCalculusLanguageDef) (id : RuleId) (arguments : List Pattern)
    {actual : RuleInstance Tm} (computed : activate definition id arguments = some actual) :
    ∃ rule premises conclusion,
      definition.1.lookupRule? id = some rule ∧
      InferenceChecker.instantiateRule? definition ⟨id, arguments⟩ = some (premises, conclusion) ∧
      actual = fromResult id rule arguments premises conclusion := by
  unfold activate at computed
  cases lookup : definition.1.lookupRule? id with
  | none => simp [lookup] at computed
  | some rule =>
      cases computedResult : InferenceChecker.instantiateRule? definition ⟨id, arguments⟩ with
      | none => simp [lookup, computedResult] at computed
      | some values =>
          obtain ⟨premises, conclusion⟩ := values
          have same : fromResult id rule arguments premises conclusion = actual := by
            simpa [lookup, computedResult] using computed
          exact ⟨rule, premises, conclusion, rfl, rfl, same.symm⟩

theorem activate_of_application {definition : ValidatedCalculusLanguageDef}
    {instance_ : InferenceChecker.RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (applied : RuleApplication definition instance_ premises conclusion) :
    ∃ rule, definition.1.lookupRule? instance_.ruleId = some rule ∧
      activate definition instance_.ruleId instance_.arguments =
        some (fromResult instance_.ruleId rule instance_.arguments premises conclusion) := by
  cases applied with
  | intro rule lookup arguments conditions heads tail =>
      refine ⟨rule, lookup, ?_⟩
      have accepted := instantiateRule?_eq_some_iff_application.mpr
        (RuleApplication.intro rule lookup arguments conditions heads tail)
      simp [activate, lookup, accepted]

theorem judgment_supported (pattern : Pattern) (scopedTerm : pattern.isWellScoped = true) :
    Term.supportedAt 0 (judgment pattern) = true := by
  simpa [judgment, Term.supportedAt, Term.Fields.supportedAt, lowerPattern_scope, Pattern.isWellScoped] using scopedTerm

theorem judgment_fixed (pattern : Pattern) (scopedTerm : pattern.isWellScoped = true) :
    FixedMatching.Fixed action (judgment pattern) :=
  ABTProtectedParameters.fixed_of_supported _ _ (judgment_supported pattern scopedTerm)

theorem requestFields_supported (formals : List (String × Nat)) (arguments : List Pattern)
    (accepted : argumentsValidAt formals arguments = true) :
    Term.Fields.supportedAt 0 (requestFields formals arguments) = true := by
  induction formals generalizing arguments with
  | nil => cases arguments <;> rfl
  | cons formal formals earlier =>
      obtain ⟨name, depth⟩ := formal
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          have split : argumentValidAt depth argument = true ∧ argumentsValidAt formals arguments = true :=
            by simpa only [argumentsValidAt, Bool.and_eq_true] using accepted
          have argumentParts : argument.isGroundAt depth = true ∧ argument.hasCanonicalBinderMetadata = true :=
            by simpa only [argumentValidAt, Bool.and_eq_true] using split.1
          have scopedTerm := isWellScopedAt_of_isGroundAt argumentParts.1
          change (Term.supportedAt (0 + depth) (lowerPattern argument) && Term.Fields.supportedAt 0 (requestFields formals arguments)) = true
          rw [Nat.zero_add, lowerPattern_scope, scopedTerm, earlier arguments split.2]
          rfl

theorem request_fixed (id : RuleId) (rule : RuleSchema) (arguments : List Pattern)
    (accepted : argumentsValidAt rule.metavariables arguments = true) :
    FixedMatching.Fixed action (request id rule arguments) :=
  ABTProtectedParameters.fixed_of_supported _ _ (requestFields_supported rule.metavariables arguments accepted)

private theorem scopedList_iff (patterns : List Pattern) :
    Pattern.isWellScopedListAt 0 patterns = true ↔ ∀ pattern ∈ patterns, pattern.isWellScoped = true := by
  induction patterns with
  | nil => simp [Pattern.isWellScopedListAt]
  | cons first rest earlier => simp [Pattern.isWellScopedListAt, Pattern.isWellScoped, earlier]

private theorem premise_scopes {formals : List (String × Nat)} {arguments schemas results : List Pattern}
    (accepted : argumentsValidAt formals arguments = true)
    (instances : InstantiatesList formals arguments schemas results)
    (scopedTerm : ∀ schema ∈ schemas, schema.isWellScoped = true) :
    ∀ result ∈ results, result.isWellScoped = true :=
  (scopedList_iff results).mp (InstantiatesListAt.results_areWellScoped accepted instances ((scopedList_iff schemas).mpr scopedTerm))

theorem application_scopes {definition : ValidatedCalculusLanguageDef}
    {instance_ : InferenceChecker.RuleInstance} {premises : List Pattern} {conclusion : Pattern}
    (applied : RuleApplication definition instance_ premises conclusion) :
    (∀ premise ∈ premises, premise.isWellScoped = true) ∧ conclusion.isWellScoped = true := by
  have output := isWellScoped_of_isGround applied.conclusion_safety.1
  cases applied with
  | intro rule lookup arguments conditions heads tail =>
      refine ⟨premise_scopes arguments heads ?_, output⟩
      have valid := rule_isValidIn_of_lookup definition lookup
      simp only [RuleSchema.isValidIn, Bool.and_eq_true] at valid
      have validV1 : RuleSchema.isLocallyValid rule = true := valid.1
      have all : (RuleSchema.patterns rule).all Pattern.isWellScoped = true := by
        simp only [RuleSchema.isLocallyValid, Bool.and_eq_true] at validV1
        exact validV1.1.1.2
      intro premise member
      exact List.all_eq_true.mp all premise (List.mem_append_left _ member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaActivation
