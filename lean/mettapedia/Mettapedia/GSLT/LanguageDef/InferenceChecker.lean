import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.Basic
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.Util.LinearHash

/-!
# Generic inference-rule checker

This file defines a source-neutral proof checker over `Pattern` judgments in a
flat `CalculusLanguageDef`; contexts, theories, and any auxiliary side
conditions remain ordinary `Pattern` data and ordered judgment premises.

V1 assigns every metavariable one exact occurrence depth.  Schema
instantiation replaces only declared free metavariables at that depth and
preserves every `Pattern` constructor, including explicit `.subst` nodes.
Collection-rest metavariables are rejected, and schema binder metadata must be
canonical.  No implicit lifting is performed.  V2 adds a finite structural
judgment signature: every premise and conclusion has a declared outer head and
arity, and every fixed nested data-constructor occurrence resolves against the
underlying `LanguageDef`.  Metavariable payloads remain deliberately
unclassified until the source anchors determine their carrier discipline.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceChecker

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceExtension

/-- Rule identifier plus arguments in the schema's declared order. -/
structure RuleInstance where
  ruleId : RuleId
  arguments : List Pattern
deriving Repr

/-- Raw, untrusted proof tree.  Child order is semantically significant. -/
inductive RawProof where
  | node : RuleInstance → List RawProof → RawProof
deriving Repr

/-! ## V1 local validation and V2 definition validation -/

-- V1 rejects collection-rest metavariables anywhere in a rule schema.
mutual
def patternHasNoCollectionRest : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply _ arguments => patternsHaveNoCollectionRest arguments
  | .lambda _ body => patternHasNoCollectionRest body
  | .multiLambda _ _ body => patternHasNoCollectionRest body
  | .subst body replacement =>
      patternHasNoCollectionRest body && patternHasNoCollectionRest replacement
  | .collection _ elements rest =>
      rest.isNone && patternsHaveNoCollectionRest elements
termination_by pattern => sizeOf pattern

def patternsHaveNoCollectionRest : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      patternHasNoCollectionRest pattern && patternsHaveNoCollectionRest patterns
termination_by patterns => sizeOf patterns
end

-- Free schema metavariable occurrences annotated with their ambient binder
-- depth. Explicit-substitution bodies contribute one binder; replacements do
-- not.
mutual
def patternMetavariableOccurrencesAt (depth : Nat) : Pattern → List (String × Nat)
  | .bvar _ => []
  | .fvar name => [(name, depth)]
  | .apply _ arguments =>
      patternsMetavariableOccurrencesAt depth arguments
  | .lambda _ body => patternMetavariableOccurrencesAt (depth + 1) body
  | .multiLambda arity _ body =>
      patternMetavariableOccurrencesAt (depth + arity) body
  | .subst body replacement =>
      patternMetavariableOccurrencesAt (depth + 1) body ++
        patternMetavariableOccurrencesAt depth replacement
  | .collection _ elements _ =>
      patternsMetavariableOccurrencesAt depth elements
termination_by pattern => sizeOf pattern

def patternsMetavariableOccurrencesAt (depth : Nat) :
    List Pattern → List (String × Nat)
  | [] => []
  | pattern :: patterns =>
      patternMetavariableOccurrencesAt depth pattern ++
        patternsMetavariableOccurrencesAt depth patterns
termination_by patterns => sizeOf patterns
end

def RuleSchema.patterns (rule : RuleSchema) : List Pattern :=
  rule.premises ++ [rule.conclusion]

def RuleSchema.metavariableNames (rule : RuleSchema) : List String :=
  rule.metavariables.map (fun formal => formal.1)

def RuleSchema.occurrences (rule : RuleSchema) : List (String × Nat) :=
  patternsMetavariableOccurrencesAt 0 (RuleSchema.patterns rule)

/-- Schema validation is intentionally exact: identifiers and metavariable
names are nonempty, names are unique, every declared formal occurs and every
occurrence has exactly its declared depth, patterns are locally scoped,
collection rests are absent, and binder metadata is canonical. -/
def RuleSchema.isLocallyValid (rule : RuleSchema) : Bool :=
  let occurrences := RuleSchema.occurrences rule
  (rule.id.value != "") &&
    (RuleSchema.metavariableNames rule).all (fun name => name != "") &&
    ((RuleSchema.metavariableNames rule).eraseDups.length ==
      (RuleSchema.metavariableNames rule).length) &&
    occurrences.all (fun occurrence => rule.metavariables.contains occurrence) &&
    rule.metavariables.all (fun formal => occurrences.contains formal) &&
    (RuleSchema.patterns rule).all Pattern.isWellScoped &&
    (RuleSchema.patterns rule).all patternHasNoCollectionRest &&
    (RuleSchema.patterns rule).all Pattern.hasCanonicalBinderMetadata

def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.ruleIds
    (definition : CalculusLanguageDef) : List RuleId :=
  definition.rules.map (fun rule => rule.id)

def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.lookupRule?
    (definition : CalculusLanguageDef) (id : RuleId) :
    Option RuleSchema :=
  definition.rules.find? fun rule => decide (rule.id = id)

/-- Appending new rules after an existing rule table preserves every
successful lookup in the original table.  No converse holds in general. -/
theorem _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.lookupRule?_append_of_eq_some
    (definition : CalculusLanguageDef) (extraRules : List RuleSchema)
    {id : RuleId} {rule : RuleSchema}
    (hlookup : definition.lookupRule? id = some rule) :
    ({ definition with rules := definition.rules ++ extraRules } :
        CalculusLanguageDef).lookupRule? id = some rule := by
  unfold CalculusLanguageDef.lookupRule? at hlookup ⊢
  have preserve : ∀ rules : List RuleSchema,
      List.find? (fun candidate => decide (candidate.id = id)) rules =
          some rule →
        List.find? (fun candidate => decide (candidate.id = id))
            (rules ++ extraRules) = some rule := by
    intro rules hfind
    induction rules with
    | nil => simp at hfind
    | cons head tail ih =>
        cases hhead : decide (head.id = id) with
        | false =>
            rw [List.find?_cons, hhead] at hfind
            change List.find? (fun candidate => decide (candidate.id = id))
                (head :: (tail ++ extraRules)) = some rule
            rw [List.find?_cons, hhead]
            exact ih hfind
        | true =>
            rw [List.find?_cons, hhead] at hfind
            change List.find? (fun candidate => decide (candidate.id = id))
                (head :: (tail ++ extraRules)) = some rule
            rw [List.find?_cons, hhead]
            exact hfind
  exact preserve definition.rules hlookup

def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.judgmentHeads
    (definition : CalculusLanguageDef) : List String :=
  definition.judgments.map (fun judgment => judgment.head)

/-- A raw definition is admitted only when its base language validates and
all inference-rule identifiers and schemas satisfy the V1 binding boundary.
This does not validate inference-judgment constructor names against a separate
judgment signature; V1 intentionally has no such signature yet. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.hasValidLocalRulesFast
    (definition : CalculusLanguageDef) : Bool :=
  definition.toLanguageDef.validate.isEmpty &&
    definition.rules.all RuleSchema.isLocallyValid &&
    Mettapedia.Util.LinearHash.allDistinct definition.ruleIds

@[implemented_by CalculusLanguageDef.hasValidLocalRulesFast]
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.hasValidLocalRules
    (definition : CalculusLanguageDef) : Bool :=
  definition.toLanguageDef.validate.isEmpty &&
    definition.rules.all RuleSchema.isLocallyValid &&
    (definition.ruleIds.eraseDups.length == definition.ruleIds.length)

/-- Hash-indexed V1 validation is extensionally identical to the structural
specification. -/
theorem _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.hasValidLocalRulesFast_eq_hasValidLocalRules
    (definition : CalculusLanguageDef) :
    definition.hasValidLocalRulesFast = definition.hasValidLocalRules := by
  simp only [CalculusLanguageDef.hasValidLocalRulesFast, CalculusLanguageDef.hasValidLocalRules]
  rw [Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]

/-- Fail-closed lookup of a data constructor at an exact arity.  Although a
validated `LanguageDef` already has unique constructor labels, this helper is
also safe when used while validation is still in progress. -/
def languageHasConstructorArity (language : LanguageDef)
    (head : String) (arity : Nat) : Bool :=
  match language.terms.filter (fun declaration => declaration.label == head) with
  | [declaration] => declaration.params.length == arity
  | _ => false

/- All fixed constructor occurrences in a schema fragment resolve against
the language at their authored arity.  Free variables are schema holes, so
this predicate makes no claim about constructors later supplied by a rule
instance. -/
mutual
def fixedConstructorsValid (language : LanguageDef) : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply head arguments =>
      languageHasConstructorArity language head arguments.length &&
        fixedConstructorListsValid language arguments
  | .lambda _ body => fixedConstructorsValid language body
  | .multiLambda _ _ body => fixedConstructorsValid language body
  | .subst body replacement =>
      fixedConstructorsValid language body &&
        fixedConstructorsValid language replacement
  | .collection _ elements _ => fixedConstructorListsValid language elements
termination_by pattern => sizeOf pattern

def fixedConstructorListsValid (language : LanguageDef) : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      fixedConstructorsValid language pattern &&
        fixedConstructorListsValid language patterns
termination_by patterns => sizeOf patterns
end

/-- Fail-closed lookup of one declared outer judgment shape. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.lookupJudgment?
    (definition : CalculusLanguageDef)
    (head : String) (arity : Nat) : Option JudgmentDecl :=
  match definition.judgments.filter fun declaration =>
      declaration.head == head && declaration.arity == arity with
  | [declaration] => some declaration
  | _ => none

/-- The outer head and arity form one declared judgment. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.hasJudgmentShape
    (definition : CalculusLanguageDef) : Pattern → Bool
  | .apply head arguments =>
      (definition.lookupJudgment? head arguments.length).isSome
  | _ => false

/-- A rule-schema judgment has a declared outer shape and only declared fixed
nested constructor occurrences.  Binder forms are structural Pattern forms;
scope and canonical metadata remain the responsibility of V1. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.judgmentSchemaValid
    (definition : CalculusLanguageDef) : Pattern → Bool
  | .apply head arguments =>
      (definition.lookupJudgment? head arguments.length).isSome &&
        fixedConstructorListsValid definition.toLanguageDef arguments
  | _ => false

/-- A generic side-condition declaration may only reference existing formal
arguments at the exact depths required by its operation. -/
def RuleSideCondition.isValidFor
    (formals : List (String × Nat)) : RuleSideCondition → Bool
  | .explicitSubstitution ambientDepth bodyArgument replacementArgument
      resultArgument =>
      match formals[bodyArgument]?, formals[replacementArgument]?,
          formals[resultArgument]? with
      | some (_, bodyDepth), some (_, replacementDepth), some (_, resultDepth) =>
          bodyDepth == ambientDepth + 1 &&
            replacementDepth == ambientDepth && resultDepth == ambientDepth
      | _, _, _ => false
  | .unusedBinderElimination ambientDepth bodyArgument resultArgument =>
      match formals[bodyArgument]?, formals[resultArgument]? with
      | some (_, bodyDepth), some (_, resultDepth) =>
          bodyDepth == ambientDepth + 1 && resultDepth == ambientDepth
      | _, _ => false

def RuleSchema.isValidIn (definition : CalculusLanguageDef) (rule : RuleSchema) : Bool :=
  RuleSchema.isLocallyValid rule &&
    ((RuleSchema.patterns rule).all definition.judgmentSchemaValid &&
      rule.sideConditions.all
        (RuleSideCondition.isValidFor rule.metavariables))

/-- The V2 signature itself is finite, unambiguous, and disjoint from the
ordinary term-constructor namespace.  The three metasyntax heads are also
reserved rather than silently reclassified as judgments. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.judgmentSignatureValid
    (definition : CalculusLanguageDef) : Bool :=
  definition.judgments.all (fun judgment => judgment.head != "") &&
    (definition.judgmentHeads.eraseDups.length ==
      definition.judgmentHeads.length) &&
    definition.judgmentHeads.all (fun head =>
      !(definition.toLanguageDef.terms.any fun declaration => declaration.label == head) &&
        !([Pattern.zipHead, Pattern.mapHead, Pattern.evalHead].contains head))

/-- A rooted conversion interface names a nonempty, versioned binary judgment
in the same `LanguageDef`; absence means that the language declares no
conversion-certificate interface. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.conversionDeclarationValid
    (definition : CalculusLanguageDef) : Bool :=
  match definition.conversion with
  | none => true
  | some declaration =>
      declaration.judgmentHead != "" && declaration.version != "" &&
        (definition.lookupJudgment? declaration.judgmentHead 2).isSome

/-- Contextual V2 admission.  V1 remains a useful local schema boundary; V2
adds the definition-dependent judgment, fixed-constructor, generic
side-condition, and rooted-conversion checks. -/
def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.isValid
    (definition : CalculusLanguageDef) : Bool :=
  definition.hasValidLocalRules &&
    definition.judgmentSignatureValid &&
    definition.rules.all (RuleSchema.isValidIn definition) &&
    definition.conversionDeclarationValid

/-- Proof-carrying validated definition used by the checker. -/
abbrev _root_.Mettapedia.GSLT.LanguageDef.ValidatedCalculusLanguageDef :=
  { definition : CalculusLanguageDef // definition.isValid = true }

def _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.validate?
    (definition : CalculusLanguageDef) :
    Option ValidatedCalculusLanguageDef :=
  if h : definition.isValid = true then some ⟨definition, h⟩ else none

private theorem eraseDups_length_le {α : Type} [BEq α]
    (values : List α) :
    values.eraseDups.length ≤ values.length := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h size ih =>
      cases values with
      | nil => simp
      | cons value values =>
          simp only [List.length_cons] at hlength
          subst size
          rw [List.eraseDups_cons]
          simp only [List.length_cons]
          apply Nat.succ_le_succ
          exact
            (ih _ (by
              have :=
                List.length_filter_le (fun candidate => !candidate == value)
                  values
              omega) _ rfl).trans
              (List.length_filter_le _ _)

private theorem find?_eq_some_of_mem_of_unique_keys
    {α β : Type} [BEq β] [LawfulBEq β] [DecidableEq β]
    (key : α → β) (values : List α) (target : α)
    (hunique : (values.map key).eraseDups.length = values.length)
    (hmem : target ∈ values) :
    values.find? (fun value => decide (key value = key target)) =
      some target := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [List.find?]
      · rw [List.map_cons, List.eraseDups_cons] at hunique
        simp only [List.length_cons, Nat.succ.injEq] at hunique
        have heraseLe :=
          eraseDups_length_le
            ((tail.map key).filter fun value => !value == key head)
        have hfilterLe := List.length_filter_le
          (fun value => !value == key head) (tail.map key)
        have htailLeFilter :
            (tail.map key).length ≤
              ((tail.map key).filter fun value =>
                !value == key head).length := by
          simp only [List.length_map]
          rw [← hunique]
          exact heraseLe
        have hfilterLength :
            ((tail.map key).filter fun value => !value == key head).length =
              (tail.map key).length :=
          Nat.le_antisymm hfilterLe htailLeFilter
        have hall := List.length_filter_eq_length_iff.mp hfilterLength
        have hheadNe : key head ≠ key target := by
          intro heq
          have htarget : key target ∈ tail.map key :=
            List.mem_map_of_mem hmem
          have hkept := hall (key target) htarget
          simp [heq] at hkept
        have htailUnique :
            (tail.map key).eraseDups.length = tail.length := by
          have hfilterEq :
              (tail.map key).filter (fun value => !value == key head) =
                tail.map key :=
            List.filter_eq_self.mpr hall
          rw [hfilterEq] at hunique
          exact hunique
        rw [List.find?_cons]
        simp [hheadNe, ih htailUnique hmem]

/-- Membership selects the exact stored rule in a validated definition.
This is the reusable lookup boundary supplied by V2's unique rule identifiers. -/
theorem lookupRule?_eq_some_of_mem
    (definition : ValidatedCalculusLanguageDef) {rule : RuleSchema}
    (hmem : rule ∈ definition.1.rules) :
    definition.1.lookupRule? rule.id = some rule := by
  have hvalid := definition.2
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true, beq_iff_eq] at hvalid
  have hunique :
      (definition.1.rules.map RuleSchema.id).eraseDups.length =
        definition.1.rules.length := by
    simpa [CalculusLanguageDef.ruleIds] using hvalid.1.1.1.2
  simpa [CalculusLanguageDef.lookupRule?] using
    find?_eq_some_of_mem_of_unique_keys
      RuleSchema.id definition.1.rules rule hunique hmem

/-- V2 schema validity always contains the independently useful outer
judgment-shape fact. -/
theorem _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.hasJudgmentShape_of_judgmentSchemaValid
    {definition : CalculusLanguageDef} {judgment : Pattern}
    (hvalid : definition.judgmentSchemaValid judgment = true) :
    definition.hasJudgmentShape judgment = true := by
  cases judgment <;>
    simp_all [CalculusLanguageDef.judgmentSchemaValid,
      CalculusLanguageDef.hasJudgmentShape]

/-- Exact decomposition of contextual schema validation into the declared
outer shape and the fixed nested-constructor check. -/
theorem _root_.Mettapedia.GSLT.LanguageDef.CalculusLanguageDef.judgmentSchemaValid_iff
    {definition : CalculusLanguageDef} {judgment : Pattern} :
    definition.judgmentSchemaValid judgment = true ↔
      definition.hasJudgmentShape judgment = true ∧
        match judgment with
        | .apply _ arguments =>
            fixedConstructorListsValid definition.toLanguageDef arguments = true
        | _ => False := by
  cases judgment <;>
    simp [CalculusLanguageDef.judgmentSchemaValid,
      CalculusLanguageDef.hasJudgmentShape]

/-- Every rule stored in a validated definition satisfies its contextual V2
schema checks. -/
theorem rule_isValidIn_of_mem (definition : ValidatedCalculusLanguageDef)
    {rule : RuleSchema} (hmem : rule ∈ definition.1.rules) :
    RuleSchema.isValidIn definition.1 rule = true := by
  have hvalid := definition.2
  simp only [CalculusLanguageDef.isValid, Bool.and_eq_true] at hvalid
  exact (List.all_eq_true.mp hvalid.1.2) rule hmem

/-- Successful rule lookup in a validated definition recovers contextual
V2 validity for that exact stored rule. -/
theorem rule_isValidIn_of_lookup (definition : ValidatedCalculusLanguageDef)
    {id : RuleId} {rule : RuleSchema}
    (hlookup : definition.1.lookupRule? id = some rule) :
    RuleSchema.isValidIn definition.1 rule = true := by
  exact rule_isValidIn_of_mem definition
    (List.mem_of_find?_eq_some hlookup)

/-- Local V1 validity exposes well-scopedness of the conclusion. -/
theorem RuleSchema.conclusion_isWellScoped_of_validV1 {rule : RuleSchema}
    (hvalid : RuleSchema.isLocallyValid rule = true) :
    rule.conclusion.isWellScoped = true := by
  have hall : (RuleSchema.patterns rule).all Pattern.isWellScoped = true := by
    simp only [RuleSchema.isLocallyValid, Bool.and_eq_true] at hvalid
    exact hvalid.1.1.2
  exact (List.all_eq_true.mp hall) rule.conclusion (by
    simp [RuleSchema.patterns])

/-- Local V1 validity exposes canonical binder metadata of the conclusion. -/
theorem RuleSchema.conclusion_hasCanonicalBinderMetadata_of_validV1
    {rule : RuleSchema} (hvalid : RuleSchema.isLocallyValid rule = true) :
    rule.conclusion.hasCanonicalBinderMetadata = true := by
  have hall :
      (RuleSchema.patterns rule).all Pattern.hasCanonicalBinderMetadata = true := by
    simp only [RuleSchema.isLocallyValid, Bool.and_eq_true] at hvalid
    exact hvalid.2
  exact (List.all_eq_true.mp hall) rule.conclusion (by
    simp [RuleSchema.patterns])

/-- Contextual V2 validity exposes the conclusion's authored judgment shape. -/
theorem RuleSchema.conclusion_hasJudgmentShape_of_validIn
    {definition : CalculusLanguageDef} {rule : RuleSchema}
    (hvalid : RuleSchema.isValidIn definition rule = true) :
    definition.hasJudgmentShape rule.conclusion = true := by
  have hall :
      (RuleSchema.patterns rule).all definition.judgmentSchemaValid = true :=
    by
      simp only [RuleSchema.isValidIn, Bool.and_eq_true] at hvalid
      exact hvalid.2.1
  exact definition.hasJudgmentShape_of_judgmentSchemaValid
    ((List.all_eq_true.mp hall) rule.conclusion (by
      simp [RuleSchema.patterns]))

/-- One argument is closed relative to its declared occurrence depth and has
canonical binder metadata. -/
def argumentValidAt (depth : Nat) (argument : Pattern) : Bool :=
  argument.isGroundAt depth && argument.hasCanonicalBinderMetadata

/-- Ordered proof arguments must be valid at the exact occurrence depth
declared by their corresponding formal. Length mismatch also fails. -/
def argumentsValidAt : List (String × Nat) → List Pattern → Bool
  | [], [] => true
  | (_, depth) :: formals, argument :: arguments =>
      argumentValidAt depth argument && argumentsValidAt formals arguments
  | _, _ => false

def RuleInstance.argumentsValidFor (ruleInstance : RuleInstance)
    (formals : List (String × Nat)) : Bool :=
  argumentsValidAt formals ruleInstance.arguments

/-- Execute one generic side condition over the rule instance's ordered
argument vector.  Failure to resolve an argument position fails closed. -/
@[simp] def RuleSideCondition.holds
    (arguments : List Pattern) : RuleSideCondition → Bool
  | .explicitSubstitution _ bodyArgument replacementArgument resultArgument =>
      match arguments[bodyArgument]?, arguments[replacementArgument]?,
          arguments[resultArgument]? with
      | some body, some replacement, some result =>
          decide (instantiateBVar replacement body = result)
      | _, _, _ => false
  | .unusedBinderElimination _ bodyArgument resultArgument =>
      match arguments[bodyArgument]?, arguments[resultArgument]? with
      | some body, some result => decide (dropBVar? body = some result)
      | _, _ => false

def RuleSchema.sideConditionsHold
    (rule : RuleSchema) (arguments : List Pattern) : Bool :=
  rule.sideConditions.all (RuleSideCondition.holds arguments)

@[simp] theorem RuleSchema.sideConditionsHold_of_empty
    (rule : RuleSchema) (arguments : List Pattern)
    (hempty : rule.sideConditions = []) :
    RuleSchema.sideConditionsHold rule arguments = true := by
  simp [RuleSchema.sideConditionsHold, hempty]

/-- At depth zero, relative argument validity degenerates to ordinary
top-level groundness plus canonical binder metadata. -/
theorem argumentValidAt_zero (argument : Pattern) :
    argumentValidAt 0 argument =
      (argument.isGround && argument.hasCanonicalBinderMetadata) := rfl

/-! ## Schema instantiation -/

/-- Lookup an argument by its declared name and exact occurrence depth. -/
def lookupArgumentAt? :
    List (String × Nat) → List Pattern → String → Nat → Option Pattern
  | formal :: formals, argument :: arguments, target, depth =>
      if formal = (target, depth) then some argument
      else lookupArgumentAt? formals arguments target depth
  | _, _, _, _ => none

mutual

/-- Executable V1 schema instantiation at an ambient binder depth.  It
replaces only exact-depth free variables and preserves every constructor; in
particular, `.subst` is not run. -/
def instantiateSchemaAt? (formals : List (String × Nat))
    (arguments : List Pattern) (depth : Nat) : Pattern → Option Pattern
  | .bvar index => some (.bvar index)
  | .fvar name => lookupArgumentAt? formals arguments name depth
  | .apply constructor schemas => do
      let results ← instantiateSchemasAt? formals arguments depth schemas
      some (.apply constructor results)
  | .lambda binder body => do
      let result ← instantiateSchemaAt? formals arguments (depth + 1) body
      some (.lambda binder result)
  | .multiLambda arity binders body => do
      let result ← instantiateSchemaAt? formals arguments (depth + arity) body
      some (.multiLambda arity binders result)
  | .subst body replacement => do
      let bodyResult ← instantiateSchemaAt? formals arguments (depth + 1) body
      let replacementResult ← instantiateSchemaAt? formals arguments depth replacement
      some (.subst bodyResult replacementResult)
  | .collection collectionType schemas rest =>
      match rest with
      | some _ => none
      | none => do
          let results ← instantiateSchemasAt? formals arguments depth schemas
          some (.collection collectionType results none)
termination_by schema => sizeOf schema

def instantiateSchemasAt? (formals : List (String × Nat))
    (arguments : List Pattern) (depth : Nat) :
    List Pattern → Option (List Pattern)
  | [] => some []
  | schema :: schemas => do
      let result ← instantiateSchemaAt? formals arguments depth schema
      let results ← instantiateSchemasAt? formals arguments depth schemas
      some (result :: results)
termination_by schemas => sizeOf schemas

end

def instantiateSchema? (formals : List (String × Nat))
    (arguments : List Pattern) (schema : Pattern) : Option Pattern :=
  instantiateSchemaAt? formals arguments 0 schema

def instantiateSchemas? (formals : List (String × Nat))
    (arguments schemas : List Pattern) : Option (List Pattern) :=
  instantiateSchemasAt? formals arguments 0 schemas

/-- Executable list instantiation preserves exact list length whenever it
succeeds. -/
theorem instantiateSchemasAt?_length_eq
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (hresult : instantiateSchemasAt? formals arguments depth schemas = some results) :
    schemas.length = results.length := by
  cases schemas with
  | nil =>
      simp only [instantiateSchemasAt?, Option.some.injEq] at hresult
      subst results
      rfl
  | cons schema schemas =>
      simp only [instantiateSchemasAt?] at hresult
      cases hhead : instantiateSchemaAt? formals arguments depth schema with
      | none => simp [hhead] at hresult
      | some result =>
          cases htail : instantiateSchemasAt? formals arguments depth schemas with
          | none => simp [hhead, htail] at hresult
          | some tailResults =>
              have heq : result :: tailResults = results := by
                simpa [hhead, htail] using hresult
              subst results
              simp [instantiateSchemasAt?_length_eq htail]
termination_by sizeOf schemas

/-! Ground schemas are closed under every argument environment.  This is the
reusable fact boundary: a generated ground rule needs no metavariable replay,
and its instantiated conclusion is exactly its authored conclusion. -/

mutual

theorem instantiateSchemaAt?_eq_self_of_ground
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schema : Pattern)
    (ground : schema.isGroundAt depth = true) :
    instantiateSchemaAt? formals arguments depth schema = some schema := by
  cases schema with
  | bvar index => simp [instantiateSchemaAt?]
  | fvar name => simp [Pattern.isGroundAt] at ground
  | apply constructor schemas =>
      simp only [Pattern.isGroundAt] at ground
      simp [instantiateSchemaAt?,
        instantiateSchemasAt?_eq_self_of_ground formals arguments depth
          schemas ground]
  | lambda binder body =>
      simp only [Pattern.isGroundAt] at ground
      simp [instantiateSchemaAt?, instantiateSchemaAt?_eq_self_of_ground
        formals arguments (depth + 1) body ground]
  | multiLambda arity binders body =>
      simp only [Pattern.isGroundAt] at ground
      simp [instantiateSchemaAt?, instantiateSchemaAt?_eq_self_of_ground
        formals arguments (depth + arity) body ground]
  | subst body replacement =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at ground
      simp [instantiateSchemaAt?, instantiateSchemaAt?_eq_self_of_ground
        formals arguments (depth + 1) body ground.1,
        instantiateSchemaAt?_eq_self_of_ground formals arguments depth
          replacement ground.2]
  | collection collectionType schemas rest =>
      simp only [Pattern.isGroundAt, Bool.and_eq_true] at ground
      cases rest with
      | some restName => simp at ground
      | none =>
          simp [instantiateSchemaAt?,
            instantiateSchemasAt?_eq_self_of_ground formals arguments depth
              schemas ground.1]
termination_by sizeOf schema

theorem instantiateSchemasAt?_eq_self_of_ground
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schemas : List Pattern)
    (ground : Pattern.isGroundListAt depth schemas = true) :
    instantiateSchemasAt? formals arguments depth schemas = some schemas := by
  cases schemas with
  | nil => simp [instantiateSchemasAt?]
  | cons schema schemas =>
      simp only [Pattern.isGroundListAt, Bool.and_eq_true] at ground
      simp [instantiateSchemasAt?, instantiateSchemaAt?_eq_self_of_ground
        formals arguments depth schema ground.1,
        instantiateSchemasAt?_eq_self_of_ground formals arguments depth
          schemas ground.2]
termination_by sizeOf schemas

end

mutual

/-- Declarative structural schema instantiation, independent of the Boolean
proof checker. -/
inductive InstantiatesAt (formals : List (String × Nat))
    (arguments : List Pattern) : Nat → Pattern → Pattern → Prop where
  | bvar (depth index : Nat) :
      InstantiatesAt formals arguments depth (.bvar index) (.bvar index)
  | fvar {name : String} {argument : Pattern}
      {depth : Nat}
      (lookup : lookupArgumentAt? formals arguments name depth = some argument) :
      InstantiatesAt formals arguments depth (.fvar name) argument
  | apply {constructor : String} {schemas results : List Pattern}
      {depth : Nat}
      (items : InstantiatesListAt formals arguments depth schemas results) :
      InstantiatesAt formals arguments depth (.apply constructor schemas)
        (.apply constructor results)
  | lambda {binder : Option String} {body result : Pattern}
      {depth : Nat}
      (inner : InstantiatesAt formals arguments (depth + 1) body result) :
      InstantiatesAt formals arguments depth (.lambda binder body)
        (.lambda binder result)
  | multiLambda {arity : Nat} {binders : List String} {body result : Pattern}
      {depth : Nat}
      (inner : InstantiatesAt formals arguments (depth + arity) body result) :
      InstantiatesAt formals arguments depth (.multiLambda arity binders body)
        (.multiLambda arity binders result)
  | subst {body replacement bodyResult replacementResult : Pattern}
      {depth : Nat}
      (left : InstantiatesAt formals arguments (depth + 1) body bodyResult)
      (right : InstantiatesAt formals arguments depth replacement replacementResult) :
      InstantiatesAt formals arguments depth (.subst body replacement)
        (.subst bodyResult replacementResult)
  | collection {collectionType : CollType} {schemas results : List Pattern}
      {depth : Nat}
      (items : InstantiatesListAt formals arguments depth schemas results) :
      InstantiatesAt formals arguments depth
        (.collection collectionType schemas none)
        (.collection collectionType results none)

inductive InstantiatesListAt (formals : List (String × Nat))
    (arguments : List Pattern) : Nat → List Pattern → List Pattern → Prop where
  | nil (depth : Nat) : InstantiatesListAt formals arguments depth [] []
  | cons {schema result : Pattern} {schemas results : List Pattern}
      {depth : Nat}
      (head : InstantiatesAt formals arguments depth schema result)
      (tail : InstantiatesListAt formals arguments depth schemas results) :
      InstantiatesListAt formals arguments depth
        (schema :: schemas) (result :: results)

end

abbrev Instantiates (formals : List (String × Nat))
    (arguments : List Pattern) (schema result : Pattern) : Prop :=
  InstantiatesAt formals arguments 0 schema result

abbrev InstantiatesList (formals : List (String × Nat))
    (arguments schemas results : List Pattern) : Prop :=
  InstantiatesListAt formals arguments 0 schemas results

/-! ### Executable/declarative agreement -/

mutual

theorem instantiateSchemaAt?_sound {formals : List (String × Nat)}
    {arguments : List Pattern} {depth : Nat} {schema result : Pattern}
    (h : instantiateSchemaAt? formals arguments depth schema = some result) :
    InstantiatesAt formals arguments depth schema result := by
  cases schema with
  | bvar index =>
      simp only [instantiateSchemaAt?, Option.some.injEq] at h
      subst result
      exact .bvar depth index
  | fvar name =>
      exact .fvar (by simpa only [instantiateSchemaAt?] using h)
  | apply constructor schemas =>
      simp only [instantiateSchemaAt?] at h
      cases hitems : instantiateSchemasAt? formals arguments depth schemas with
      | none => simp [hitems] at h
      | some results =>
          have heq : Pattern.apply constructor results = result := by
            simpa [hitems] using h
          subst result
          exact .apply (instantiateSchemasAt?_sound hitems)
  | lambda binder body =>
      simp only [instantiateSchemaAt?] at h
      cases hbody : instantiateSchemaAt? formals arguments (depth + 1) body with
      | none => simp [hbody] at h
      | some bodyResult =>
          have heq : Pattern.lambda binder bodyResult = result := by
            simpa [hbody] using h
          subst result
          exact .lambda (instantiateSchemaAt?_sound hbody)
  | multiLambda arity binders body =>
      simp only [instantiateSchemaAt?] at h
      cases hbody : instantiateSchemaAt? formals arguments (depth + arity) body with
      | none => simp [hbody] at h
      | some bodyResult =>
          have heq : Pattern.multiLambda arity binders bodyResult = result := by
            simpa [hbody] using h
          subst result
          exact .multiLambda (instantiateSchemaAt?_sound hbody)
  | subst body replacement =>
      simp only [instantiateSchemaAt?] at h
      cases hbody : instantiateSchemaAt? formals arguments (depth + 1) body with
      | none => simp [hbody] at h
      | some bodyResult =>
          cases hreplacement :
              instantiateSchemaAt? formals arguments depth replacement with
          | none => simp [hbody, hreplacement] at h
          | some replacementResult =>
              have heq : Pattern.subst bodyResult replacementResult = result := by
                simpa [hbody, hreplacement] using h
              subst result
              exact .subst (instantiateSchemaAt?_sound hbody)
                (instantiateSchemaAt?_sound hreplacement)
  | collection collectionType schemas rest =>
      cases rest with
      | some restName => simp [instantiateSchemaAt?] at h
      | none =>
          simp only [instantiateSchemaAt?] at h
          cases hitems : instantiateSchemasAt? formals arguments depth schemas with
          | none => simp [hitems] at h
          | some results =>
              have heq : Pattern.collection collectionType results none = result := by
                simpa [hitems] using h
              subst result
              exact .collection (instantiateSchemasAt?_sound hitems)
termination_by sizeOf schema

theorem instantiateSchemasAt?_sound {formals : List (String × Nat)}
    {arguments : List Pattern} {depth : Nat} {schemas results : List Pattern}
    (h : instantiateSchemasAt? formals arguments depth schemas = some results) :
    InstantiatesListAt formals arguments depth schemas results := by
  cases schemas with
  | nil =>
      simp only [instantiateSchemasAt?, Option.some.injEq] at h
      subst results
      exact .nil depth
  | cons schema schemas =>
      simp only [instantiateSchemasAt?] at h
      cases hhead : instantiateSchemaAt? formals arguments depth schema with
      | none => simp [hhead] at h
      | some result =>
          cases htail : instantiateSchemasAt? formals arguments depth schemas with
          | none => simp [hhead, htail] at h
          | some tailResults =>
              have heq : result :: tailResults = results := by
                simpa [hhead, htail] using h
              subst results
              exact .cons (instantiateSchemaAt?_sound hhead)
                (instantiateSchemasAt?_sound htail)
termination_by sizeOf schemas

end

mutual

theorem instantiateSchemaAt?_complete {formals : List (String × Nat)}
    {arguments : List Pattern} {depth : Nat} {schema result : Pattern}
    (h : InstantiatesAt formals arguments depth schema result) :
    instantiateSchemaAt? formals arguments depth schema = some result := by
  cases h with
  | bvar => simp [instantiateSchemaAt?]
  | fvar lookup => simpa only [instantiateSchemaAt?] using lookup
  | apply items =>
      simp [instantiateSchemaAt?, instantiateSchemasAt?_complete items]
  | lambda inner =>
      simp [instantiateSchemaAt?, instantiateSchemaAt?_complete inner]
  | multiLambda inner =>
      simp [instantiateSchemaAt?, instantiateSchemaAt?_complete inner]
  | subst left right =>
      simp [instantiateSchemaAt?, instantiateSchemaAt?_complete left,
        instantiateSchemaAt?_complete right]
  | collection items =>
      simp [instantiateSchemaAt?, instantiateSchemasAt?_complete items]

theorem instantiateSchemasAt?_complete {formals : List (String × Nat)}
    {arguments : List Pattern} {depth : Nat} {schemas results : List Pattern}
    (h : InstantiatesListAt formals arguments depth schemas results) :
    instantiateSchemasAt? formals arguments depth schemas = some results := by
  cases h with
  | nil => simp [instantiateSchemasAt?]
  | cons head tail =>
      simp [instantiateSchemasAt?, instantiateSchemaAt?_complete head,
        instantiateSchemasAt?_complete tail]

end

/-- Structural list instantiation preserves exact arity. -/
theorem InstantiatesListAt.length_eq
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (hinst : InstantiatesListAt formals arguments depth schemas results) :
    schemas.length = results.length :=
  instantiateSchemasAt?_length_eq (instantiateSchemasAt?_complete hinst)

/-- Instantiation preserves a declared outer judgment head and arity.  This is
intentionally only an outer-shape theorem: metavariable payloads are not
silently classified as language data. -/
theorem InstantiatesAt.preservesJudgmentShape
    {definition : CalculusLanguageDef} {formals : List (String × Nat)}
    {arguments : List Pattern} {depth : Nat} {schema result : Pattern}
    (hinst : InstantiatesAt formals arguments depth schema result)
    (hshape : definition.hasJudgmentShape schema = true) :
    definition.hasJudgmentShape result = true := by
  cases hinst with
  | apply items =>
      simp only [CalculusLanguageDef.hasJudgmentShape] at hshape ⊢
      simpa [items.length_eq] using hshape
  | bvar | fvar | lambda | multiLambda | subst | collection =>
      simp [CalculusLanguageDef.hasJudgmentShape] at hshape


/-- Exact executable/declarative correspondence at any ambient depth. -/
theorem instantiateSchemaAt?_eq_some_iff_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern} :
    instantiateSchemaAt? formals arguments depth schema = some result ↔
      InstantiatesAt formals arguments depth schema result :=
  ⟨instantiateSchemaAt?_sound, instantiateSchemaAt?_complete⟩

/-- At every ambient depth, executable schema instantiation is equivalent to
the declarative structural relation. -/
theorem instantiateSchemaAt_eq_some_iff_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern} :
    instantiateSchemaAt? formals arguments depth schema = some result ↔
      InstantiatesAt formals arguments depth schema result :=
  instantiateSchemaAt?_eq_some_iff_instantiates

/-- Exact top-level executable/declarative correspondence. -/
theorem instantiateSchema?_eq_some_iff_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {schema result : Pattern} :
    instantiateSchema? formals arguments schema = some result ↔
      Instantiates formals arguments schema result :=
  instantiateSchemaAt?_eq_some_iff_instantiates

/-- Top-level executable schema instantiation is equivalent to the
declarative structural relation. -/
theorem instantiateSchema_eq_some_iff_instantiates
    {formals : List (String × Nat)} {arguments : List Pattern}
    {schema result : Pattern} :
    instantiateSchema? formals arguments schema = some result ↔
      Instantiates formals arguments schema result :=
  instantiateSchema?_eq_some_iff_instantiates

/-- Declarative structural instantiation is functional. -/
theorem InstantiatesAt.functional
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema first second : Pattern}
    (hfirst : InstantiatesAt formals arguments depth schema first)
    (hsecond : InstantiatesAt formals arguments depth schema second) :
    first = second := by
  apply Option.some.inj
  exact (instantiateSchemaAt?_complete hfirst).symm.trans
    (instantiateSchemaAt?_complete hsecond)

/-- Declarative list instantiation is functional. -/
theorem InstantiatesListAt.functional
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas : List Pattern} {first second : List Pattern}
    (hfirst : InstantiatesListAt formals arguments depth schemas first)
    (hsecond : InstantiatesListAt formals arguments depth schemas second) :
    first = second := by
  apply Option.some.inj
  exact (instantiateSchemasAt?_complete hfirst).symm.trans
    (instantiateSchemasAt?_complete hsecond)

/-! ### Scope safety -/

/-- Successful lookup from an argument vector validated against its formals
recovers both relative groundness and canonical binder metadata. -/
theorem argument_valid_of_lookup {formals : List (String × Nat)}
    {arguments : List Pattern} {name : String} {depth : Nat} {argument : Pattern}
    (hvalid : argumentsValidAt formals arguments = true)
    (hlookup : lookupArgumentAt? formals arguments name depth = some argument) :
    argument.isGroundAt depth = true ∧
      argument.hasCanonicalBinderMetadata = true := by
  induction formals generalizing arguments with
  | nil => simp [lookupArgumentAt?] at hlookup
  | cons formal formals ih =>
      cases arguments with
      | nil => simp [lookupArgumentAt?] at hlookup
      | cons first rest =>
          simp only [argumentsValidAt, argumentValidAt, Bool.and_eq_true] at hvalid
          simp only [lookupArgumentAt?] at hlookup
          split at hlookup
          · rename_i heq
            have hargument : first = argument := Option.some.inj hlookup
            subst argument
            have hdepth : formal.2 = depth := congrArg Prod.snd heq
            rw [← hdepth]
            exact hvalid.1
          · exact ih hvalid.2 hlookup

mutual

/-- Structural instantiation of a well-scoped schema with relatively ground
arguments remains well scoped at the same ambient depth. -/
theorem InstantiatesAt.result_isWellScoped
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesAt formals arguments depth schema result)
    (hschema : schema.isWellScopedAt depth = true) :
    result.isWellScopedAt depth = true := by
  cases hinst with
  | bvar => exact hschema
  | fvar lookup =>
      exact isWellScopedAt_of_isGroundAt
        (argument_valid_of_lookup harguments lookup).1
  | apply items =>
      simp only [Pattern.isWellScopedAt] at hschema ⊢
      exact InstantiatesListAt.results_areWellScoped harguments items hschema
  | lambda inner =>
      simp only [Pattern.isWellScopedAt] at hschema ⊢
      exact InstantiatesAt.result_isWellScoped harguments inner hschema
  | multiLambda inner =>
      simp only [Pattern.isWellScopedAt] at hschema ⊢
      exact InstantiatesAt.result_isWellScoped harguments inner hschema
  | subst left right =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at hschema ⊢
      exact ⟨InstantiatesAt.result_isWellScoped harguments left hschema.1,
        InstantiatesAt.result_isWellScoped harguments right hschema.2⟩
  | collection items =>
      simp only [Pattern.isWellScopedAt] at hschema ⊢
      exact InstantiatesListAt.results_areWellScoped harguments items hschema

theorem InstantiatesListAt.results_areWellScoped
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesListAt formals arguments depth schemas results)
    (hschemas : Pattern.isWellScopedListAt depth schemas = true) :
    Pattern.isWellScopedListAt depth results = true := by
  cases hinst with
  | nil => rfl
  | cons head tail =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at hschemas ⊢
      exact ⟨InstantiatesAt.result_isWellScoped harguments head hschemas.1,
        InstantiatesListAt.results_areWellScoped harguments tail hschemas.2⟩

end

mutual

/-- Successful exact-depth instantiation eliminates every schema metavariable:
the result is ground relative to the same ambient depth. -/
theorem InstantiatesAt.result_isGroundAt
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesAt formals arguments depth schema result)
    (hschema : schema.isWellScopedAt depth = true) :
    result.isGroundAt depth = true := by
  cases hinst with
  | bvar =>
      simpa only [Pattern.isWellScopedAt, Pattern.isGroundAt] using hschema
  | fvar lookup => exact (argument_valid_of_lookup harguments lookup).1
  | apply items =>
      simp only [Pattern.isWellScopedAt] at hschema
      simp only [Pattern.isGroundAt]
      exact InstantiatesListAt.results_areGroundAt harguments items hschema
  | lambda inner =>
      simp only [Pattern.isWellScopedAt] at hschema
      simp only [Pattern.isGroundAt]
      exact InstantiatesAt.result_isGroundAt harguments inner hschema
  | multiLambda inner =>
      simp only [Pattern.isWellScopedAt] at hschema
      simp only [Pattern.isGroundAt]
      exact InstantiatesAt.result_isGroundAt harguments inner hschema
  | subst left right =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at hschema
      simp only [Pattern.isGroundAt, Bool.and_eq_true]
      exact ⟨InstantiatesAt.result_isGroundAt harguments left hschema.1,
        InstantiatesAt.result_isGroundAt harguments right hschema.2⟩
  | collection items =>
      simp only [Pattern.isWellScopedAt] at hschema
      simp only [Pattern.isGroundAt, Option.isNone, Bool.and_true]
      exact InstantiatesListAt.results_areGroundAt harguments items hschema

theorem InstantiatesListAt.results_areGroundAt
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesListAt formals arguments depth schemas results)
    (hschemas : Pattern.isWellScopedListAt depth schemas = true) :
    Pattern.isGroundListAt depth results = true := by
  cases hinst with
  | nil => rfl
  | cons head tail =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at hschemas
      simp only [Pattern.isGroundListAt, Bool.and_eq_true]
      exact ⟨InstantiatesAt.result_isGroundAt harguments head hschemas.1,
        InstantiatesListAt.results_areGroundAt harguments tail hschemas.2⟩

end

mutual

/-- Canonical schema metadata and canonical arguments yield a canonical
instantiated result. -/
theorem InstantiatesAt.result_hasCanonicalBinderMetadata
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesAt formals arguments depth schema result)
    (hschema : schema.hasCanonicalBinderMetadata = true) :
    result.hasCanonicalBinderMetadata = true := by
  cases hinst with
  | bvar => rfl
  | fvar lookup => exact (argument_valid_of_lookup harguments lookup).2
  | apply items =>
      simp only [Pattern.hasCanonicalBinderMetadata] at hschema ⊢
      exact InstantiatesListAt.results_haveCanonicalBinderMetadata
        harguments items hschema
  | lambda inner =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at hschema ⊢
      exact ⟨hschema.1,
        InstantiatesAt.result_hasCanonicalBinderMetadata harguments inner hschema.2⟩
  | multiLambda inner =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at hschema ⊢
      exact ⟨hschema.1,
        InstantiatesAt.result_hasCanonicalBinderMetadata harguments inner hschema.2⟩
  | subst left right =>
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at hschema ⊢
      exact
        ⟨InstantiatesAt.result_hasCanonicalBinderMetadata harguments left hschema.1,
          InstantiatesAt.result_hasCanonicalBinderMetadata harguments right hschema.2⟩
  | collection items =>
      simp only [Pattern.hasCanonicalBinderMetadata] at hschema ⊢
      exact InstantiatesListAt.results_haveCanonicalBinderMetadata
        harguments items hschema

theorem InstantiatesListAt.results_haveCanonicalBinderMetadata
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schemas results : List Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesListAt formals arguments depth schemas results)
    (hschemas : Pattern.hasCanonicalBinderMetadataList schemas = true) :
    Pattern.hasCanonicalBinderMetadataList results = true := by
  cases hinst with
  | nil => rfl
  | cons head tail =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
        at hschemas ⊢
      exact
        ⟨InstantiatesAt.result_hasCanonicalBinderMetadata harguments head hschemas.1,
          InstantiatesListAt.results_haveCanonicalBinderMetadata
            harguments tail hschemas.2⟩

end

/-- Complete V1 instantiation safety contract. -/
theorem instantiation_safety_contract
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {schema result : Pattern}
    (harguments : argumentsValidAt formals arguments = true)
    (hinst : InstantiatesAt formals arguments depth schema result)
    (hscoped : schema.isWellScopedAt depth = true)
    (hcanonical : schema.hasCanonicalBinderMetadata = true) :
    result.isGroundAt depth = true ∧
      result.isWellScopedAt depth = true ∧
      result.hasCanonicalBinderMetadata = true :=
  ⟨InstantiatesAt.result_isGroundAt harguments hinst hscoped,
    InstantiatesAt.result_isWellScoped harguments hinst hscoped,
    InstantiatesAt.result_hasCanonicalBinderMetadata
      harguments hinst hcanonical⟩

/-! ## Rule application and derivations -/

/-- Independent declarative application of one explicit rule instance. -/
inductive RuleApplication (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern) : Prop where
  | intro (rule : RuleSchema)
      (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rule)
      (argumentsValid :
        argumentsValidAt rule.metavariables ruleInstance.arguments = true)
      (sideConditionsValid :
        RuleSchema.sideConditionsHold rule ruleInstance.arguments = true)
      (premisesInstantiate :
        InstantiatesList rule.metavariables ruleInstance.arguments rule.premises premises)
      (conclusionInstantiates :
        Instantiates rule.metavariables ruleInstance.arguments rule.conclusion conclusion) :
      RuleApplication definition ruleInstance premises conclusion

/-- Executable local rule instantiation.  It does not inspect child proofs. -/
def instantiateRule? (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) : Option (List Pattern × Pattern) :=
  match definition.1.lookupRule? ruleInstance.ruleId with
  | none => none
  | some rule =>
      if argumentsValidAt rule.metavariables ruleInstance.arguments then do
        if RuleSchema.sideConditionsHold rule ruleInstance.arguments then do
          let premises ←
            instantiateSchemas? rule.metavariables ruleInstance.arguments rule.premises
          let conclusion ←
            instantiateSchema? rule.metavariables ruleInstance.arguments rule.conclusion
          some (premises, conclusion)
        else
          none
      else
        none

/-- Exact correspondence between executable local instantiation and the
declarative rule-application relation. -/
theorem instantiateRule?_eq_some_iff_application
    {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern} :
    instantiateRule? definition ruleInstance = some (premises, conclusion) ↔
      RuleApplication definition ruleInstance premises conclusion := by
  constructor
  · intro h
    simp only [instantiateRule?] at h
    cases hlookup : definition.1.lookupRule? ruleInstance.ruleId with
    | none => simp [hlookup] at h
    | some rule =>
        by_cases harguments :
            argumentsValidAt rule.metavariables ruleInstance.arguments = true
        · cases hpremises :
              RuleSchema.sideConditionsHold rule ruleInstance.arguments with
          | false => simp [hlookup, harguments, hpremises] at h
          | true =>
              cases hpremisesInst :
                  instantiateSchemas? rule.metavariables ruleInstance.arguments
                    rule.premises with
              | none => simp [hlookup, harguments, hpremises, hpremisesInst] at h
              | some premiseResults =>
                  cases hconclusion :
                      instantiateSchema? rule.metavariables ruleInstance.arguments
                        rule.conclusion with
                  | none =>
                      simp [hlookup, harguments, hpremises, hpremisesInst,
                        hconclusion] at h
                  | some conclusionResult =>
                      have heq : (premiseResults, conclusionResult) =
                          (premises, conclusion) := by
                        simpa [hlookup, harguments, hpremises, hpremisesInst,
                          hconclusion] using h
                      cases heq
                      exact .intro rule hlookup harguments hpremises
                        (instantiateSchemasAt?_sound hpremisesInst)
                        (instantiateSchemaAt?_sound hconclusion)
        · simp [hlookup, harguments] at h
  · rintro ⟨rule, hlookup, harguments, hsideConditions, hpremises, hconclusion⟩
    have hpremises' :
        instantiateSchemas? rule.metavariables ruleInstance.arguments rule.premises =
          some premises := instantiateSchemasAt?_complete hpremises
    have hconclusion' :
        instantiateSchema? rule.metavariables ruleInstance.arguments rule.conclusion =
          some conclusion := instantiateSchemaAt?_complete hconclusion
    simp [instantiateRule?, hlookup, harguments, hsideConditions,
      hpremises', hconclusion']

/-- Executable rule instantiation is equivalent to declarative rule
application. -/
theorem instantiateRule_eq_some_iff_application
    {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern} :
    instantiateRule? definition ruleInstance = some (premises, conclusion) ↔
      RuleApplication definition ruleInstance premises conclusion :=
  instantiateRule?_eq_some_iff_application

/-- One explicit rule instance has at most one ordered premise vector and one
conclusion. -/
theorem RuleApplication.outputs_unique
    {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {firstPremises secondPremises : List Pattern}
    {firstConclusion secondConclusion : Pattern}
    (hfirst : RuleApplication definition ruleInstance
      firstPremises firstConclusion)
    (hsecond : RuleApplication definition ruleInstance
      secondPremises secondConclusion) :
    firstPremises = secondPremises ∧
      firstConclusion = secondConclusion := by
  have hpairs : (firstPremises, firstConclusion) =
      (secondPremises, secondConclusion) := by
    apply Option.some.inj
    exact (instantiateRule?_eq_some_iff_application.mpr hfirst).symm.trans
      (instantiateRule?_eq_some_iff_application.mpr hsecond)
  exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

/-- A declarative application in a V2 definition produces a declared outer
judgment shape. -/
theorem RuleApplication.conclusion_hasJudgmentShape
    {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (happlication : RuleApplication definition ruleInstance premises conclusion) :
    definition.1.hasJudgmentShape conclusion = true := by
  cases happlication with
  | intro rule hlookup _ _ _ hconclusion =>
      have hvalid := rule_isValidIn_of_lookup definition hlookup
      exact hconclusion.preservesJudgmentShape
        (RuleSchema.conclusion_hasJudgmentShape_of_validIn hvalid)

/-- Ground rule arguments plus V1 scope/canonical admission make every
declaratively produced conclusion ground and canonical. -/
theorem RuleApplication.conclusion_safety
    {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (happlication : RuleApplication definition ruleInstance premises conclusion) :
    conclusion.isGround = true ∧
      conclusion.hasCanonicalBinderMetadata = true := by
  cases happlication with
  | intro rule hlookup harguments _ _ hconclusion =>
      have hvalidIn := rule_isValidIn_of_lookup definition hlookup
      have hvalidV1 : RuleSchema.isLocallyValid rule = true := by
        simp only [RuleSchema.isValidIn, Bool.and_eq_true] at hvalidIn
        exact hvalidIn.1
      have hsafety := instantiation_safety_contract harguments hconclusion
        (RuleSchema.conclusion_isWellScoped_of_validV1 hvalidV1)
        (RuleSchema.conclusion_hasCanonicalBinderMetadata_of_validV1 hvalidV1)
      exact ⟨hsafety.1, hsafety.2.2⟩

/-- Local Boolean node boundary over an explicit instance and claimed ordered
premise judgments/conclusion. -/
def checkNode (definition : ValidatedCalculusLanguageDef)
    (ruleInstance : RuleInstance) (claimedPremises : List Pattern)
    (claimedConclusion : Pattern) : Bool :=
  match instantiateRule? definition ruleInstance with
  | none => false
  | some (premises, conclusion) =>
      decide (premises = claimedPremises) &&
        decide (conclusion = claimedConclusion)

/-- G1: the local Boolean boundary is exact for declarative rule
application. -/
theorem G1_checkNode_iff_application
    {definition : ValidatedCalculusLanguageDef} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern} :
    checkNode definition ruleInstance premises conclusion = true ↔
      RuleApplication definition ruleInstance premises conclusion := by
  constructor
  · intro hcheck
    simp only [checkNode] at hcheck
    cases hlocal : instantiateRule? definition ruleInstance with
    | none => simp [hlocal] at hcheck
    | some localResult =>
        rcases localResult with ⟨actualPremises, actualConclusion⟩
        simp only [hlocal, Bool.and_eq_true, decide_eq_true_eq] at hcheck
        rcases hcheck with ⟨hpremises, hconclusion⟩
        subst premises
        subst conclusion
        exact instantiateRule?_eq_some_iff_application.mp hlocal
  · intro happlication
    have hlocal :=
      instantiateRule?_eq_some_iff_application.mpr happlication
    simp [checkNode, hlocal]

mutual

/-- Type-valued derivations.  The companion list index forces children to
match the ordered premise slots exactly. -/
inductive Derivation (definition : ValidatedCalculusLanguageDef) : Pattern → Type where
  | byRule (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (application : RuleApplication definition ruleInstance premises conclusion)
      (children : DerivationList definition premises) :
      Derivation definition conclusion

inductive DerivationList (definition : ValidatedCalculusLanguageDef) :
    List Pattern → Type where
  | nil : DerivationList definition []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : Derivation definition premise)
      (tail : DerivationList definition premises) :
      DerivationList definition (premise :: premises)

end

/-! ### Generic semantic interpretation -/

mutual

/-- Any interpretation closed under every admitted rule application holds for
all Type-valued derivations.  This is the generic induction boundary used by
source-specific adequacy theorems. -/
theorem Derivation.sound_of_ruleApplications
    {definition : ValidatedCalculusLanguageDef} (meaning : Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      RuleApplication definition ruleInstance premises conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    {goal : Pattern} (derivation : Derivation definition goal) :
    meaning goal := by
  cases derivation with
  | byRule ruleInstance application children =>
      exact ruleSound ruleInstance _ _ application
        (DerivationList.all_meaning meaning ruleSound children)
termination_by sizeOf derivation

/-- Ordered derivation lists satisfy an interpretation pointwise. -/
theorem DerivationList.all_meaning
    {definition : ValidatedCalculusLanguageDef} (meaning : Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      RuleApplication definition ruleInstance premises conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    {premises : List Pattern} (derivations : DerivationList definition premises) :
    ∀ premise ∈ premises, meaning premise := by
  cases derivations with
  | nil => simp
  | cons head tail =>
      intro premise membership
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · exact equality ▸
          Derivation.sound_of_ruleApplications meaning ruleSound head
      · exact DerivationList.all_meaning meaning ruleSound tail premise membership
termination_by sizeOf derivations

decreasing_by
  all_goals simp_all <;> omega

end

/-! ## Proof-preserving definition extension -/

/-- `target` retains every rule lookup exposed by `source`, with the same
schema.  This is the exact boundary needed to reuse derivations after adding
new rules or extending the underlying term vocabulary: it does not claim that
the target is conservative for new judgments. -/
def RuleLookupRefines (source target : ValidatedCalculusLanguageDef) : Prop :=
  ∀ ruleId rule,
    source.1.lookupRule? ruleId = some rule →
      target.1.lookupRule? ruleId = some rule

/-- A validated definition whose rule table appends to the source table is
automatically a proof-preserving extension, regardless of changes to its
language or judgment signature.  Those changes are already covered by the
target's own V2 validation proof. -/
theorem RuleLookupRefines.of_rules_eq_append
    {source target : ValidatedCalculusLanguageDef} (extraRules : List RuleSchema)
    (hrules : target.1.rules = source.1.rules ++ extraRules) :
    RuleLookupRefines source target := by
  intro ruleId rule hlookup
  have happended :=
    CalculusLanguageDef.lookupRule?_append_of_eq_some source.1 extraRules hlookup
  unfold CalculusLanguageDef.lookupRule? at happended ⊢
  rw [hrules]
  exact happended

theorem RuleLookupRefines.refl (definition : ValidatedCalculusLanguageDef) :
    RuleLookupRefines definition definition := by
  intro ruleId rule hlookup
  exact hlookup

theorem RuleLookupRefines.trans
    {first second third : ValidatedCalculusLanguageDef}
    (hfirst : RuleLookupRefines first second)
    (hsecond : RuleLookupRefines second third) :
    RuleLookupRefines first third := by
  intro ruleId rule hlookup
  exact hsecond ruleId rule (hfirst ruleId rule hlookup)

/-- Missing a source rule is an executable obstruction to lookup refinement;
the extension relation cannot silently weaken or replace a rule. -/
theorem not_ruleLookupRefines_of_missing
    {source target : ValidatedCalculusLanguageDef} {ruleId : RuleId}
    {rule : RuleSchema}
    (hsource : source.1.lookupRule? ruleId = some rule)
    (htarget : target.1.lookupRule? ruleId = none) :
    ¬ RuleLookupRefines source target := by
  intro hrefines
  have := hrefines ruleId rule hsource
  rw [htarget] at this
  contradiction

/-- Replacing a source rule by a different schema at the same identifier also
violates lookup refinement. -/
theorem not_ruleLookupRefines_of_replaced
    {source target : ValidatedCalculusLanguageDef} {ruleId : RuleId}
    {sourceRule targetRule : RuleSchema}
    (hsource : source.1.lookupRule? ruleId = some sourceRule)
    (htarget : target.1.lookupRule? ruleId = some targetRule)
    (hne : sourceRule ≠ targetRule) :
    ¬ RuleLookupRefines source target := by
  intro hrefines
  have hretained := hrefines ruleId sourceRule hsource
  rw [htarget] at hretained
  exact hne (Option.some.inj hretained.symm)

/-- A rule application transports whenever its exact rule schema is retained. -/
theorem RuleApplication.transport
    {source target : ValidatedCalculusLanguageDef}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (hrefines : RuleLookupRefines source target)
    (application :
      RuleApplication source ruleInstance premises conclusion) :
    RuleApplication target ruleInstance premises conclusion := by
  cases application with
  | intro rule hlookup harguments hsideConditions hpremises hconclusion =>
      exact .intro rule (hrefines ruleInstance.ruleId rule hlookup)
        harguments hsideConditions hpremises hconclusion

mutual

/-- Transport a derivation through a proof-preserving rule extension without
changing its goal, rule instances, or ordered child structure. -/
def Derivation.transport
    {source target : ValidatedCalculusLanguageDef}
    (hrefines : RuleLookupRefines source target) {goal : Pattern} :
    Derivation source goal → Derivation target goal
  | .byRule ruleInstance application children =>
      .byRule ruleInstance (application.transport hrefines)
        (DerivationList.transport hrefines children)

/-- Ordered premise derivations transport pointwise through the same rule
extension. -/
def DerivationList.transport
    {source target : ValidatedCalculusLanguageDef}
    (hrefines : RuleLookupRefines source target) {premises : List Pattern} :
    DerivationList source premises → DerivationList target premises
  | .nil => .nil
  | .cons head tail =>
      .cons (Derivation.transport hrefines head)
        (DerivationList.transport hrefines tail)

end

/-! ## Fuel-free raw checker -/

mutual

/-- Fuel-free checker by structural recursion over the raw proof tree. -/
def checkRaw (definition : ValidatedCalculusLanguageDef) :
    Pattern → RawProof → Bool
  | goal, .node ruleInstance children =>
      match instantiateRule? definition ruleInstance with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) &&
            checkRawChildren definition premises children
termination_by _ proof => sizeOf proof

def checkRawChildren (definition : ValidatedCalculusLanguageDef) :
    List Pattern → List RawProof → Bool
  | [], [] => true
  | premise :: premises, child :: children =>
      checkRaw definition premise child &&
        checkRawChildren definition premises children
  | _, _ => false
termination_by _ children => sizeOf children

end

/-- Native accepted-proof subtype. -/
def CheckedProof (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :=
  { proof : RawProof // checkRaw definition goal proof = true }

/-- A fixed raw proof artifact can be accepted for at most one goal. -/
theorem checkRaw_goal_unique
    {definition : ValidatedCalculusLanguageDef} {proof : RawProof}
    {firstGoal secondGoal : Pattern}
    (hfirst : checkRaw definition firstGoal proof = true)
    (hsecond : checkRaw definition secondGoal proof = true) :
    firstGoal = secondGoal := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at hfirst hsecond
      cases hlocal : instantiateRule? definition ruleInstance with
      | none => simp [hlocal] at hfirst
      | some localResult =>
          rcases localResult with ⟨premises, conclusion⟩
          simp only [hlocal, Bool.and_eq_true, decide_eq_true_eq] at hfirst hsecond
          exact hfirst.1.symm.trans hsecond.1

/-- Every accepted goal has a declared V2 outer judgment head and arity. -/
theorem checkRaw_true_goal_hasJudgmentShape
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} {proof : RawProof}
    (hcheck : checkRaw definition goal proof = true) :
    definition.1.hasJudgmentShape goal = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at hcheck
      cases hlocal : instantiateRule? definition ruleInstance with
      | none => simp [hlocal] at hcheck
      | some localResult =>
          rcases localResult with ⟨premises, conclusion⟩
          simp only [hlocal, Bool.and_eq_true, decide_eq_true_eq] at hcheck
          have happlication :
              RuleApplication definition ruleInstance premises conclusion :=
            instantiateRule?_eq_some_iff_application.mp hlocal
          rw [← hcheck.1]
          exact happlication.conclusion_hasJudgmentShape

/-- End-to-end safety: acceptance cannot manufacture an open or
metadata-noncanonical goal.  This theorem does not claim that constructors
inside runtime metavariable payloads are declared or carrier-typed. -/
theorem checkRaw_true_goal_safety
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} {proof : RawProof}
    (hcheck : checkRaw definition goal proof = true) :
    goal.isGround = true ∧ goal.hasCanonicalBinderMetadata = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at hcheck
      cases hlocal : instantiateRule? definition ruleInstance with
      | none => simp [hlocal] at hcheck
      | some localResult =>
          rcases localResult with ⟨premises, conclusion⟩
          simp only [hlocal, Bool.and_eq_true, decide_eq_true_eq] at hcheck
          have happlication :
              RuleApplication definition ruleInstance premises conclusion :=
            instantiateRule?_eq_some_iff_application.mp hlocal
          rw [← hcheck.1]
          exact happlication.conclusion_safety

/-! ## G1--G3 correspondence -/

mutual

/-- Every accepted raw tree denotes a Type-valued derivation.  The stronger
G2 theorem below additionally preserves exact raw-tree identity. -/
theorem checkRaw_soundness {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {proof : RawProof}
    (hcheck : checkRaw definition goal proof = true) :
    Nonempty (Derivation definition goal) := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at hcheck
      cases happlication : instantiateRule? definition ruleInstance with
      | none => simp [happlication] at hcheck
      | some applicationResult =>
          rcases applicationResult with ⟨premises, conclusion⟩
          simp only [happlication, Bool.and_eq_true, decide_eq_true_eq] at hcheck
          rcases hcheck with ⟨hconclusion, hchildren⟩
          subst goal
          have happ : RuleApplication definition ruleInstance premises conclusion :=
            instantiateRule?_eq_some_iff_application.mp happlication
          rcases checkRawChildren_sound hchildren with ⟨childrenDerivation⟩
          exact ⟨Derivation.byRule ruleInstance happ childrenDerivation⟩
termination_by sizeOf proof

theorem checkRawChildren_sound {definition : ValidatedCalculusLanguageDef}
    {premises : List Pattern} {proofs : List RawProof}
    (hcheck : checkRawChildren definition premises proofs = true) :
    Nonempty (DerivationList definition premises) := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => exact ⟨.nil⟩
      | cons proof proofs => simp [checkRawChildren] at hcheck
  | cons premise premises =>
      cases proofs with
      | nil => simp [checkRawChildren] at hcheck
      | cons proof proofs =>
          simp only [checkRawChildren, Bool.and_eq_true] at hcheck
          rcases checkRaw_soundness hcheck.1 with ⟨head⟩
          rcases checkRawChildren_sound hcheck.2 with ⟨tail⟩
          exact ⟨.cons head tail⟩
termination_by sizeOf proofs

end

mutual

/-- Erase a typed derivation to the native raw proof format. -/
def Derivation.erase {definition : ValidatedCalculusLanguageDef} {goal : Pattern} :
    Derivation definition goal → RawProof
  | .byRule ruleInstance _ children =>
      .node ruleInstance (DerivationList.erase children)

def DerivationList.erase {definition : ValidatedCalculusLanguageDef}
    {premises : List Pattern} : DerivationList definition premises → List RawProof
  | .nil => []
  | .cons head tail => Derivation.erase head :: DerivationList.erase tail

end

mutual

/-- CalculusLanguageDef extension preserves the exact raw proof artifact, not merely
the existence of some derivation of the same goal. -/
@[simp] theorem Derivation.erase_transport
    {source target : ValidatedCalculusLanguageDef}
    (hrefines : RuleLookupRefines source target) {goal : Pattern}
    (derivation : Derivation source goal) :
    (derivation.transport hrefines).erase = derivation.erase := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp [Derivation.transport, Derivation.erase,
        DerivationList.erase_transport hrefines children]

/-- Exact erasure preservation for ordered premise lists. -/
@[simp] theorem DerivationList.erase_transport
    {source target : ValidatedCalculusLanguageDef}
    (hrefines : RuleLookupRefines source target) {premises : List Pattern}
    (derivations : DerivationList source premises) :
    (derivations.transport hrefines).erase = derivations.erase := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [DerivationList.transport, DerivationList.erase,
        Derivation.erase_transport hrefines head,
        DerivationList.erase_transport hrefines tail]

end

mutual

/-- Erasing any typed derivation produces an accepted raw tree. -/
theorem checkRaw_erase {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} (derivation : Derivation definition goal) :
    checkRaw definition goal derivation.erase = true := by
  cases derivation with
  | byRule ruleInstance application children =>
      have happlication :
          instantiateRule? definition ruleInstance =
            some (_, goal) :=
        instantiateRule?_eq_some_iff_application.mpr application
      simp only [Derivation.erase, checkRaw, happlication,
        decide_true]
      exact DerivationList.checkRawChildren_erase children

theorem DerivationList.checkRawChildren_erase
    {definition : ValidatedCalculusLanguageDef} {premises : List Pattern}
    (derivations : DerivationList definition premises) :
    checkRawChildren definition premises derivations.erase = true := by
  cases derivations with
  | nil => simp [DerivationList.erase, checkRawChildren]
  | cons head tail =>
      simp only [DerivationList.erase, checkRawChildren, Bool.and_eq_true]
      exact ⟨checkRaw_erase head,
        DerivationList.checkRawChildren_erase tail⟩

end

mutual

/-- Exact reconstruction of an accepted raw tree. -/
theorem checkRaw_exists_derivation_with_exact_erasure
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} {proof : RawProof}
    (hcheck : checkRaw definition goal proof = true) :
    ∃ derivation : Derivation definition goal, derivation.erase = proof := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at hcheck
      cases hlocal : instantiateRule? definition ruleInstance with
      | none => simp [hlocal] at hcheck
      | some localResult =>
          rcases localResult with ⟨premises, conclusion⟩
          simp only [hlocal, Bool.and_eq_true, decide_eq_true_eq] at hcheck
          rcases hcheck with ⟨hconclusion, hchildren⟩
          subst goal
          have happlication :
              RuleApplication definition ruleInstance premises conclusion :=
            instantiateRule?_eq_some_iff_application.mp hlocal
          rcases checkRawChildren_exists_derivations_with_exact_erasure hchildren with
            ⟨childDerivations, herasure⟩
          refine ⟨Derivation.byRule ruleInstance happlication childDerivations, ?_⟩
          simp [Derivation.erase, herasure]
termination_by sizeOf proof

theorem checkRawChildren_exists_derivations_with_exact_erasure
    {definition : ValidatedCalculusLanguageDef} {premises : List Pattern}
    {proofs : List RawProof}
    (hcheck : checkRawChildren definition premises proofs = true) :
    ∃ derivations : DerivationList definition premises,
      derivations.erase = proofs := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => exact ⟨.nil, by simp [DerivationList.erase]⟩
      | cons proof proofs => simp [checkRawChildren] at hcheck
  | cons premise premises =>
      cases proofs with
      | nil => simp [checkRawChildren] at hcheck
      | cons proof proofs =>
          simp only [checkRawChildren, Bool.and_eq_true] at hcheck
          rcases checkRaw_exists_derivation_with_exact_erasure hcheck.1 with
            ⟨head, hhead⟩
          rcases checkRawChildren_exists_derivations_with_exact_erasure hcheck.2 with
            ⟨tail, htail⟩
          refine ⟨.cons head tail, ?_⟩
          simp [DerivationList.erase, hhead, htail]
termination_by sizeOf proofs

end

/-- G2: raw checking is exactly equivalent to the existence of a typed
derivation whose erasure is that same raw artifact. -/
theorem G2_checkRaw_iff_exists_derivation_erases_to
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} {proof : RawProof} :
    checkRaw definition goal proof = true ↔
      ∃ derivation : Derivation definition goal, derivation.erase = proof := by
  constructor
  · exact checkRaw_exists_derivation_with_exact_erasure
  · rintro ⟨derivation, rfl⟩
    exact checkRaw_erase derivation

/-- Retaining every used rule preserves acceptance of the identical raw proof
tree.  New target rules may add proofs, so no converse is asserted. -/
theorem checkRaw_true_of_ruleLookupRefines
    {source target : ValidatedCalculusLanguageDef} {goal : Pattern}
    {proof : RawProof} (hrefines : RuleLookupRefines source target)
    (hsource : checkRaw source goal proof = true) :
    checkRaw target goal proof = true := by
  rcases G2_checkRaw_iff_exists_derivation_erases_to.mp hsource with
    ⟨derivation, herasure⟩
  have htarget := checkRaw_erase (derivation.transport hrefines)
  rw [Derivation.erase_transport, herasure] at htarget
  exact htarget

/-- A checked proof transports with exactly the same raw proof payload. -/
def CheckedProof.transport
    {source target : ValidatedCalculusLanguageDef} {goal : Pattern}
    (hrefines : RuleLookupRefines source target)
    (proof : CheckedProof source goal) : CheckedProof target goal :=
  ⟨proof.1, checkRaw_true_of_ruleLookupRefines hrefines proof.2⟩

/-- G3: native checked proof objects exist exactly when a typed derivation
exists. -/
theorem G3_checkedProof_nonempty_iff_derivation
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} :
    Nonempty (CheckedProof definition goal) ↔
      Nonempty (Derivation definition goal) := by
  constructor
  · rintro ⟨⟨proof, hcheck⟩⟩
    rcases checkRaw_exists_derivation_with_exact_erasure hcheck with
      ⟨derivation, _⟩
    exact ⟨derivation⟩
  · rintro ⟨derivation⟩
    exact ⟨⟨derivation.erase, checkRaw_erase derivation⟩⟩

/-! ## Generic corpus and boundary fixtures -/

private def ruleId (name : String) : RuleId := ⟨name⟩

private def judgmentDecl (head : String) (arity : Nat) : JudgmentDecl :=
  { head, arity }

private def judgmentFact (theory proposition : Pattern) : Pattern :=
  .apply "Fact" [theory, proposition]

private def judgmentEdge (theory source target : Pattern) : Pattern :=
  .apply "Edge" [theory, source, target]

private def judgmentPath (theory source target : Pattern) : Pattern :=
  .apply "Path" [theory, source, target]

private def factRule : RuleSchema :=
  { id := ruleId "fact"
    metavariables := [("theory", 0), ("proposition", 0)]
    premises := []
    conclusion := judgmentFact (.fvar "theory") (.fvar "proposition") }

private def edgeRule : RuleSchema :=
  { id := ruleId "edge"
    metavariables := [("theory", 0), ("source", 0), ("target", 0)]
    premises := []
    conclusion :=
      judgmentEdge (.fvar "theory") (.fvar "source") (.fvar "target") }

private def stepRule : RuleSchema :=
  { id := ruleId "step"
    metavariables :=
      [("theory", 0), ("source", 0), ("middle", 0), ("target", 0)]
    premises :=
      [ judgmentEdge (.fvar "theory") (.fvar "source") (.fvar "middle")
      , judgmentEdge (.fvar "theory") (.fvar "middle") (.fvar "target") ]
    conclusion :=
      judgmentPath (.fvar "theory") (.fvar "source") (.fvar "target") }

private def corpusDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "generic-inference-corpus"
    judgments :=
      [judgmentDecl "Fact" 2, judgmentDecl "Edge" 3, judgmentDecl "Path" 3]
    rules := [factRule, edgeRule, stepRule] }

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

theorem corpusDefinition_valid : corpusDefinition.isValid = true := by
  simp [corpusDefinition, CalculusLanguageDef.isValid,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.hasValidLocalRules, CalculusLanguageDef.ruleIds,
    emptyLanguage_validate, factRule, edgeRule, stepRule, ruleId,
    judgmentDecl, judgmentFact, judgmentEdge, judgmentPath,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorsValid,
    RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    fixedConstructorListsValid,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  decide

private def corpus : ValidatedCalculusLanguageDef :=
  ⟨corpusDefinition, corpusDefinition_valid⟩

private def extraFactRule : RuleSchema :=
  { factRule with id := ruleId "fact-extra" }

private def extendedCorpusDefinition : CalculusLanguageDef :=
  { corpusDefinition with rules := corpusDefinition.rules ++ [extraFactRule] }

private theorem extendedCorpusDefinition_valid :
    extendedCorpusDefinition.isValid = true := by
  simp [extendedCorpusDefinition, corpusDefinition,
    CalculusLanguageDef.isValid, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.ruleIds, emptyLanguage_validate, extraFactRule,
    factRule, edgeRule, stepRule, ruleId, judgmentDecl, judgmentFact,
    judgmentEdge, judgmentPath, RuleSchema.isValidIn,
    CalculusLanguageDef.judgmentSchemaValid, CalculusLanguageDef.lookupJudgment?,
    fixedConstructorsValid, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, fixedConstructorListsValid,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  decide

private def extendedCorpus : ValidatedCalculusLanguageDef :=
  ⟨extendedCorpusDefinition, extendedCorpusDefinition_valid⟩

/-- Positive extension fixture: adding a genuinely new rule preserves every
lookup and hence every proof in the original corpus. -/
theorem corpus_refines_extendedCorpus :
    RuleLookupRefines corpus extendedCorpus := by
  apply RuleLookupRefines.of_rules_eq_append [extraFactRule]
  rfl

private def emptyRuleCorpusDefinition : CalculusLanguageDef :=
  { corpusDefinition with rules := [] }

private theorem emptyRuleCorpusDefinition_valid :
    emptyRuleCorpusDefinition.isValid = true := by
  simp [emptyRuleCorpusDefinition, corpusDefinition,
    CalculusLanguageDef.isValid, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.hasValidLocalRules,
    CalculusLanguageDef.ruleIds, emptyLanguage_validate, judgmentDecl,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

private def emptyRuleCorpus : ValidatedCalculusLanguageDef :=
  ⟨emptyRuleCorpusDefinition, emptyRuleCorpusDefinition_valid⟩

/-- Negative extension fixture: removing the `fact` rule destroys lookup
refinement. -/
theorem corpus_does_not_refine_emptyRuleCorpus :
    ¬ RuleLookupRefines corpus emptyRuleCorpus := by
  apply not_ruleLookupRefines_of_missing
      (ruleId := ruleId "fact") (rule := factRule)
  · rfl
  · rfl

private def theoryData : Pattern := .apply "TheoryState" []
private def aData : Pattern := .apply "A" []
private def bData : Pattern := .apply "B" []
private def cData : Pattern := .apply "C" []

private def factProof : RawProof :=
  .node { ruleId := ruleId "fact", arguments := [theoryData, aData] } []

private def edgeABProof : RawProof :=
  .node
    { ruleId := ruleId "edge", arguments := [theoryData, aData, bData] } []

private def edgeBCProof : RawProof :=
  .node
    { ruleId := ruleId "edge", arguments := [theoryData, bData, cData] } []

private def stepProof : RawProof :=
  .node
    { ruleId := ruleId "step"
      arguments := [theoryData, aData, bData, cData] }
    [edgeABProof, edgeBCProof]

theorem corpus_fact_accepts :
    checkRaw corpus (judgmentFact theoryData aData) factProof = true := by
  simp [checkRaw, checkRawChildren, factProof, corpus, corpusDefinition,
    factRule, edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?, judgmentFact,
    judgmentEdge, judgmentPath, theoryData, aData, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def corpusFactChecked :
    CheckedProof corpus (judgmentFact theoryData aData) :=
  ⟨factProof, corpus_fact_accepts⟩

/-- The nontrivial extension fixture accepts the identical raw proof payload. -/
theorem extendedCorpus_fact_accepts :
    checkRaw extendedCorpus (judgmentFact theoryData aData) factProof = true :=
  checkRaw_true_of_ruleLookupRefines
    corpus_refines_extendedCorpus corpus_fact_accepts

theorem corpusFactChecked_transport_payload :
    (corpusFactChecked.transport corpus_refines_extendedCorpus).1 = factProof :=
  rfl

theorem corpus_edge_accepts :
    checkRaw corpus (judgmentEdge theoryData aData bData) edgeABProof = true := by
  simp [checkRaw, checkRawChildren, edgeABProof, corpus, corpusDefinition,
    factRule, edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?, judgmentFact,
    judgmentEdge, judgmentPath, theoryData, aData, bData, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

theorem corpus_step_accepts :
    checkRaw corpus (judgmentPath theoryData aData cData) stepProof = true := by
  simp [checkRaw, checkRawChildren, edgeABProof, edgeBCProof, stepProof, corpus,
    corpusDefinition, factRule, edgeRule, stepRule, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, judgmentFact, judgmentEdge,
    judgmentPath, theoryData, aData, bData, cData, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def swappedStepProof : RawProof :=
  .node
    { ruleId := ruleId "step"
      arguments := [theoryData, aData, bData, cData] }
    [edgeBCProof, edgeABProof]

private def omittedStepProof : RawProof :=
  .node
    { ruleId := ruleId "step"
      arguments := [theoryData, aData, bData, cData] }
    [edgeABProof]

private def extraStepProof : RawProof :=
  .node
    { ruleId := ruleId "step"
      arguments := [theoryData, aData, bData, cData] }
    [edgeABProof, edgeBCProof, edgeBCProof]

private def unknownRuleProof : RawProof :=
  .node { ruleId := ruleId "unknown", arguments := [] } []

private def wrongArityProof : RawProof :=
  .node
    { ruleId := ruleId "edge", arguments := [theoryData, aData] } []

private def nongroundArgumentProof : RawProof :=
  .node
    { ruleId := ruleId "fact", arguments := [theoryData, .fvar "open"] } []

private def swappedArgumentFactProof : RawProof :=
  .node
    { ruleId := ruleId "fact", arguments := [aData, theoryData] } []

private def extraArgumentFactProof : RawProof :=
  .node
    { ruleId := ruleId "fact", arguments := [theoryData, aData, bData] } []

theorem corpus_swapped_children_reject :
    checkRaw corpus (judgmentPath theoryData aData cData) swappedStepProof = false := by
  simp [checkRaw, checkRawChildren, edgeABProof, edgeBCProof, swappedStepProof,
    corpus, corpusDefinition, factRule, edgeRule, stepRule, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, judgmentFact, judgmentEdge,
    judgmentPath, theoryData, aData, bData, cData, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem corpus_omitted_child_reject :
    checkRaw corpus (judgmentPath theoryData aData cData) omittedStepProof = false := by
  simp [checkRaw, checkRawChildren, edgeABProof, omittedStepProof, corpus,
    corpusDefinition, factRule, edgeRule, stepRule, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, judgmentFact, judgmentEdge,
    judgmentPath, theoryData, aData, bData, cData, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem corpus_extra_child_reject :
    checkRaw corpus (judgmentPath theoryData aData cData) extraStepProof = false := by
  simp [checkRaw, checkRawChildren, edgeABProof, edgeBCProof, extraStepProof,
    corpus, corpusDefinition, factRule, edgeRule, stepRule, instantiateRule?,
    CalculusLanguageDef.lookupRule?, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, judgmentFact, judgmentEdge,
    judgmentPath, theoryData, aData, bData, cData, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem corpus_unknown_rule_reject :
    checkRaw corpus (judgmentFact theoryData aData) unknownRuleProof = false := by
  simp [checkRaw, unknownRuleProof, corpus, corpusDefinition, factRule,
    edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?, judgmentFact,
    judgmentEdge, judgmentPath, theoryData, aData, ruleId]

theorem corpus_wrong_arity_reject :
    checkRaw corpus (judgmentEdge theoryData aData bData) wrongArityProof = false := by
  simp [checkRaw, wrongArityProof, corpus, corpusDefinition, factRule,
    edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, judgmentFact, judgmentEdge, judgmentPath, theoryData,
    aData, bData, ruleId]

theorem corpus_nonground_argument_reject :
    checkRaw corpus (judgmentFact theoryData aData) nongroundArgumentProof = false := by
  simp [checkRaw, nongroundArgumentProof, corpus, corpusDefinition, factRule,
    edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, judgmentFact, judgmentEdge, judgmentPath,
    theoryData, aData, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]

theorem corpus_swapped_arguments_reject :
    checkRaw corpus (judgmentFact theoryData aData) swappedArgumentFactProof = false := by
  simp [checkRaw, swappedArgumentFactProof, corpus, corpusDefinition,
    factRule, edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, argumentValidAt, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?, judgmentFact,
    judgmentEdge, judgmentPath, theoryData, aData, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

theorem corpus_extra_argument_reject :
    checkRaw corpus (judgmentFact theoryData aData) extraArgumentFactProof = false := by
  simp [checkRaw, extraArgumentFactProof, corpus, corpusDefinition,
    factRule, edgeRule, stepRule, instantiateRule?, CalculusLanguageDef.lookupRule?,
    argumentsValidAt, judgmentFact, judgmentEdge, judgmentPath, theoryData,
    aData, bData, ruleId]

/-! ### Exact-depth and structural-substitution gates -/

theorem exactDepth_binder_relative_instantiates :
    argumentsValidAt [("captured", 1)] [.bvar 0] = true ∧
      instantiateSchema? [("captured", 1)] [.bvar 0]
          (.lambda none (.fvar "captured")) =
        some (.lambda none (.bvar 0)) := by
  simp [argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.hasCanonicalBinderMetadata]

theorem depthZero_bvar_reject :
    argumentsValidAt [("x", 0)] [.bvar 0] = false := by
  rfl

theorem outOfScope_bvar_reject :
    argumentsValidAt [("x", 1)] [.bvar 1] = false := by
  rfl

private def wrongDepthZeroRule : RuleSchema :=
  { id := ruleId "wrong-depth-zero"
    metavariables := [("x", 1)]
    premises := []
    conclusion := .fvar "x" }

private def wrongDepthTwoRule : RuleSchema :=
  { id := ruleId "wrong-depth-two"
    metavariables := [("x", 1)]
    premises := []
    conclusion := .lambda none (.lambda none (.fvar "x")) }

theorem wrongDepthZero_schema_reject :
    RuleSchema.isLocallyValid wrongDepthZeroRule = false := by
  simp [wrongDepthZeroRule, RuleSchema.isLocallyValid, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt]

theorem wrongDepthTwo_schema_reject :
    RuleSchema.isLocallyValid wrongDepthTwoRule = false := by
  simp [wrongDepthTwoRule, RuleSchema.isLocallyValid, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt]

/-- N4: one literal schema name cannot stand simultaneously for values at
depth zero and depth one.  The offending mixed-depth occurrence is rejected
at admission, before any rule instance is checked. -/
private def literalMixedDepthRule : RuleSchema :=
  { id := ruleId "literal-mixed-depth"
    metavariables := [("x", 0)]
    premises := []
    conclusion :=
      .apply "MixedDepth" [.fvar "x", .lambda none (.fvar "x")] }

theorem literalMixedDepth_schema_reject :
    RuleSchema.isLocallyValid literalMixedDepthRule = false := by
  simp [literalMixedDepthRule, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt]

/-- The depth-blind matcher counterexample is rejected: a value captured at
depth one cannot be reused unchanged at depth two. -/
theorem depthBlind_inner_reuse_rejects :
    instantiateSchema? [("x", 1)] [.bvar 0]
        (.lambda none (.lambda none (.fvar "x"))) = none := by
  simp [instantiateSchema?, instantiateSchemaAt?, lookupArgumentAt?]

theorem betaGolden_preserves_explicit_subst :
    argumentsValidAt [("body", 1), ("argument", 0)]
        [.bvar 0, .apply "K" []] = true ∧
      instantiateSchema? [("body", 1), ("argument", 0)]
          [.bvar 0, .apply "K" []]
          (.subst (.fvar "body") (.fvar "argument")) =
        some (.subst (.bvar 0) (.apply "K" [])) := by
  simp [argumentsValidAt, argumentValidAt, instantiateSchema?,
    instantiateSchemaAt?, lookupArgumentAt?, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def namedBinderRule : RuleSchema :=
  { id := ruleId "named-binder"
    metavariables := [("body", 1)]
    premises := []
    conclusion := .lambda (some "x") (.fvar "body") }

theorem namedBinder_schema_reject :
    RuleSchema.isLocallyValid namedBinderRule = false := by
  simp [namedBinderRule, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.hasCanonicalBinderMetadata]

theorem namedBinder_argument_reject :
    argumentsValidAt [("function", 0)]
      [.lambda (some "x") (.bvar 0)] = false := by
  decide

private def collectionRestRule : RuleSchema :=
  { id := ruleId "collection-rest"
    metavariables := [("rest", 0)]
    premises := []
    conclusion := .collection .vec [] (some "rest") }

theorem collectionRest_schema_reject :
    RuleSchema.isLocallyValid collectionRestRule = false := by
  simp [collectionRestRule, RuleSchema.isLocallyValid, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt]

private def duplicateMetavariableRule : RuleSchema :=
  { id := ruleId "duplicate-metavariable"
    metavariables := [("x", 0), ("x", 0)]
    premises := []
    conclusion := .fvar "x" }

theorem duplicateMetavariable_schema_reject :
    RuleSchema.isLocallyValid duplicateMetavariableRule = false := by
  decide

/-! ### V2 judgment-signature gates -/

private def pairConstructor : GrammarRule :=
  { label := "Pair"
    category := "Datum"
    params :=
      [ .simple "left" (.base "Datum")
      , .simple "right" (.base "Datum") ]
    syntaxPattern := [] }

private def signatureFixtureLanguage : LanguageDef :=
  { name := "inference-signature-fixture"
    types := [TypeDecl.plain "Datum"]
    terms := [pairConstructor]
    equations := []
    rewrites := [] }

private def judgmentHolds (datum : Pattern) : Pattern :=
  .apply "Holds" [datum]

private def nestedConstructorRule : RuleSchema :=
  { id := ruleId "nested-constructor"
    metavariables := [("left", 0), ("right", 0)]
    premises := []
    conclusion :=
      judgmentHolds (.apply "Pair" [.fvar "left", .fvar "right"]) }

private def nestedConstructorDefinition : CalculusLanguageDef :=
  { toLanguageDef := signatureFixtureLanguage
    judgments := [judgmentDecl "Holds" 1]
    rules := [nestedConstructorRule] }

theorem nestedConstructor_schema_accepts :
    (nestedConstructorDefinition.judgmentSchemaValid
      nestedConstructorRule.conclusion) = true := by
  simp [nestedConstructorDefinition, nestedConstructorRule, judgmentHolds,
    CalculusLanguageDef.judgmentSchemaValid, CalculusLanguageDef.lookupJudgment?,
    judgmentDecl, fixedConstructorListsValid, fixedConstructorsValid,
    languageHasConstructorArity, signatureFixtureLanguage, pairConstructor]

private def unknownNestedConstructorRule : RuleSchema :=
  { id := ruleId "unknown-nested-constructor"
    metavariables := [("datum", 0)]
    premises := []
    conclusion := judgmentHolds (.apply "UnknownData" [.fvar "datum"]) }

private def wrongNestedArityRule : RuleSchema :=
  { id := ruleId "wrong-nested-arity"
    metavariables := [("datum", 0)]
    premises := []
    conclusion := judgmentHolds (.apply "Pair" [.fvar "datum"]) }

theorem unknownNestedConstructor_schema_reject :
    (nestedConstructorDefinition.judgmentSchemaValid
      unknownNestedConstructorRule.conclusion) = false := by
  simp [nestedConstructorDefinition, unknownNestedConstructorRule,
    judgmentHolds, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, judgmentDecl, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    signatureFixtureLanguage, pairConstructor]

theorem wrongNestedArity_schema_reject :
    (nestedConstructorDefinition.judgmentSchemaValid
      wrongNestedArityRule.conclusion) = false := by
  simp [nestedConstructorDefinition, wrongNestedArityRule,
    judgmentHolds, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, judgmentDecl, fixedConstructorListsValid,
    fixedConstructorsValid, languageHasConstructorArity,
    signatureFixtureLanguage, pairConstructor]

theorem unknownJudgmentHead_schema_reject :
    (nestedConstructorDefinition.judgmentSchemaValid
      (.apply "UnknownJudgment" [.fvar "datum"])) = false := by
  simp [nestedConstructorDefinition, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, judgmentDecl]

theorem wrongJudgmentArity_schema_reject :
    (nestedConstructorDefinition.judgmentSchemaValid
      (.apply "Holds" [.fvar "left", .fvar "right"])) = false := by
  simp [nestedConstructorDefinition, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, judgmentDecl]

private def binderJudgmentRule : RuleSchema :=
  { id := ruleId "binder-judgment"
    metavariables := [("body", 1)]
    premises := []
    conclusion := .apply "Scoped" [.lambda none (.fvar "body")] }

private def binderJudgmentDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "binder-judgment-fixture"
    judgments := [judgmentDecl "Scoped" 1]
    rules := [binderJudgmentRule] }

/-- V2 imposes no ad hoc ban on a binder-bearing judgment argument; V1's
exact-depth, scope, and canonical-metadata gates remain authoritative. -/
theorem binderJudgment_definition_accepts :
    binderJudgmentDefinition.isValid = true := by
  simp [binderJudgmentDefinition, CalculusLanguageDef.isValid,
    CalculusLanguageDef.hasValidLocalRules, CalculusLanguageDef.ruleIds,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    binderJudgmentRule, judgmentDecl, ruleId,
    RuleSchema.isValidIn, CalculusLanguageDef.judgmentSchemaValid,
    CalculusLanguageDef.lookupJudgment?, fixedConstructorListsValid,
    fixedConstructorsValid, RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    emptyLanguage_validate]
  decide

private def constructorCollisionDefinition : CalculusLanguageDef :=
  { toLanguageDef := signatureFixtureLanguage
    judgments := [judgmentDecl "Pair" 2] }

theorem constructorJudgmentCollision_reject :
    constructorCollisionDefinition.judgmentSignatureValid = false := by
  simp [constructorCollisionDefinition,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    judgmentDecl, signatureFixtureLanguage, pairConstructor]

private def duplicateIdDefinition : CalculusLanguageDef :=
  { toLanguageDef := LanguageDef.empty "duplicate-id"
    judgments :=
      [judgmentDecl "Fact" 2, judgmentDecl "Edge" 3, judgmentDecl "Path" 3]
    rules := [factRule, factRule] }

theorem duplicateId_definition_reject :
    duplicateIdDefinition.isValid = false := by
  have hV1 : duplicateIdDefinition.hasValidLocalRules = false := by
    unfold duplicateIdDefinition CalculusLanguageDef.hasValidLocalRules CalculusLanguageDef.ruleIds
    simp only [Bool.and_eq_false_iff]
    right
    decide
  simp [CalculusLanguageDef.isValid, hV1]

end Mettapedia.GSLT.LanguageDef.InferenceChecker
