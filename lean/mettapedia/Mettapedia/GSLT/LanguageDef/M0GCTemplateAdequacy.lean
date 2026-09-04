import Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering

/-!
# Source adequacy for the M0GC rule-template language

The generated M0GC C replay loop does not invoke the generic source-rule
instantiator.  It matches a finite template language consisting only of
formal-variable slots and ordered applications.  This module isolates that
language before physical table flattening and proves that compiling an
authored applicative schema into a template preserves its exact source
instantiation.

Side conditions and binders are deliberately outside this template fragment.
They must be realized by a richer generated checker rather than silently
accepted by the M0GC matcher.

Maturity boundary: this is a fully connected proof of concept for the bounded
applicative M0GC lane, not the endgame NIK template language.  Its semantic
commuting theorems are intended to survive replacement, but the binder-free
carrier and finite rule-profile specialization are explicitly non-final.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Independent template language -/

/-- The logical carrier implemented by M0GC template matching, before numeric
symbol encoding and flat-table layout. -/
inductive SchemaTemplate where
  | variable (slot : Nat)
  | application (head : String) (arguments : List SchemaTemplate)

mutual

private def decEqSchemaTemplate :
    (first second : SchemaTemplate) → Decidable (first = second)
  | .variable first, .variable second =>
      if equal : first = second then
        isTrue (by cases equal; rfl)
      else isFalse (fun equality => by cases equality; exact equal rfl)
  | .variable _, .application _ _ =>
      isFalse (fun equality => by cases equality)
  | .application _ _, .variable _ =>
      isFalse (fun equality => by cases equality)
  | .application firstHead firstArguments,
      .application secondHead secondArguments =>
      match decEq firstHead secondHead,
          decEqSchemaTemplateList firstArguments secondArguments with
      | isTrue headEqual, isTrue argumentsEqual =>
          isTrue (by cases headEqual; cases argumentsEqual; rfl)
      | isFalse headDifferent, _ =>
          isFalse (fun equality => by cases equality; exact headDifferent rfl)
      | _, isFalse argumentsDifferent =>
          isFalse (fun equality => by
            cases equality
            exact argumentsDifferent rfl)

private def decEqSchemaTemplateList :
    (first second : List SchemaTemplate) → Decidable (first = second)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun equality => by cases equality)
  | _ :: _, [] => isFalse (fun equality => by cases equality)
  | first :: firstTail, second :: secondTail =>
      match decEqSchemaTemplate first second,
          decEqSchemaTemplateList firstTail secondTail with
      | isTrue headEqual, isTrue tailEqual =>
          isTrue (by cases headEqual; cases tailEqual; rfl)
      | isFalse headDifferent, _ =>
          isFalse (fun equality => by
            cases equality
            exact headDifferent rfl)
      | _, isFalse tailDifferent =>
          isFalse (fun equality => by
            cases equality
            exact tailDifferent rfl)

end

instance : DecidableEq SchemaTemplate := decEqSchemaTemplate

/-- Resolve one authored formal occurrence to its left-to-right slot.  The
depth coordinate is retained, so two same-named occurrences at different
binder depths are never identified. -/
def compileSlot? : List (String × Nat) → String → Nat → Option Nat
  | [], _, _ => none
  | formal :: formals, name, depth =>
      if formal = (name, depth) then some 0
      else (compileSlot? formals name depth).map Nat.succ

mutual

/-- Compile exactly the application/free-metavariable fragment at one ambient
depth. -/
def compileTemplateAt? (formals : List (String × Nat)) (depth : Nat) :
    Pattern → Option SchemaTemplate
  | .fvar name => (compileSlot? formals name depth).map .variable
  | .apply head arguments => do
      let compiled ← compileTemplatesAt? formals depth arguments
      some (.application head compiled)
  | .bvar _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ |
      .collection _ _ _ => none
termination_by pattern => sizeOf pattern

def compileTemplatesAt? (formals : List (String × Nat)) (depth : Nat) :
    List Pattern → Option (List SchemaTemplate)
  | [] => some []
  | pattern :: patterns => do
      let head ← compileTemplateAt? formals depth pattern
      let tail ← compileTemplatesAt? formals depth patterns
      some (head :: tail)
termination_by patterns => sizeOf patterns

end

def compileTemplate? (formals : List (String × Nat)) (pattern : Pattern) :
    Option SchemaTemplate :=
  compileTemplateAt? formals 0 pattern

def compileTemplates? (formals : List (String × Nat))
    (patterns : List Pattern) : Option (List SchemaTemplate) :=
  compileTemplatesAt? formals 0 patterns

mutual

/-- Instantiate one compiled template with an ordered source argument vector. -/
def instantiateTemplate? (arguments : List Pattern) :
    SchemaTemplate → Option Pattern
  | .variable slot => arguments[slot]?
  | .application head templates => do
      let instantiated ← instantiateTemplates? arguments templates
      some (.apply head instantiated)
termination_by template => sizeOf template

def instantiateTemplates? (arguments : List Pattern) :
    List SchemaTemplate → Option (List Pattern)
  | [] => some []
  | template :: templates => do
      let head ← instantiateTemplate? arguments template
      let tail ← instantiateTemplates? arguments templates
      some (head :: tail)
termination_by templates => sizeOf templates

end

/-! ## Slot and schema adequacy -/

/-- Compiled positional lookup is exactly the existing named, depth-indexed
source lookup. -/
theorem compileSlot?_bind_getElem?_eq_lookupArgumentAt? :
    ∀ (formals : List (String × Nat)) (arguments : List Pattern)
      (name : String) (depth : Nat),
      (compileSlot? formals name depth).bind (fun slot => arguments[slot]?) =
        lookupArgumentAt? formals arguments name depth := by
  intro formals
  induction formals with
  | nil =>
      intro arguments name depth
      simp [compileSlot?, lookupArgumentAt?]
  | cons formal formals inductionHypothesis =>
      intro arguments name depth
      cases arguments with
      | nil =>
          by_cases hmatch : formal = (name, depth)
          · simp [compileSlot?, lookupArgumentAt?, hmatch]
          · simp [compileSlot?, lookupArgumentAt?, hmatch]
      | cons argument arguments =>
          by_cases hmatch : formal = (name, depth)
          · simp [compileSlot?, lookupArgumentAt?, hmatch]
          · cases slotEq : compileSlot? formals name depth with
            | none =>
                have tailLookup :=
                  inductionHypothesis arguments name depth
                rw [slotEq] at tailLookup
                simpa [compileSlot?, lookupArgumentAt?, hmatch, slotEq] using
                  tailLookup
            | some slot =>
                have tailLookup :=
                  inductionHypothesis arguments name depth
                rw [slotEq] at tailLookup
                simpa [compileSlot?, lookupArgumentAt?, hmatch, slotEq] using
                  tailLookup

/-- Successful template compilation preserves exact source instantiation at
the same binder depth. -/
theorem instantiateTemplate?_of_compileTemplateAt? :
    ∀ (formals : List (String × Nat)) (arguments : List Pattern)
      (depth : Nat) (schema : Pattern) (template : SchemaTemplate),
      compileTemplateAt? formals depth schema = some template →
        instantiateTemplate? arguments template =
          instantiateSchemaAt? formals arguments depth schema := by
  intro formals arguments depth schema
  refine Pattern.rec
    (motive_1 := fun source => ∀ target,
      compileTemplateAt? formals depth source = some target →
        instantiateTemplate? arguments target =
          instantiateSchemaAt? formals arguments depth source)
    (motive_2 := fun sources => ∀ targets,
      compileTemplatesAt? formals depth sources = some targets →
        instantiateTemplates? arguments targets =
          instantiateSchemasAt? formals arguments depth sources)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ schema
  · intro index target compiled
    simp [compileTemplateAt?] at compiled
  · intro name target compiled
    simp only [compileTemplateAt?] at compiled
    cases slotEq : compileSlot? formals name depth with
    | none => simp [slotEq] at compiled
    | some slot =>
        simp [slotEq] at compiled
        subst target
        have bridge :=
          compileSlot?_bind_getElem?_eq_lookupArgumentAt?
            formals arguments name depth
        rw [slotEq] at bridge
        simpa [instantiateTemplate?, instantiateSchemaAt?] using bridge
  · intro head sources sourcesIH target compiled
    simp only [compileTemplateAt?] at compiled
    cases childrenEq : compileTemplatesAt? formals depth sources with
    | none => simp [childrenEq] at compiled
    | some targets =>
        simp [childrenEq] at compiled
        subst target
        simp only [instantiateTemplate?, instantiateSchemaAt?]
        rw [sourcesIH targets childrenEq]
  · intro binder body bodyIH target compiled
    simp [compileTemplateAt?] at compiled
  · intro arity binders body bodyIH target compiled
    simp [compileTemplateAt?] at compiled
  · intro body replacement bodyIH replacementIH target compiled
    simp [compileTemplateAt?] at compiled
  · intro collectionType sources rest sourcesIH target compiled
    simp [compileTemplateAt?] at compiled
  · intro targets compiled
    simp only [compileTemplatesAt?, Option.some.injEq] at compiled
    subst targets
    simp [instantiateTemplates?, instantiateSchemasAt?]
  · intro source sources sourceIH sourcesIH targets compiled
    simp only [compileTemplatesAt?] at compiled
    cases headEq : compileTemplateAt? formals depth source with
    | none => simp [headEq] at compiled
    | some head =>
        cases tailEq : compileTemplatesAt? formals depth sources with
        | none => simp [headEq, tailEq] at compiled
        | some tail =>
            simp [headEq, tailEq] at compiled
            subst targets
            simp only [instantiateTemplates?, instantiateSchemasAt?]
            rw [sourceIH head headEq, sourcesIH tail tailEq]

/-- Ordered template vectors preserve exact ordered schema instantiation. -/
theorem instantiateTemplates?_of_compileTemplatesAt?
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) : ∀ (schemas : List Pattern)
      (templates : List SchemaTemplate),
      compileTemplatesAt? formals depth schemas = some templates →
        instantiateTemplates? arguments templates =
          instantiateSchemasAt? formals arguments depth schemas := by
  intro schemas
  induction schemas with
  | nil =>
      intro templates compiled
      simp only [compileTemplatesAt?, Option.some.injEq] at compiled
      subst templates
      simp [instantiateTemplates?, instantiateSchemasAt?]
  | cons schema schemas inductionHypothesis =>
      intro templates compiled
      simp only [compileTemplatesAt?] at compiled
      cases headEq : compileTemplateAt? formals depth schema with
      | none => simp [headEq] at compiled
      | some head =>
          cases tailEq : compileTemplatesAt? formals depth schemas with
          | none => simp [headEq, tailEq] at compiled
          | some tail =>
              simp [headEq, tailEq] at compiled
              subst templates
              simp only [instantiateTemplates?, instantiateSchemasAt?]
              rw [instantiateTemplate?_of_compileTemplateAt?
                formals arguments depth schema head headEq]
              rw [inductionHypothesis tail tailEq]

/-! ## Complete rule templates -/

structure RuleTemplate where
  ruleId : RuleId
  formalCount : Nat
  premises : List SchemaTemplate
  conclusion : SchemaTemplate
deriving DecidableEq

/-- M0GC's template fragment admits only depth-zero applicative schemas and no
generic side conditions. -/
def compileRuleTemplate? (rule : RuleSchema) : Option RuleTemplate := do
  match rule.sideConditions with
  | [] =>
      if rule.metavariables.all (fun formal => formal.2 == 0) then
        let premises ← compileTemplates? rule.metavariables rule.premises
        let conclusion ← compileTemplate? rule.metavariables rule.conclusion
        some
          { ruleId := rule.id
            formalCount := rule.metavariables.length
            premises
            conclusion }
      else none
  | _ :: _ => none

def RuleTemplate.instantiate? (template : RuleTemplate)
    (arguments : List Pattern) : Option (List Pattern × Pattern) := do
  if arguments.length = template.formalCount then
    let premises ← instantiateTemplates? arguments template.premises
    let conclusion ← instantiateTemplate? arguments template.conclusion
    some (premises, conclusion)
  else none

/-- Successful rule-template instantiation exposes the exact formal arity;
the argument vector cannot be silently truncated or padded. -/
theorem RuleTemplate.argument_length_of_instantiate
    {template : RuleTemplate} {arguments : List Pattern}
    {result : List Pattern × Pattern}
    (instantiated : template.instantiate? arguments = some result) :
    arguments.length = template.formalCount := by
  unfold RuleTemplate.instantiate? at instantiated
  by_cases arity : arguments.length = template.formalCount
  · exact arity
  · simp [arity] at instantiated

/-- Source schema instantiation without rule lookup, argument admissibility,
or side-condition checking. -/
def instantiateRuleSchemas? (rule : RuleSchema)
    (arguments : List Pattern) : Option (List Pattern × Pattern) := do
  let premises ← instantiateSchemas? rule.metavariables arguments rule.premises
  let conclusion ← instantiateSchema? rule.metavariables arguments rule.conclusion
  some (premises, conclusion)

/-- A compiled rule exposes its exact authored identifier. -/
theorem compileRuleTemplate?_ruleId
    {rule : RuleSchema} {template : RuleTemplate}
    (compiled : compileRuleTemplate? rule = some template) :
    template.ruleId = rule.id := by
  cases sideConditionsEq : rule.sideConditions with
  | nil =>
      by_cases depthZero :
          rule.metavariables.all (fun formal => formal.2 == 0) = true
      · cases premisesEq :
            compileTemplates? rule.metavariables rule.premises with
        | none =>
            simp [compileRuleTemplate?, sideConditionsEq, depthZero,
              premisesEq] at compiled
        | some premiseTemplates =>
            cases conclusionEq :
                compileTemplate? rule.metavariables rule.conclusion with
            | none =>
                simp [compileRuleTemplate?, sideConditionsEq, depthZero,
                  premisesEq, conclusionEq] at compiled
            | some conclusionTemplate =>
                simp [compileRuleTemplate?, sideConditionsEq, depthZero,
                  premisesEq, conclusionEq] at compiled
                subst template
                rfl
      · simp [compileRuleTemplate?, sideConditionsEq, depthZero] at compiled
  | cons condition conditions =>
      simp [compileRuleTemplate?, sideConditionsEq] at compiled

/-- A compiled template retains the exact length of the authored formal
vector.  This is the arity bridge used when a physical matcher has already
checked the template's explicit argument count. -/
theorem compileRuleTemplate?_formalCount
    {rule : RuleSchema} {template : RuleTemplate}
    (compiled : compileRuleTemplate? rule = some template) :
    template.formalCount = rule.metavariables.length := by
  cases sideConditionsEq : rule.sideConditions with
  | nil =>
      by_cases depthZero :
          rule.metavariables.all (fun formal => formal.2 == 0) = true
      · cases premisesEq :
            compileTemplates? rule.metavariables rule.premises with
        | none =>
            simp [compileRuleTemplate?, sideConditionsEq, depthZero,
              premisesEq] at compiled
        | some premiseTemplates =>
            cases conclusionEq :
                compileTemplate? rule.metavariables rule.conclusion with
            | none =>
                simp [compileRuleTemplate?, sideConditionsEq, depthZero,
                  premisesEq, conclusionEq] at compiled
            | some conclusionTemplate =>
                simp [compileRuleTemplate?, sideConditionsEq, depthZero,
                  premisesEq, conclusionEq] at compiled
                subst template
                rfl
      · simp [compileRuleTemplate?, sideConditionsEq, depthZero] at compiled
  | cons condition conditions =>
      simp [compileRuleTemplate?, sideConditionsEq] at compiled

/-- Template compilation preserves the complete source schema pair whenever
the argument vector has the declared arity. -/
theorem RuleTemplate.instantiate_of_compile
    {rule : RuleSchema} {template : RuleTemplate}
    (compiled : compileRuleTemplate? rule = some template)
    (arguments : List Pattern)
    (arity : arguments.length = rule.metavariables.length) :
    template.instantiate? arguments =
      instantiateRuleSchemas? rule arguments := by
  cases sideConditionsEq : rule.sideConditions with
  | nil =>
      by_cases depthZero :
          rule.metavariables.all (fun formal => formal.2 == 0) = true
      · cases premisesEq :
            compileTemplates? rule.metavariables rule.premises with
        | none =>
            simp [compileRuleTemplate?, sideConditionsEq, depthZero,
              premisesEq] at compiled
        | some premiseTemplates =>
            cases conclusionEq :
                compileTemplate? rule.metavariables rule.conclusion with
            | none =>
                simp [compileRuleTemplate?, sideConditionsEq, depthZero,
                  premisesEq, conclusionEq] at compiled
            | some conclusionTemplate =>
                simp [compileRuleTemplate?, sideConditionsEq, depthZero,
                  premisesEq, conclusionEq] at compiled
                subst template
                have premisesAt :
                    compileTemplatesAt? rule.metavariables 0 rule.premises =
                      some premiseTemplates := by
                  simpa [compileTemplates?] using premisesEq
                have conclusionAt :
                    compileTemplateAt? rule.metavariables 0 rule.conclusion =
                      some conclusionTemplate := by
                  simpa [compileTemplate?] using conclusionEq
                have premisesAdequate :=
                  instantiateTemplates?_of_compileTemplatesAt?
                    rule.metavariables arguments 0 rule.premises
                    premiseTemplates premisesAt
                have conclusionAdequate :=
                  instantiateTemplate?_of_compileTemplateAt?
                    rule.metavariables arguments 0 rule.conclusion
                    conclusionTemplate conclusionAt
                simp [RuleTemplate.instantiate?, arity,
                  instantiateRuleSchemas?, instantiateSchemas?,
                  instantiateSchema?, premisesAdequate, conclusionAdequate]
      · simp [compileRuleTemplate?, sideConditionsEq, depthZero] at compiled
  | cons condition conditions =>
      simp [compileRuleTemplate?, sideConditionsEq] at compiled

/-- Argument admissibility includes exact correspondence with the formal
vector; there is no truncating zip behavior at the template boundary. -/
theorem argumentsValidAt_length_eq
    {formals : List (String × Nat)} {arguments : List Pattern}
    (valid : argumentsValidAt formals arguments = true) :
    arguments.length = formals.length := by
  induction formals generalizing arguments with
  | nil =>
      cases arguments <;> simp [argumentsValidAt] at valid ⊢
  | cons formal formals inductionHypothesis =>
      cases arguments with
      | nil => simp [argumentsValidAt] at valid
      | cons argument arguments =>
          simp only [argumentsValidAt, Bool.and_eq_true] at valid
          simp [inductionHypothesis valid.2]

/-- Once the ordinary source lookup and argument-admissibility guards hold,
the generated template result is exactly `instantiateRule?`. -/
theorem RuleTemplate.instantiate_eq_source_rule
    {definition : ValidatedCalculusLanguageDef}
    {rule : RuleSchema} {template : RuleTemplate}
    (compiled : compileRuleTemplate? rule = some template)
    (arguments : List Pattern)
    (lookup : definition.1.lookupRule? rule.id = some rule)
    (argumentsValid :
      argumentsValidAt rule.metavariables arguments = true) :
    template.instantiate? arguments =
      instantiateRule? definition { ruleId := rule.id, arguments } := by
  have arity := argumentsValidAt_length_eq argumentsValid
  rw [RuleTemplate.instantiate_of_compile compiled arguments arity]
  have sideConditionsEmpty : rule.sideConditions = [] := by
    cases sideConditionsEq : rule.sideConditions with
    | nil => rfl
    | cons condition conditions =>
        simp [compileRuleTemplate?, sideConditionsEq] at compiled
  simp [instantiateRule?, instantiateRuleSchemas?, lookup, argumentsValid,
    sideConditionsEmpty]

/-! ## Discriminating source canaries -/

open Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering

def binaryTemplate : RuleTemplate :=
  { ruleId := ⟨"pair"⟩
    formalCount := 2
    premises := []
    conclusion :=
      .application "pair" [.variable 0, .variable 1] }

theorem compile_binaryRule :
    compileRuleTemplate? binaryRule = some binaryTemplate := by
  simp [compileRuleTemplate?, binaryRule, binaryTemplate, compileTemplates?,
    compileTemplate?, compileTemplateAt?, compileTemplatesAt?, compileSlot?]

def left : Pattern := .apply "left" []

def right : Pattern := .apply "right" []

theorem binary_template_exact :
    binaryTemplate.instantiate? [left, right] =
      instantiateRule? ⟨binaryDefinition, binaryDefinition_valid⟩
        { ruleId := ⟨"pair"⟩, arguments := [left, right] } := by
  apply RuleTemplate.instantiate_eq_source_rule compile_binaryRule
  · rfl
  · rfl

/-- A binder-bearing rule cannot masquerade as an M0GC application template. -/
theorem binder_rule_rejected : compileRuleTemplate? binderRule = none := by
  simp [compileRuleTemplate?, binderRule]

/-- A rule whose validity depends on a generic side condition is also outside
the template-only checker. -/
theorem side_condition_rule_rejected :
    compileRuleTemplate? sideConditionRule = none := by
  simp [compileRuleTemplate?, sideConditionRule]

#print axioms compileSlot?_bind_getElem?_eq_lookupArgumentAt?
#print axioms instantiateTemplate?_of_compileTemplateAt?
#print axioms RuleTemplate.instantiate_of_compile
#print axioms RuleTemplate.instantiate_eq_source_rule
#print axioms compileRuleTemplate?_formalCount
#print axioms RuleTemplate.argument_length_of_instantiate
#print axioms binary_template_exact
#print axioms binder_rule_rejected
#print axioms side_condition_rule_rejected

end Mettapedia.GSLT.LanguageDef.M0GCTemplateAdequacy
