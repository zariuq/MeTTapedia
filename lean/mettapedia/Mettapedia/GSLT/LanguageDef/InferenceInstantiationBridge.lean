import Mettapedia.GSLT.LanguageDef.InferenceExtraction
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Source-binding to inference-schema instantiation

This module relates the binding application used by `LanguageDef` rewrite
semantics to the ordered-argument instantiation used by the generated
proof-relevant inference checker.

The first supported fragment is deliberately exact: fixed constructor trees,
depth-zero metavariables, and fixed collections.  Object-language binders such
as HOL's `AbsTerm` remain ordinary constructors.  Meta-level binders, explicit
substitution nodes, and collection rests are outside this fragment because
their source and checker operations intentionally have different semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Read checker arguments from a source rewrite binding in the checker's
declared order.  The first bridge supports only depth-zero formals. -/
def argumentsOfBindings? : List (String × Nat) → Bindings → Option (List Pattern)
  | [], _ => some []
  | (name, depth) :: formals, bindings => do
      guard (depth == 0)
      let argument ← bindings.lookup name
      let arguments ← argumentsOfBindings? formals bindings
      some (argument :: arguments)

/-- Reconstruct a binding row from the checker's positional argument vector.
The operation is deliberately fail-closed on an arity mismatch.  Binder
depth remains part of the formal row, while `Bindings` records only the
name-to-value projection used by source rewrite instantiation. -/
def bindingsOfArguments? : List (String × Nat) → List Pattern → Option Bindings
  | [], [] => some []
  | (name, _depth) :: formals, argument :: arguments => do
      let bindings ← bindingsOfArguments? formals arguments
      some ((name, argument) :: bindings)
  | _, _ => none

/-- Every checker-valid argument vector has a positional binding row. -/
theorem bindingsOfArguments?_exists_of_argumentsValidAt :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern},
      argumentsValidAt formals arguments = true →
        ∃ bindings, bindingsOfArguments? formals arguments = some bindings := by
  intro formals
  induction formals with
  | nil =>
      intro arguments valid
      cases arguments with
      | nil => exact ⟨[], rfl⟩
      | cons argument arguments =>
          simp [argumentsValidAt] at valid
  | cons formal formals inductionHypothesis =>
      intro arguments valid
      cases arguments with
      | nil => simp [argumentsValidAt] at valid
      | cons argument arguments =>
          rcases formal with ⟨name, depth⟩
          simp only [argumentsValidAt, Bool.and_eq_true] at valid
          obtain ⟨bindings, bindingsEq⟩ :=
            inductionHypothesis valid.2
          exact ⟨(name, argument) :: bindings, by
            simp [bindingsOfArguments?, bindingsEq]⟩

/-- A binding prepended under a different name does not change lookup. -/
theorem bindings_lookup_cons_ne {headName name : String}
    (different : headName ≠ name) (value : Pattern) (bindings : Bindings) :
    Bindings.lookup ((headName, value) :: bindings) name =
      Bindings.lookup bindings name := by
  unfold Bindings.lookup
  rw [List.find?_cons_of_neg (by simpa using different)]

/-- An unrelated binding may be skipped while extracting a positional
argument vector. -/
theorem argumentsOfBindings?_cons_irrelevant :
    ∀ {formals : List (String × Nat)} {headName : String}
      {value : Pattern} {bindings : Bindings},
      headName ∉ formals.map Prod.fst →
      argumentsOfBindings? formals ((headName, value) :: bindings) =
        argumentsOfBindings? formals bindings := by
  intro formals
  induction formals with
  | nil => intro _ _ _ _; rfl
  | cons formal formals inductionHypothesis =>
      intro headName value bindings absent
      rcases formal with ⟨name, depth⟩
      have parts : headName ≠ name ∧ headName ∉ formals.map Prod.fst := by
        simpa using absent
      simp [argumentsOfBindings?, bindings_lookup_cons_ne parts.1,
        inductionHypothesis parts.2]

/-- On a depth-zero, name-unique formal row, positional reconstruction is a
right inverse of ordered argument extraction.  This is the anti-splicing
boundary used when one checked rule instance must determine one coherent
source binding environment. -/
theorem argumentsOfBindings?_of_bindingsOfArguments :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern}
      {bindings : Bindings},
      (formals.map Prod.fst).Nodup →
      (∀ formal ∈ formals, formal.2 = 0) →
      bindingsOfArguments? formals arguments = some bindings →
      argumentsOfBindings? formals bindings = some arguments := by
  intro formals
  induction formals with
  | nil =>
      intro arguments bindings _names _depths decoded
      cases arguments with
      | nil =>
          have bindingsEq : bindings = [] := by
            simpa [bindingsOfArguments?] using decoded.symm
          subst bindings
          rfl
      | cons argument arguments =>
          simp [bindingsOfArguments?] at decoded
  | cons formal formals inductionHypothesis =>
      intro arguments bindings names depths decoded
      cases arguments with
      | nil => simp [bindingsOfArguments?] at decoded
      | cons argument arguments =>
          rcases formal with ⟨name, depth⟩
          have depthZero : depth = 0 :=
            depths (name, depth) (by simp)
          subst depth
          have namesParts : name ∉ formals.map Prod.fst ∧
              (formals.map Prod.fst).Nodup := by
            simpa using names
          cases tailEq : bindingsOfArguments? formals arguments with
          | none => simp [bindingsOfArguments?, tailEq] at decoded
          | some tailBindings =>
              have bindingsEq :
                  bindings = (name, argument) :: tailBindings := by
                simpa [bindingsOfArguments?, tailEq] using decoded.symm
              subst bindings
              have tailArguments := inductionHypothesis namesParts.2
                (fun inner member =>
                  depths inner (List.mem_cons_of_mem _ member)) tailEq
              simp [argumentsOfBindings?, Bindings.lookup,
                argumentsOfBindings?_cons_irrelevant namesParts.1,
                tailArguments]

/-- Positional reconstruction covers every declared formal name when the
formal row is name-unique. -/
theorem bindingsOfArguments?_lookup_isSome :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern}
      {bindings : Bindings},
      (formals.map Prod.fst).Nodup →
      bindingsOfArguments? formals arguments = some bindings →
      ∀ formal ∈ formals,
        (Bindings.lookup bindings formal.1).isSome := by
  intro formals
  induction formals with
  | nil =>
      intro arguments bindings _names _decoded formal member
      cases member
  | cons head formals inductionHypothesis =>
      intro arguments bindings names decoded formal member
      cases arguments with
      | nil => simp [bindingsOfArguments?] at decoded
      | cons argument arguments =>
          rcases head with ⟨headName, headDepth⟩
          have namesParts : headName ∉ formals.map Prod.fst ∧
              (formals.map Prod.fst).Nodup := by
            simpa using names
          cases tailEq : bindingsOfArguments? formals arguments with
          | none => simp [bindingsOfArguments?, tailEq] at decoded
          | some tailBindings =>
              have bindingsEq :
                  bindings = (headName, argument) :: tailBindings := by
                simpa [bindingsOfArguments?, tailEq] using decoded.symm
              subst bindings
              rcases List.mem_cons.mp member with headEq | tailMember
              · subst formal
                simp [Bindings.lookup]
              · have different : headName ≠ formal.1 := by
                  intro equal
                  exact namesParts.1
                    (List.mem_map.mpr ⟨formal, tailMember, equal.symm⟩)
                rw [bindings_lookup_cons_ne different]
                exact inductionHypothesis namesParts.2 tailEq formal tailMember

/-- Positional reconstruction agrees exactly with the checker's own lookup
at every declared formal.  Name uniqueness is essential because `Bindings`
forgets binder depth while the checker retains it in the formal coordinate. -/
theorem bindingsOfArguments?_lookup_eq_lookupArgumentAt? :
    ∀ {formals : List (String × Nat)} {arguments : List Pattern}
      {bindings : Bindings},
      (formals.map Prod.fst).Nodup →
      bindingsOfArguments? formals arguments = some bindings →
      ∀ formal ∈ formals,
        Bindings.lookup bindings formal.1 =
          lookupArgumentAt? formals arguments formal.1 formal.2 := by
  intro formals
  induction formals with
  | nil =>
      intro arguments bindings _names _decoded formal member
      cases member
  | cons head formals inductionHypothesis =>
      intro arguments bindings names decoded formal member
      cases arguments with
      | nil => simp [bindingsOfArguments?] at decoded
      | cons argument arguments =>
          rcases head with ⟨headName, headDepth⟩
          have namesParts : headName ∉ formals.map Prod.fst ∧
              (formals.map Prod.fst).Nodup := by
            simpa using names
          cases tailEq : bindingsOfArguments? formals arguments with
          | none => simp [bindingsOfArguments?, tailEq] at decoded
          | some tailBindings =>
              have bindingsEq :
                  bindings = (headName, argument) :: tailBindings := by
                simpa [bindingsOfArguments?, tailEq] using decoded.symm
              subst bindings
              rcases List.mem_cons.mp member with headEq | tailMember
              · subst formal
                simp [Bindings.lookup, lookupArgumentAt?]
              · have differentName : headName ≠ formal.1 := by
                  intro equal
                  exact namesParts.1
                    (List.mem_map.mpr ⟨formal, tailMember, equal.symm⟩)
                have differentFormal :
                    (headName, headDepth) ≠ (formal.1, formal.2) := by
                  intro equal
                  exact differentName (Prod.mk.inj equal).1
                rw [bindings_lookup_cons_ne differentName]
                simp only [lookupArgumentAt?, if_neg differentFormal]
                exact inductionHypothesis namesParts.2 tailEq formal tailMember

/-- Every declared formal has one exact checker lookup in a valid argument
vector.  Name uniqueness is the boundary that lets the name-indexed binding
projection recover the original depth-aware coordinate. -/
theorem lookupArgumentAt?_exists_of_argumentsValidAt
    {formals : List (String × Nat)} {arguments : List Pattern}
    (namesNodup : (formals.map Prod.fst).Nodup)
    (valid : argumentsValidAt formals arguments = true)
    (formal : String × Nat) (member : formal ∈ formals) :
    ∃ argument,
      lookupArgumentAt? formals arguments formal.1 formal.2 = some argument := by
  obtain ⟨bindings, bindingsExact⟩ :=
    bindingsOfArguments?_exists_of_argumentsValidAt valid
  have present : (Bindings.lookup bindings formal.1).isSome :=
    bindingsOfArguments?_lookup_isSome namesNodup bindingsExact formal member
  obtain ⟨argument, bindingLookup⟩ := Option.isSome_iff_exists.mp present
  refine ⟨argument, ?_⟩
  rw [← bindingsOfArguments?_lookup_eq_lookupArgumentAt? namesNodup
    bindingsExact formal member]
  exact bindingLookup

mutual

/-- Patterns on which source `applyBindings` and checker instantiation have
the same structural meaning.  Every free variable must be a declared
depth-zero formal. -/
inductive BindingSchemaFragment (formals : List (String × Nat)) : Pattern → Prop
  | bvar (index : Nat) : BindingSchemaFragment formals (.bvar index)
  | fvar {name : String} (declared : (name, 0) ∈ formals) :
      BindingSchemaFragment formals (.fvar name)
  | apply {constructor : String} {arguments : List Pattern}
      (items : BindingSchemasFragment formals arguments) :
      BindingSchemaFragment formals (.apply constructor arguments)
  | collection {collectionType : CollType} {elements : List Pattern}
      (items : BindingSchemasFragment formals elements) :
      BindingSchemaFragment formals (.collection collectionType elements none)

inductive BindingSchemasFragment (formals : List (String × Nat)) :
    List Pattern → Prop
  | nil : BindingSchemasFragment formals []
  | cons {pattern : Pattern} {patterns : List Pattern}
      (head : BindingSchemaFragment formals pattern)
      (tail : BindingSchemasFragment formals patterns) :
      BindingSchemasFragment formals (pattern :: patterns)

end

mutual

/-- The supported first-order fragment is monotone in its formal inventory.
This transports a source-local fragment proof into a larger generated rule
without rechecking the pattern. -/
theorem BindingSchemaFragment.mono
    {smaller larger : List (String × Nat)} {pattern : Pattern}
    (fragment : BindingSchemaFragment smaller pattern)
    (included : ∀ formal ∈ smaller, formal ∈ larger) :
    BindingSchemaFragment larger pattern := by
  cases fragment with
  | bvar index => exact .bvar index
  | fvar declared => exact .fvar (included _ declared)
  | apply items => exact .apply (items.mono included)
  | collection items => exact .collection (items.mono included)

/-- List-valued monotonicity of the supported first-order fragment. -/
theorem BindingSchemasFragment.mono
    {smaller larger : List (String × Nat)} {patterns : List Pattern}
    (fragment : BindingSchemasFragment smaller patterns)
    (included : ∀ formal ∈ smaller, formal ∈ larger) :
    BindingSchemasFragment larger patterns := by
  cases fragment with
  | nil => exact .nil
  | cons head tail => exact .cons (head.mono included) (tail.mono included)

end

mutual

/-- Executable recognizer for the exact source/checker instantiation
fragment. -/
def checkBindingSchemaFragment (formals : List (String × Nat)) : Pattern → Bool
  | .bvar _ => true
  | .fvar name => formals.contains (name, 0)
  | .apply _ arguments => checkBindingSchemasFragment formals arguments
  | .lambda _ _ => false
  | .multiLambda _ _ _ => false
  | .subst _ _ => false
  | .collection _ elements rest =>
      rest.isNone && checkBindingSchemasFragment formals elements
termination_by pattern => sizeOf pattern

def checkBindingSchemasFragment (formals : List (String × Nat)) :
    List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      checkBindingSchemaFragment formals pattern &&
        checkBindingSchemasFragment formals patterns
termination_by patterns => sizeOf patterns

end


mutual

/-- The executable fragment recognizer produces the structural evidence used
by the correspondence theorem. -/
theorem bindingSchemaFragment_of_check
    {formals : List (String × Nat)} {schema : Pattern}
    (hcheck : checkBindingSchemaFragment formals schema = true) :
    BindingSchemaFragment formals schema := by
  cases schema with
  | bvar index => exact .bvar index
  | fvar name =>
      exact .fvar (by simpa [checkBindingSchemaFragment] using hcheck)
  | apply constructor arguments =>
      exact .apply (bindingSchemasFragment_of_check (by
        simpa [checkBindingSchemaFragment] using hcheck))
  | lambda binder body => simp [checkBindingSchemaFragment] at hcheck
  | multiLambda arity binders body =>
      simp [checkBindingSchemaFragment] at hcheck
  | subst body replacement => simp [checkBindingSchemaFragment] at hcheck
  | collection collectionType elements rest =>
      cases rest with
      | none =>
          exact .collection (bindingSchemasFragment_of_check (by
            simpa [checkBindingSchemaFragment] using hcheck))
      | some restName => simp [checkBindingSchemaFragment] at hcheck

theorem bindingSchemasFragment_of_check
    {formals : List (String × Nat)} {schemas : List Pattern}
    (hcheck : checkBindingSchemasFragment formals schemas = true) :
    BindingSchemasFragment formals schemas := by
  cases schemas with
  | nil => exact .nil
  | cons schema schemas =>
      have checks := Bool.and_eq_true_iff.mp (by
        simpa [checkBindingSchemasFragment] using hcheck)
      exact .cons (bindingSchemaFragment_of_check checks.1)
        (bindingSchemasFragment_of_check checks.2)

end

/-- `Bindings.lookup` and the gradual source operation select the same value
when the lookup is present. -/
theorem applyBindings_fvar_eq_of_lookup {bindings : Bindings}
    {name : String} {value : Pattern}
    (hlookup : bindings.lookup name = some value) :
    applyBindings bindings (.fvar name) = value := by
  simp only [Bindings.lookup] at hlookup
  simp only [applyBindings]
  cases hfind : bindings.find? (fun pair => pair.1 == name) with
  | none => simp [hfind] at hlookup
  | some pair =>
      rcases pair with ⟨foundName, foundValue⟩
      simp [hfind] at hlookup
      subst value
      simp

/-- Successful argument extraction makes every declared occurrence look up to
the exact value that source binding application substitutes. -/
theorem lookupArgumentAt?_argumentsOfBindings
    {formals : List (String × Nat)} {bindings : Bindings}
    {arguments : List Pattern} {name : String}
    (harguments : argumentsOfBindings? formals bindings = some arguments)
    (hdeclared : (name, 0) ∈ formals) :
    lookupArgumentAt? formals arguments name 0 =
      some (applyBindings bindings (.fvar name)) := by
  induction formals generalizing arguments with
  | nil => simp at hdeclared
  | cons formal formals ih =>
      rcases formal with ⟨formalName, depth⟩
      cases hdepth : depth == 0 with
      | false => simp [argumentsOfBindings?, hdepth] at harguments
      | true =>
        cases hlookup : bindings.lookup formalName with
        | none => simp [argumentsOfBindings?, hdepth, hlookup] at harguments
        | some argument =>
            cases htail : argumentsOfBindings? formals bindings with
            | none =>
                simp [argumentsOfBindings?, hdepth, hlookup, htail] at harguments
            | some tailArguments =>
                have hargumentsEq : argument :: tailArguments = arguments := by
                  simpa [argumentsOfBindings?, hdepth, hlookup, htail] using harguments
                subst arguments
                have hdepthZero : depth = 0 := by
                  simpa using hdepth
                subst depth
                have hmember :
                    (name, 0) = (formalName, 0) ∨ (name, 0) ∈ formals := by
                  simpa only [List.mem_cons] using hdeclared
                by_cases heq : (formalName, 0) = (name, 0)
                · have hname : formalName = name := (Prod.mk.inj heq).1
                  subst formalName
                  simp [lookupArgumentAt?,
                    applyBindings_fvar_eq_of_lookup hlookup]
                · simp [lookupArgumentAt?, heq]
                  exact ih htail (hmember.resolve_left (fun equality => heq equality.symm))

mutual

/-- On the supported fragment, ordered checker instantiation is exactly source
binding application. -/
theorem instantiateSchemaAt?_eq_applyBindings
    {formals : List (String × Nat)} {bindings : Bindings}
    {arguments : List Pattern} {schema : Pattern}
    (hfragment : BindingSchemaFragment formals schema)
    (harguments : argumentsOfBindings? formals bindings = some arguments) :
    instantiateSchemaAt? formals arguments 0 schema =
      some (applyBindings bindings schema) := by
  cases hfragment with
  | bvar index => simp [instantiateSchemaAt?, applyBindings]
  | fvar declared =>
      simpa only [instantiateSchemaAt?] using
        lookupArgumentAt?_argumentsOfBindings harguments declared
  | apply items =>
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemasAt?_eq_applyBindings items harguments]
  | collection items =>
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemasAt?_eq_applyBindings items harguments]

theorem instantiateSchemasAt?_eq_applyBindings
    {formals : List (String × Nat)} {bindings : Bindings}
    {arguments schemas : List Pattern}
    (hfragment : BindingSchemasFragment formals schemas)
    (harguments : argumentsOfBindings? formals bindings = some arguments) :
    instantiateSchemasAt? formals arguments 0 schemas =
      some (schemas.map (applyBindings bindings)) := by
  cases hfragment with
  | nil => simp [instantiateSchemasAt?]
  | cons head tail =>
      simp [instantiateSchemasAt?,
        instantiateSchemaAt?_eq_applyBindings head harguments,
        instantiateSchemasAt?_eq_applyBindings tail harguments]

end

mutual

/-- A direct pointwise lookup correspondence is sufficient for checker
instantiation to equal source binding application.  Unlike the ordered-row
theorem above, this reverse-facing form does not require reconstructing the
entire checker argument vector from the binding row. -/
theorem instantiateSchemaAt?_eq_applyBindings_of_lookup
    {formals : List (String × Nat)} {arguments : List Pattern}
    {bindings : Bindings} {schema : Pattern}
    (fragment : BindingSchemaFragment formals schema)
    (covered : ∀ name, (name, 0) ∈ formals →
      (Bindings.lookup bindings name).isSome)
    (lookupExact : ∀ name, (name, 0) ∈ formals →
      lookupArgumentAt? formals arguments name 0 =
        Bindings.lookup bindings name) :
    instantiateSchemaAt? formals arguments 0 schema =
      some (applyBindings bindings schema) := by
  cases fragment with
  | bvar index => simp [instantiateSchemaAt?, applyBindings]
  | @fvar name declared =>
      obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
        (covered name declared)
      have argumentEq :
          lookupArgumentAt? formals arguments name 0 = some value :=
        (lookupExact name declared).trans valueEq
      simpa [instantiateSchemaAt?,
        applyBindings_fvar_eq_of_lookup valueEq] using argumentEq
  | apply items =>
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemasAt?_eq_applyBindings_of_lookup items covered
          lookupExact]
  | collection items =>
      simp [instantiateSchemaAt?, applyBindings,
        instantiateSchemasAt?_eq_applyBindings_of_lookup items covered
          lookupExact]

theorem instantiateSchemasAt?_eq_applyBindings_of_lookup
    {formals : List (String × Nat)} {arguments : List Pattern}
    {bindings : Bindings} {schemas : List Pattern}
    (fragment : BindingSchemasFragment formals schemas)
    (covered : ∀ name, (name, 0) ∈ formals →
      (Bindings.lookup bindings name).isSome)
    (lookupExact : ∀ name, (name, 0) ∈ formals →
      lookupArgumentAt? formals arguments name 0 =
        Bindings.lookup bindings name) :
    instantiateSchemasAt? formals arguments 0 schemas =
      some (schemas.map (applyBindings bindings)) := by
  cases fragment with
  | nil => simp [instantiateSchemasAt?]
  | cons head tail =>
      simp [instantiateSchemasAt?,
        instantiateSchemaAt?_eq_applyBindings_of_lookup head covered
          lookupExact,
        instantiateSchemasAt?_eq_applyBindings_of_lookup tail covered
          lookupExact]

end


/-- Top-level spelling of the source/checker correspondence. -/
theorem instantiateSchema?_eq_applyBindings
    {formals : List (String × Nat)} {bindings : Bindings}
    {arguments : List Pattern} {schema : Pattern}
    (hfragment : BindingSchemaFragment formals schema)
    (harguments : argumentsOfBindings? formals bindings = some arguments) :
    instantiateSchema? formals arguments schema =
      some (applyBindings bindings schema) :=
  instantiateSchemaAt?_eq_applyBindings hfragment harguments

/-- For an extracted authored rule in the supported fragment, checker
instantiation produces exactly the judgment obtained by interpreting the
source rewrite output. -/
theorem RuleExtraction.instantiatedConclusion_eq_sourceOutput
    {profile : InferenceExtraction.EvidenceProfile}
    (extraction : InferenceExtraction.RuleExtraction profile)
    {bindings : Bindings} {arguments : List Pattern}
    (hfragment : BindingSchemaFragment extraction.schema.metavariables
      extraction.schema.conclusion)
    (harguments : argumentsOfBindings? extraction.schema.metavariables bindings =
      some arguments) :
    instantiateSchema? extraction.schema.metavariables arguments
        extraction.schema.conclusion =
      InferenceExtraction.sourceOutputJudgment? profile
        (applyBindings bindings extraction.source.right) := by
  rw [instantiateSchema?_eq_applyBindings hfragment harguments]
  exact (extraction.sourceOutputJudgment?_applyBindings bindings).symm

/-- The complete ordered premise vector has the same source/checker
instantiation correspondence. -/
theorem RuleExtraction.instantiatedPremises_eq_applyBindings
    {profile : InferenceExtraction.EvidenceProfile}
    (extraction : InferenceExtraction.RuleExtraction profile)
    {bindings : Bindings} {arguments : List Pattern}
    (hfragment : BindingSchemasFragment extraction.schema.metavariables
      extraction.schema.premises)
    (harguments : argumentsOfBindings? extraction.schema.metavariables bindings =
      some arguments) :
    instantiateSchemas? extraction.schema.metavariables arguments
        extraction.schema.premises =
      some (extraction.schema.premises.map (applyBindings bindings)) :=
  instantiateSchemasAt?_eq_applyBindings hfragment harguments

/-- A source-rule binding in the supported fragment becomes an actual
declarative application of the corresponding generated checker rule.  The
lookup hypothesis pins the generated rule inside the validated definition;
the argument-validity hypothesis is the checker's explicit closed-data
boundary. -/
theorem RuleExtraction.ruleApplicationOfBinding
    {profile : InferenceExtraction.EvidenceProfile}
    (extraction : InferenceExtraction.RuleExtraction profile)
    (definition : ValidatedCalculusLanguageDef)
    {bindings : Bindings} {arguments : List Pattern}
    (hlookup : definition.1.lookupRule? extraction.schema.id =
      some extraction.schema)
    (hvalid : argumentsValidAt extraction.schema.metavariables arguments = true)
    (hpremises : BindingSchemasFragment extraction.schema.metavariables
      extraction.schema.premises)
    (hconclusion : BindingSchemaFragment extraction.schema.metavariables
      extraction.schema.conclusion)
    (harguments : argumentsOfBindings? extraction.schema.metavariables bindings =
      some arguments) :
    RuleApplication definition
      { ruleId := extraction.schema.id, arguments := arguments }
      (extraction.schema.premises.map (applyBindings bindings))
      (applyBindings bindings extraction.schema.conclusion) := by
  have hpremiseInstantiation :=
    instantiateSchemasAt?_eq_applyBindings hpremises harguments
  have hpremiseInstantiation' :
      instantiateSchemas? extraction.schema.metavariables arguments
          extraction.schema.premises =
        some (extraction.schema.premises.map (applyBindings bindings)) := by
    simpa [instantiateSchemas?] using hpremiseInstantiation
  have hconclusionInstantiation :=
    instantiateSchema?_eq_applyBindings hconclusion harguments
  have hsideConditions := RuleSchema.sideConditionsHold_of_empty
    extraction.schema arguments extraction.sideConditionsEmpty
  apply instantiateRule?_eq_some_iff_application.mp
  simp [instantiateRule?, hlookup, hvalid,
    hsideConditions, hpremiseInstantiation', hconclusionInstantiation]

/-- The conclusion of the generated application is precisely the
proof-relevant interpretation of the authored source reduct. -/
theorem RuleExtraction.sourceReductJudgment
    {profile : InferenceExtraction.EvidenceProfile}
    (extraction : InferenceExtraction.RuleExtraction profile)
    {bindings : Bindings} {sourceReduct : Pattern}
    (hreduct : applyBindings bindings extraction.source.right = sourceReduct) :
    InferenceExtraction.sourceOutputJudgment? profile sourceReduct =
      some (applyBindings bindings extraction.schema.conclusion) := by
  rw [← hreduct]
  exact extraction.sourceOutputJudgment?_applyBindings bindings

/-! Rejection and positive teeth for the exact bridge boundary. -/

private def fixedSchema : Pattern :=
  .apply "Pair" [.fvar "x", .collection .vec [.fvar "y"] none]

private def fixedFormals : List (String × Nat) := [("x", 0), ("y", 0)]

private def fixedBindings : Bindings :=
  [("y", .apply "Y" []), ("x", .apply "X" [])]

example : BindingSchemaFragment fixedFormals fixedSchema := by
  exact .apply (.cons (.fvar (by simp [fixedFormals]))
    (.cons (.collection (.cons (.fvar (by simp [fixedFormals])) .nil)) .nil))

#guard decide
  (argumentsOfBindings? fixedFormals fixedBindings =
    some [.apply "X" [], .apply "Y" []])

#guard decide
  (bindingsOfArguments? fixedFormals [.apply "X" [], .apply "Y" []] =
    some [("x", .apply "X" []), ("y", .apply "Y" [])])

#guard decide
  (instantiateSchema? fixedFormals [.apply "X" [], .apply "Y" []] fixedSchema =
    some (applyBindings fixedBindings fixedSchema))

#guard (argumentsOfBindings? [("x", 1)] fixedBindings).isNone
#guard (argumentsOfBindings? [("missing", 0)] fixedBindings).isNone
#guard (bindingsOfArguments? fixedFormals [.apply "X" []]).isNone

example : ¬ BindingSchemaFragment fixedFormals
    (.lambda none (.fvar "x")) := by
  intro h
  cases h

example : ¬ BindingSchemaFragment fixedFormals
    (.subst (.fvar "x") (.fvar "y")) := by
  intro h
  cases h

example : ¬ BindingSchemaFragment fixedFormals
    (.collection .vec [] (some "rest")) := by
  intro h
  cases h

#print axioms bindingsOfArguments?_exists_of_argumentsValidAt
#print axioms argumentsOfBindings?_cons_irrelevant
#print axioms argumentsOfBindings?_of_bindingsOfArguments
#print axioms bindingsOfArguments?_lookup_isSome
#print axioms bindingsOfArguments?_lookup_eq_lookupArgumentAt?
#print axioms lookupArgumentAt?_exists_of_argumentsValidAt
#print axioms BindingSchemaFragment.mono
#print axioms instantiateSchemaAt?_eq_applyBindings_of_lookup

end Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
