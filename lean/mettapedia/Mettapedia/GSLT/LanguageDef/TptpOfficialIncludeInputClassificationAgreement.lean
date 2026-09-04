import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualRootDispatch

/-!
# Exact agreement for official include-input classification

This module connects an independent total classification of official TPTP
top-level inputs to contextual execution of the declared classification
language.  Every accepted formula family produces its original official input
with source provenance; every include input preserves its directive and span.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationLanguageDef

namespace Carrier

abbrev encodeString :=
  TptpOfficialIncludeResolutionCarrier.encodeString
abbrev encodeIndex :=
  TptpOfficialIncludeResolutionResultCarrier.encodeIndex
abbrev encodeIncludeEdges :=
  TptpOfficialIncludeResolutionResultCarrier.encodeIncludeEdges
abbrev encodeResolvedFormula :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolvedFormula

end Carrier

inductive ClassifiedInput where
  | formula (value : ResolvedFormula)
  | include (directive span : Pattern)
  deriving DecidableEq, Repr

private def resolved (sourceId sourceDigest : String) (inputIndex : Nat)
    (path : List IncludeEdge) (name : String) (input : Pattern) :
    ClassifiedInput :=
  .formula {
    name := name
    input := input
    origin := {
      sourceId := sourceId
      sourceDigest := sourceDigest
      sourceInputIndex := inputIndex
      includePath := path }
  }

@[simp] private theorem encodeResolvedFormula_exact
    (sourceId sourceDigest : String) (inputIndex : Nat)
    (path : List IncludeEdge) (name : String) (input : Pattern) :
    Carrier.encodeResolvedFormula {
        name := name
        input := input
        origin := {
          sourceId := sourceId
          sourceDigest := sourceDigest
          sourceInputIndex := inputIndex
          includePath := path }} =
      resolvedFormula (Carrier.encodeString name) input
        (formulaOrigin (Carrier.encodeString sourceId)
          (Carrier.encodeString sourceDigest) (Carrier.encodeIndex inputIndex)
          (Carrier.encodeIncludeEdges path)) := by
  rfl

/-- Independent one-input classification.  Its clauses inspect the official
AST directly and do not call the declared rewrite engine. -/
def classifyInput? (sourceId sourceDigest : String) (inputIndex : Nat)
    (path : List IncludeEdge) : Pattern -> Option ClassifiedInput
  | input@(.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-1"
        [.apply "tptp92-ast:thf-annotated:alt-1"
          [sourceName, _, _, _]],
        .apply "tptp92-ast:source-span" [_, _]]) => do
      let name <- decodeCanonicalName? sourceName
      some (resolved sourceId sourceDigest inputIndex path name input)
  | input@(.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-2"
        [.apply "tptp92-ast:tff-annotated:alt-1"
          [sourceName, _, _, _]],
        .apply "tptp92-ast:source-span" [_, _]]) => do
      let name <- decodeCanonicalName? sourceName
      some (resolved sourceId sourceDigest inputIndex path name input)
  | input@(.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-3"
        [.apply "tptp92-ast:tcf-annotated:alt-1"
          [sourceName, _, _, _]],
        .apply "tptp92-ast:source-span" [_, _]]) => do
      let name <- decodeCanonicalName? sourceName
      some (resolved sourceId sourceDigest inputIndex path name input)
  | input@(.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-4"
        [.apply "tptp92-ast:fof-annotated:alt-1"
          [sourceName, _, _, _]],
        .apply "tptp92-ast:source-span" [_, _]]) => do
      let name <- decodeCanonicalName? sourceName
      some (resolved sourceId sourceDigest inputIndex path name input)
  | input@(.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-5"
        [.apply "tptp92-ast:cnf-annotated:alt-1"
          [sourceName, _, _, _]],
        .apply "tptp92-ast:source-span" [_, _]]) => do
      let name <- decodeCanonicalName? sourceName
      some (resolved sourceId sourceDigest inputIndex path name input)
  | input@(.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-6"
        [.apply "tptp92-ast:tpi-annotated:alt-1"
          [sourceName, _, _, _]],
        .apply "tptp92-ast:source-span" [_, _]]) => do
      let name <- decodeCanonicalName? sourceName
      some (resolved sourceId sourceDigest inputIndex path name input)
  | .apply "tptp92-ast:tptp-input:alt-2"
      [directive, span@(.apply "tptp92-ast:source-span" [_, _])] =>
      some (.include directive span)
  | _ => none

def encodeClassifiedInput : ClassifiedInput -> Pattern
  | .formula value => formulaOutcome (Carrier.encodeResolvedFormula value)
  | .include directive span => includeOutcome directive span

def encodeRequest (sourceId sourceDigest : String) (inputIndex : Nat)
    (path : List IncludeEdge) (input : Pattern) : Pattern :=
  classify (Carrier.encodeString sourceId) (Carrier.encodeString sourceDigest)
    (Carrier.encodeIndex inputIndex) (Carrier.encodeIncludeEdges path) input

private abbrev base : BasePremiseEvaluator :=
  engineBasePremises RelationEnv.empty

/-- Exact singleton results are stable above a finite contextual depth. -/
def EventuallyExact (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel ->
    rewriteAt base language fuel source = [result]

private theorem nameRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-input:decode-name") =
      nameRules := by
  rfl

private theorem classificationRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-input:classify") =
      [classifyFormulaRule, includeRule] := by
  rfl

private theorem inspectionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-input:inspect-formula") =
      inspectFormulaRules := by
  rfl

private theorem finalizeRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-input:decode-formula") =
      [finalizeFormulaRule] := by
  rfl

private theorem eventuallyExact_of_one_step (source result : Pattern)
    (step : ∀ fuel, rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor

private theorem eventuallyExact_of_one_premise
    (premiseSource premiseResult source result : Pattern)
    (premiseExact : EventuallyExact premiseSource premiseResult)
    (step : ∀ fuel,
      rewriteAt base language fuel premiseSource = [premiseResult] ->
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases premiseExact with ⟨requiredFuel, premiseExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using
        step predecessor (premiseExact predecessor (by omega))

local macro "classification_row_simp" : tactic =>
  `(tactic|
    simp [nameRules, inspectFormulaRules, nameWordRule, nameIntegerRule,
      classifyFormulaRule, inspectFormulaRule, finalizeFormulaRule,
      includeRule, annotatedFormula, locatedFormulaInput, sourceSpan,
      sourceNameWord, sourceIntegerName, sourceAtomicWord, sourceToken,
      decodeName, decodedName, classify, inspectFormula, decodeFormula,
      formulaOutcome, includeOutcome,
      formulaOrigin, resolvedFormula, mkRule, congruence, typed, a, v,
      applyRuleUsing, matchPatternForRule_eq_syntactic, premisesUsing,
      premiseStepUsing, matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

theorem name_lower_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeName (sourceNameWord "tptp92-ast:atomic-word:alt-1"
        "tptp92-ast:token:lower-word" lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceNameWord, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  classification_row_simp

theorem name_singleQuoted_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeName (sourceNameWord "tptp92-ast:atomic-word:alt-2"
        "tptp92-ast:token:single-quoted" lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceNameWord, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  classification_row_simp

theorem name_backQuoted_eventuallyExact (lexeme : Pattern) :
    EventuallyExact
      (decodeName (sourceNameWord "tptp92-ast:atomic-word:alt-3"
        "tptp92-ast:token:back-quoted" lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceNameWord, sourceAtomicWord, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  classification_row_simp

theorem name_integer_eventuallyExact (lexeme : Pattern) :
    EventuallyExact (decodeName (sourceIntegerName lexeme))
      (decodedName lexeme) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [decodeName, sourceIntegerName, sourceToken, a]
  rw [rewriteAt_eq_root_filter, nameRootRules]
  classification_row_simp

theorem decodeCanonicalName_eventuallyExact (source : Pattern)
    (result : String)
    (decoded : decodeCanonicalName? source = some result) :
    EventuallyExact (decodeName source)
      (decodedName (Carrier.encodeString result)) := by
  fun_cases decodeCanonicalName? source
  · rename_i word
    fun_cases decodeCanonicalAtomicWord? word
    · rename_i lexeme
      simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact name_lower_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact name_singleQuoted_eventuallyExact (.apply lexeme [])
    · rename_i lexeme
      simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
      subst result
      exact name_backQuoted_eventuallyExact (.apply lexeme [])
    · simp [decodeCanonicalName?, decodeCanonicalAtomicWord?] at decoded
  · rename_i lexeme
    simp [decodeCanonicalName?] at decoded
    subst result
    exact name_integer_eventuallyExact (.apply lexeme [])
  · simp [decodeCanonicalName?] at decoded

inductive FormulaFamily where
  | thf | tff | tcf | fof | cnf | tpi
  deriving DecidableEq, Repr

def FormulaFamily.wrapperLabel : FormulaFamily -> String
  | .thf => "tptp92-ast:annotated-formula:alt-1"
  | .tff => "tptp92-ast:annotated-formula:alt-2"
  | .tcf => "tptp92-ast:annotated-formula:alt-3"
  | .fof => "tptp92-ast:annotated-formula:alt-4"
  | .cnf => "tptp92-ast:annotated-formula:alt-5"
  | .tpi => "tptp92-ast:annotated-formula:alt-6"

def FormulaFamily.annotatedLabel : FormulaFamily -> String
  | .thf => "tptp92-ast:thf-annotated:alt-1"
  | .tff => "tptp92-ast:tff-annotated:alt-1"
  | .tcf => "tptp92-ast:tcf-annotated:alt-1"
  | .fof => "tptp92-ast:fof-annotated:alt-1"
  | .cnf => "tptp92-ast:cnf-annotated:alt-1"
  | .tpi => "tptp92-ast:tpi-annotated:alt-1"

def FormulaFamily.ruleName : FormulaFamily -> String
  | .thf => "tptp-include-input:inspect-thf"
  | .tff => "tptp-include-input:inspect-tff"
  | .tcf => "tptp-include-input:inspect-tcf"
  | .fof => "tptp-include-input:inspect-fof"
  | .cnf => "tptp-include-input:inspect-cnf"
  | .tpi => "tptp-include-input:inspect-tpi"

def FormulaFamily.bodyType : FormulaFamily -> String
  | .thf => "Tptp92Ast:thf-formula"
  | .tff => "Tptp92Ast:tff-formula"
  | .tcf => "Tptp92Ast:tcf-formula"
  | .fof => "Tptp92Ast:fof-formula"
  | .cnf => "Tptp92Ast:cnf-formula"
  | .tpi => "Tptp92Ast:tpi-formula"

private def inspectBindings
    (origin sourceName role body annotations span : Pattern) : Bindings :=
  [("sourceName", sourceName), ("body", body),
    ("annotations", annotations), ("role", role), ("span", span),
    ("origin", origin)]

private theorem inspect_match_exact
    (wrapperLabel annotatedLabel : String)
    (origin sourceName role body annotations span : Pattern) :
    let input := locatedFormulaInput wrapperLabel annotatedLabel sourceName role
      body annotations span
    matchPattern
        (inspectFormula (v "origin")
          (locatedFormulaInput wrapperLabel annotatedLabel (v "sourceName")
            (v "role") (v "body") (v "annotations") (v "span")))
        (inspectFormula origin input) =
      [inspectBindings origin sourceName role body annotations span] := by
  simp [inspectBindings, inspectFormula, locatedFormulaInput,
    annotatedFormula, a, v, matchPattern, matchArgs, mergeBindings]

/-- A finite path whose every edge has one exact reduct above a finite local
fuel threshold.  It preserves determinism at each declared micro-step. -/
inductive ExactPath : Pattern -> Pattern -> Prop where
  | done (state : Pattern) : ExactPath state state
  | step {source middle target : Pattern} :
      EventuallyExact source middle -> ExactPath middle target ->
      ExactPath source target

private theorem classify_formula_eventuallyExact
    (sourceId sourceDigest inputIndex path annotated start stop : Pattern) :
    let span := sourceSpan start stop
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact (classify sourceId sourceDigest inputIndex path input)
      (inspectFormula (formulaOrigin sourceId sourceDigest inputIndex path)
        input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [classify, a]
  rw [rewriteAt_eq_root_filter, classificationRootRules]
  classification_row_simp

theorem include_eventuallyExact
    (sourceId sourceDigest inputIndex path directive start stop : Pattern) :
    let span := sourceSpan start stop
    EventuallyExact
      (classify sourceId sourceDigest inputIndex path
        (.apply "tptp92-ast:tptp-input:alt-2" [directive, span]))
      (includeOutcome directive span) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [classify, a]
  rw [rewriteAt_eq_root_filter, classificationRootRules]
  classification_row_simp

private theorem apply_inspectFormulaRule_family_exact (fuel : Nat)
    (family : FormulaFamily)
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula family.wrapperLabel family.annotatedLabel
      sourceName role body annotations
    let input : Pattern :=
      .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    applyRuleUsing base language (rewriteAt base language fuel)
        (inspectFormulaRule family.ruleName family.wrapperLabel
          family.annotatedLabel family.bodyType)
        (inspectFormula origin input) =
      [decodeFormula origin sourceName input] := by
  simp only [inspectFormulaRule, mkRule, typed, a, applyRuleUsing,
    matchPatternForRule_eq_syntactic]
  have initialMatch := inspect_match_exact family.wrapperLabel
    family.annotatedLabel origin sourceName role body annotations span
  simp only [locatedFormulaInput, a] at initialMatch
  rw [initialMatch]
  simp [inspectBindings, premisesUsing, decodeFormula, annotatedFormula, a, v,
    applyBindingsForRule, applyBindings]

@[simp] private theorem apply_inspectFormulaRule_mismatch (fuel : Nat)
    (ruleName ruleWrapper ruleAnnotated bodyType inputWrapper inputAnnotated :
      String)
    (origin sourceName role body annotations span : Pattern)
    (different : ruleWrapper ≠ inputWrapper) :
    applyRuleUsing base language (rewriteAt base language fuel)
        (inspectFormulaRule ruleName ruleWrapper ruleAnnotated bodyType)
        (.apply "tptp-include-input:inspect-formula"
          [origin,
            .apply "tptp92-ast:tptp-input:alt-1"
              [.apply inputWrapper
                [.apply inputAnnotated
                  [sourceName, role, body, annotations]], span]]) = [] := by
  simp [inspectFormulaRule, inspectFormula, annotatedFormula, mkRule, typed,
    a, v, applyRuleUsing, matchPatternForRule_eq_syntactic, matchPattern,
    matchArgs, different]

private theorem inspect_thf_eventuallyExact
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula "tptp92-ast:annotated-formula:alt-1"
      "tptp92-ast:thf-annotated:alt-1" sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [inspectFormula, annotatedFormula, a]
  rw [rewriteAt_eq_root_filter, inspectionRootRules]
  simp only [inspectFormulaRules, List.flatMap_cons, List.flatMap_nil]
  have exactRow := apply_inspectFormulaRule_family_exact fuel .thf origin
    sourceName role body annotations span
  simp only [FormulaFamily.ruleName, FormulaFamily.wrapperLabel,
    FormulaFamily.annotatedLabel, FormulaFamily.bodyType, inspectFormula,
    annotatedFormula, a] at exactRow
  rw [exactRow]
  simp

private theorem inspect_tff_eventuallyExact
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula "tptp92-ast:annotated-formula:alt-2"
      "tptp92-ast:tff-annotated:alt-1" sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [inspectFormula, annotatedFormula, a]
  rw [rewriteAt_eq_root_filter, inspectionRootRules]
  simp only [inspectFormulaRules, List.flatMap_cons, List.flatMap_nil]
  have exactRow := apply_inspectFormulaRule_family_exact fuel .tff origin
    sourceName role body annotations span
  simp only [FormulaFamily.ruleName, FormulaFamily.wrapperLabel,
    FormulaFamily.annotatedLabel, FormulaFamily.bodyType, inspectFormula,
    annotatedFormula, a] at exactRow
  rw [exactRow]
  simp

private theorem inspect_tcf_eventuallyExact
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula "tptp92-ast:annotated-formula:alt-3"
      "tptp92-ast:tcf-annotated:alt-1" sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [inspectFormula, annotatedFormula, a]
  rw [rewriteAt_eq_root_filter, inspectionRootRules]
  simp only [inspectFormulaRules, List.flatMap_cons, List.flatMap_nil]
  have exactRow := apply_inspectFormulaRule_family_exact fuel .tcf origin
    sourceName role body annotations span
  simp only [FormulaFamily.ruleName, FormulaFamily.wrapperLabel,
    FormulaFamily.annotatedLabel, FormulaFamily.bodyType, inspectFormula,
    annotatedFormula, a] at exactRow
  rw [exactRow]
  simp

private theorem inspect_fof_eventuallyExact
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula "tptp92-ast:annotated-formula:alt-4"
      "tptp92-ast:fof-annotated:alt-1" sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [inspectFormula, annotatedFormula, a]
  rw [rewriteAt_eq_root_filter, inspectionRootRules]
  simp only [inspectFormulaRules, List.flatMap_cons, List.flatMap_nil]
  have exactRow := apply_inspectFormulaRule_family_exact fuel .fof origin
    sourceName role body annotations span
  simp only [FormulaFamily.ruleName, FormulaFamily.wrapperLabel,
    FormulaFamily.annotatedLabel, FormulaFamily.bodyType, inspectFormula,
    annotatedFormula, a] at exactRow
  rw [exactRow]
  simp

private theorem inspect_cnf_eventuallyExact
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula "tptp92-ast:annotated-formula:alt-5"
      "tptp92-ast:cnf-annotated:alt-1" sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [inspectFormula, annotatedFormula, a]
  rw [rewriteAt_eq_root_filter, inspectionRootRules]
  simp only [inspectFormulaRules, List.flatMap_cons, List.flatMap_nil]
  have exactRow := apply_inspectFormulaRule_family_exact fuel .cnf origin
    sourceName role body annotations span
  simp only [FormulaFamily.ruleName, FormulaFamily.wrapperLabel,
    FormulaFamily.annotatedLabel, FormulaFamily.bodyType, inspectFormula,
    annotatedFormula, a] at exactRow
  rw [exactRow]
  simp

private theorem inspect_tpi_eventuallyExact
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula "tptp92-ast:annotated-formula:alt-6"
      "tptp92-ast:tpi-annotated:alt-1" sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  apply eventuallyExact_of_one_step
  intro fuel
  simp only [inspectFormula, annotatedFormula, a]
  rw [rewriteAt_eq_root_filter, inspectionRootRules]
  simp only [inspectFormulaRules, List.flatMap_cons, List.flatMap_nil]
  have exactRow := apply_inspectFormulaRule_family_exact fuel .tpi origin
    sourceName role body annotations span
  simp only [FormulaFamily.ruleName, FormulaFamily.wrapperLabel,
    FormulaFamily.annotatedLabel, FormulaFamily.bodyType, inspectFormula,
    annotatedFormula, a] at exactRow
  rw [exactRow]
  simp

private theorem inspect_formula_eventuallyExact
    (family : FormulaFamily)
    (origin sourceName role body annotations span : Pattern) :
    let annotated := annotatedFormula family.wrapperLabel family.annotatedLabel
      sourceName role body annotations
    let input := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
    EventuallyExact
      (inspectFormula origin input)
      (decodeFormula origin sourceName input) := by
  cases family
  · exact inspect_thf_eventuallyExact origin sourceName role body annotations span
  · exact inspect_tff_eventuallyExact origin sourceName role body annotations span
  · exact inspect_tcf_eventuallyExact origin sourceName role body annotations span
  · exact inspect_fof_eventuallyExact origin sourceName role body annotations span
  · exact inspect_cnf_eventuallyExact origin sourceName role body annotations span
  · exact inspect_tpi_eventuallyExact origin sourceName role body annotations span

private theorem finalize_rewriteAt_exact (fuel : Nat)
    (origin sourceName input name : Pattern)
    (nameStep : rewriteAt base language fuel (decodeName sourceName) =
      [decodedName name]) :
    rewriteAt base language (fuel + 1)
        (decodeFormula origin sourceName input) =
      [formulaOutcome (resolvedFormula name input origin)] := by
  simp only [decodeName, decodedName, decodeFormula, a] at nameStep ⊢
  rw [rewriteAt_eq_root_filter, finalizeRootRules]
  classification_row_simp
  simp [nameStep, matchPattern, matchArgs, mergeBindings]

private theorem finalize_eventuallyExact
    (origin sourceName input name : Pattern)
    (nameExact : EventuallyExact (decodeName sourceName)
      (decodedName name)) :
    EventuallyExact
      (decodeFormula origin sourceName input)
      (formulaOutcome (resolvedFormula name input origin)) :=
  eventuallyExact_of_one_premise _ _ _ _ nameExact
    (fun fuel nameStep => finalize_rewriteAt_exact fuel origin sourceName input
      name nameStep)

private theorem formula_exact_path
    (family : FormulaFamily)
    (sourceId sourceDigest : String) (inputIndex : Nat)
    (path : List IncludeEdge)
    (sourceName role body annotations start stop : Pattern) (name : String)
    (decoded : decodeCanonicalName? sourceName = some name) :
    let span := sourceSpan start stop
    let input := locatedFormulaInput family.wrapperLabel family.annotatedLabel
      sourceName role body annotations span
    ExactPath (encodeRequest sourceId sourceDigest inputIndex path input)
      (encodeClassifiedInput
        (resolved sourceId sourceDigest inputIndex path name input)) := by
  let encodedSource := Carrier.encodeString sourceId
  let encodedDigest := Carrier.encodeString sourceDigest
  let encodedIndex := Carrier.encodeIndex inputIndex
  let encodedPath := Carrier.encodeIncludeEdges path
  let encodedOrigin := formulaOrigin encodedSource encodedDigest encodedIndex
    encodedPath
  let annotated := annotatedFormula family.wrapperLabel family.annotatedLabel
    sourceName role body annotations
  let span := sourceSpan start stop
  let input : Pattern := .apply "tptp92-ast:tptp-input:alt-1" [annotated, span]
  apply ExactPath.step
    (classify_formula_eventuallyExact encodedSource encodedDigest encodedIndex
      encodedPath annotated start stop)
  apply ExactPath.step
    (inspect_formula_eventuallyExact family encodedOrigin sourceName role body
      annotations span)
  apply ExactPath.step
  · exact finalize_eventuallyExact encodedOrigin sourceName input
      (Carrier.encodeString name)
      (decodeCanonicalName_eventuallyExact sourceName name decoded)
  · simpa [encodeClassifiedInput, resolved, locatedFormulaInput, input, a,
      annotated, encodedOrigin, encodedSource, encodedDigest, encodedIndex,
      encodedPath] using
      ExactPath.done
        (formulaOutcome
          (resolvedFormula (Carrier.encodeString name) input
            encodedOrigin))

theorem classifyInput_exact_path
    (sourceId sourceDigest : String) (inputIndex : Nat)
    (path : List IncludeEdge) (input : Pattern) (result : ClassifiedInput)
    (classified : classifyInput? sourceId sourceDigest inputIndex path input =
      some result) :
    ExactPath (encodeRequest sourceId sourceDigest inputIndex path input)
      (encodeClassifiedInput result) := by
  fun_cases classifyInput? sourceId sourceDigest inputIndex path input
  · rename_i sourceName role body annotations start stop
    rcases Option.bind_eq_some_iff.mp classified with
      ⟨name, decoded, equality⟩
    cases equality
    exact formula_exact_path .thf sourceId sourceDigest inputIndex path
      sourceName role body annotations start stop name decoded
  · rename_i sourceName role body annotations start stop
    rcases Option.bind_eq_some_iff.mp classified with
      ⟨name, decoded, equality⟩
    cases equality
    exact formula_exact_path .tff sourceId sourceDigest inputIndex path
      sourceName role body annotations start stop name decoded
  · rename_i sourceName role body annotations start stop
    rcases Option.bind_eq_some_iff.mp classified with
      ⟨name, decoded, equality⟩
    cases equality
    exact formula_exact_path .tcf sourceId sourceDigest inputIndex path
      sourceName role body annotations start stop name decoded
  · rename_i sourceName role body annotations start stop
    rcases Option.bind_eq_some_iff.mp classified with
      ⟨name, decoded, equality⟩
    cases equality
    exact formula_exact_path .fof sourceId sourceDigest inputIndex path
      sourceName role body annotations start stop name decoded
  · rename_i sourceName role body annotations start stop
    rcases Option.bind_eq_some_iff.mp classified with
      ⟨name, decoded, equality⟩
    cases equality
    exact formula_exact_path .cnf sourceId sourceDigest inputIndex path
      sourceName role body annotations start stop name decoded
  · rename_i sourceName role body annotations start stop
    rcases Option.bind_eq_some_iff.mp classified with
      ⟨name, decoded, equality⟩
    cases equality
    exact formula_exact_path .tpi sourceId sourceDigest inputIndex path
      sourceName role body annotations start stop name decoded
  · rename_i directive start stop
    cases classified
    apply ExactPath.step
    · simpa [encodeRequest, sourceSpan, a] using
        include_eventuallyExact (Carrier.encodeString sourceId)
          (Carrier.encodeString sourceDigest) (Carrier.encodeIndex inputIndex)
          (Carrier.encodeIncludeEdges path) directive start stop
    · exact ExactPath.done
        (includeOutcome directive (sourceSpan start stop))
  · simp_all [classifyInput?]

namespace Canary

def lexeme (value : String) : Pattern := .apply value []

def lowerName (value : String) : Pattern :=
  sourceNameWord "tptp92-ast:atomic-word:alt-1"
    "tptp92-ast:token:lower-word" (lexeme value)

def role : Pattern :=
  .apply "tptp92-ast:formula-role:alt-1"
    [.apply "tptp92-ast:token:lower-word" [lexeme "axiom"]]

def annotations : Pattern := .apply "tptp92-ast:annotations:alt-2" []
def span : Pattern := .apply "tptp92-ast:source-span" [lexeme "0", lexeme "1"]
def body : Pattern := .apply "canary-body" []

def thfInput : Pattern :=
  locatedFormulaInput "tptp92-ast:annotated-formula:alt-1"
    "tptp92-ast:thf-annotated:alt-1" (lowerName "thf_one") role body
    annotations span

def tffInput : Pattern :=
  locatedFormulaInput "tptp92-ast:annotated-formula:alt-2"
    "tptp92-ast:tff-annotated:alt-1" (lowerName "tff_one") role body
    annotations span

def tcfInput : Pattern :=
  locatedFormulaInput "tptp92-ast:annotated-formula:alt-3"
    "tptp92-ast:tcf-annotated:alt-1" (lowerName "tcf_one") role body
    annotations span

def fofInput : Pattern :=
  locatedFormulaInput "tptp92-ast:annotated-formula:alt-4"
    "tptp92-ast:fof-annotated:alt-1" (lowerName "fof_one") role body
    annotations span

def cnfInput : Pattern :=
  locatedFormulaInput "tptp92-ast:annotated-formula:alt-5"
    "tptp92-ast:cnf-annotated:alt-1" (lowerName "cnf_one") role body
    annotations span

def tpiInput : Pattern :=
  locatedFormulaInput "tptp92-ast:annotated-formula:alt-6"
    "tptp92-ast:tpi-annotated:alt-1" (lowerName "tpi_one") role body
    annotations span

def includeInput : Pattern :=
  .apply "tptp92-ast:tptp-input:alt-2"
    [.apply "canary-include" [], span]

example : ∃ result,
    classifyInput? "root" "digest" 0 [] thfInput = some result ∧
      ExactPath (encodeRequest "root" "digest" 0 [] thfInput)
        (encodeClassifiedInput result) := by
  refine ⟨resolved "root" "digest" 0 [] "thf_one" thfInput, rfl, ?_⟩
  exact classifyInput_exact_path _ _ _ _ _ _ rfl

example : classifyInput? "root" "digest" 1 [] tffInput =
    some (resolved "root" "digest" 1 [] "tff_one" tffInput) := by
  rfl

example : classifyInput? "root" "digest" 2 [] tcfInput =
    some (resolved "root" "digest" 2 [] "tcf_one" tcfInput) := by
  rfl

example : classifyInput? "root" "digest" 3 [] fofInput =
    some (resolved "root" "digest" 3 [] "fof_one" fofInput) := by
  rfl

example : classifyInput? "root" "digest" 4 [] cnfInput =
    some (resolved "root" "digest" 4 [] "cnf_one" cnfInput) := by
  rfl

example : classifyInput? "root" "digest" 5 [] tpiInput =
    some (resolved "root" "digest" 5 [] "tpi_one" tpiInput) := by
  rfl

example : classifyInput? "root" "digest" 1 [] includeInput =
    some (.include (.apply "canary-include" []) span) := by
  rfl

example : classifyInput? "root" "digest" 0 []
    (.apply "tptp92-ast:tptp-input:alt-1"
      [.apply "tptp92-ast:annotated-formula:alt-1" [body], span]) = none := by
  rfl

example : classifyInput? "root" "digest" 0 []
    (locatedFormulaInput "tptp92-ast:annotated-formula:alt-4"
      "tptp92-ast:fof-annotated:alt-1" (.apply "bad-name" []) role body
      annotations span) = none := by
  rfl

example : classifyInput? "root" "digest" 0 []
    (locatedFormulaInput "tptp92-ast:annotated-formula:alt-4"
      "tptp92-ast:fof-annotated:alt-1" (lowerName "bad_span") role body
      annotations (.apply "not-a-source-span" [])) = none := by
  rfl

example : classifyInput? "root" "digest" 0 []
    (.apply "tptp92-ast:tptp-input:alt-2"
      [.apply "canary-include" [], .apply "not-a-source-span" []]) = none := by
  rfl

example : classifyInput? "root" "digest" 0 []
    (.apply "not-an-official-input" []) = none := by
  rfl

end Canary

#print axioms classifyInput_exact_path

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationAgreement
