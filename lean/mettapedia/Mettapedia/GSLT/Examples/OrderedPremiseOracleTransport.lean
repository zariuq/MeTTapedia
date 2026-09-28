import Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport
import Mettapedia.GSLT.Examples.TypedPremiseOutput
import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

/-!
# A relation output consumed by a later scoped step premise

The first authored premise produces `Y` from a root equality query. The
second premise uses that same open contextual value as its step source and
produces `Z`. Duplicating the selected step answer moves the old result to
ordinal one while the root event stays at ordinal zero. The final lambda
retains the ambient variable supplied before its binder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.OrderedPremiseOracleTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding
open Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport
open Mettapedia.GSLT.Examples.TypedPremiseOutput

private abbrev term : TypeExpr := .base "Term"

/-- The second premise has an explicit empty local binder context; its
source is supplied by the preceding equality query in the caller's context. -/
def orderedRule : RewriteRule :=
  { sortedPremiseRule with
    «name» := "ordered-root-output-then-step"
    typeContext := [("X", term), ("Y", term), ("Z", term)]
    premises :=
      [.relationQuery "eq" [.fvar "X", .fvar "Y"],
       .scopedStep
        { binders := [], resultType := term,
          source := .fvar "Y", target := .fvar "Z" }]
    right := .lambda none (.fvar "Z")
    «bindings» := some
      { dependencies := [("X", []), ("Y", []), ("Z", [])] } }

def orderedLanguage : LanguageDef :=
  { sortedPremiseLanguage with «rewrites» := [orderedRule] }

theorem ordered_language_validates : orderedLanguage.validate = [] := by
  simp [LanguageDef.validate, orderedLanguage, orderedRule,
    sortedPremiseLanguage, sortedPremiseRule,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.declaredPremiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseLanguage,
    Mettapedia.OSLF.MeTTaIL.ScopedRuleRegression.premiseRule,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputLanguage,
    Mettapedia.OSLF.MeTTaIL.RuleBindingRegression.premiseOutputRule,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateTerm, LanguageDef.validateRewrite,
    LanguageDef.validateTypeExpr_eq_nil_iff,
    LanguageDef.validatePatternConstructors,
    LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.term, TypeExpr.baseType,
    TypeExpr.baseNames,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    LanguageDef.premiseStepTypeExprs,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]
  decide +kernel

theorem ordered_rule_admitted :
    admittedFor orderedRule
      { dependencies := [("X", []), ("Y", []), ("Z", [])] } = true := by
  decide +kernel

theorem ordered_rule_schema_typed :
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.RewriteHasType
      orderedLanguage orderedRule := by
  refine ⟨.arrow term term, ?_, ?_⟩
  · exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)
  · exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound
      (by decide +kernel)

/-- The authored pair compiles in place to the canonical sorted premise
representation: the second premise has its explicit empty local context. -/
theorem ordered_premises_compile :
    Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileRulePremises?
      orderedLanguage orderedRule =
      some [.relationQuery "eq" [.fvar "X", .fvar "Y"],
        .step
          { binders := [], resultType := term,
            source := .fvar "Y", target := .fvar "Z" }] := by
  decide +kernel

/-- A selected open value is returned without closing over the right-hand
lambda's binder. -/
def openOracle : StepOracle Unit := fun _ source =>
  if source = .bvar 0 then [((), .bvar 0)] else []

def duplicatedOpenOracle : StepOracle Unit := fun depth source =>
  openOracle depth source ++ openOracle depth source

def occurrenceEmbedding (depth : Nat) (source : Pattern) :
    Embedding
      (fun oldValue newValue =>
        oldValue.2 = newValue.2 ∧ oldValue.1 = newValue.1)
      (openOracle depth source) (duplicatedOpenOracle depth source) where
  position :=
    (Embedding.afterPrefix (openOracle depth source)
      (openOracle depth source)).position
  relates := by
    intro i
    have same :=
      (Embedding.afterPrefix (openOracle depth source)
        (openOracle depth source)).relates i
    exact ⟨congrArg Prod.snd same, congrArg Prod.fst same⟩

/-- Root then step: the root ordinal is zero, and the original step answer
is ordinal zero before duplicating the oracle list. -/
theorem original_ordered_firing_shape :
    (applyRuleWithOracle openOracle RelationEnv.empty orderedLanguage 1
      orderedRule openInput).map
        (fun firing => (firing.history, firing.target)) =
      [([.root 0 0, .step 1 0 ()], openOutput)] := by
  decide +kernel

/-- The generic transport theorem applies to the entire two-premise authored
rule and retains the open result and each intermediate contextual assignment. -/
theorem ordered_firing_transports :
    ∃ spec oldFiring newFiring,
      orderedRule.bindings = some spec ∧
      oldFiring ∈ applyRuleWithOracle openOracle RelationEnv.empty
        orderedLanguage 1 orderedRule openInput ∧
      newFiring ∈ applyRuleWithOracle duplicatedOpenOracle
        RelationEnv.empty orderedLanguage 1 orderedRule openInput ∧
      oldFiring.target = openOutput ∧
      newFiring.target = openOutput ∧
      RunTransport Eq openOracle duplicatedOpenOracle
        occurrenceEmbedding RelationEnv.empty orderedLanguage
        orderedLanguage orderedRule spec 1 0 orderedRule.premises
        oldFiring.captured oldFiring.completed oldFiring.history
        newFiring.history := by
  have tagged : ([.root 0 0, .step 1 0 ()], openOutput) ∈
      (applyRuleWithOracle openOracle RelationEnv.empty orderedLanguage 1
        orderedRule openInput).map
          (fun firing => (firing.history, firing.target)) := by
    rw [original_ordered_firing_shape]
    simp
  obtain ⟨oldFiring, selected, shape⟩ := List.mem_map.mp tagged
  have targetEq : oldFiring.target = openOutput :=
    congrArg Prod.snd shape
  obtain ⟨spec, newFiring, binding, newSelected, _, _, targetTransport,
      historyTransport⟩ :=
    applyRuleWithOracle_transport Eq openOracle duplicatedOpenOracle
      occurrenceEmbedding RelationEnv.empty orderedLanguage
        orderedLanguage 1 orderedRule openInput oldFiring selected
  exact ⟨spec, oldFiring, newFiring, binding, selected,
    newSelected, targetEq, targetTransport.trans targetEq,
    historyTransport⟩

/-- The root event remains first; the old step answer is the second duplicate
at premise index one. Both copies reach the same open target. -/
theorem duplicated_ordered_firing_shape :
    (applyRuleWithOracle duplicatedOpenOracle RelationEnv.empty
      orderedLanguage 1 orderedRule openInput).map
        (fun firing => (firing.history, firing.target)) =
      [([.root 0 0, .step 1 0 ()], openOutput),
       ([.root 0 0, .step 1 1 ()], openOutput)] := by
  decide +kernel

/-- If the root relation produces no contextual `Y`, the later step has no
source to execute. This detects loss of the ordered assignment dependency. -/
def missingRootOutputRule : RewriteRule :=
  { orderedRule with
    «name» := "missing-root-output"
    premises :=
      [.relationQuery "missing" [.fvar "X", .fvar "Y"],
       .scopedStep
        { binders := [], resultType := term,
          source := .fvar "Y", target := .fvar "Z" }] }

def missingRootOutputLanguage : LanguageDef :=
  { orderedLanguage with «rewrites» := [missingRootOutputRule] }

theorem missing_root_output_blocks_step :
    applyRuleWithOracle openOracle RelationEnv.empty
      missingRootOutputLanguage 1 missingRootOutputRule openInput = [] := by
  decide +kernel

#print axioms ordered_language_validates
#print axioms ordered_rule_admitted
#print axioms ordered_rule_schema_typed
#print axioms ordered_premises_compile
#print axioms original_ordered_firing_shape
#print axioms ordered_firing_transports
#print axioms duplicated_ordered_firing_shape
#print axioms missing_root_output_blocks_step

end Mettapedia.GSLT.Examples.OrderedPremiseOracleTransport
