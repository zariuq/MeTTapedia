import Mettapedia.GSLT.LanguageDef.Cost.FiniteActivePair
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteRestBoundary
import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mettapedia.GSLT.LanguageDef.TypedFullSpineRecovery

/-!
# Synchronous funding at the selected active pair

Only the interacting input and output occur inside the signed envelope.
The authored parallel-context rule retains an arbitrary external wrapped
remainder. Source specialization, rule binding admission, and actual runtime
controls are separate from any general subject-reduction theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePair

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- Binding metadata elaborated on the unchanged authored COMM patterns.
The source's collection remainder is explicitly given its collection type. -/
def sourceBindingSpec : RuleBindingSpec where
  dependencies := [("n", []), ("p", [TypeExpr.name]), ("q", []), ("k", []), ("rest", [])]
  occurrences :=
    [{ name := "p", site := .left, path := [0, 1, 0], arguments := [.bvar 0] },
     { name := "p", site := .right, path := [0, 0], arguments := [.bvar 0] }]

def sourceAnnotatedRule : RewriteRule :=
  { rhoSyncCommRewrite with
    typeContext := rhoSyncCommRewrite.typeContext ++
      [("rest", .collection .hashBag TypeExpr.proc)]
    bindings := some sourceBindingSpec }

theorem source_binding_admitted : admittedFor sourceAnnotatedRule sourceBindingSpec = true := by
  decide +kernel

theorem source_patterns_preserved : sourceAnnotatedRule.left = rhoSyncCommRewrite.left ∧
    sourceAnnotatedRule.right = rhoSyncCommRewrite.right ∧
    sourceAnnotatedRule.premises = rhoSyncCommRewrite.premises := ⟨rfl, rfl, rfl⟩

/-- The generated metadata is transported from that source annotation,
with envelope paths and dependency sorts determined by the finite profile. -/
def bindingSpec : RuleBindingSpec :=
  communicationDecoration.costActivePairBindingSpec sourceBindingSpec

def rule : RewriteRule :=
  { communicationDecoration.costActivePairRewrite with bindings := some bindingSpec }

theorem binding_admitted : admittedFor rule bindingSpec = true := by decide +kernel

/-- This is the source ParCong shape with its free variables renamed and
their sorts elaborated in the wrapped fibre. Its reduction premise remains. -/
def parallelRule : RewriteRule where
  name := rhoParCongRewrite.name
  typeContext :=
    [(costSourceSchemaName "S", .base costWrappedSortName),
     (costSourceSchemaName "T", .base costWrappedSortName),
     (costSourceSchemaName "rest", .collection .hashBag (.base costWrappedSortName))]
  premises := rhoParCongRewrite.premises.map (mapPremiseSchemaNames costSourceSchemaName)
  left := mapPatternSchemaNames costSourceSchemaName rhoParCongRewrite.left
  right := mapPatternSchemaNames costSourceSchemaName rhoParCongRewrite.right
  bindings := some { dependencies :=
    [(costSourceSchemaName "S", []), (costSourceSchemaName "T", []),
      (costSourceSchemaName "rest", [])] }

def language : LanguageDef :=
  { communicationDecoration.costWholeLanguage with rewrites := [rule, parallelRule] }

theorem rule_valid : LanguageDef.validateRewrite language rule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
    | rfl
    | decide +kernel
    | (rule_patterns [rule, communicationDecoration, ContinuationDecorationProfile.costActivePairRewrite,
        ContinuationDecorationProfile.costActivePairSource,
        ContinuationDecorationProfile.costActivePairTarget,
        ContinuationDecorationProfile.costActivePairRedex,
        ContinuationDecorationProfile.costActivePairContractum,
        ContinuationDecorationProfile.mapContractum, rhoSyncIGSLT, rhoSyncInteractivePresentation,
        rhoSyncCommRewrite, closeRootCollectionRest, mapPatternSchemaNames,
        mapPatternListSchemaNames, mapPattern, mapPatternList, language,
        ContinuationDecorationProfile.costWholeRedexRewrite,
        ContinuationDecorationProfile.costWholeRedexTypeContext,
        ContinuationDecorationProfile.costRetypedSourceContext,
        ContinuationDecorationProfile.contractumSymbols]
       decide +kernel)

theorem parallel_valid : LanguageDef.validateRewrite language parallelRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence
    (source := costSourceSchemaName "S") (target := costSourceSchemaName "T") <;>
    first
    | rfl
    | decide +kernel
    | (rule_patterns [parallelRule, rhoParCongRewrite, mapPatternSchemaNames,
        mapPatternListSchemaNames, language]
       decide +kernel)

theorem language_valid : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      communicationDecoration.costWholeLanguage FiniteWhole.language_valid
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      communicationDecoration.costWholeLanguage FiniteWhole.language_valid
  · exact LanguageDef.equationNames_nodup_of_validate_eq_nil
      communicationDecoration.costWholeLanguage FiniteWhole.language_valid
  · decide +kernel
  · intro term member
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil _
      FiniteWhole.language_valid term member
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_validate_eq_nil _
      FiniteWhole.language_valid equation member
  · intro rewrite member
    have cases : rewrite = rule ∨ rewrite = parallelRule := by simpa [language] using member
    rcases cases with rfl | rfl
    · exact rule_valid
    · exact parallel_valid

theorem binding_declarations_valid : bindingDeclarationsValid language = true := by
  unfold bindingDeclarationsValid
  rw [language_valid]
  decide +kernel

def presentation : ValidatedReflectiveLanguageDef where
  core := ⟨language, language_valid⟩
  reflection := ⟨communicationDecoration.costWholeReflectionProfile
    FiniteWhole.sourceReflection.1, by decide +kernel⟩

/-- Binding metadata and the contextual frame do not change the funded
active-pair pattern or its computed continuation. -/
theorem rule_patterns : rule.left = communicationDecoration.costActivePairSource ∧
    rule.right = communicationDecoration.costActivePairTarget := ⟨rfl, rfl⟩

theorem pair_redex_sorted : HasSort communicationDecoration.costCoreLanguage
    communicationDecoration.costWholeRedexFreeContext []
    communicationDecoration.costActivePairRedex (costBaseSortName "Proc") :=
  communicationDecoration.costActivePairRedex_hasType communicationDecoration_redexRetypable

theorem pair_contractum_sorted : HasSort communicationDecoration.costCoreLanguage
    communicationDecoration.costWholeRedexFreeContext []
    communicationDecoration.costActivePairContractum costWrappedSortName :=
  communicationDecoration.costActivePairContractum_hasType communicationDecoration_wrappable

def sourcePair (channel body sent after : Pattern) : Pattern := .collection .hashBag
  [.apply "PInput" [channel, .lambda none body],
    .apply "POutputK" [channel, sent, after]] none

def sourceResidual (body sent after : Pattern) : Pattern := .collection .hashBag
  [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar (.apply "NQuote" [sent]) body, after] none

/-- Every raw minimal pair remains an actual instance of the original
authored COMM rule, whose captured internal remainder is empty. -/
theorem source_pair_is_authored (channel body sent after : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty) rhoSyncCalc
      (sourcePair channel body sent after) (sourceResidual body sent after) := by
  apply step_of_rule (rule := rhoSyncCommRewrite)
    (initialBindings := [("k", after), ("q", sent),
      ("rest", .collection .hashBag [] none), ("p", body), ("n", channel)])
    (finalBindings := [("k", after), ("q", sent),
      ("rest", .collection .hashBag [] none), ("p", body), ("n", channel)])
  · exact List.mem_cons_self
  · rw [matchPatternForRule_eq_syntactic]
    simp [rhoSyncCommRewrite, sourcePair, matchPattern, matchArgs, matchBag, mergeBindings]
  · exact .nil
  · simp [rhoSyncCommRewrite, Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing_empty,
      rhoSyncCommRewrite, applyRuleBindings, applyBindingsScoped, applyBindingsScopedList,
      captureDepth, captureDepthList, restSplice, sourceResidual,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

def external : Pattern := .apply costSignedConstructorName
  [.apply (costBaseConstructorName "PZero") [], FiniteWhole.unitSignature]

def framedSource : Pattern := .collection .hashBag [FiniteWhole.source, external] none
def framedTarget : Pattern := .collection .hashBag [FiniteWhole.target, external] none

theorem framed_source_typed : HasSort language FreeTypeContext.empty []
    framedSource costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem framed_target_typed : HasSort language FreeTypeContext.empty []
    framedTarget costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem pair_reflective_reducts : rewriteStepWithReflection presentation.reflection.1
    language FiniteWhole.source = [FiniteWhole.target] := by decide +kernel

theorem framed_reflective_reducts :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt
      (.reflection presentation.reflection.1)
      (engineBasePremises Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
      language 2 framedSource = [framedTarget] := by decide +kernel

/-- An unmatched process inside the signature remains outside this selected
pair rule, even though the earlier whole-redex construction consumed it. -/
theorem internal_rest_rejected : rewriteStepWithReflection presentation.reflection.1
    language FiniteRestBoundary.source = [] := by decide +kernel

theorem empty_stack_rejected : rewriteStepWithReflection presentation.reflection.1
    language (FiniteWhole.sourceWithStack FiniteWhole.emptyStack) = [] := by decide +kernel

theorem wrong_key_rejected : rewriteStepWithReflection presentation.reflection.1
    language (FiniteWhole.sourceWithStack FiniteWhole.wrongStack) = [] := by decide +kernel

#print axioms binding_declarations_valid
#print axioms source_pair_is_authored
#print axioms framed_reflective_reducts

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePair
