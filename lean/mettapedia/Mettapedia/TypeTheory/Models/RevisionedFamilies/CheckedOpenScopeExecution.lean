import Mettapedia.TypeTheory.Models.RevisionedFamilies.ComputedOpenAnswerFamily
import Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability
import Mettapedia.OSLF.Framework.WMCalculusGuardedExecutableOccurrence
import Mettapedia.OSLF.Framework.EngineOccurrenceGSLT

/-!
# Checked open extraction, guarded execution, and dependent answer use

A checked open match computes an intrinsic substitution for the authored
`Extract(W,q)` schema. A successful outside-scope premise then produces an
actual engine occurrence and an answer receipt for that very substitution.
Scope/query decoding is tied to the interpreted captured query, rather than
to unrelated semantic values. The occurrence survives dependent answer use.

The consumer below is a term in the existing semantic families CwF. This
does not yet give an authored Prime eliminator or generic binder semantics.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenScopeExecution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCombinedNamedFirstOrder
open Mettapedia.OSLF.Framework.WMCalculusCombinedOpenReification
open Mettapedia.OSLF.Framework.WMCalculusCombinedGenericOpenCodec
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusGuardedExecutableOccurrence
open Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider (singletonX)
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.Framework.EngineOccurrenceGSLT
open Mettapedia.TypeTheory.Models.RevisionedFamilies.ComputedOpenAnswerFamily

private abbrev EvidenceSort := TypeExpr.base "BinaryEvidence"
private abbrev CombinedLang := wmExtVertexLanguageDefGuarded combinedVertex

def extractSchema : Pattern := pExtract (.fvar "W") (.fvar "q")

def extractFree : FreeTypeContext :=
  fun variableName => if variableName == "W" then some (.base "State")
    else if variableName == "q" then some (.base "Query") else none

def extractEntries : List (String × TypeExpr) :=
  [("W", .base "State"), ("q", .base "Query")]

theorem extractEntries_fromUsed :
    fromUsed extractFree extractSchema.freeFvarNames = extractEntries := by
  cbv

abbrev ExtractContext := contextSorts extractEntries

def extractTerm : Term CombinedSignature ExtractContext EvidenceSort :=
  extract (.var .zero) (.var (.succ .zero))

def extractFragment : FirstOrder extractTerm :=
  .extract (.variable .zero) (.variable (.succ .zero))

theorem extractSchema_computes :
    reifyOpen? CombinedLang extractEntries extractSchema EvidenceSort =
      some extractTerm := by
  cbv

def targetEntries (free : FreeTypeContext) (bindings : Bindings) :=
  fromUsed free (capturedTargetNames extractEntries bindings)

/-- The returned substitution retains its computation equation and the
exact named target of the substituted intrinsic schema. -/
structure CheckedExtract (entries : List (String × TypeExpr)) (bindings : Bindings)
    (world query : Pattern) where
  sigma : Sub CombinedSignature ExtractContext
    (contextSorts entries)
  computed : reifyOpenImages? CombinedLang entries
    bindings extractEntries = some sigma
  supported : ∀ sort position, FirstOrder (sigma sort position)
  targetNamed : namedErase (names entries)
    (FirstOrder.substitute sigma supported extractFragment) = pExtract world query

/-- Successful executable admission produces the schema's computed
substitution without choosing a model or inventing alternative images. -/
theorem checkedExtract_of_answers
    (free : FreeTypeContext) (bindings : Bindings) (world query : Pattern)
    (returned : bindings ∈ checkedOpenAnswers extractFree free extractSchema
      EvidenceSort (pExtract world query)) :
    Nonempty (CheckedExtract (targetEntries free bindings) bindings world query) := by
  have images :=
    checkedOpenAnswers_all_images_supported_receipt extractFree free
      extractSchema EvidenceSort (pExtract world query) bindings returned
  dsimp only at images
  rw [extractEntries_fromUsed] at images
  obtain ⟨sigma, computed, supported, variableReceipt⟩ := images
  obtain ⟨plan, _, _, compiled, planReturned⟩ :=
    (checkedOpenAnswers_mem_iff extractFree free extractSchema EvidenceSort
      (pExtract world query) bindings).mp returned
  obtain ⟨ran, _⟩ :=
    (checkedPlanAnswersFromPattern_mem_iff extractFree free extractSchema plan
      (pExtract world query) bindings).mp planReturned
  have matched : bindings ∈ matchPattern extractSchema (pExtract world query) := by
    rw [← run_compilePattern? extractSchema (pExtract world query) plan compiled]
    exact ran
  refine ⟨⟨sigma, computed, supported, ?_⟩⟩
  have sourceNamed : namedErase (names extractEntries) extractFragment =
      extractSchema := rfl
  have matchedNamed : bindings ∈ matchPattern
      (namedErase (names extractEntries) extractFragment) (pExtract world query) := by
    rw [sourceNamed]
    exact matched
  rw [← matchPattern_namedErase_correct (names extractEntries) extractFragment
    (pExtract world query) bindings matchedNamed]
  exact (applyBindings_namedErase_eq_namedErase_substitute
    (names extractEntries) (names (targetEntries free bindings))
    bindings sigma supported variableReceipt extractFragment).symm

namespace CheckedExtract

variable {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}

/-- Every receipt over the same actual decoder input retains exactly the
same substitution. The support certificate is not a second choice of images. -/
theorem sigma_unique (first second : CheckedExtract entries bindings world query) :
    first.sigma = second.sigma :=
  Option.some.inj (first.computed.symm.trans second.computed)

def worldValue {State Query Ev Ov Scope : Type}
    (receipt : CheckedExtract entries bindings world query)
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)) : State :=
  FirstOrder.denote reading environment (receipt.supported _ .zero)

def queryValue {State Query Ev Ov Scope : Type}
    (receipt : CheckedExtract entries bindings world query)
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)) : Query :=
  FirstOrder.denote reading environment (receipt.supported _ (.succ .zero))

/-- The same captured state/query pair interprets the computed target. -/
theorem target_denotes {State Query Ev Ov Scope : Type}
    (receipt : CheckedExtract entries bindings world query)
    (reading : CombinedReading State Query Ev Ov Scope)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)) :
    FirstOrder.denote reading environment
        (FirstOrder.substitute receipt.sigma receipt.supported extractFragment) =
      reading.core.extract (receipt.worldValue reading environment)
        (receipt.queryValue reading environment) := rfl

end CheckedExtract

/-- An actual guarded engine occurrence and its computed intrinsic answer.
Occurrence identity is data; its admission and semantic correctness are proofs. -/
structure ExecutedAnswer {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries))
    (scopeHandle : Pattern) (scope : Scope) (answer : Ev) where
  scopeDecoded : lookupHandle provider.handles.scopes scopeHandle = some scope
  queryDecoded : lookupHandle provider.handles.queries query =
    some (receipt.queryValue reading environment)
  occurrence : RewriteOccurrence
  admitted : occurrence ∈ rewriteAtOccurrences
    (engineBasePremises (relationEnv provider)) CombinedLang 1
    (pExtract (pForget scopeHandle world) query)
  rule : occurrence.ruleName = "WM_ForgetOutside_Guarded"
  target : occurrence.target = pExtract world query
  intrinsic : evidenceAnswerFamily reading
    (FirstOrder.substitute receipt.sigma receipt.supported extractFragment)
    answer environment
  capability : IntrinsicSupportedRequestReceipt reading
    (outsideCapability reading scope) (receipt.worldValue reading environment)
    (receipt.queryValue reading environment) answer

/-- The stored numbered engine occurrence inhabits the existing
proof-relevant judgment's operational GSLT. Its endpoints are the exact
authored source and target of the checked guarded rule. -/
def ExecutedAnswer.proofRelevantEvent
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment scopeHandle scope answer) :
    (system (engineBasePremises (relationEnv provider)) CombinedLang 1).Event :=
  acceptedEvent (engineBasePremises (relationEnv provider)) CombinedLang 1
    (pExtract (pForget scopeHandle world) query) (pExtract world query)
    execution.occurrence execution.admitted execution.target

@[simp] theorem ExecutedAnswer.proofRelevantEvent_occurrence
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment scopeHandle scope answer) :
    eventOccurrence (engineBasePremises (relationEnv provider)) CombinedLang 1
      execution.proofRelevantEvent = execution.occurrence := rfl

@[simp] theorem ExecutedAnswer.proofRelevantEvent_site
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment scopeHandle scope answer) :
    eventSite (engineBasePremises (relationEnv provider)) CombinedLang 1
      execution.proofRelevantEvent =
        (execution.occurrence.ruleIndex, "WM_ForgetOutside_Guarded",
          execution.occurrence.alternativeIndex) := by
  rw [eventSite, execution.proofRelevantEvent_occurrence, execution.rule]

/-- The checked event's site identifies an actual authored guarded rule and
the exact alternative returned at that rule, not merely a matching string. -/
theorem ExecutedAnswer.authoredRuleSelected
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment scopeHandle scope answer) :
    ∃ rule,
      CombinedLang.rewrites[execution.occurrence.ruleIndex]? = some rule ∧
      rule.name = "WM_ForgetOutside_Guarded" ∧
      (applyRuleUsing (engineBasePremises (relationEnv provider)) CombinedLang
        (rewriteAt (engineBasePremises (relationEnv provider)) CombinedLang 0)
        rule (pExtract (pForget scopeHandle world) query))[execution.occurrence.alternativeIndex]? =
          some (pExtract world query) := by
  obtain ⟨rule, selected, nameEq, alternative⟩ :=
    rewriteAtOccurrences_selected (engineBasePremises (relationEnv provider))
      CombinedLang 0 (pExtract (pForget scopeHandle world) query)
      execution.occurrence execution.admitted
  refine ⟨rule, selected, nameEq.symm.trans execution.rule, ?_⟩
  simpa only [execution.target] using alternative

/-- One checked premise yields the engine event and both dependent receipts
for the actual computed capture. The provider must decode the captured query. -/
theorem execute_checked_extract {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries))
    (scopeHandle : Pattern) (scope : Scope)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries query =
      some (receipt.queryValue reading environment))
    (success : [("q", query), ("W", world), ("S", scopeHandle)] ∈
      applyPremisesWithEnv (relationEnv provider) CombinedLang
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scopeHandle)]) :
    Nonempty (ExecutedAnswer reading provider receipt environment scopeHandle scope
      (reading.core.extract (receipt.worldValue reading environment)
        (receipt.queryValue reading environment))) := by
  obtain ⟨occurrence, admitted, target, rule⟩ :=
    checked_forget_named_occurrence (relationEnv provider)
      scopeHandle world query success
  have supported := checked_premise_supports reading provider CombinedLang
    scopeHandle world query scope (receipt.queryValue reading environment)
    (receipt.worldValue reading environment) scopeDecode queryDecode success
  exact ⟨⟨scopeDecode, queryDecode, occurrence, admitted, rule, target,
    ⟨receipt.target_denotes reading environment⟩,
    intrinsicReceipt_of_supported reading (outsideCapability reading scope)
      _ _ supported⟩⟩

/-- The whole admission-to-execution seam: an actual checked match first
fixes the intrinsic capture. At every model environment, successful checked
guard evaluation for its decoded query then yields the supported engine event.
No environment inhabitance is needed to compute the capture. -/
theorem checkedOpenAnswers_execute
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    (free : FreeTypeContext) (bindings : Bindings) (world query : Pattern)
    (returned : bindings ∈ checkedOpenAnswers extractFree free extractSchema
      EvidenceSort (pExtract world query)) :
    ∃ receipt : CheckedExtract (targetEntries free bindings) bindings world query,
      ∀ environment : Environment (State := State) (Query := Query)
          (Ev := Ev) (Ov := Ov) (Scope := Scope)
          (contextSorts (targetEntries free bindings)),
        ∀ (scopeHandle : Pattern) (scope : Scope),
          lookupHandle provider.handles.scopes scopeHandle = some scope →
          lookupHandle provider.handles.queries query =
            some (receipt.queryValue reading environment) →
          [("q", query), ("W", world), ("S", scopeHandle)] ∈
            applyPremisesWithEnv (relationEnv provider) CombinedLang
              ruleForgetOutsideGuarded.premises
              [("q", query), ("W", world), ("S", scopeHandle)] →
          Nonempty (ExecutedAnswer reading provider receipt environment scopeHandle scope
            (reading.core.extract (receipt.worldValue reading environment)
              (receipt.queryValue reading environment))) := by
  obtain ⟨receipt⟩ := checkedExtract_of_answers free bindings world query returned
  exact ⟨receipt, fun environment scopeHandle scope scopeDecode queryDecode success =>
    execute_checked_extract reading provider receipt environment
      scopeHandle scope scopeDecode queryDecode success⟩

/-- A dependent client consumes the retained equality; it neither repeats
the matcher nor asks the outside-scope provider a second time. -/
def consume {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment scopeHandle scope answer)
    (family : Ev → Type)
    (value : family (reading.core.extract (receipt.worldValue reading environment)
      (receipt.queryValue reading environment))) : family answer :=
  execution.capability.checked.checked ▸ value

/-- Use the existing CwF's context extension by the execution family. This
is a semantic dependent term consuming a checked answer, not a newly authored
syntax former. The execution witness remains in the extended context. -/
def consumeTerm {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries))
    (scopeHandle : Pattern) (scope : Scope)
    (family : Ev → Type)
    (value : family (reading.core.extract (receipt.worldValue reading environment)
      (receipt.queryValue reading environment))) :
    familiesCwF.Tm (mode := stageOfNat 0)
      (familiesCwF.ext Ev
        (ExecutedAnswer reading provider receipt environment scopeHandle scope))
      (fun answerAndExecution => family answerAndExecution.1) :=
  fun answerAndExecution => consume answerAndExecution.2 family value

/-- The retained support also checks the answer before the guarded
forgetting step, so the receipt concerns both sides of that engine event. -/
theorem source_answer {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment scopeHandle scope answer) :
    reading.core.extract (reading.forget scope (receipt.worldValue reading environment))
      (receipt.queryValue reading environment) = answer :=
  (reading.forgetOutside execution.capability.supported).trans
    execution.capability.checked.checked

/-- A checked execution can be reused at another model environment when
the computed captured world and query still denote the same request. The
original numbered occurrence is retained; neither matching nor guard
evaluation is repeated. This is deliberately not arbitrary state change. -/
def ExecutedAnswer.transport_same_request
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {firstEnvironment secondEnvironment : Environment (State := State)
      (Query := Query) (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (sameWorld : receipt.worldValue reading firstEnvironment =
      receipt.worldValue reading secondEnvironment)
    (sameQuery : receipt.queryValue reading firstEnvironment =
      receipt.queryValue reading secondEnvironment)
    (execution : ExecutedAnswer reading provider receipt firstEnvironment
      scopeHandle scope answer) :
    ExecutedAnswer reading provider receipt secondEnvironment
      scopeHandle scope answer := by
  have sameAnswer :
      reading.core.extract (receipt.worldValue reading secondEnvironment)
        (receipt.queryValue reading secondEnvironment) = answer := by
    rw [← sameWorld, ← sameQuery]
    exact execution.capability.checked.checked
  have supported :
      (outsideCapability reading scope).supports
        (receipt.worldValue reading secondEnvironment)
        (receipt.queryValue reading secondEnvironment) := by
    rw [← sameWorld, ← sameQuery]
    exact execution.capability.supported
  refine {
    scopeDecoded := execution.scopeDecoded
    queryDecoded := ?_
    occurrence := execution.occurrence
    admitted := execution.admitted
    rule := execution.rule
    target := execution.target
    intrinsic := ⟨(receipt.target_denotes reading secondEnvironment).trans sameAnswer⟩
    capability := ⟨supported, ⟨sameAnswer⟩⟩
  }
  rw [← sameQuery]
  exact execution.queryDecoded

@[simp] theorem ExecutedAnswer.transport_same_request_occurrence
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {firstEnvironment secondEnvironment : Environment (State := State)
      (Query := Query) (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (sameWorld : receipt.worldValue reading firstEnvironment =
      receipt.worldValue reading secondEnvironment)
    (sameQuery : receipt.queryValue reading firstEnvironment =
      receipt.queryValue reading secondEnvironment)
    (execution : ExecutedAnswer reading provider receipt firstEnvironment
      scopeHandle scope answer) :
    (execution.transport_same_request sameWorld sameQuery).occurrence =
      execution.occurrence := rfl

@[simp] theorem ExecutedAnswer.transport_same_request_event
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {firstEnvironment secondEnvironment : Environment (State := State)
      (Query := Query) (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (sameWorld : receipt.worldValue reading firstEnvironment =
      receipt.worldValue reading secondEnvironment)
    (sameQuery : receipt.queryValue reading firstEnvironment =
      receipt.queryValue reading secondEnvironment)
    (execution : ExecutedAnswer reading provider receipt firstEnvironment
      scopeHandle scope answer) :
    (execution.transport_same_request sameWorld sameQuery).proofRelevantEvent =
      execution.proofRelevantEvent := rfl

/-- At fixed checked request and answer, the occurrence is the only
proof-relevant datum in an execution receipt. Its other fields certify
admission, support, and exactness for that occurrence. -/
theorem ExecutedAnswer.ext_occurrence
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (first second : ExecutedAnswer reading provider receipt environment
      scopeHandle scope answer)
    (same : first.occurrence = second.occurrence) : first = second := by
  cases first
  cases second
  cases same
  congr
  · dsimp only [evidenceAnswerFamily]
    exact Subsingleton.elim _ _
  · have unique : Subsingleton
        (IntrinsicSupportedRequestReceipt reading
          (outsideCapability reading scope)
          (receipt.worldValue reading environment)
          (receipt.queryValue reading environment) answer) :=
        ⟨by
          rintro ⟨_, ⟨_⟩⟩ ⟨_, ⟨_⟩⟩
          rfl⟩
    exact unique.elim _ _

/-- Reusing a checked execution at its current request is the identity. -/
theorem ExecutedAnswer.transport_same_request_id
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (execution : ExecutedAnswer reading provider receipt environment
      scopeHandle scope answer) :
    execution.transport_same_request rfl rfl = execution := by
  apply ExecutedAnswer.ext_occurrence
  rfl

/-- Two equal-request environment changes transport one retained event
exactly as their composite; no intermediate guard or matcher runs. -/
theorem ExecutedAnswer.transport_same_request_comp
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {firstEnvironment middleEnvironment lastEnvironment : Environment
      (State := State) (Query := Query) (Ev := Ev) (Ov := Ov) (Scope := Scope)
      (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {answer : Ev}
    (firstWorld : receipt.worldValue reading firstEnvironment =
      receipt.worldValue reading middleEnvironment)
    (firstQuery : receipt.queryValue reading firstEnvironment =
      receipt.queryValue reading middleEnvironment)
    (secondWorld : receipt.worldValue reading middleEnvironment =
      receipt.worldValue reading lastEnvironment)
    (secondQuery : receipt.queryValue reading middleEnvironment =
      receipt.queryValue reading lastEnvironment)
    (execution : ExecutedAnswer reading provider receipt firstEnvironment
      scopeHandle scope answer) :
    (execution.transport_same_request firstWorld firstQuery).transport_same_request
        secondWorld secondQuery =
      execution.transport_same_request (firstWorld.trans secondWorld)
        (firstQuery.trans secondQuery) := by
  apply ExecutedAnswer.ext_occurrence
  rfl

/-! ## A counted, compound capture and its dependent consumer -/

namespace CountedExample

def free : FreeTypeContext :=
  fun variableName => if variableName == "a" || variableName == "b" then some (.base "State")
    else if variableName == "q2" then some (.base "Query") else none

def world : Pattern := pRevise (.fvar "a") (.fvar "b")
def query : Pattern := .fvar "q2"
def bindings : Bindings := [("q", query), ("W", world)]

theorem match_accepted : bindings ∈
    checkedOpenAnswers extractFree free extractSchema EvidenceSort
      (pExtract world query) := by
  unfold checkedOpenAnswers checkedPlanAnswersFromPattern
  rw [extractEntries_fromUsed]
  cbv
  exact List.Mem.head _

def entries : List (String × TypeExpr) :=
  [("a", .base "State"), ("b", .base "State"), ("q2", .base "Query")]

theorem entries_computed : targetEntries free bindings = entries := by cbv

/-- This is the same constructor-tree substitution computed by the generic
codec, not a separately chosen semantic assignment. -/
def capture : CheckedExtract entries bindings world query where
  sigma := by
    intro sort position
    cases position with
    | zero => exact revise (.var .zero) (.var (.succ .zero))
    | succ earlier =>
        cases earlier with
        | zero => exact .var (.succ (.succ .zero))
        | succ impossible => cases impossible
  computed := by
    cbv
    congr 1
    funext sort position
    cases position with
    | zero => rfl
    | succ earlier =>
        cases earlier with
        | zero => rfl
        | succ impossible => cases impossible
  supported := fun _ position => by
    cases position with
    | zero => exact .revise (.variable .zero) (.variable (.succ .zero))
    | succ earlier =>
        cases earlier with
        | zero => exact .variable (.succ (.succ .zero))
        | succ impossible => cases impossible
  targetNamed := by rfl

def environment (queryValue : String) :
    Environment (State := CountState) (Query := String) (Ev := Nat)
      (Ov := Nat) (Scope := CountScope)
      (contextSorts entries) := by
  intro sort position
  cases position with
  | zero => exact countingCore.world "y"
  | succ earlier =>
      cases earlier with
      | zero => exact countingCore.world "y"
      | succ earlier =>
          cases earlier with
          | zero => exact queryValue
          | succ impossible => cases impossible

/-- The same revised world can be represented by putting both counted
atoms in the first captured state and none in the second. -/
def repartitionedEnvironment (queryValue : String) :
    Environment (State := CountState) (Query := String) (Ev := Nat)
      (Ov := Nat) (Scope := CountScope)
      (contextSorts entries) := by
  intro sort position
  cases position with
  | zero => exact countingCore.revise (countingCore.world "y") (countingCore.world "y")
  | succ earlier =>
      cases earlier with
      | zero => exact fun _ => 0
      | succ earlier =>
          cases earlier with
          | zero => exact queryValue
          | succ impossible => cases impossible

theorem repartitioned_same_world (queryValue : String) :
    capture.worldValue countingCombined (environment queryValue) =
      capture.worldValue countingCombined
        (repartitionedEnvironment queryValue) := by
  funext queried
  rfl

theorem repartitioned_same_query (queryValue : String) :
    capture.queryValue countingCombined (environment queryValue) =
      capture.queryValue countingCombined
        (repartitionedEnvironment queryValue) := rfl

/-- The transport is not merely across two names for the same complete
environment: its first state component really changes. -/
theorem repartitioned_environment_ne :
    environment "y" ≠ repartitionedEnvironment "y" := by
  intro equal
  have atFirst := congrArg
    (fun env : Environment (State := CountState) (Query := String)
      (Ev := Nat) (Ov := Nat) (Scope := CountScope)
      (contextSorts entries) =>
        env (.base "State") (.zero) "y") equal
  norm_num [environment, repartitionedEnvironment, countingCore] at atFirst

def scopeHandle : Pattern := .fvar "scope"

def provider (queryValue : String) :
    CheckedProvider CountScope String countingCombined.inScope :=
  Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider.checkedProvider
    { scopes := [(scopeHandle, singletonX)]
      queries := [(query, queryValue)] }

theorem outside_premise : [("q", query), ("W", world), ("S", scopeHandle)] ∈
    applyPremisesWithEnv (relationEnv (provider "y")) CombinedLang
      ruleForgetOutsideGuarded.premises
      [("q", query), ("W", world), ("S", scopeHandle)] := by
  decide +kernel

/-- A genuine guarded rewrite, not a zero-step witness, supplies the count
of both captured worlds and retains its actual engine occurrence. -/
theorem counted_execution :
    Nonempty (ExecutedAnswer countingCombined (provider "y") capture
      (environment "y") scopeHandle singletonX 2) := by
  exact execute_checked_extract countingCombined (provider "y") capture
    (environment "y") scopeHandle singletonX rfl rfl outside_premise

/-- A genuinely different distribution of captured state counts reuses
the already checked guarded event at its unchanged observed request. -/
theorem repartitioned_execution :
    Nonempty (ExecutedAnswer countingCombined (provider "y") capture
      (repartitionedEnvironment "y") scopeHandle singletonX 2) := by
  obtain ⟨execution⟩ := counted_execution
  exact ⟨execution.transport_same_request
    (repartitioned_same_world "y") (repartitioned_same_query "y")⟩

/-- The compound checked capture yields an actual operational GSLT step,
while `counted_execution` still carries its intrinsic and guarded answer. -/
theorem counted_operational_step :
    (system (engineBasePremises (relationEnv (provider "y"))) CombinedLang 1).theory.Step
      (.query (pExtract (pForget scopeHandle world) query))
      (.answer (pExtract (pForget scopeHandle world) query)
        (pExtract world query)) := by
  obtain ⟨execution⟩ := counted_execution
  exact (system (engineBasePremises (relationEnv (provider "y"))) CombinedLang 1).steps.erase
    execution.proofRelevantEvent.evidence

theorem wrong_answer_rejected :
    ¬ Nonempty (ExecutedAnswer countingCombined (provider "y") capture
      (environment "y") scopeHandle singletonX 1) := by
  rintro ⟨execution⟩
  have wrong : (2 : Nat) = 1 := execution.intrinsic.checked
  omega

theorem inside_premise_rejected :
    applyPremisesWithEnv (relationEnv (provider "x")) CombinedLang
      ruleForgetOutsideGuarded.premises
      [("q", query), ("W", world), ("S", scopeHandle)] = [] := by
  decide +kernel

theorem unsupported_execution_rejected (answer : Nat) :
    ¬ Nonempty (ExecutedAnswer countingCombined (provider "x") capture
      (environment "x") scopeHandle singletonX answer) := by
  rintro ⟨execution⟩
  apply execution.capability.supported
  change singletonX "x"
  decide +kernel

/-- Reusing a provider row for a different semantic query does not meet
the decoding contract, even though its raw handle is unchanged. -/
theorem stale_query_decode_rejected :
    lookupHandle (provider "y").handles.queries query ≠
      some (capture.queryValue countingCombined (environment "x")) := by
  decide +kernel

/-- Both semantic queries are outside the scope, but support alone does
not authorize replaying a receipt decoded for a different query. -/
theorem stale_supported_execution_rejected (answer : Nat) :
    ¬ Nonempty (ExecutedAnswer countingCombined (provider "y") capture
      (environment "z") scopeHandle singletonX answer) := by
  rintro ⟨execution⟩
  have different : (some "y" : Option String) ≠ some "z" := by decide +kernel
  exact different execution.queryDecoded

theorem stale_queries_both_supported :
    ¬ singletonX "y" ∧ ¬ singletonX "z" := by decide +kernel

/-- This dependent result is indexed by the received count, not by a fixed
host length. The original occurrence is returned unchanged beside it. -/
def consumeCounted {answer : Nat}
    (execution : ExecutedAnswer countingCombined (provider "y") capture
      (environment "y") scopeHandle singletonX answer) :
    RewriteOccurrence × Fin (answer + 1) :=
  (execution.occurrence, consumeTerm countingCombined (provider "y") capture
    (environment "y") scopeHandle singletonX (fun count => Fin (count + 1))
    ⟨2, by decide +kernel⟩ ⟨answer, execution⟩)

theorem consumeCounted_retains_occurrence {answer : Nat}
    (execution : ExecutedAnswer countingCombined (provider "y") capture
      (environment "y") scopeHandle singletonX answer) :
    (consumeCounted execution).1 = execution.occurrence := rfl

theorem consumeCounted_value {answer : Nat}
    (execution : ExecutedAnswer countingCombined (provider "y") capture
      (environment "y") scopeHandle singletonX answer) :
    (consumeCounted execution).2.val = 2 := by
  have answerEq : (2 : Nat) = answer := execution.intrinsic.checked
  subst answer
  rfl

end CountedExample

#print axioms checkedExtract_of_answers
#print axioms execute_checked_extract
#print axioms checkedOpenAnswers_execute
#print axioms consume
#print axioms consumeTerm
#print axioms source_answer
#print axioms ExecutedAnswer.transport_same_request
#print axioms ExecutedAnswer.transport_same_request_event
#print axioms ExecutedAnswer.ext_occurrence
#print axioms ExecutedAnswer.transport_same_request_id
#print axioms ExecutedAnswer.transport_same_request_comp
#print axioms CountedExample.match_accepted
#print axioms CountedExample.counted_execution
#print axioms CountedExample.repartitioned_environment_ne
#print axioms CountedExample.repartitioned_execution
#print axioms CountedExample.counted_operational_step
#print axioms ExecutedAnswer.proofRelevantEvent_site
#print axioms ExecutedAnswer.authoredRuleSelected
#print axioms CountedExample.wrong_answer_rejected
#print axioms CountedExample.unsupported_execution_rejected
#print axioms CountedExample.stale_query_decode_rejected
#print axioms CountedExample.stale_supported_execution_rejected
#print axioms CountedExample.consumeCounted_value

end Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenScopeExecution
