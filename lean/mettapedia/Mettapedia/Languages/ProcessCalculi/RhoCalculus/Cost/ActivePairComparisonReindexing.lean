import Mettapedia.GSLT.LanguageDef.ScopedComparisonReindexing
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivePairCanonicalExecution

/-!
# Context reindexing of the actual repeated COMM channel

The source-selected comparator survives every bounded ambient reindexing.
The actual matcher retains the reindexed receiver's raw spelling, while the
body's local input binder remains fixed. The generated signature comparison
and purse-head equality remain literal.

Controls distinguish ordinarily scoped open quotations from sealed literal
names. The nonempty-spine controls exercise the generic contextual-value
interface; the authored COMM channel itself has an empty dependency spine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairComparisonReindexing

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ScopedComparisonReindexing
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ReflectiveCanonical ScopedReflectiveComparison
open ActivePair (rule bindingSpec language pairAssignment)
open ActivePairCanonicalExecution (profile fundedPairChannels)
open ActivePairNameComparison (declaration)

private theorem selected_distinct (selectedDeclaration : ReflectivePresentationDecl)
    (selected : ReflectiveSubstitution.matchingPresentationForRule? profile rule =
      some selectedDeclaration) :
    selectedDeclaration.quoteConstructor ≠ selectedDeclaration.dropConstructor := by
  have same : selectedDeclaration = declaration :=
    Option.some.inj (selected.symm.trans ActivePairNameComparison.declaration_selected)
  subst selectedDeclaration
  decide +kernel

/-- This is the actual source-selected Name check, not an independently
chosen canonical declaration. -/
theorem channel_comparison_rename (rename : Nat → Nat) (depth : Nat)
    {receiver sender : Pattern}
    (accepted : bodyComparison profile rule (costSourceSchemaName "n") receiver sender = true) :
    bodyComparison profile rule (costSourceSchemaName "n")
      (ContextSubstitution.renameAmbientBVarsAt rename depth receiver)
      (ContextSubstitution.renameAmbientBVarsAt rename depth sender) = true :=
  bodyComparison_rename profile rule selected_distinct _ rename depth accepted

/-- Any well-defined ambient index map preserves the actual funded pair's
successful match. Reindexing under the body fixes its local input binder. -/
theorem scoped_match_pair_reindex (source target : List TypeExpr) (rename : Nat → Nat)
    (bounded : ∀ index, index < source.length → rename index < target.length)
    (receiver sender body sent after signature tail : Pattern)
    (accepted : bodyComparison profile rule (costSourceSchemaName "n") receiver sender = true)
    (receiverScoped : receiver.isWellScopedAt source.length = true)
    (senderScoped : sender.isWellScopedAt source.length = true)
    (bodyScoped : body.isWellScopedAt (1 + source.length) = true)
    (sentScoped : sent.isWellScopedAt source.length = true)
    (afterScoped : after.isWellScopedAt source.length = true)
    (signatureScoped : signature.isWellScopedAt source.length = true)
    (tailScoped : tail.isWellScopedAt source.length = true) :
    ScopedRuleMatching.matchRuleWithAt (bodyComparison profile rule) rule bindingSpec target.length
      (fundedPairChannels
        (ContextSubstitution.renameAmbientBVarsAt rename 0 receiver)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 sender)
        (ContextSubstitution.renameAmbientBVarsAt rename 1 body)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 sent)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 after)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 signature)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 tail)) =
      [pairAssignment target
        (ContextSubstitution.renameAmbientBVarsAt rename 0 receiver)
        (ContextSubstitution.renameAmbientBVarsAt rename 1 body)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 sent)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 after)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 signature)
        (ContextSubstitution.renameAmbientBVarsAt rename 0 tail)] := by
  apply ActivePairCanonicalExecution.scoped_match_pair target
  · exact channel_comparison_rename rename 0 accepted
  · exact rename_wellScoped rename source.length target.length 0 bounded receiverScoped
  · exact rename_wellScoped rename source.length target.length 0 bounded senderScoped
  · simpa only [Nat.add_comm] using
      rename_wellScoped rename source.length target.length 1 bounded
        (by simpa only [Nat.add_comm] using bodyScoped)
  · exact rename_wellScoped rename source.length target.length 0 bounded sentScoped
  · exact rename_wellScoped rename source.length target.length 0 bounded afterScoped
  · exact rename_wellScoped rename source.length target.length 0 bounded signatureScoped
  · exact rename_wellScoped rename source.length target.length 0 bounded tailScoped

/-- A Name containing a receiver body under its own local binder. Its two
parameters denote ordinary ambient variables; it is intentionally not a
sealed literal quotation. -/
def openName (channel ambient : Nat) : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PInput")
      [.bvar channel, .lambda none
        (.apply (costWrappedConstructorName "PDrop") [.bvar (ambient + 1)])]]

def expandedOpenName (channel ambient : Nat) : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.collection .hashBag
      [FiniteWhole.baseZero,
       .apply (costBaseConstructorName "PInput")
         [.bvar channel, .lambda none
           (.apply (costWrappedConstructorName "PDrop") [.bvar (ambient + 1)])]] none]

def nameType : TypeExpr := .base (costBaseSortName "Name")

/-- Ordinary typing admits this open comparison input; literal quotation
sealing does not. No reflective admission is inferred from ordinary scope. -/
theorem open_names_typed_not_sealed :
    HasType language FreeTypeContext.empty [nameType, nameType] (openName 0 1) nameType ∧
    HasType language FreeTypeContext.empty [nameType, nameType] (expandedOpenName 0 1) nameType ∧
    ¬ ReflectiveWellSorted.ReflectiveScopeSafeAt profile 2 (openName 0 1) := by
  refine ⟨checkHasType_sound (by decide +kernel), checkHasType_sound (by decide +kernel), ?_⟩
  intro sealed
  have checked := sealed declaration (by decide +kernel)
  have rejected : ScopedPattern.binderSafeAt declaration.quoteConstructor 2 (openName 0 1) = false :=
    by decide +kernel
  rw [rejected] at checked
  contradiction

/-- Reindexing moves both ambient references while preserving the inner
binder and the source-selected canonical comparison. -/
theorem nested_open_reindex :
    ContextSubstitution.renameAmbientBVarsAt (fun index => index + 2) 0 (openName 0 1) =
      openName 2 3 ∧
    bodyComparison profile rule (costSourceSchemaName "n")
      (ContextSubstitution.renameAmbientBVarsAt (fun index => index + 2) 0 (openName 0 1))
      (ContextSubstitution.renameAmbientBVarsAt (fun index => index + 2) 0
        (expandedOpenName 0 1)) = true := by
  constructor
  · decide +kernel
  · exact channel_comparison_rename _ 0 (by decide +kernel)

def capturedName : ContextualValue := ⟨[nameType], 1, openName 0 1⟩
def capturedExpandedName : ContextualValue := ⟨[nameType], 1, expandedOpenName 0 1⟩

/-- The supported spine selects one of two local binders, keeps the ambient
variable separate, and recovers both raw bodies exactly. -/
theorem nonempty_spine_recovery :
    recoverValue? [nameType] 1 2 [.bvar 1] (openName 1 2) = some capturedName ∧
    recoverValue? [nameType] 1 2 [.bvar 1] (expandedOpenName 1 2) = some capturedExpandedName ∧
    capturedName.body ≠ capturedExpandedName.body ∧
    bodyComparison profile rule (costSourceSchemaName "n")
      capturedName.body capturedExpandedName.body = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact (bodyComparison_recover profile rule selected_distinct _ [nameType] 1 2 [.bvar 1]
    (left := openName 1 2) (right := expandedOpenName 1 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).2.2.2.2

/-- The same recovered values instantiate at a different nonempty spine;
comparison is preserved despite movement of both context segments. -/
theorem nonempty_spine_instantiation :
    instantiateValue? capturedName 1 3 [.bvar 2] = some (openName 2 3) ∧
    instantiateValue? capturedExpandedName 1 3 [.bvar 2] = some (expandedOpenName 2 3) ∧
    bodyComparison profile rule (costSourceSchemaName "n")
      (openName 2 3) (expandedOpenName 2 3) = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact bodyComparison_instantiate profile rule selected_distinct _ 1 3 [.bvar 2] [2]
    (by decide +kernel) (leftValue := capturedName) (rightValue := capturedExpandedName)
    rfl (by decide +kernel) (by decide +kernel) nonempty_spine_recovery.2.2.2

/-- A sealed quotation with a genuinely local Name occurrence beneath its
own receiver binder. -/
def nestedName : Pattern := .apply (costBaseConstructorName "NQuote")
  [.apply (costBaseConstructorName "PInput")
    [FiniteWhole.canonicalChannel, .lambda none FiniteWhole.localBody]]

def expandedNestedName : Pattern := .apply (costBaseConstructorName "NQuote")
  [.collection .hashBag [FiniteWhole.baseZero,
    .apply (costBaseConstructorName "PInput")
      [FiniteWhole.canonicalChannel, .lambda none FiniteWhole.localBody]] none]

private theorem profile_sealed_of_two (depth : Nat) (pattern : Pattern)
    (base : ScopedPattern.binderSafeAt declaration.quoteConstructor depth pattern = true)
    (wrapped : ScopedPattern.binderSafeAt
      ActivePairContextualReflection.declaration.quoteConstructor depth pattern = true) :
    ReflectiveWellSorted.ReflectiveScopeSafeAt profile depth pattern := by
  intro chosen member
  have presentations : profile.presentations =
      [declaration, ActivePairContextualReflection.declaration] := rfl
  rw [presentations] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact base
  · exact wrapped

/-- The nested quotation control lies in the actual reflective Name fibre,
and its two literal spellings remain different after context extension. -/
theorem nested_names_admitted :
    HasType language FreeTypeContext.empty [] nestedName nameType ∧
    HasType language FreeTypeContext.empty [] expandedNestedName nameType ∧
    ReflectiveWellSorted.ReflectiveScopeSafeAt profile 0 nestedName ∧
    ReflectiveWellSorted.ReflectiveScopeSafeAt profile 0 expandedNestedName ∧
    nestedName ≠ expandedNestedName ∧
    bodyComparison profile rule (costSourceSchemaName "n")
      (ContextSubstitution.renameAmbientBVarsAt (fun index => index + 2) 0 nestedName)
      (ContextSubstitution.renameAmbientBVarsAt (fun index => index + 2) 0 expandedNestedName) = true := by
  refine ⟨checkHasType_sound (by decide +kernel), checkHasType_sound (by decide +kernel),
    profile_sealed_of_two _ _ (by decide +kernel) (by decide +kernel),
    profile_sealed_of_two _ _ (by decide +kernel) (by decide +kernel),
    by decide +kernel, ?_⟩
  exact channel_comparison_rename _ 0 (by decide +kernel)

/-- Extending the actual ambient context moves the open channel from index
zero to index one; the input-local body variable remains index zero. -/
theorem open_channel_extension_match :
    ScopedRuleMatching.matchRuleWithAt (bodyComparison profile rule) rule bindingSpec 2
      (fundedPairChannels (.bvar 1) (.bvar 1) FiniteWhole.localBody
        ActivePairCanonicalExecution.closedPayload ActivePairCanonicalExecution.closedAfter
        FiniteWhole.unitSignature FiniteWhole.retainedTail) =
      [pairAssignment [.base costSignatureSortName, nameType] (.bvar 1)
        FiniteWhole.localBody ActivePairCanonicalExecution.closedPayload
        ActivePairCanonicalExecution.closedAfter FiniteWhole.unitSignature FiniteWhole.retainedTail] := by
  have matched := scoped_match_pair_reindex [nameType]
    [.base costSignatureSortName, nameType] (fun index => index + 1)
    (by intro index bound; simp only [List.length_cons, List.length_nil] at *; omega)
    (.bvar 0) (.bvar 0) FiniteWhole.localBody
    ActivePairCanonicalExecution.closedPayload ActivePairCanonicalExecution.closedAfter
    FiniteWhole.unitSignature FiniteWhole.retainedTail
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  convert matched using 1 <;> decide +kernel

/-- The reindexed open channel is also an admitted Name, and the actual
source-selected rule fires with typed source and residual. Its local body
activates the same nonempty payload retained before context extension. -/
theorem open_channel_extension_typed_firing :
    ReflectiveWellSorted.ReflectiveScopeSafeAt profile 2 (.bvar 1) ∧
    HasSort language FreeTypeContext.empty [.base costSignatureSortName, nameType]
      (fundedPairChannels (.bvar 1) (.bvar 1) FiniteWhole.localBody
        ActivePairCanonicalExecution.closedPayload ActivePairCanonicalExecution.closedAfter
        FiniteWhole.unitSignature FiniteWhole.retainedTail) costWrappedSortName ∧
    ScopedReflectiveExecution.applyRuleCanonicalAt profile Engine.RelationEnv.empty language 2 rule
      (fundedPairChannels (.bvar 1) (.bvar 1) FiniteWhole.localBody
        ActivePairCanonicalExecution.closedPayload ActivePairCanonicalExecution.closedAfter
        FiniteWhole.unitSignature FiniteWhole.retainedTail) =
      [ActivePairCanonicalExecution.closedTarget] ∧
    HasSort language FreeTypeContext.empty [.base costSignatureSortName, nameType]
      ActivePairCanonicalExecution.closedTarget costWrappedSortName := by
  refine ⟨profile_sealed_of_two _ _ (by decide +kernel) (by decide +kernel), ?_⟩
  exact ActivePairCanonicalExecution.canonical_typed_firing
    [.base costSignatureSortName, nameType] (.bvar 1) (.bvar 1)
    FiniteWhole.localBody ActivePairCanonicalExecution.closedPayload
    ActivePairCanonicalExecution.closedAfter FiniteWhole.unitSignature FiniteWhole.retainedTail
    (by decide +kernel)
    (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))
    (checkHasType_sound (by decide +kernel)) (by decide +kernel)
    (profile_sealed_of_two _ _ (by decide +kernel) (by decide +kernel))
    (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))
    (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))

def orderedOpenName : Pattern := .apply (costBaseConstructorName "NQuote")
  [.collection .hashBag [.bvar 0, .bvar 1] none]

def reverseFirstTwo (index : Nat) : Nat :=
  if index = 0 then 1 else if index = 1 then 0 else index

/-- Swapping two ambient variables reverses the selected parallel order.
Thus even an ordinary typed Name does not support literal normalizer
commutation. This input is not asserted to be a sealed quotation. -/
theorem literal_normalizer_commutation_fails :
    HasType language FreeTypeContext.empty
      [.base (costBaseSortName "Proc"), .base (costBaseSortName "Proc")]
      orderedOpenName nameType ∧
    canonicalize declaration
      (ContextSubstitution.renameAmbientBVarsAt reverseFirstTwo 0 orderedOpenName) ≠
      ContextSubstitution.renameAmbientBVarsAt reverseFirstTwo 0
        (canonicalize declaration orderedOpenName) := by
  refine ⟨checkHasType_sound (by decide +kernel), ?_⟩
  have normalized : canonicalize declaration orderedOpenName = orderedOpenName := by
    simp [orderedOpenName, declaration, canonicalize, canonicalizeList,
      normalizeParallelElements, parallelSplice, collapseParallel,
      PatternCode.sortPatterns, List.mergeSort, PatternCode.patternCode,
      ReflectiveSubstitution.finishNormalizeReflectiveApply,
      costBaseReflectivePresentationDecl, rhoReflectivePresentation, Nat.pair,
      ReflectionExtension.mapReflectivePresentation, costBaseStaticReflectiveSymbols]
  have reordered : canonicalize declaration
      (ContextSubstitution.renameAmbientBVarsAt reverseFirstTwo 0 orderedOpenName) =
      orderedOpenName := by
    simp [orderedOpenName, declaration, canonicalize, canonicalizeList,
      normalizeParallelElements, parallelSplice, collapseParallel,
      PatternCode.sortPatterns, List.mergeSort, PatternCode.patternCode,
      ReflectiveSubstitution.finishNormalizeReflectiveApply,
      costBaseReflectivePresentationDecl, rhoReflectivePresentation, Nat.pair,
      ReflectionExtension.mapReflectivePresentation, costBaseStaticReflectiveSymbols,
      ContextSubstitution.renameAmbientBVarsAt, reverseFirstTwo]
  rw [normalized, reordered]
  decide +kernel

/-- A noninjective map can create canonical equality. The generic law is
preservation; its converse would be false even for admitted open variables. -/
theorem noninjective_comparison_reflection_fails :
    bodyComparison profile rule (costSourceSchemaName "n") (.bvar 0) (.bvar 1) = false ∧
    bodyComparison profile rule (costSourceSchemaName "n")
      (ContextSubstitution.renameAmbientBVarsAt (fun _ => 0) 0 (.bvar 0))
      (ContextSubstitution.renameAmbientBVarsAt (fun _ => 0) 0 (.bvar 1)) = true := by
  decide +kernel

/-- Repeated local indices and term-valued arguments remain outside the
recoverable-spine interface; comparison does not relax these checks. -/
theorem unsupported_spines_rejected :
    variableSpine? 1 [.bvar 0, .bvar 0] = none ∧
    variableSpine? 1 [nestedName] = none := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.ActivePairComparisonReindexing
