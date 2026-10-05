import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationValidation
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousDecoration

/-!
# Synchronous rho finite-continuation and binder controls

The existing three-payload decoration validates, and its redex and instantiated
contractum accept arbitrary well-typed payloads in their actual local contexts.
The input body lives below one extra name binder; the sent process and the
output continuation live in the ambient context.  Concrete controls exercise
both the consumed binder and an ambient name that survives its elimination.

These are signature, sorting, and substitution results.  They do not assert
that the generated funded interaction or its operational adequacy is built.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

theorem communicationDecoration_validate :
    communicationDecoration.generatedLanguage.validate = [] :=
  communicationDecoration.generatedLanguage_validate rhoSyncContinuationRetyping.noDuplicates

/-- The two-slot signature validates too; validation alone cannot supply the
missing sent-process continuation or make its contractum wrappable. -/
theorem legacySignature_valid_but_not_wrappable :
    (ContinuationDecorationProfile.ofRetypingPlan
      rhoSyncContinuationRetyping).generatedLanguage.validate = [] ∧
    ¬ (ContinuationDecorationProfile.ofRetypingPlan rhoSyncContinuationRetyping).Wrappable :=
  ⟨ContinuationDecorationProfile.generatedLanguage_validate
      (ContinuationDecorationProfile.ofRetypingPlan rhoSyncContinuationRetyping)
      rhoSyncContinuationRetyping.noDuplicates,
    decoration_separates_two_slots.2.2⟩

/-- The exact three-payload redex, after filling its named schema parameters. -/
def decoratedRedex (channel body sent after : Pattern) : Pattern :=
  .collection .hashBag
    [.apply (costBaseConstructorName "PInput") [channel, .lambda none body],
      .apply (costBaseConstructorName "POutputK") [channel, sent, after]] none

theorem decoratedRedex_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {channel body sent after : Pattern}
    (channelTyped : HasType communicationDecoration.generatedLanguage free bound
      channel (.base (costBaseSortName "Name")))
    (bodyTyped : HasType communicationDecoration.generatedLanguage free
      (.base (costBaseSortName "Name") :: bound) body (.base costWrappedSortName))
    (sentTyped : HasType communicationDecoration.generatedLanguage free bound
      sent (.base costWrappedSortName))
    (afterTyped : HasType communicationDecoration.generatedLanguage free bound
      after (.base costWrappedSortName)) :
    HasType communicationDecoration.generatedLanguage free bound
      (decoratedRedex channel body sent after) (.base (costBaseSortName "Proc")) := by
  apply HasType.collectionConstructor
    (rule := communicationDecoration.baseConstructor rhoCalc.terms[3])
    (parameterName := "ps") (elementType := .base (costBaseSortName "Proc"))
  · exact communicationDecoration.baseConstructor_mem _ rhoSyncParallelConstructor.2
  · exact communicationDecoration_parallel_parameters
  · apply ElementsHaveType.cons
    · apply HasType.constructor
        (rule := communicationDecoration.baseConstructor rhoCalc.terms[5])
      · exact communicationDecoration.baseConstructor_mem _ rhoSyncInputConstructor.2
      · simp [UsesBareCollection, communicationDecoration_input_parameters]
      · rw [communicationDecoration_input_parameters]
        exact .cons trivial rfl channelTyped
          (.cons trivial rfl (HasType.lambda bodyTyped) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := communicationDecoration.baseConstructor rhoSyncOutputRule)
        · exact communicationDecoration.baseConstructor_mem _ rhoSyncOutputConstructor.2
        · simp [UsesBareCollection, communicationDecoration_output_parameters]
        · rw [communicationDecoration_output_parameters]
          exact .cons trivial rfl channelTyped
            (.cons trivial rfl sentTyped (.cons trivial rfl afterTyped .nil))
      · exact .nil _ _

theorem decoratedQuote_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {sent : Pattern}
    (sentTyped : HasType communicationDecoration.generatedLanguage free bound
      sent (.base costWrappedSortName)) :
    HasType communicationDecoration.generatedLanguage free bound
      (.apply (costWrappedConstructorName "NQuote") [sent])
      (.base (costBaseSortName "Name")) := by
  apply HasType.constructor
    (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2])
  · exact communicationDecoration.wrappedConstructor_mem rhoSyncQuoteConstructor
      (mem_continuationConstructors_of_label_ne rhoSyncInteractionCut rhoSyncQuoteConstructor
        (by decide) (by decide))
  · simp [UsesBareCollection, rhoSync_costWrappedQuote_params]
  · rw [rhoSync_costWrappedQuote_params]
    exact .cons trivial rfl sentTyped .nil

/-- The actual substitution eliminates the input-local name binder. -/
def instantiatedContractum (body sent after : Pattern) : Pattern :=
  .collection .hashBag
    [instantiateBVar (.apply (costWrappedConstructorName "NQuote") [sent]) body,
      after] none

theorem instantiatedContractum_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {body sent after : Pattern}
    (bodyTyped : HasType communicationDecoration.generatedLanguage free
      (.base (costBaseSortName "Name") :: bound) body (.base costWrappedSortName))
    (sentTyped : HasType communicationDecoration.generatedLanguage free bound
      sent (.base costWrappedSortName))
    (afterTyped : HasType communicationDecoration.generatedLanguage free bound
      after (.base costWrappedSortName)) :
    HasType communicationDecoration.generatedLanguage free bound
      (instantiatedContractum body sent after) (.base costWrappedSortName) := by
  apply HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[3])
    (parameterName := "ps") (elementType := .base costWrappedSortName)
  · exact communicationDecoration.wrappedConstructor_mem rhoSyncParallelConstructor
      (mem_continuationConstructors_of_label_ne rhoSyncInteractionCut rhoSyncParallelConstructor
        (by decide) (by decide))
  · rfl
  · exact .cons (bodyTyped.instantiateBVar (decoratedQuote_typed sentTyped))
      (.cons afterTyped (.nil _ _))

namespace FiniteContinuationControls

def zero : Pattern := .apply (costWrappedConstructorName "PZero") []
def localBody : Pattern := .apply (costWrappedConstructorName "PDrop") [.bvar 0]
def ambientBody : Pattern := .apply (costWrappedConstructorName "PDrop") [.bvar 1]

theorem zero_typed : HasType communicationDecoration.generatedLanguage
    FreeTypeContext.empty [] zero (.base costWrappedSortName) :=
  checkHasType_sound (by decide +kernel)

theorem localBody_typed : HasType communicationDecoration.generatedLanguage
    FreeTypeContext.empty [.base (costBaseSortName "Name")]
    localBody (.base costWrappedSortName) :=
  checkHasType_sound (by decide +kernel)

theorem ambientBody_typed : HasType communicationDecoration.generatedLanguage
    FreeTypeContext.empty
    [.base (costBaseSortName "Name"), .base (costBaseSortName "Name")]
    ambientBody (.base costWrappedSortName) :=
  checkHasType_sound (by decide +kernel)

/-- A closed positive witness has all three payloads, with the input payload
admitted in its own one-name context. -/
theorem actual_redex_typed : HasType communicationDecoration.generatedLanguage
    FreeTypeContext.empty []
    (decoratedRedex (.apply (costWrappedConstructorName "NQuote") [zero])
      localBody zero zero) (.base (costBaseSortName "Proc")) :=
  decoratedRedex_typed (decoratedQuote_typed zero_typed) localBody_typed zero_typed zero_typed

theorem actual_contractum_typed : HasType communicationDecoration.generatedLanguage
    FreeTypeContext.empty [] (instantiatedContractum localBody zero zero)
    (.base costWrappedSortName) :=
  instantiatedContractum_typed localBody_typed zero_typed zero_typed

/-- The consumed local name receives the quote; an ambient name is merely
reindexed and remains available after the local binder is consumed. -/
theorem local_and_ambient_activation :
    instantiateBVar (.apply (costWrappedConstructorName "NQuote") [zero]) localBody =
      .apply (costWrappedConstructorName "PDrop")
        [.apply (costWrappedConstructorName "NQuote") [zero]] ∧
    instantiateBVar (.apply (costWrappedConstructorName "NQuote") [zero]) ambientBody =
      localBody := by
  decide +kernel

/-- A continuation admitted below the input binder is not automatically an
admitted sent process in the empty ambient context. -/
theorem localBody_not_closed : ¬ HasType communicationDecoration.generatedLanguage
    FreeTypeContext.empty [] localBody (.base costWrappedSortName) := by
  intro typed
  have inScope := typed.isWellScopedAt
  simp [localBody, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] at inScope

end FiniteContinuationControls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
