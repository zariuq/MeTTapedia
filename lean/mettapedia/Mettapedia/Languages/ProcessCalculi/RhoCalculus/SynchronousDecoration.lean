import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousWrapping

/-!
# Synchronous rho communication on a decorated continuation bundle

The sent process and the output continuation occupy different declared
parameters of the same output. Decorating both, together with the input
body, types the actual communication redex and contractum. Restricting the
bundle to the two primary slots retains the established negative result.

These are generated sorting statements. No transport to the stronger Cost
iteration or activation contract is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The sent process is an additional continuation of the actual output,
separate from its primary continuation after sending. -/
def sentProcessSlot : ContinuationDecorationSlot rhoSyncInteractionCut.environment where
  position :=
    { index := 1
      inBounds := by decide
      hasInteractingResult := rfl }
  pattern := .fvar "q"
  schemaVariable := .plain "q"
  form := .introduced
    (by
      change RepresentedBy rhoSyncOutputRule
        (.apply "POutputK" [.fvar "n", .fvar "q", .fvar "k"])
      simp [RepresentedBy, UsesBareCollection, rhoSyncOutputRule])
    rfl

/-- The three payload variables are decorated. Constructors remain the
original finite declaration-derived hereditary closure. -/
def communicationDecoration : ContinuationDecorationProfile rhoSyncInteractionCut where
  environmentAdditional := [sentProcessSlot]
  constructorClosure := rhoSyncContinuationRetyping.wrappedConstructors

theorem communicationDecoration_variables :
    communicationDecoration.generatedFreeContext "p" = some (.base costWrappedSortName) ∧
      communicationDecoration.generatedFreeContext "q" = some (.base costWrappedSortName) ∧
      communicationDecoration.generatedFreeContext "k" = some (.base costWrappedSortName) := by
  decide +kernel

theorem communicationDecoration_output_parameters :
    (communicationDecoration.baseConstructor rhoSyncOutputRule).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .simple "q" (.base costWrappedSortName),
        .simple "k" (.base costWrappedSortName)] := by
  decide +kernel

theorem communicationDecoration_input_parameters :
    (communicationDecoration.baseConstructor rhoCalc.terms[5]).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .abstraction "p"
          (.arrow (.base (costBaseSortName "Name")) (.base costWrappedSortName))] := by
  decide +kernel

theorem communicationDecoration_parallel_parameters :
    (communicationDecoration.baseConstructor rhoCalc.terms[3]).params =
      [.simple "ps" (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  decide +kernel

/-- All three selected variables are accepted by their corresponding
authored constructor parameters in the exact communication redex. -/
theorem communicationDecoration_redexRetypable : communicationDecoration.RedexRetypable := by
  unfold ContinuationDecorationProfile.RedexRetypable
  change HasType communicationDecoration.generatedLanguage
    communicationDecoration.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "PInput") [.fvar "n", .lambda none (.fvar "p")],
        .apply (costBaseConstructorName "POutputK") [.fvar "n", .fvar "q", .fvar "k"]]
      (some "rest")) (.base (costBaseSortName "Proc"))
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
        exact .cons trivial rfl (HasType.fvar rfl)
          (.cons trivial rfl (HasType.lambda (HasType.fvar rfl)) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := communicationDecoration.baseConstructor rhoSyncOutputRule)
        · exact communicationDecoration.baseConstructor_mem _ rhoSyncOutputConstructor.2
        · simp [UsesBareCollection, communicationDecoration_output_parameters]
        · rw [communicationDecoration_output_parameters]
          exact .cons trivial rfl (HasType.fvar rfl)
            (.cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil))
      · exact .nil _ _

theorem communicationDecoration_contractum :
    communicationDecoration.mapContractum rhoSyncCommRewrite.right =
      .collection .hashBag
        [.subst (.fvar "p") (.apply (costWrappedConstructorName "NQuote") [.fvar "q"]),
          .fvar "k"] (some "rest") := by
  have quote : "NQuote" ∈ communicationDecoration.wrappedLabels := by decide +kernel
  simp only [rhoSyncCommRewrite, ContinuationDecorationProfile.mapContractum,
    mapPattern, mapPatternList_eq_map, ContinuationDecorationProfile.contractumSymbols,
    quote, if_true, List.map_cons, List.map_nil]

/-- Quotation of the decorated sent process and substitution into the
decorated input body preserve the wrapped sort; the output continuation is
released as another wrapped component. -/
theorem communicationDecoration_wrappable : communicationDecoration.Wrappable := by
  unfold ContinuationDecorationProfile.Wrappable
  change HasType communicationDecoration.generatedLanguage
    communicationDecoration.generatedFreeContext []
    (communicationDecoration.mapContractum rhoSyncCommRewrite.right) (.base costWrappedSortName)
  rw [communicationDecoration_contractum]
  apply HasType.collectionConstructor
    (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[3])
    (parameterName := "ps") (elementType := .base costWrappedSortName)
  · exact communicationDecoration.wrappedConstructor_mem rhoSyncParallelConstructor
      (mem_continuationConstructors_of_label_ne rhoSyncInteractionCut rhoSyncParallelConstructor
        (by decide) (by decide))
  · rfl
  · apply ElementsHaveType.cons
    · apply HasType.subst (domain := .base (costBaseSortName "Name"))
      · exact HasType.fvar rfl
      · apply HasType.constructor
          (rule := costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2])
        · exact communicationDecoration.wrappedConstructor_mem rhoSyncQuoteConstructor
            (mem_continuationConstructors_of_label_ne rhoSyncInteractionCut rhoSyncQuoteConstructor
              (by decide) (by decide))
        · simp [UsesBareCollection, rhoSync_costWrappedQuote_params]
        · rw [rhoSync_costWrappedQuote_params]
          exact .cons trivial rfl (HasType.fvar rfl) .nil
    · exact .cons (HasType.fvar rfl) (.nil _ _)

/-- The finite-bundle repair adds genuine expressive power while leaving
the two-slot result valid for its original profile. -/
theorem decoration_separates_two_slots :
    communicationDecoration.RedexRetypable ∧ communicationDecoration.Wrappable ∧
      ¬ (ContinuationDecorationProfile.ofRetypingPlan
        rhoSyncContinuationRetyping).Wrappable :=
  ⟨communicationDecoration_redexRetypable, communicationDecoration_wrappable,
    fun legacy => rhoSync_not_wrappable rhoSyncInteractionCut rhoSyncContinuationRetyping
      ((ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mp legacy)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
