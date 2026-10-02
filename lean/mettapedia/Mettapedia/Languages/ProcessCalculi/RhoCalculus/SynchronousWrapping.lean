import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
import Mettapedia.GSLT.LanguageDef.ContinuationSignatureInversion
import Mettapedia.GSLT.LanguageDef.Interaction.CollectionCutShape
import Mettapedia.GSLT.LanguageDef.Continued.CutShape

/-!
# The synchronous rho calculus is not wrappable

The communication cut of the synchronous rho calculus has a continuation
signature, and its redex stays sorted when the body of the input and the
process after the output are moved to the wrapped fibre.  Its contractum does
not: no cut of this calculus is wrappable.

The reason is a count.  A cut moves two schema variables to the wrapped
fibre, its two continuation variables.  The contractum of synchronous
communication needs three there: the body of the input, which becomes a
component of the residual composition; the process after the output, which
becomes another; and the sent process, which is quoted, and quotation in the
continuation signature takes a wrapped process.  The asynchronous calculus
needs only the first and the third, and the pi calculus, which substitutes
the carried name without quoting it, needs only the first two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## The communication cut: continuation signature and redex -/

/-- The contractum is headed by parallel composition, which is neither
introduction. -/
theorem rhoSyncContinuationRetyping : ContinuationRetypingPlan rhoSyncInteractionCut :=
  ⟨mem_continuationConstructors_of_label_ne rhoSyncInteractionCut rhoSyncParallelConstructor
    (by decide) (by decide)⟩

@[simp]
theorem rhoSync_costBaseParallel_params :
    (costBaseConstructor rhoSyncInteractionCut rhoCalc.terms[3]).params =
      [.simple "ps" (.collection .hashBag (.base (costBaseSortName "Proc")))] := by
  decide +kernel

@[simp]
theorem rhoSync_costBaseInput_params :
    (costBaseConstructor rhoSyncInteractionCut rhoCalc.terms[5]).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .abstraction "p"
          (.arrow (.base (costBaseSortName "Name")) (.base costWrappedSortName))] := by
  decide +kernel

@[simp]
theorem rhoSync_costBaseOutput_params :
    (costBaseConstructor rhoSyncInteractionCut rhoSyncOutputRule).params =
      [.simple "n" (.base (costBaseSortName "Name")),
        .simple "q" (.base (costBaseSortName "Proc")),
        .simple "k" (.base costWrappedSortName)] := by
  decide +kernel

/-- The redex stays sorted when the body of the input and the process after
the output are moved to the wrapped fibre. -/
theorem rhoSyncContinuationRetyping_redexRetypable :
    rhoSyncContinuationRetyping.RedexRetypable := by
  unfold ContinuationRetypingPlan.RedexRetypable
  change HasType rhoSyncContinuationRetyping.generatedLanguage
    rhoSyncContinuationRetyping.generatedFreeContext []
    (.collection .hashBag
      [.apply (costBaseConstructorName "PInput") [.fvar "n", .lambda none (.fvar "p")],
        .apply (costBaseConstructorName "POutputK") [.fvar "n", .fvar "q", .fvar "k"]]
      (some "rest"))
    (.base (costBaseSortName "Proc"))
  apply HasType.collectionConstructor
    (rule := costBaseConstructor rhoSyncInteractionCut rhoCalc.terms[3])
    (parameterName := "ps") (elementType := .base (costBaseSortName "Proc"))
  · exact rhoSyncContinuationRetyping.costBaseConstructor_mem_generated _
      rhoSyncParallelConstructor.2
  · exact rhoSync_costBaseParallel_params
  · apply ElementsHaveType.cons
    · apply HasType.constructor
        (rule := costBaseConstructor rhoSyncInteractionCut rhoCalc.terms[5])
      · exact rhoSyncContinuationRetyping.costBaseConstructor_mem_generated _
          rhoSyncInputConstructor.2
      · simp [UsesBareCollection, rhoSync_costBaseInput_params]
      · rw [rhoSync_costBaseInput_params]
        exact .cons trivial rfl (HasType.fvar rfl)
          (.cons trivial rfl (HasType.lambda (HasType.fvar rfl)) .nil)
    · apply ElementsHaveType.cons
      · apply HasType.constructor
          (rule := costBaseConstructor rhoSyncInteractionCut rhoSyncOutputRule)
        · exact rhoSyncContinuationRetyping.costBaseConstructor_mem_generated _
            rhoSyncOutputConstructor.2
        · simp [UsesBareCollection, rhoSync_costBaseOutput_params]
        · rw [rhoSync_costBaseOutput_params]
          exact .cons trivial rfl (HasType.fvar rfl)
            (.cons trivial rfl (HasType.fvar rfl) (.cons trivial rfl (HasType.fvar rfl) .nil))
      · exact .nil _ _

/-- With the process after the output as environment continuation, the sent
process keeps its base sort. -/
theorem rhoSync_datum_stays_base :
    rhoSyncContinuationRetyping.generatedFreeContext "q" =
        some (.base (costBaseSortName "Proc")) ∧
      rhoSyncContinuationRetyping.generatedFreeContext "k" =
        some (.base costWrappedSortName) ∧
      rhoSyncContinuationRetyping.generatedFreeContext "p" =
        some (.base costWrappedSortName) := by
  decide +kernel

/-! ## Every cut has the input and the output as its operands -/

/-- No constructor of the calculus has two plain parameters, so no core
contact is an ordered binary constructor. -/
theorem rhoSync_core_not_binary
    (contact : CoreContactPresentation rhoSyncValidatedLanguageDef) :
    contact.representation ≠ .binary := by
  intro binary
  have represents := contact.representsCore
  rw [binary] at represents
  obtain ⟨first, firstType, second, secondType, parameters⟩ :=
    params_of_coreContactRepresentation?_binary represents
  have membership : contact.constructor.1 ∈ rhoSyncCalc.terms := contact.constructor.2
  simp only [rhoSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with same | same | same | same | same | same <;>
    · rw [same] at parameters
      simp [rhoCalc, rhoSyncOutputRule] at parameters

/-- **The operands are forced.**  Whatever cut is given, its program
introduction is the input and its environment introduction is the output. -/
theorem rhoSync_cut_introductions (cut : InteractionCutPresentation rhoSyncIGSLT) :
    cut.program.constructor.1.label = "PInput" ∧
      cut.environment.constructor.1.label = "POutputK" := by
  have left : rhoSyncIGSLT.presentation.interactionRewrite.1.left =
      .collection .hashBag
        [.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
          .apply "POutputK" [.fvar "n", .fvar "q", .fvar "k"]] (some "rest") := rfl
  obtain ⟨program, environment⟩ := cut.operands_of_collection_left
    (rhoSync_core_not_binary cut.coreContact) left (by decide) (by decide)
  exact ⟨(cut.program.of_apply program).1, (cut.environment.of_apply environment).1⟩

/-! ## No cut is wrappable -/

/-- Quotation in the continuation signature takes a wrapped process. -/
theorem rhoSync_costWrappedQuote_params :
    (costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[2]).params =
      [.simple "p" (.base costWrappedSortName)] := by
  decide +kernel

/-- The wrapped copies of the constructors of the calculus, by parameters:
only parallel composition has a single collection parameter, and its elements
are wrapped. -/
theorem rhoSync_wrapped_collection_elementType
    {constructor : DeclaredConstructor rhoSyncValidatedLanguageDef}
    {parameterName : String} {collectionType : CollType} {elementType : TypeExpr}
    (parameters : (costWrappedConstructor (theory := rhoSyncIGSLT) constructor.1).params =
      [.simple parameterName (.collection collectionType elementType)]) :
    elementType = .base costWrappedSortName := by
  have membership : constructor.1 ∈ rhoSyncCalc.terms := constructor.2
  simp only [rhoSyncCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with same | same | same | same | same | same
  · rw [same, show (costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[0]).params =
        [] from by decide +kernel] at parameters
    cases parameters
  · rw [same, show (costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[1]).params =
        [.simple "n" (.base (costBaseSortName "Name"))] from by decide +kernel] at parameters
    simp at parameters
  · rw [same, rhoSync_costWrappedQuote_params] at parameters
    simp at parameters
  · rw [same, show (costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[3]).params =
        [.simple "ps" (.collection .hashBag (.base costWrappedSortName))] from
          by decide +kernel] at parameters
    simp only [List.cons.injEq, TermParam.simple.injEq, TypeExpr.collection.injEq,
      and_true] at parameters
    exact parameters.2.2.symm
  · rw [same, show (costWrappedConstructor (theory := rhoSyncIGSLT) rhoSyncOutputRule).params =
        [.simple "n" (.base (costBaseSortName "Name")),
          .simple "q" (.base costWrappedSortName),
          .simple "k" (.base costWrappedSortName)] from by decide +kernel] at parameters
    simp at parameters
  · rw [same, show (costWrappedConstructor (theory := rhoSyncIGSLT) rhoCalc.terms[5]).params =
        [.simple "n" (.base (costBaseSortName "Name")),
          .abstraction "p"
            (.arrow (.base (costBaseSortName "Name")) (.base costWrappedSortName))] from
          by decide +kernel] at parameters
    simp at parameters

/-- **No cut of the synchronous rho calculus is wrappable.**  The contractum
needs the body of the input, the sent process and the process after the
output at the wrapped sort, and a cut wraps two variables. -/
theorem rhoSync_not_wrappable (cut : InteractionCutPresentation rhoSyncIGSLT)
    (plan : ContinuationRetypingPlan cut) : ¬ plan.Wrappable := by
  intro wrappable
  obtain ⟨programLabel, environmentLabel⟩ := rhoSync_cut_introductions cut
  have quoteWrapped : rhoSyncQuoteConstructor ∈ plan.wrappedConstructors :=
    mem_continuationConstructors_of_label_ne cut rhoSyncQuoteConstructor
      (by rw [programLabel]; decide) (by rw [environmentLabel]; decide)
  have quoteLabel : "NQuote" ∈ plan.wrappedLabels :=
    (plan.mem_wrappedLabels_iff rhoSyncQuoteConstructor).mpr quoteWrapped
  have translated :
      plan.mapContractum rhoSyncCommRewrite.right =
        .collection .hashBag
          [.subst (.fvar "p") (.apply (costWrappedConstructorName "NQuote") [.fvar "q"]),
            .fvar "k"] (some "rest") := by
    simp [rhoSyncCommRewrite, mapContractum_collection, mapContractum_subst, mapContractum_apply,
      mapContractum_fvar, quoteLabel]
  unfold ContinuationRetypingPlan.Wrappable at wrappable
  change HasType plan.generatedLanguage plan.generatedFreeContext []
    (plan.mapContractum rhoSyncCommRewrite.right) (.base costWrappedSortName) at wrappable
  rw [translated] at wrappable
  obtain ⟨rule, ruleMember, category, parameterName, elementType, parameters, elements⟩ :=
    wrappable.collection_base_inv
  obtain ⟨constructor, -, rfl, -⟩ := plan.wrapped_category_inv ruleMember category
  obtain rfl := rhoSync_wrapped_collection_elementType parameters
  cases elements with
  | cons substitutionTyped rest =>
      cases rest with
      | cons continuationTyped _ =>
          obtain ⟨domain, bodyTyped, replacementTyped⟩ := substitutionTyped.subst_inv
          obtain ⟨-, quoteArguments⟩ :=
            plan.hasType_wrapped_apply_inv rhoSyncQuoteConstructor quoteWrapped
              replacementTyped
          rw [show (costWrappedConstructor (theory := rhoSyncIGSLT)
              rhoSyncQuoteConstructor.1).params = [.simple "p" (.base costWrappedSortName)]
            from rhoSync_costWrappedQuote_params] at quoteArguments
          obtain ⟨datumTyped, -⟩ := quoteArguments.simple_cons_inv
          have bodyWrapped := plan.wrapped_variable bodyTyped.fvar_inv
          have datumWrapped := plan.wrapped_variable datumTyped.fvar_inv
          have continuationWrapped := plan.wrapped_variable continuationTyped.fvar_inv
          rcases bodyWrapped with body | body <;>
            rcases datumWrapped with datum | datum <;>
              rcases continuationWrapped with continuation | continuation <;>
                first
                  | exact absurd (body.trans datum.symm) (by decide)
                  | exact absurd (body.trans continuation.symm) (by decide)
                  | exact absurd (datum.trans continuation.symm) (by decide)

/-- No continued interactive GSLT has the synchronous rho calculus as its
underlying iGSLT: its wrappability witness would be a wrappable cut. -/
theorem rhoSync_not_underlying (theory : CIGSLT) : theory.theory ≠ rhoSyncIGSLT := by
  intro same
  obtain ⟨underlying, reflection, cut, openCanonical, retyping, bareWrapped, canonicalTyping,
    equationsRetypable, reflectiveRetypable, envelopeStable, redexRetypable, wrappable⟩ :=
    theory
  subst same
  exact rhoSync_not_wrappable cut retyping wrappable

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous
