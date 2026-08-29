import Mettapedia.GSLT.LanguageDef.IncrementalCalculusGenerator
import Mettapedia.GSLT.LanguageDef.ConstructorPermutation
import Mettapedia.OSLF.Framework.ContextualModalExtension
import Mettapedia.OSLF.Framework.GroundedRewriteOccurrence

/-!
# Incremental compilation of contextual modal signatures

The batch carrier and modal generators are each append-stable, but grouping
all carrier-universe declarations before all modal declarations is not stable
under later carrier growth: a new universe row would be inserted before an
old modal row.  This module uses the generic writer-state compiler to emit one
heterogeneous delta per selected occurrence:

1. allocate only carrier rows not seen earlier;
2. emit the occurrence's contextual modal declaration at its global slot.

The resulting artifact is one flat `CalculusLanguageDef`. Generator state and
deltas are an internal compilation factorization, and exact continuation is
certified by `definition_append` and `definition_appendOnly`.

This compiler consumes exactly the profile-free grounded typing demand needed
to build a signature. Local `star`/`box` choices belong to the later proof-
calculus generator; they are deliberately absent from this API.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace ContextualModalSignatureCompiler

/-- One singleton grounded atom, used to feed the compositional generator. -/
def singleton {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    SelectedNativeTypeFoundation.Demand source :=
  occurrence.singletonDemand

/-- The exact modal declaration introduced after an already compiled prefix. -/
def modalTerm {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) : GrammarRule :=
  ContextualModalSignature.modalRule
    (ContextualModalExtension.compiledCarrierName
      (compiled.append (singleton occurrence)))
    compiled.typings.length occurrence.typing

/-- Heterogeneous delta for one occurrence: new carrier rows first, then the
contextual modal row whose signature can refer to those carriers. -/
def stepExtension {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    CalculusLanguageExtension :=
  let next := singleton occurrence
  (SelectedNativeTypeFoundation.appendExtension
      compiled next).comp
    (ConstructorTermExtension.ofList [modalTerm compiled occurrence])

/-- One selected occurrence as a lawful stateful compilation arrow. -/
def occurrenceArrow {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    StatefulCalculusExtension
      (SelectedNativeTypeFoundation.Demand source)
      (SelectedNativeTypeFoundation.Demand source) where
  run compiled :=
    (compiled.append (singleton occurrence),
      stepExtension compiled occurrence)

/-- Stateful generator whose state is exactly the already compiled demand. -/
def generator (source : ValidatedLanguageDef) :
    IncrementalCalculusGenerator
      (SelectedNativeTypeFoundation.Demand source)
      (GroundedRewriteOccurrence source) where
  step compiled occurrence := (occurrenceArrow occurrence).run compiled

/-- The generic generator's single-input arrow is exactly the contextual
occurrence arrow, rather than an independently encoded execution path. -/
theorem stepArrow_eq_occurrenceArrow {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    (generator source).stepArrow occurrence = occurrenceArrow occurrence := by
  apply StatefulCalculusExtension.ext
  intro compiled
  rfl

/-- The empty flat carrier calculus is the initial compilation object. -/
def base (source : ValidatedLanguageDef) : CalculusLanguageDef :=
  SelectedNativeTypeFoundation.definition
    (SelectedNativeTypeFoundation.Demand.empty source)

/-- Canonical flat contextual-modal signature generated in authored order. -/
def definition {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    CalculusLanguageDef :=
  (generator source).compileFrom (base source)
    (SelectedNativeTypeFoundation.Demand.empty source)
    demand.groundedOccurrences

/-- The public flat definition is precisely the language coordinate of the
lawfully composed occurrence arrow. -/
theorem definition_eq_inputArrow_apply {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    definition demand =
      ((((generator source).inputArrow demand.groundedOccurrences).apply
        (SelectedNativeTypeFoundation.Demand.empty source) (base source))).2 := by
  have applied := IncrementalCalculusGenerator.inputArrow_apply
    (generator source) (base source)
    (SelectedNativeTypeFoundation.Demand.empty source)
    demand.groundedOccurrences
  exact (congrArg Prod.snd applied).symm

/-- Running an arbitrary occurrence suffix records exactly that suffix in the
state, with no hidden generator coordinate. -/
theorem runFrom_state {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    ((generator source).runFrom compiled occurrences).1 =
      compiled.append (GroundedRewriteOccurrence.demandOfList occurrences) := by
  induction occurrences generalizing compiled with
  | nil =>
      change compiled =
        compiled.append (SelectedNativeTypeFoundation.Demand.empty source)
      exact (SelectedNativeTypeFoundation.Demand.append_empty compiled).symm
  | cons occurrence occurrences inductionHypothesis =>
      simp only [IncrementalCalculusGenerator.runFrom_cons]
      change
        ((generator source).runFrom
          (compiled.append (singleton occurrence)) occurrences).1 =
            compiled.append
              (GroundedRewriteOccurrence.demandOfList
                (occurrence :: occurrences))
      rw [inductionHypothesis]
      rw [GroundedRewriteOccurrence.demandOfList_cons,
        SelectedNativeTypeFoundation.Demand.append_assoc]
      rfl

/-- Compiling the complete demand leaves that same demand as continuation
state. -/
theorem finalState {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    ((generator source).runFrom
      (SelectedNativeTypeFoundation.Demand.empty source)
      demand.groundedOccurrences).1 = demand := by
  rw [runFrom_state]
  rw [SelectedNativeTypeFoundation.Demand.demandOfList_groundedOccurrences]
  exact SelectedNativeTypeFoundation.Demand.empty_append demand

/-- Exact residual extension for continuing a previously compiled demand. -/
def continuationExtension {source : ValidatedLanguageDef}
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    CalculusLanguageExtension :=
  ((generator source).runFrom compiled residual.groundedOccurrences).2

/-- Continuing by one atomic occurrence is exactly the occurrence's authored
stateful extension.  There is no second singleton compilation path. -/
theorem continuationExtension_singleton {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    continuationExtension compiled (singleton occurrence) =
      stepExtension compiled occurrence := by
  unfold continuationExtension singleton
  rw [SelectedNativeTypeFoundation.Demand.groundedOccurrences_singletonDemand]
  simp [IncrementalCalculusGenerator.runFrom, generator, occurrenceArrow,
    CalculusLanguageExtension.comp_empty]

/-- The batch residual for one occurrence is the same modal row emitted by
the chronological compiler at that global occurrence slot. -/
theorem appendedModalTerms_singleton {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    ContextualModalExtension.appendedModalTerms compiled
        (singleton occurrence) =
      [modalTerm compiled occurrence] := by
  unfold ContextualModalExtension.appendedModalTerms
  simp [singleton, GroundedRewriteOccurrence.singletonDemand, modalTerm]

/-- One chronological carrier/modal step is the grouped batch step up to the
explicit constructor-order permutation that moves newly allocated carrier
constructors ahead of the already emitted modal prefix. -/
theorem groupedStep_constructorPermutation
    {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    ConstructorPermutation
      ((stepExtension compiled occurrence).apply
        (ContextualModalExtension.language compiled))
      (ContextualModalExtension.language
        (compiled.append (singleton occurrence))) := by
  constructor
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.comp,
      CalculusLanguageExtension.apply, List.append_assoc]
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.comp_apply]
  · simp only [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      CalculusLanguageExtension.comp_apply,
      CalculusLanguageExtension.apply_terms,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton,
      SelectedNativeTypeFoundation.definition_terms]
    have swapped :
        (ContextualModalExtension.modalTerms compiled ++
          (SelectedNativeTypeFoundation.appendExtension compiled
            (singleton occurrence)).newTerms).Perm
        ((SelectedNativeTypeFoundation.appendExtension compiled
            (singleton occurrence)).newTerms ++
          ContextualModalExtension.modalTerms compiled) :=
      List.perm_append_comm
    have withFoundation := swapped.append_left
      (CarrierUniverseSignature.termsFor
        (SelectedNativeTypeFoundation.stableCarrierNames compiled))
    have withModal := withFoundation.append_right [modalTerm compiled occurrence]
    simpa [List.append_assoc] using withModal
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.comp_apply]
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.comp_apply]
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.comp_apply]
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.comp_apply]
  · simp [stepExtension, ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList,
      SelectedNativeTypeFoundation.definition_append,
      ContextualModalExtension.modalTerms_append,
      appendedModalTerms_singleton, CalculusLanguageExtension.apply]

/-- Splitting a nonempty occurrence stream into its head and tail agrees with
ordered demand composition. -/
theorem append_cons {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    compiled.append
        (GroundedRewriteOccurrence.demandOfList (occurrence :: occurrences)) =
      (compiled.append (singleton occurrence)).append
        (GroundedRewriteOccurrence.demandOfList occurrences) := by
  rw [GroundedRewriteOccurrence.demandOfList_cons,
    SelectedNativeTypeFoundation.Demand.append_assoc]
  rfl

/-- The continuation for a nonempty stream factors through its head arrow and
the continuation computed from the resulting state. -/
theorem continuationExtension_cons {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    continuationExtension compiled
        (GroundedRewriteOccurrence.demandOfList (occurrence :: occurrences)) =
      (stepExtension compiled occurrence).comp
        (continuationExtension
          (compiled.append (singleton occurrence))
          (GroundedRewriteOccurrence.demandOfList occurrences)) := by
  unfold continuationExtension
  rw [SelectedNativeTypeFoundation.Demand.groundedOccurrences_demandOfList,
    SelectedNativeTypeFoundation.Demand.groundedOccurrences_demandOfList]
  rfl

private theorem continuation_constructorPermutation_ofList
    {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    ConstructorPermutation
      ((continuationExtension compiled
          (GroundedRewriteOccurrence.demandOfList occurrences)).apply
        (ContextualModalExtension.language compiled))
      (ContextualModalExtension.language
        (compiled.append
          (GroundedRewriteOccurrence.demandOfList occurrences))) := by
  induction occurrences generalizing compiled with
  | nil =>
      rw [GroundedRewriteOccurrence.demandOfList_nil,
        SelectedNativeTypeFoundation.Demand.append_empty]
      simpa [continuationExtension,
        IncrementalCalculusGenerator.runFrom,
        CalculusLanguageExtension.empty_apply] using
        ConstructorPermutation.refl
          (ContextualModalExtension.language compiled)
  | cons occurrence occurrences inductionHypothesis =>
      let next := compiled.append (singleton occurrence)
      let tail := GroundedRewriteOccurrence.demandOfList occurrences
      have first := groupedStep_constructorPermutation compiled occurrence
      have lifted := first.apply_extension
        (continuationExtension next tail)
      have remainder := inductionHypothesis next
      have composed := lifted.trans remainder
      rw [continuationExtension_cons,
        CalculusLanguageExtension.comp_apply, append_cons]
      exact composed

/-- Every chronological continuation normalizes to the grouped carrier/modal
batch language by a proof-carrying constructor permutation. The theorem
retains the authored compilation history through induction; it does not try
to recover that history from the flat target. -/
theorem continuation_constructorPermutation
    {source : ValidatedLanguageDef}
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    ConstructorPermutation
      ((continuationExtension compiled residual).apply
        (ContextualModalExtension.language compiled))
      (ContextualModalExtension.language
        (compiled.append residual)) := by
  simpa using
    continuation_constructorPermutation_ofList compiled
      residual.groundedOccurrences

/-- The grouped specification has the same empty object as the chronological
compiler. -/
theorem grouped_empty_eq_base (source : ValidatedLanguageDef) :
    ContextualModalExtension.language
        (SelectedNativeTypeFoundation.Demand.empty source) =
      base source := by
  change
    (ConstructorTermExtension.ofList
      (ContextualModalExtension.modalTerms
        (SelectedNativeTypeFoundation.Demand.empty source))).apply
      (SelectedNativeTypeFoundation.definition
        (SelectedNativeTypeFoundation.Demand.empty source)) =
      SelectedNativeTypeFoundation.definition
        (SelectedNativeTypeFoundation.Demand.empty source)
  rw [ContextualModalExtension.Canary.empty_has_no_modal_terms]
  change CalculusLanguageExtension.empty.apply
      (SelectedNativeTypeFoundation.definition
        (SelectedNativeTypeFoundation.Demand.empty source)) = _
  exact CalculusLanguageExtension.empty_apply _

/-- Demand append compiles by applying only the chronological residual to the
already compiled flat artifact. -/
theorem definition_append {source : ValidatedLanguageDef}
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    definition (compiled.append residual) =
      (continuationExtension compiled residual).apply
        (definition compiled) := by
  unfold definition continuationExtension
  rw [SelectedNativeTypeFoundation.Demand.groundedOccurrences_append]
  unfold IncrementalCalculusGenerator.compileFrom
  rw [IncrementalCalculusGenerator.runFrom_append]
  simp only
  rw [finalState]
  exact CalculusLanguageExtension.comp_apply _ _ _

/-- The chronological compiler and the grouped batch specification generate
the same flat constructor theory up to an explicit row-order permutation. -/
theorem definition_constructorPermutation_grouped
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    ConstructorPermutation (definition demand)
      (ContextualModalExtension.language demand) := by
  have normalized := continuation_constructorPermutation
    (SelectedNativeTypeFoundation.Demand.empty source) demand
  rw [grouped_empty_eq_base,
    SelectedNativeTypeFoundation.Demand.empty_append] at normalized
  have definitionEmpty :
      definition (SelectedNativeTypeFoundation.Demand.empty source) =
        base source := by
    unfold definition IncrementalCalculusGenerator.compileFrom
    change
      ((generator source).runFrom
        (SelectedNativeTypeFoundation.Demand.empty source) []).2.apply
          (base source) =
          base source
    rw [IncrementalCalculusGenerator.runFrom_nil]
    exact CalculusLanguageExtension.empty_apply (base source)
  have compiled := definition_append
    (SelectedNativeTypeFoundation.Demand.empty source) demand
  rw [SelectedNativeTypeFoundation.Demand.empty_append, definitionEmpty]
    at compiled
  rw [compiled]
  exact normalized

/-- Chronological generation passes the ordinary language-definition
validator.  Validation is transported from the independently checked grouped
specification through the explicit constructor-permutation certificate. -/
theorem definition_language_validate {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    (definition demand).toLanguageDef.validate = [] := by
  apply (definition_constructorPermutation_grouped demand).symm
    |>.target_validate_of_constructorOnly
  · simp [ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList]
  · simp [ContextualModalExtension.language,
      ContextualModalExtension.extension, ConstructorTermExtension.ofList]
  · exact ContextualModalExtension.language_validate demand

/-- Whole-language refinement is append-only in every row family.  This is
the property that the grouped batch ordering cannot provide. -/
theorem definition_appendOnly {source : ValidatedLanguageDef}
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    CalculusLanguageExtension.AppendOnlyCalculusRefinement
      (definition compiled) (definition (compiled.append residual)) := by
  rw [definition_append]
  exact CalculusLanguageExtension.apply_appendOnly _ _

/-- The carrier-first/modal-second batch order is not an incremental
composition law.  Whenever an existing modal row is followed by genuinely
new carrier constructors, the new carriers are inserted before that old
modal row, so the earlier flat language is not a prefix of the result. -/
theorem groupedLanguage_not_appendOnly_of_carrierGrowth
    {source : ValidatedLanguageDef}
    (earlier later : SelectedNativeTypeFoundation.Demand source)
    (earlierHasModal :
      ContextualModalExtension.modalTerms earlier ≠ [])
    (newCarrierTerms :
      (SelectedNativeTypeFoundation.appendExtension earlier later).newTerms ≠
        []) :
    ¬ CalculusLanguageExtension.AppendOnlyCalculusRefinement
      (ContextualModalExtension.language earlier)
      (ContextualModalExtension.language (earlier.append later)) := by
  intro refinement
  cases earlierRows : ContextualModalExtension.modalTerms earlier with
  | nil => exact earlierHasModal earlierRows
  | cons earlierModal earlierTail =>
      cases residualRows :
          (SelectedNativeTypeFoundation.appendExtension earlier later).newTerms with
      | nil => exact newCarrierTerms residualRows
      | cons newCarrier carrierTail =>
          have foundationTerms :
              (SelectedNativeTypeFoundation.definition
                (earlier.append later)).terms =
                (SelectedNativeTypeFoundation.definition earlier).terms ++
                  (SelectedNativeTypeFoundation.appendExtension
                    earlier later).newTerms := by
            rw [SelectedNativeTypeFoundation.definition_append]
            rfl
          have termsPrefix := refinement.terms
          simp only [ContextualModalExtension.language_terms] at termsPrefix
          rw [foundationTerms, ContextualModalExtension.modalTerms_append,
            earlierRows, residualRows] at termsPrefix
          rw [List.prefix_iff_getElem?] at termsPrefix
          have boundary := termsPrefix
            (SelectedNativeTypeFoundation.definition earlier).terms.length
            (by simp)
          have headEquality : earlierModal = newCarrier := by
            have reverse : newCarrier = earlierModal := by
              simpa using boundary
            exact reverse.symm
          subst newCarrier
          have disjoint :=
            ContextualModalExtension.foundation_modalTermLabels_disjoint
              (earlier.append later)
          have inFoundation : earlierModal.label ∈
              (SelectedNativeTypeFoundation.definition
                (earlier.append later)).terms.map (·.label) := by
            rw [foundationTerms, List.map_append, residualRows]
            simp
          have absentFromModal :=
            (List.disjoint_left.mp disjoint) inFoundation
          apply absentFromModal
          rw [ContextualModalExtension.modalTerms_append, earlierRows,
            List.map_append]
          simp

@[simp]
theorem modalTerm_label {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source) :
    (modalTerm compiled occurrence).label =
      SelectedModalNaming.label compiled.typings.length :=
  rfl

/-- Restarting allocation after a nonempty prefix changes the modal wire name;
the state-free compilation is therefore rejected rather than conflated with
incremental continuation. -/
theorem modalTerm_ne_restarted_of_nonempty
    {source : ValidatedLanguageDef}
    (compiled : SelectedNativeTypeFoundation.Demand source)
    (occurrence : GroundedRewriteOccurrence source)
    (nonempty : compiled.typings ≠ []) :
    modalTerm compiled occurrence ≠
      modalTerm (SelectedNativeTypeFoundation.Demand.empty source)
        occurrence := by
  intro equality
  have labels := congrArg GrammarRule.label equality
  change SelectedModalNaming.label compiled.typings.length =
    SelectedModalNaming.label 0 at labels
  have slots : compiled.typings.length = 0 :=
    SelectedModalNaming.label_injective labels
  exact nonempty (List.length_eq_zero_iff.mp slots)

/-! ## Positive control -/

/-- Empty input is compiled to the ordinary empty carrier calculus without
inventing a modal row. -/
theorem definition_empty (source : ValidatedLanguageDef) :
    definition (SelectedNativeTypeFoundation.Demand.empty source) =
      base source := by
  unfold definition IncrementalCalculusGenerator.compileFrom
  change
    ((generator source).runFrom
      (SelectedNativeTypeFoundation.Demand.empty source) []).2.apply
        (base source) =
        base source
  rw [IncrementalCalculusGenerator.runFrom_nil]
  exact CalculusLanguageExtension.empty_apply (base source)

#print axioms runFrom_state
#print axioms stepArrow_eq_occurrenceArrow
#print axioms definition_eq_inputArrow_apply
#print axioms finalState
#print axioms continuationExtension_singleton
#print axioms appendedModalTerms_singleton
#print axioms groupedStep_constructorPermutation
#print axioms append_cons
#print axioms continuationExtension_cons
#print axioms continuation_constructorPermutation
#print axioms grouped_empty_eq_base
#print axioms definition_append
#print axioms definition_constructorPermutation_grouped
#print axioms definition_language_validate
#print axioms definition_appendOnly
#print axioms groupedLanguage_not_appendOnly_of_carrierGrowth
#print axioms modalTerm_ne_restarted_of_nonempty
#print axioms definition_empty

end ContextualModalSignatureCompiler

end Mettapedia.OSLF.Framework
