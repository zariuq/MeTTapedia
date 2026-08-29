import Mettapedia.GSLT.LanguageDef.IncrementalCalculusGenerator
import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-!
# Incremental compilation of selected native-type calculi

The complete contextual native-type generator has several dependent row
families.  A new occurrence can allocate carrier rows, then refer to those
carriers from a modal constructor, contextual claims, and profile-sensitive
inference rules.  Grouping each family globally is therefore not stable under
later growth.

This module emits one dependency-ordered `CalculusLanguageExtension` per
profiled occurrence.  The generator state is exactly the already compiled
demand, and the public result remains one flat `CalculusLanguageDef`.
Shared contextual rows are emitted by the first nonempty step rather than by
the empty generator, so an empty request generates no unused type-theory
scaffolding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeCalculusCompiler

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework

abbrev Demand (source : ValidatedLanguageDef) :=
  SelectedNativeTypeDemand source

abbrev Input (source : ValidatedLanguageDef) :=
  ProfiledRewriteOccurrence source

private theorem extension_ext
    {first second : CalculusLanguageExtension}
    (types : first.newTypes = second.newTypes)
    (terms : first.newTerms = second.newTerms)
    (equations : first.newEquations = second.newEquations)
    (rewrites : first.newRewrites = second.newRewrites)
    (judgments : first.newJudgments = second.newJudgments)
    (rules : first.newRules = second.newRules)
    (rename : first.rename = second.rename) : first = second := by
  cases first
  cases second
  simp_all

private theorem occurrenceFamily_congr
    {source : ValidatedLanguageDef} {Result : Type}
    (family : (demand : Demand source) →
      SelectedNativeTypeContextualCalculus.Occurrence demand → Result)
    {first second : Demand source}
    (demandEquality : first = second)
    (firstSlot : SelectedNativeTypeContextualCalculus.Occurrence first)
    (secondSlot : SelectedNativeTypeContextualCalculus.Occurrence second)
    (slotEquality : firstSlot.val = secondSlot.val) :
    family first firstSlot = family second secondSlot := by
  cases demandEquality
  have slotsEqual : firstSlot = secondSlot := Fin.ext slotEquality
  cases slotsEqual
  rfl

/-- One atomic profiled demand. -/
def singleton {source : ValidatedLanguageDef}
    (occurrence : Input source) : Demand source where
  occurrences := [occurrence]

/-- State after consuming one profiled occurrence. -/
def nextDemand {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) : Demand source :=
  compiled.append (singleton occurrence)

/-- The new occurrence receives the next stable global slot. -/
def nextSlot {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) :
    SelectedNativeTypeContextualCalculus.Occurrence
      (nextDemand compiled occurrence) :=
  ⟨compiled.occurrences.length, by
    simp [nextDemand, singleton, SelectedNativeTypeDemand.append]⟩

@[simp] theorem nextSlot_val {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) :
    (nextSlot compiled occurrence).val = compiled.occurrences.length :=
  rfl

/-- Exact carrier rows allocated by one occurrence after a compiled prefix. -/
def carrierExtension {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) :
    CalculusLanguageExtension :=
  SelectedNativeTypeFoundation.appendExtension compiled.foundation
    (singleton occurrence).foundation

/-- Names of exactly the newly allocated carriers.  Existing carriers do not
receive duplicate contextual-claim rows. -/
def newCarrierNames {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) : List String :=
  (carrierExtension compiled occurrence).newTypes.map fun declaration =>
    declaration.name

/-- Shared formula/context rows are demanded exactly by the first selected
occurrence. -/
def sharedContextExtension {source : ValidatedLanguageDef}
    (compiled : Demand source) : CalculusLanguageExtension :=
  if compiled.occurrences.isEmpty then
    ContextualCarrierClaims.contextExtension
  else
    CalculusLanguageExtension.empty

/-- Rows depending on the exact occurrence and its global slot. -/
def profiledOccurrenceExtension {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) :
    CalculusLanguageExtension :=
  let next := nextDemand compiled occurrence
  let slot := nextSlot compiled occurrence
  { newTerms :=
      SelectedNativeTypeContextualCalculus.supportTermsAt next slot
    newRules :=
      SelectedNativeTypeContextualCalculus.rulesAt next slot }

/-- One complete dependency-ordered compiler step:

1. allocate newly required carrier rows;
2. emit the modal constructor at its stable global occurrence slot;
3. emit the shared contextual signature on the first step;
4. emit claim rows only for newly allocated carriers; and
5. emit the occurrence-local support constructors and profiled rules.
-/
def stepExtension {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrence : Input source) :
    CalculusLanguageExtension :=
  (carrierExtension compiled occurrence).comp
    ((ConstructorTermExtension.ofList
      [ContextualModalSignatureCompiler.modalTerm compiled.foundation
        occurrence.groundedOccurrence]).comp
      ((sharedContextExtension compiled).comp
        ((ContextualCarrierClaims.carrierExtension
          (newCarrierNames compiled occurrence)).comp
          (profiledOccurrenceExtension compiled occurrence))))

/-- One profiled occurrence as a stateful flat-calculus extension. -/
def occurrenceArrow {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    StatefulCalculusExtension (Demand source) (Demand source) where
  run compiled :=
    (nextDemand compiled occurrence, stepExtension compiled occurrence)

/-- Stateful complete native-type generator. -/
def generator (source : ValidatedLanguageDef) :
    IncrementalCalculusGenerator (Demand source) (Input source) where
  step compiled occurrence := (occurrenceArrow occurrence).run compiled

/-- No selected occurrence means no generated native-type scaffolding. -/
def base (source : ValidatedLanguageDef) : CalculusLanguageDef :=
  SelectedNativeTypeFoundation.definition
    (SelectedNativeTypeFoundation.Demand.empty source)

/-- Compile one demand into a single flat calculus language. -/
def definition {source : ValidatedLanguageDef}
    (demand : Demand source) : CalculusLanguageDef :=
  (generator source).compileFrom (base source)
    (SelectedNativeTypeDemand.empty source) demand.occurrences

/-- Running an arbitrary suffix records exactly that suffix in the state. -/
theorem runFrom_state {source : ValidatedLanguageDef}
    (compiled : Demand source) (occurrences : List (Input source)) :
    ((generator source).runFrom compiled occurrences).1 =
      compiled.append ⟨occurrences⟩ := by
  induction occurrences generalizing compiled with
  | nil =>
      change compiled = compiled.append ⟨[]⟩
      exact (SelectedNativeTypeDemand.append_empty compiled).symm
  | cons occurrence occurrences inductionHypothesis =>
      simp only [IncrementalCalculusGenerator.runFrom_cons]
      change
        ((generator source).runFrom
          (nextDemand compiled occurrence) occurrences).1 =
            compiled.append ⟨occurrence :: occurrences⟩
      rw [inductionHypothesis]
      apply SelectedNativeTypeDemand.ext
      simp [nextDemand, singleton, SelectedNativeTypeDemand.append,
        List.append_assoc]

/-- Complete compilation leaves the original demand as continuation state. -/
theorem finalState {source : ValidatedLanguageDef}
    (demand : Demand source) :
    ((generator source).runFrom
      (SelectedNativeTypeDemand.empty source) demand.occurrences).1 =
        demand := by
  rw [runFrom_state]
  exact SelectedNativeTypeDemand.empty_append demand

/-- Exact residual extension for continuing a compiled profiled demand. -/
def continuationExtension {source : ValidatedLanguageDef}
    (compiled residual : Demand source) : CalculusLanguageExtension :=
  ((generator source).runFrom compiled residual.occurrences).2

/-- Compilation of ordered demand composition reuses the first flat artifact
and applies only the state-dependent residual extension. -/
theorem definition_append {source : ValidatedLanguageDef}
    (first second : Demand source) :
    definition (first.append second) =
      (continuationExtension first second).apply (definition first) := by
  unfold definition continuationExtension
  rw [SelectedNativeTypeDemand.append_occurrences]
  rw [IncrementalCalculusGenerator.compileFrom_append]
  simp only
  rw [finalState]
  rfl

/-- Every continuation is a genuine append-only refinement of the already
compiled flat language. -/
theorem definition_appendOnly {source : ValidatedLanguageDef}
    (first second : Demand source) :
    CalculusLanguageExtension.AppendOnlyCalculusRefinement
      (definition first) (definition (first.append second)) := by
  rw [definition_append]
  exact CalculusLanguageExtension.apply_appendOnly _ _

/-- A singleton profiled demand has exactly the foundation used by the
profile-forgetting modal-signature compiler. -/
theorem singleton_foundation {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    (singleton occurrence).foundation =
      ContextualModalSignatureCompiler.singleton
        occurrence.groundedOccurrence := by
  apply SelectedNativeTypeFoundation.Demand.ext
  rfl

/-- Compiling one input is application of its one stateful extension; this
keeps singleton comparison proofs at the algebraic layer. -/
theorem definition_singleton_step {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    definition (singleton occurrence) =
      (stepExtension (SelectedNativeTypeDemand.empty source) occurrence).apply
        (base source) := by
  simp [definition, generator, IncrementalCalculusGenerator.compileFrom,
    IncrementalCalculusGenerator.runFrom, occurrenceArrow, singleton,
    CalculusLanguageExtension.comp_empty]

/-- Starting from no carriers, the carrier residual allocates exactly all
stable carrier names of the singleton demand. -/
theorem newCarrierNames_empty {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    newCarrierNames (SelectedNativeTypeDemand.empty source) occurrence =
      SelectedNativeTypeFoundation.stableCarrierNames
        (singleton occurrence).foundation := by
  let emptyFoundation := SelectedNativeTypeFoundation.Demand.empty source
  have foundationRows := congrArg (fun generated : CalculusLanguageDef =>
      generated.types)
    (SelectedNativeTypeFoundation.definition_append emptyFoundation
      (singleton occurrence).foundation)
  rw [SelectedNativeTypeFoundation.Demand.empty_append] at foundationRows
  have emptyTypes :
      SelectedNativeTypeFoundation.stableCarrierTypes emptyFoundation = [] := by
    rfl
  have addedTypes :
      (SelectedNativeTypeFoundation.appendExtension emptyFoundation
        (singleton occurrence).foundation).newTypes =
        SelectedNativeTypeFoundation.stableCarrierTypes
          (singleton occurrence).foundation := by
    simpa [SelectedNativeTypeFoundation.definition_types, emptyTypes] using
      foundationRows.symm
  unfold newCarrierNames carrierExtension
  rw [SelectedNativeTypeDemand.empty_foundation, addedTypes]
  rfl

/-- On an empty prefix the first two compiler layers are exactly the existing
carrier/modal signature step. -/
theorem signatureStep_empty {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    (carrierExtension (SelectedNativeTypeDemand.empty source) occurrence).comp
        (ConstructorTermExtension.ofList
          [ContextualModalSignatureCompiler.modalTerm
            (SelectedNativeTypeDemand.empty source).foundation
            occurrence.groundedOccurrence]) =
      ContextualModalSignatureCompiler.stepExtension
        (SelectedNativeTypeFoundation.Demand.empty source)
        occurrence.groundedOccurrence := by
  unfold carrierExtension ContextualModalSignatureCompiler.stepExtension
  rw [SelectedNativeTypeDemand.empty_foundation, singleton_foundation]

/-- The occurrence-local profile delta for the first input is the complete
singleton profile delta. -/
theorem profiledOccurrenceExtension_empty {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    profiledOccurrenceExtension (SelectedNativeTypeDemand.empty source)
        occurrence =
      SelectedNativeTypeContextualCalculus.profileExtension
        (singleton occurrence) := by
  have demandEq :
      nextDemand (SelectedNativeTypeDemand.empty source) occurrence =
        singleton occurrence :=
    SelectedNativeTypeDemand.empty_append (singleton occurrence)
  have supportRows :
      SelectedNativeTypeContextualCalculus.supportTermsAt
          (nextDemand (SelectedNativeTypeDemand.empty source) occurrence)
          (nextSlot (SelectedNativeTypeDemand.empty source) occurrence) =
        SelectedNativeTypeContextualCalculus.supportTerms
          (singleton occurrence) := by
    calc
      _ = SelectedNativeTypeContextualCalculus.supportTermsAt
          (singleton occurrence) ⟨0, by simp [singleton]⟩ :=
        occurrenceFamily_congr
          SelectedNativeTypeContextualCalculus.supportTermsAt demandEq _ _ rfl
      _ = _ := by
        simp [SelectedNativeTypeContextualCalculus.supportTerms, singleton]
  have ruleRows :
      SelectedNativeTypeContextualCalculus.rulesAt
          (nextDemand (SelectedNativeTypeDemand.empty source) occurrence)
          (nextSlot (SelectedNativeTypeDemand.empty source) occurrence) =
        SelectedNativeTypeContextualCalculus.profiledRules
          (singleton occurrence) := by
    calc
      _ = SelectedNativeTypeContextualCalculus.rulesAt
          (singleton occurrence) ⟨0, by simp [singleton]⟩ :=
        occurrenceFamily_congr
          SelectedNativeTypeContextualCalculus.rulesAt demandEq _ _ rfl
      _ = _ := by
        simp [SelectedNativeTypeContextualCalculus.profiledRules, singleton]
  unfold profiledOccurrenceExtension
    SelectedNativeTypeContextualCalculus.profileExtension
  dsimp only
  apply extension_ext
  · rfl
  · exact supportRows
  · rfl
  · rfl
  · rfl
  · exact ruleRows
  · rfl

/-- The carrier/modal prefix of the first profiled step is the already proved
singleton modal signature. -/
theorem signatureApplication_empty {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    (ConstructorTermExtension.ofList
        [ContextualModalSignatureCompiler.modalTerm
          (SelectedNativeTypeDemand.empty source).foundation
          occurrence.groundedOccurrence]).apply
      ((carrierExtension (SelectedNativeTypeDemand.empty source) occurrence).apply
        (base source)) =
      ContextualModalExtension.language (singleton occurrence).foundation := by
  rw [← CalculusLanguageExtension.comp_apply, signatureStep_empty]
  rw [singleton_foundation]
  let emptyFoundation := SelectedNativeTypeFoundation.Demand.empty source
  let singletonFoundation :=
    ContextualModalSignatureCompiler.singleton occurrence.groundedOccurrence
  calc
    (ContextualModalSignatureCompiler.stepExtension emptyFoundation
        occurrence.groundedOccurrence).apply (base source) =
        (ContextualModalSignatureCompiler.continuationExtension
          emptyFoundation singletonFoundation).apply
          (ContextualModalSignatureCompiler.definition emptyFoundation) := by
            rw [ContextualModalSignatureCompiler.continuationExtension_singleton,
              ContextualModalSignatureCompiler.definition_empty]
            rfl
    _ = ContextualModalSignatureCompiler.definition
          (emptyFoundation.append singletonFoundation) :=
      (ContextualModalSignatureCompiler.definition_append
        emptyFoundation singletonFoundation).symm
    _ = ContextualModalSignatureCompiler.definition singletonFoundation := by
      rw [SelectedNativeTypeFoundation.Demand.empty_append]
    _ = ContextualModalExtension.language singletonFoundation :=
      SelectedNativeTypeContextualCalculus.singletonCompiler_eq_grouped
        occurrence.groundedOccurrence

/-- The incremental compiler agrees on a singleton with the independently
authored complete contextual calculus.  This is not self-validation: the two
objects are constructed by different composition paths. -/
theorem definition_singleton_eq_contextual {source : ValidatedLanguageDef}
    (occurrence : Input source) :
    definition (singleton occurrence) =
      SelectedNativeTypeContextualCalculus.definition
        (singleton occurrence) := by
  rw [definition_singleton_step]
  unfold stepExtension
  simp only [CalculusLanguageExtension.comp_apply]
  rw [newCarrierNames_empty, profiledOccurrenceExtension_empty]
  rw [signatureApplication_empty]
  unfold sharedContextExtension
  simp only [SelectedNativeTypeDemand.empty_occurrences, List.isEmpty_nil,
    if_true]
  unfold SelectedNativeTypeContextualCalculus.definition
    SelectedNativeTypeContextualCalculus.signature
  rw [singleton_foundation]
  rw [SelectedNativeTypeContextualCalculus.singletonCompiler_eq_grouped]
  unfold ContextualCarrierClaims.apply ContextualCarrierClaims.extension
  rw [CalculusLanguageExtension.comp_apply]

/-- The empty demand produces exactly the empty carrier foundation. -/
@[simp] theorem definition_empty (source : ValidatedLanguageDef) :
    definition (SelectedNativeTypeDemand.empty source) = base source := by
  simp [definition, IncrementalCalculusGenerator.compileFrom,
    CalculusLanguageExtension.empty_apply]

/-! ## Positive and negative controls -/

namespace Canary

open SelectedNativeTypeContextualCalculus.Canary

/-- On the concrete non-root two-rely witness, chronological compilation is
the same flat calculus already admitted by the complete checker. -/
theorem middle_definition_eq_contextual :
    definition (middleDemand .star) =
      SelectedNativeTypeContextualCalculus.definition
        (middleDemand .star) := by
  exact definition_singleton_eq_contextual (middleOccurrence .star)

/-- The chronological compiler therefore produces a fully validated nonempty
profile-sensitive calculus, not merely a compositional row trace. -/
theorem middle_definition_valid :
    (definition (middleDemand .star)).isValid = true := by
  rw [middle_definition_eq_contextual]
  exact SelectedNativeTypeContextualCalculus.Canary.middle_definition_valid

/-- Chronological compilation preserves the profile distinction all the way
to the emitted flat calculus.  In particular, the compiler is not constant in
the hypercube coordinate. -/
theorem middle_compiled_endpoints_distinct :
    definition (middleDemand .star) ≠ definition (middleDemand .box) := by
  change
    definition (singleton (middleOccurrence .star)) ≠
      definition (singleton (middleOccurrence .box))
  rw [definition_singleton_eq_contextual (middleOccurrence .star),
    definition_singleton_eq_contextual (middleOccurrence .box)]
  exact
    SelectedNativeTypeContextualCalculus.Canary.middle_endpoint_definitions_distinct

/-- The admitted compiler output denotes one ordinary GSLT: object-language
steps and proof-search steps are the two summands of its transition system. -/
def middleCompiledTheory : Mettapedia.GSLT.GSLT :=
  (definition (middleDemand .star)).toGSLTOfNoEquations
    middle_definition_valid rfl

private theorem totalization_congr
    {first second : CalculusLanguageDef} (equality : first = second)
    (firstValid : first.isAdmitted = true)
    (firstEquations : first.equations = [])
    (secondValid : second.isAdmitted = true)
    (secondEquations : second.equations = []) :
    first.toGSLTOfNoEquations firstValid firstEquations =
      second.toGSLTOfNoEquations secondValid secondEquations := by
  subst second
  rfl

/-- Chronological compilation and the independently grouped construction
denote the same total GSLT on the concrete witness. -/
theorem middleCompiledTheory_eq_contextual :
    middleCompiledTheory =
      SelectedNativeTypeContextualCalculus.Canary.middleTheory := by
  unfold middleCompiledTheory
    SelectedNativeTypeContextualCalculus.Canary.middleTheory
  exact totalization_congr middle_definition_eq_contextual _ _ _ _

/-- The first occurrence has global slot zero. -/
theorem first_slot_is_zero
    {source : ValidatedLanguageDef} (occurrence : Input source) :
    (nextSlot (SelectedNativeTypeDemand.empty source) occurrence).val = 0 := by
  rfl

/-- A second occurrence receives slot one rather than reusing the first
occurrence's private names. -/
theorem second_slot_is_one
    {source : ValidatedLanguageDef} (first second : Input source) :
    (nextSlot (singleton first) second).val = 1 := by
  rfl

/-- Restarting the state would reuse a support-constructor name.  Correct
continuation allocates a distinct global slot. -/
theorem restarting_state_reuses_forbidden_label
    {source : ValidatedLanguageDef} (first second : Input source) :
    SelectedNativeTypeContextualCalculus.auxiliaryLabel
        .familyApplication
        (nextSlot (SelectedNativeTypeDemand.empty source) second).val ≠
      SelectedNativeTypeContextualCalculus.auxiliaryLabel
        .familyApplication (nextSlot (singleton first) second).val := by
  intro equality
  have slotsEqual :=
    SelectedNativeTypeContextualCalculus.auxiliaryLabel_injective
      .familyApplication equality
  change (0 : Nat) = 1 at slotsEqual
  omega

end Canary

#print axioms runFrom_state
#print axioms finalState
#print axioms definition_append
#print axioms definition_appendOnly
#print axioms definition_empty
#print axioms Canary.middle_definition_valid
#print axioms Canary.middle_compiled_endpoints_distinct
#print axioms Canary.middleCompiledTheory_eq_contextual
#print axioms Canary.restarting_state_reuses_forbidden_label

end Mettapedia.OSLF.Framework.SelectedNativeTypeCalculusCompiler
