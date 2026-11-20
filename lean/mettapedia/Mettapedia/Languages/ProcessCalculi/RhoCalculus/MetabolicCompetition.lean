import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ResourceClaimHistory
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-!
# Actual competition for a metabolic stack message

An owner and a contextual receiver are simultaneously enabled on one stack
output. Either can receive it through the independently authored closed COMM
semantics. The contextual receiver transfers the complete payload to a
different channel. Exclusive claims concern the original occurrence; equal
messages reissued by continuations are fresh occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Competition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Canonical CanonicalTyping CanonicalBag CanonicalReaction HeaderInversion
open ResourcePredation ResourceClaimHistory LanguageDefGSLT
open LanguageDefRewriteSystem CanonicalStepperCompleteness

universe u

def ownerBody (count : Nat) : Pattern :=
  .collection .hashBag [.apply "PDrop" [.bvar 0], trigger, owner count] none

def transferBody : Pattern := output acquisition (.apply "PDrop" [.bvar 0])

def transferReceiver : Pattern := input metabolic transferBody

theorem transfer_typed :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] transferReceiver :=
  .input (metabolic_typed _) (.output (acquisition_typed _) (.drop (.bvar rfl)))

theorem transfer_safe : binderSafeAt "NQuote" 0 transferReceiver = true := by
  simp [transferReceiver, transferBody, input, output, binderSafeAt, binderSafeListAt,
    metabolic, acquisition, spent, pop, zero]

private def headerPrime (header : Header)
    (closed : RhoClosedTermWellSorted rhoProc header.pattern) :
    { pattern : Pattern // IsPrime pattern } :=
  ⟨canonicalize header.pattern,
    (RhoClosedTerm.canonicalize (⟨header.pattern, closed⟩ : RhoProcess)).2,
    canonicalize_isCanonical _, header.canonical_nonunit,
    fun _ => header.canonical_nonbag _ none⟩

private def ownerPrime (count : Nat) : { pattern : Pattern // IsPrime pattern } :=
  headerPrime (.input metabolic (ownerBody count)) (ownerProcess (count + 1)).2

private def transferPrime : { pattern : Pattern // IsPrime pattern } :=
  headerPrime (.input metabolic transferBody)
    ((rhoClosedTermWellSorted_process_iff _).mpr ⟨transfer_typed, transfer_safe⟩)

private def messagePrime {Head : Type u} (encoding : Encoding Head) (stack : Stack Head) :
    { pattern : Pattern // IsPrime pattern } :=
  headerPrime (.output metabolic (payload encoding stack)) (messageProcess encoding stack).2

private theorem ownerPrime_shape (count : Nat) :
    (ownerPrime count).1 = input (canonicalize metabolic) (canonicalize (ownerBody count)) := by
  simp only [ownerPrime, headerPrime, Header.pattern, canonicalize_input]
  rfl

private theorem transferPrime_shape :
    transferPrime.1 = input (canonicalize metabolic) (canonicalize transferBody) := by
  simp only [transferPrime, headerPrime, Header.pattern, canonicalize_input]
  rfl

private theorem messagePrime_shape {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) :
    (messagePrime encoding stack).1 =
      output (canonicalize metabolic) (canonicalize (payload encoding stack)) := by
  simp only [messagePrime, headerPrime, Header.pattern, canonicalize_output]
  rfl

private def ownerOccurrence (count : Nat) : Occurrence := ⟨0, .computation, ownerPrime count⟩
private def transferOccurrence : Occurrence := ⟨1, .context, transferPrime⟩
private def messageOccurrence {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) : Occurrence := ⟨2, .computation, messagePrime encoding stack⟩

def configuration {Head : Type u} (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) : Configuration :=
  .ofList [ownerOccurrence count, transferOccurrence, messageOccurrence encoding stack]

theorem configuration_distinct {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) : Distinct (configuration encoding stack count) := by
  simp [Distinct, configuration, Configuration.ofList, ownerOccurrence, transferOccurrence,
    messageOccurrence]

private def ownerRule {Head : Type u} (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) : GroundComm where
  inputChannel := canonicalize metabolic
  outputChannel := canonicalize metabolic
  body := canonicalize (ownerBody count)
  payload := canonicalize (payload encoding stack)
  inputPrime := by rw [← ownerPrime_shape]; exact (ownerPrime count).2
  outputPrime := by rw [← messagePrime_shape]; exact (messagePrime encoding stack).2
  channels := rfl

private def transferRule {Head : Type u} (encoding : Encoding Head) (stack : Stack Head) :
    GroundComm where
  inputChannel := canonicalize metabolic
  outputChannel := canonicalize metabolic
  body := canonicalize transferBody
  payload := canonicalize (payload encoding stack)
  inputPrime := by rw [← transferPrime_shape]; exact transferPrime.2
  outputPrime := by rw [← messagePrime_shape]; exact (messagePrime encoding stack).2
  channels := rfl

def ownerFiring {Head : Type u} (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) : Firing (configuration encoding stack count) where
  inputIndex := ⟨0, by simp [configuration, Configuration.ofList]⟩
  outputIndex := ⟨1, by simp [configuration, Configuration.ofList]⟩
  rule := ownerRule encoding stack count
  inputAt := ownerPrime_shape count
  outputAt := messagePrime_shape encoding stack

def transferFiring {Head : Type u} (encoding : Encoding Head) (stack : Stack Head)
    (count : Nat) : Firing (configuration encoding stack count) where
  inputIndex := ⟨1, by simp [configuration, Configuration.ofList]⟩
  outputIndex := ⟨1, by simp [configuration, Configuration.ofList]⟩
  rule := transferRule encoding stack
  inputAt := transferPrime_shape
  outputAt := messagePrime_shape encoding stack

/-- Both alternatives are actual enabled communications before scheduling. -/
def race {Head : Type u} (encoding : Encoding Head) (stack : Stack Head) (count : Nat) :
    Race (configuration encoding stack count) where
  distinct := configuration_distinct encoding stack count
  owner := ownerFiring encoding stack count
  competitor := transferFiring encoding stack count
  sameResource := rfl
  computationResource := rfl
  ownerOrigin := rfl
  competitorOrigin := rfl

theorem enabled_owner_and_competitor {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) :
    rhoLanguageDefGSLT.Step (readout (configuration encoding stack count))
        (readout (ownerFiring encoding stack count).target) ∧
      rhoLanguageDefGSLT.Step (readout (configuration encoding stack count))
        (readout (transferFiring encoding stack count).target) ∧
      HarvestAt 2 (transferFiring encoding stack count) ∧
      ¬ HarvestAt 2 (ownerFiring encoding stack count) :=
  ⟨(ownerFiring encoding stack count).public_step,
    (transferFiring encoding stack count).public_step,
    (race encoding stack count).competitor_harvesting.1,
    (race encoding stack count).owner_spending.2⟩

theorem no_double_original_claim {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) {future : Configuration}
    (history : History (transferFiring encoding stack count).target future)
    (later : Firing future) : later.resource.key ≠ 2 :=
  (race encoding stack count).competitor_excludes_original_spend history later

theorem owner_excludes_original_harvest {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) {future : Configuration}
    (history : History (ownerFiring encoding stack count).target future)
    (later : Firing future) : ¬ HarvestAt 2 later :=
  (race encoding stack count).owner_excludes_original_harvest history later

theorem transfer_substitution {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) :
    semanticCommSubst transferBody (payload encoding stack) =
      output acquisition (payload encoding stack) := by
  simp [transferBody, semanticCommSubst, semanticSubstProc, semanticSubstName,
    semanticSubstNameMark, semanticNormalizeName, semanticNormalizeProc,
    canonicalize, canonicalizeList, normalizeQuote,
    payload_normalize, output, acquisition, spent, pop, metabolic, zero]

/-- The contextual result stores the complete received stack on its new channel. -/
theorem canonical_transfer_result {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) :
    canonicalize (transferRule encoding stack).result.1 =
      output (canonicalize acquisition) (canonicalize (payload encoding stack)) := by
  change canonicalize
    (semanticCommSubst (canonicalize transferBody) (canonicalize (payload encoding stack))) = _
  rw [SubstitutionCanonicalCommutation.canonicalize_semanticCommSubst_canonicalize
    (show ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      [rhoReflectivePresentation.nameSort] transferBody from
        .output (acquisition_typed _) (.drop (.bvar rfl)))
    (PureBoundary.rhoProcWellSorted_hashSetFree (payload_typed encoding stack [])),
    transfer_substitution]
  simp only [output, canonicalize_output]

private theorem transfer_spawned_shape {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) {occurrence : Occurrence}
    (membership : occurrence ∈ (transferFiring encoding stack count).spawned) :
    occurrence.term.1 =
      output (canonicalize acquisition) (canonicalize (payload encoding stack)) := by
  have mapped : occurrence.term.1 ∈
      ((transferFiring encoding stack count).spawned.map fun entry => entry.term.1) :=
    List.mem_map.mpr ⟨occurrence, membership, rfl⟩
  rw [Firing.spawned_patterns] at mapped
  change occurrence.term.1 ∈ ordered (fromProcess (transferRule encoding stack).result).1 at mapped
  rw [ordered_fromProcess] at mapped
  obtain ⟨pattern, patternMember, termMember⟩ := normalizeBagElements_mem_source mapped
  have shape : pattern =
      output (canonicalize acquisition) (canonicalize (payload encoding stack)) := by
    simpa only [canonical_transfer_result, List.mem_singleton] using patternMember
  rw [shape] at termMember
  simpa only [output, bagSplice, List.mem_singleton] using termMember

private theorem transferred_occurrence_shape {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) {occurrence : Occurrence}
    (membership : occurrence ∈ (transferFiring encoding stack count).target.occurrences) :
    occurrence.term.1 = input (canonicalize metabolic) (canonicalize (ownerBody count)) ∨
      occurrence.term.1 =
        output (canonicalize acquisition) (canonicalize (payload encoding stack)) := by
  rcases List.mem_append.mp membership with spawned | retained
  · exact Or.inr (transfer_spawned_shape encoding stack count spawned)
  · have equal : occurrence = ownerOccurrence count := by
      simpa [transferFiring, Firing.tail, configuration, Configuration.ofList] using retained
    exact Or.inl (equal ▸ ownerPrime_shape count)

/-- With no alternate purse or replenisher, the remaining owner input cannot
receive the transferred output. This is an isolated operational profile. -/
theorem transferred_no_firing {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat)
    (later : Firing (transferFiring encoding stack count).target) : False := by
  have inputShape := later.inputAt
  have outputShape := later.outputAt
  rcases transferred_occurrence_shape encoding stack count
    (List.getElem_mem later.inputIndex.isLt) with ownerShape | transferShape
  · rw [ownerShape] at inputShape
    have inputChannel : canonicalize metabolic = later.rule.inputChannel := by
      have fields : canonicalize metabolic = later.rule.inputChannel ∧
          canonicalize (ownerBody count) = later.rule.body := by
        simpa only [input, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq,
          true_and, and_true] using inputShape
      exact fields.1
    rcases transferred_occurrence_shape encoding stack count
      (List.mem_of_mem_eraseIdx (List.getElem_mem later.outputIndex.isLt)) with
      impossible | resourceShape
    · rw [impossible] at outputShape
      simp [input, output] at outputShape
    · rw [resourceShape] at outputShape
      have outputChannel : canonicalize acquisition = later.rule.outputChannel := by
        have fields : canonicalize acquisition = later.rule.outputChannel ∧
            canonicalize (payload encoding stack) = later.rule.payload := by
          simpa only [output, Pattern.apply.injEq, List.cons.injEq,
            true_and, and_true] using outputShape
        exact fields.1
      have channelEqual := later.rule.channels
      rw [← inputChannel, ← outputChannel, canonicalize_idempotent,
        canonicalize_idempotent] at channelEqual
      exact names_distinct.2.2.2 channelEqual.symm
  · rw [transferShape] at inputShape
    simp [input, output] at inputShape

theorem transferred_every_public_execution_quiet {Head : Type u} (encoding : Encoding Head)
    (stack : Stack Head) (count : Nat) {future : RhoProcess}
    (history : Relation.ReflTransGen rhoLanguageDefGSLT.Step
      (readout (transferFiring encoding stack count).target) future) :
    future = readout (transferFiring encoding stack count).target :=
  public_history_quiet_of_no_firing (transferred_no_firing encoding stack count) history

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Metabolic.Competition
