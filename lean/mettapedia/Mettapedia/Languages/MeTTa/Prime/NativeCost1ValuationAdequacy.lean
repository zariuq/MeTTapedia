import Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation
import Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptObservation

/-!
# Prime controls for Cost1 operational valuations

The generic Cost1 boundary makes every declared grade or value a compositional
observation of an exact proof-relevant wave history.  This module instantiates
its negative controls with real Prime schedules.

Two legal chronological schedules have equal `WorkSpan` and distinct funded
receipt histories, so WorkSpan cannot replay chronology or even recover the
first funded receipt.  Conversely, a one-wave and a two-wave execution of the
same two occurrences have the same scalar work grade and the same authored
two-occurrence truth bit while retaining different spans.  These are concrete
nonfactorization witnesses: WorkSpan, scalar grade, declared value, and truth
observation are related only by explicit maps, never by identification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeCost1ValuationAdequacy

open Mettapedia.Algebra
open Mettapedia.GSLT.Core.ControlInfluenceSeparation
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptObservation
open Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

namespace Examples

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptObservation.Examples

noncomputable section

abbrev Receipt := Multiset (SpendEvent Ground (CostName Ground))
abbrev History := List (WaveEvent Ground)

/-! ## WorkSpan does not recover exact receipts -/

/-- Read only the first funded receipt from an exact chronological history. -/
def firstReceipt : History → Option Receipt
  | [] => none
  | event :: _ => some event.receipt

@[simp] theorem firstReceipt_forward :
    firstReceipt forwardHistory = some leftSingleton.receipt :=
  rfl

@[simp] theorem firstReceipt_reverse :
    firstReceipt reverseHistory = some rightSingleton.receipt :=
  rfl

/-- The concrete valid schedules instantiate the generic Cost1 theorem:
WorkSpan cannot replay their exact histories. -/
theorem no_exact_history_recovery_from_workSpan :
    ¬ ∃ recover : WorkSpan → History,
        recover forwardSchedule.workSpan = forwardHistory ∧
          recover reverseSchedule.workSpan = reverseHistory := by
  exact no_history_recovery_of_workSpan_collision
    (first := forwardSchedule) (second := reverseSchedule)
    two_orders_same_workSpan two_orders_distinct_histories

/-- Even the first funded receipt does not factor through WorkSpan on these
two executable schedules. -/
theorem no_firstReceipt_recovery_from_workSpan :
    ¬ ∃ recover : WorkSpan → Option Receipt,
        recover forwardSchedule.workSpan = firstReceipt forwardHistory ∧
          recover reverseSchedule.workSpan = firstReceipt reverseHistory := by
  rintro ⟨recover, recoversForward, recoversReverse⟩
  have sameWorkSpan :
      forwardSchedule.workSpan = reverseSchedule.workSpan := by
    change historyWorkSpan forwardHistory = historyWorkSpan reverseHistory
    exact two_orders_same_workSpan
  apply singleton_receipts_ne
  apply Option.some.inj
  rw [← firstReceipt_forward, ← firstReceipt_reverse,
    ← recoversForward, ← recoversReverse, sameWorkSpan]

/-! ## Scalar grade and truth do not recover WorkSpan -/

abbrev oneWaveSchedule := familyOperationalSchedule oneColourFamily
abbrev twoWaveSchedule := coloringOperationalSchedule twoColouring
abbrev oneWaveHistory := Schedule.events oneWaveSchedule
abbrev twoWaveHistory := Schedule.events twoWaveSchedule

/-- Scalar funded work is a declared grade of exact history.  It deliberately
forgets chronological span. -/
def workGrade (history : History) : Nat :=
  (historyWorkSpan history).work

/-- An authored Boolean truth observation: did this execution retain exactly
two funded occurrences?  This is a canary for separation of truth readout from
the full schedule valuation, not a universal definition of semantic truth. -/
def hasTwoFundedOccurrences (history : History) : Bool :=
  decide (workGrade history = 2)

theorem oneWave_historyWorkSpan :
    historyWorkSpan oneWaveHistory = ⟨2, 1⟩ := by
  rw [historyWorkSpan_events]
  exact family_workSpan oneColourFamily

theorem twoWave_historyWorkSpan :
    historyWorkSpan twoWaveHistory = ⟨2, 2⟩ := by
  rw [historyWorkSpan_events]
  apply WorkSpan.ext
  · exact coloring_work twoColouring
  · exact coloring_span twoColouring

theorem one_two_same_workGrade :
    workGrade oneWaveHistory = workGrade twoWaveHistory := by
  rw [workGrade, workGrade, oneWave_historyWorkSpan,
    twoWave_historyWorkSpan]

theorem one_two_different_workSpan :
    historyWorkSpan oneWaveHistory ≠ historyWorkSpan twoWaveHistory := by
  rw [oneWave_historyWorkSpan, twoWave_historyWorkSpan]
  intro equal
  have spans := congrArg WorkSpan.span equal
  norm_num at spans

/-- A scalar work grade does not reconstruct WorkSpan: equal work may have
different authorized parallel span. -/
theorem no_workSpan_recovery_from_workGrade :
    ¬ ∃ recover : Nat → WorkSpan,
        recover (workGrade oneWaveHistory) = historyWorkSpan oneWaveHistory ∧
          recover (workGrade twoWaveHistory) = historyWorkSpan twoWaveHistory := by
  rintro ⟨recover, recoversOne, recoversTwo⟩
  apply one_two_different_workSpan
  rw [← recoversOne, ← recoversTwo, one_two_same_workGrade]

@[simp] theorem oneWave_hasTwoFundedOccurrences :
    hasTwoFundedOccurrences oneWaveHistory = true := by
  unfold hasTwoFundedOccurrences workGrade
  rw [oneWave_historyWorkSpan]
  rfl

@[simp] theorem twoWave_hasTwoFundedOccurrences :
    hasTwoFundedOccurrences twoWaveHistory = true := by
  unfold hasTwoFundedOccurrences workGrade
  rw [twoWave_historyWorkSpan]
  rfl

/-- The authored truth bit is also not a cost schedule: the same true
observation accompanies distinct WorkSpan values. -/
theorem no_workSpan_recovery_from_truthBit :
    ¬ ∃ recover : Bool → WorkSpan,
        recover (hasTwoFundedOccurrences oneWaveHistory) =
            historyWorkSpan oneWaveHistory ∧
          recover (hasTwoFundedOccurrences twoWaveHistory) =
            historyWorkSpan twoWaveHistory := by
  rintro ⟨recover, recoversOne, recoversTwo⟩
  apply one_two_different_workSpan
  rw [← recoversOne, ← recoversTwo,
    oneWave_hasTwoFundedOccurrences, twoWave_hasTwoFundedOccurrences]

/-! ## Annotation is conservative; semantic filtering is authored -/

/-- A nonconstant candidate-local grade distinguishes the wave spending the
left receipt from other exact waves. -/
noncomputable def leftReceiptGrade (event : WaveEvent Ground) : Bool :=
  by
    classical
    exact if event.receipt = leftSingleton.receipt then true else false

theorem rightAfterLeft_receipt_eq_rightSingleton :
    rightAfterLeft.receipt = rightSingleton.receipt :=
  rfl

theorem rightAfterLeft_receipt_ne_leftSingleton :
    rightAfterLeft.receipt ≠ leftSingleton.receipt := by
  rw [rightAfterLeft_receipt_eq_rightSingleton]
  exact singleton_receipts_ne.symm

private abbrev leftWaveEvent : WaveEvent Ground :=
  ⟨source, leftSingleton.target,
    ⟨leftSingleton.receipt, ⟨leftSingleton.parallelStep⟩⟩⟩

private abbrev rightAfterLeftWaveEvent : WaveEvent Ground :=
  ⟨leftSingleton.target, rightAfterLeft.target,
    ⟨rightAfterLeft.receipt, ⟨rightAfterLeft.parallelStep⟩⟩⟩

@[simp] private theorem leftWaveEvent_receipt :
    leftWaveEvent.receipt = leftSingleton.receipt :=
  rfl

@[simp] private theorem rightAfterLeftWaveEvent_receipt :
    rightAfterLeftWaveEvent.receipt = rightAfterLeft.receipt :=
  rfl

/-- Attaching the concrete receipt grade retains both wave occurrences and
their multiplicity under ordinary occurrence-bag observation. -/
theorem leftReceiptGrade_annotation_is_conservative :
    (eraseGradeBagObserver (WaveEvent Ground) Bool).observe
        (annotateSchedule leftReceiptGrade forwardSchedule) =
      (Schedule.events forwardSchedule : Multiset (WaveEvent Ground)) :=
  annotateSchedule_erases_to_eventBag leftReceiptGrade forwardSchedule

/-- If the language explicitly authors the receipt grade as a semantic
filter, the published event bag changes.  The change comes from that authored
filter, not from annotation or scheduling. -/
theorem leftReceiptGrade_semantic_filter_changes_eventBag :
    ((supportByGrade id
        (annotateSchedule leftReceiptGrade forwardSchedule) :
          List (WaveEvent Ground)) : Multiset (WaveEvent Ground)) ≠
      (Schedule.events forwardSchedule : Multiset (WaveEvent Ground)) := by
  have filteredLength :
      (supportByGrade id
          (annotateSchedule leftReceiptGrade forwardSchedule)).length = 1 := by
    rw [filterAnnotatedSchedule_eq_authoredSemanticFilter]
    change
      (semanticFilterByGrade leftReceiptGrade id
        [leftWaveEvent, rightAfterLeftWaveEvent]).length = 1
    simp [semanticFilterByGrade, leftReceiptGrade,
      rightAfterLeft_receipt_ne_leftSingleton]
  have originalLength : (Schedule.events forwardSchedule).length = 2 :=
    rfl
  intro equalBags
  have equalCards := congrArg Multiset.card equalBags
  change
    (supportByGrade id
        (annotateSchedule leftReceiptGrade forwardSchedule)).length =
      (Schedule.events forwardSchedule).length at equalCards
  rw [filteredLength, originalLength] at equalCards
  omega

#print axioms no_exact_history_recovery_from_workSpan
#print axioms no_firstReceipt_recovery_from_workSpan
#print axioms one_two_same_workGrade
#print axioms one_two_different_workSpan
#print axioms no_workSpan_recovery_from_workGrade
#print axioms oneWave_hasTwoFundedOccurrences
#print axioms twoWave_hasTwoFundedOccurrences
#print axioms no_workSpan_recovery_from_truthBit
#print axioms leftReceiptGrade_annotation_is_conservative
#print axioms leftReceiptGrade_semantic_filter_changes_eventBag

end

end Examples

end Mettapedia.Languages.MeTTa.Prime.NativeCost1ValuationAdequacy
