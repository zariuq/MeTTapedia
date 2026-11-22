import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQueryExecution
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceAbsenceControls

/-! # Complete, paused and stale source-query controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Query.Controls

open Mettapedia.Machines
open AbsenceControls Commutative

def before : List Occurrence := [(message .a, 0), (acknowledgement .b, 1)]
def after : List Occurrence := before ++ [(acknowledgement .a, 2)]
def duplicateMessages : List Occurrence := [(message .a, 0), (message .a, 2)]
def scan (contents : List Occurrence) := scanList label contents

def packet (source : SourceList ℕ Value Pattern) (contents : List Occurrence) (fuel : Nat) :=
  Execution.execute layer matcher label (scan contents) [] source empty fuel

def answerCount (source : SourceList ℕ Value Pattern) (contents : List Occurrence)
    (fuel : Nat) : Option Nat :=
  (Cursor.ReadOnlyQuery.completed? (scan contents) (packet source contents fuel).2).map
    fun observation => observation.answer.length

theorem actual_store_scanner_complete :
    Complete label before.toFinset (scan before) ∧
      Complete label after.toFinset (scan after) := by
  exact ⟨scanList_complete label before (by decide), scanList_complete label after (by decide)⟩

/-- A bounded query that has inspected only the message region is unfinished,
even when its current answer prefix contains no joined result. -/
theorem partial_query_is_not_absence :
    answerCount joined before 0 = none ∧ answerCount joined before 1 = none ∧
      answerCount joined before 2 = none ∧ answerCount joined before 3 = some 0 := by
  decide +kernel

theorem correlated_join_arrival :
    answerCount joined before 3 = some 0 ∧ answerCount joined after 3 = some 1 ∧
      answerCount (.absent joined .done) before 5 = some 1 ∧
      answerCount (.absent joined .done) after 3 = some 0 := by
  decide +kernel

/-- The actual query path reads only acknowledgements for the selected
message. A nonjoining acknowledgement is not a dependency of that path. -/
theorem adaptive_dependency_is_bound :
    ((ReadOnlyQuery.run (scan before) (compile layer matcher label [] joined empty)).reads.map
      Prod.snd) = [[(message .a, 0)], []] ∧
      ReadOnlyQuery.checkReads (scan (before ++ [(acknowledgement .b, 3)]))
        (ReadOnlyQuery.run (scan before) (compile layer matcher label [] joined empty)).reads = true := by
  decide +kernel

/-- The source absence row additionally retains its declared completeness
regions. Continued absence does not justify that stronger old footprint. -/
theorem absence_row_retains_full_footprint :
    answerCount (.absent joined .done) (before ++ [(acknowledgement .b, 3)]) 5 = some 1 ∧
      ReadOnlyQuery.checkReads (scan (before ++ [(acknowledgement .b, 3)]))
        (ReadOnlyQuery.run (scan before)
          (compile layer matcher label [] (.absent joined .done) empty)).reads = false := by
  decide +kernel

def oneRead : SourceList ℕ Value Pattern := .cons (.read messagePattern) .done

/-- Empty conjunction and vacuous aggregation both have a row; they are
different from a complete query returning no rows. -/
theorem vacuous_rows_are_present :
    answerCount .done [] 1 = some 1 ∧
      answerCount (.absent .done .done) [] 1 = some 0 ∧
      answerCount (.every oneRead) [] 3 = some 1 ∧
      answerCount (.absent (.every oneRead) .done) [] 3 = some 0 := by
  decide +kernel

def repeatedTake : SourceList ℕ Value Pattern :=
  .cons (.take messagePattern) (.cons (.take messagePattern) .done)

/-- Absence concerns source matches, before the separate linear-admission
check. A conflicting resource use does not make a matching row disappear. -/
theorem nonlinear_match_is_still_a_row :
    answerCount repeatedTake [(message .a, 0)] 3 = some 1 ∧
      answerCount (.absent repeatedTake .done) [(message .a, 0)] 3 = some 0 ∧
      ∀ row ∈ rows layer matcher label {(message .a, 0)} [] repeatedTake empty,
        ¬ (footprintOf row.2).Linear := by
  decide +kernel

def sharedTake : SourceList ℕ Value Pattern :=
  .cons (.letBind (.var 0) (fun _ => [.leaf .a, .leaf .b]))
    (.cons (.take (.node .message (.leaf .a) (.leaf .nil))) .done)

/-- Every filters each contributing row for linearity. A second every
therefore filters a nonlinear aggregate as one row and may be vacuous. -/
theorem nested_every_filters_the_aggregate :
    answerCount (.every sharedTake) [(message .a, 0)] 4 = some 1 ∧
      (everyFootprint layer matcher label {(message .a, 0)} [] sharedTake empty).takes.card = 2 ∧
      ¬ (everyFootprint layer matcher label {(message .a, 0)} [] sharedTake empty).Linear ∧
      (everyFootprint layer matcher label {(message .a, 0)} [] (.every sharedTake) empty).takes = 0 := by
  decide +kernel

def pureValues : SourceList ℕ Value Pattern :=
  .cons (.letBind (.var 0) (fun _ => [.leaf .a, .leaf .a])) .done

theorem computed_values_keep_positions :
    answerCount pureValues [] 1 = some 2 ∧
      ((ReadOnlyQuery.run (scan []) (compile layer matcher label [] pureValues empty)).answer.map
        fun row => row.2.filterMap fun pick => match pick with
          | .result index => some index
          | _ => none) = [[0], [1]] ∧
      answerCount (.absent pureValues .done) [] 1 = some 0 := by
  decide +kernel

theorem equal_labels_keep_occurrences :
    answerCount oneRead duplicateMessages 2 = some 2 ∧
      ((ReadOnlyQuery.run (scan duplicateMessages)
        (compile layer matcher label [] oneRead empty)).answer.map
        fun row => row.2.filterMap fun pick => match pick with
          | .keep occurrence => some occurrence
          | _ => none) = [[(message .a, 0)], [(message .a, 2)]] ∧
      answerCount (.cons (.unique .read messagePattern) .done) duplicateMessages 2 = some 0 := by
  decide +kernel

/-- The row-bag observation forgets enumeration order. The read certificate
does not: it protects the actual continuation and ordered answer stream. -/
theorem bag_agreement_does_not_validate_reordering :
    answerCount oneRead duplicateMessages 2 = some 2 ∧
      answerCount oneRead duplicateMessages.reverse 2 = some 2 ∧
      ReadOnlyQuery.checkReads (scan duplicateMessages.reverse)
        (ReadOnlyQuery.run (scan duplicateMessages)
          (compile layer matcher label [] oneRead empty)).reads = false := by
  decide +kernel

/-- A truncated provider can fabricate an empty answer. It violates the
scanner's explicit completeness premise, despite the cursor completing. -/
theorem omitted_region_reply_is_not_complete :
    (ReadOnlyQuery.run (fun _ => ([] : List Occurrence))
      (compile layer matcher label [] joined empty)).answer.length = 0 ∧
      answerCount joined after 3 = some 1 ∧
      ¬ Complete label after.toFinset (fun _ => ([] : List Occurrence)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro complete
  have impossible := complete.length (fun _ => true)
  norm_num [after, before, regionOf, label, message, acknowledgement] at impossible

def countsTwo : SourceList ℕ Value Pattern :=
  .cons (.collect .read messagePattern (.var 0)
    (fun values => if values.card = 2 then .leaf .a else .leaf .b)) .done

theorem aggregate_counts_equal_labels_twice :
    ((ReadOnlyQuery.run (scan duplicateMessages)
      (compile layer matcher label [] countsTwo empty)).answer.map fun row => row.1 0) =
        [some (.leaf .a)] := by
  decide +kernel

def commutes : Symbol → Bool := fun s => decide (s = .message)

/-- One occurrence can have two genuinely different matching alternatives. -/
theorem equational_alternatives_retained :
    ((ReadOnlyQuery.run (scan [(message .a, 0)])
      (compile (termLayer commutes) (cmatch commutes) label []
        (.cons (.read (.node .message (.var 0) (.var 1))) .done) empty)).answer.map
        fun row => (row.1 0, row.1 1)) =
      [(some (.leaf .a), some (.leaf .nil)), (some (.leaf .nil), some (.leaf .a))] := by
  decide +kernel

def resumedCount (contents : List Occurrence) : Option Nat :=
  match Cursor.ReadOnlyQuery.resumeValidated (scan before) (scan contents) 2 (packet joined before 1) with
  | .error _ => none
  | .ok result => (Cursor.ReadOnlyQuery.completed? (scan contents) result.2).map
      fun observation => observation.answer.length

/-- An unread dependency may change. The earned message read is retained,
and the resumed acknowledgement read uses the newly validated view. -/
theorem resume_sees_unread_arrival :
    answerCount joined before 3 = some 0 ∧ resumedCount after = some 1 ∧
      (packet joined before 1).1 = 1 ∧
      (Cursor.ReadOnlyQuery.recorded (scan before) (packet joined before 1).2).length = 1 := by
  decide +kernel

/-- A changed performed read refuses resumption and returns the original
saved packet, including its continuation and already paid work. -/
theorem changed_prefix_retains_refused_packet :
    Cursor.ReadOnlyQuery.resumeValidated (scan before)
      (scan [(message .b, 0), (acknowledgement .b, 1)]) 2 (packet joined before 1) =
        .error (packet joined before 1) := by
  apply Cursor.ReadOnlyQuery.resumeValidated_refused
  decide +kernel

theorem completed_negative_result_can_go_stale :
    ReadOnlyQuery.checkReads (scan after)
      (Cursor.ReadOnlyQuery.recorded (scan before) (packet joined before 3).2) = false := by
  decide +kernel

#print axioms partial_query_is_not_absence
#print axioms equational_alternatives_retained
#print axioms changed_prefix_retains_refused_packet

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Query.Controls
