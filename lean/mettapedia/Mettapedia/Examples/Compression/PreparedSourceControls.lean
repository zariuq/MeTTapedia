import Mettapedia.Machines.PreparedICSearch
import Mettapedia.Computability.BinaryCountdownMachine
import Mettapedia.Examples.Compression.PhysicalCheckControls

/-!
# Prepared tasks, normalized source clocks and countdown controls

Actual compiled-source witnesses exercise preparation and retained publication.
The countdown controls include zero, a wide borrow and a multi-debit potential
identity. None of these controls supplies native speedup or held-out evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Mettapedia.Examples.Compression.PreparedSourceControls

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability Mettapedia.Machines WordTemplateMachine
open Mettapedia.UniversalAI.TimeBoundedAIXI
open FeatureTheory.DyadicSearch

abbrev counterEquality : DecidableEq (BinaryCountdownMachine.machine.Γ BinaryCountdownMachine.machine.k₁) :=
  inferInstanceAs (DecidableEq Bool)
attribute [local instance] counterEquality

theorem counter_needs_its_final_flag_transition :
    ((FiniteStackWorker.worker BinaryCountdownMachine.machine (fun _word => [true, true, true])).searcher []).result 1 = none := by decide

theorem one_debit_retains_counter_width_and_reports_success :
    ((FiniteStackWorker.worker BinaryCountdownMachine.machine (fun _word => [true, true, true])).searcher []).result 2 =
      some [true, false, true, true] := by decide

theorem zero_is_completed_underflow_not_wraparound :
    ((FiniteStackWorker.worker BinaryCountdownMachine.machine (fun _word => [false, false])).searcher []).result 6 =
      some [false, false, false] := by decide

theorem zero_still_pays_its_scan_and_restoration :
    ((FiniteStackWorker.worker BinaryCountdownMachine.machine (fun _word => [false, false])).searcher []).result 5 = none := by decide

theorem a_wide_borrow_uses_header_sized_storage :
    ((FiniteStackWorker.worker BinaryCountdownMachine.machine
      (fun _word => List.replicate 64 false ++ [true])).searcher []).result 130 =
      some (true :: (List.replicate 64 true ++ [false])) ∧
      ∀ budget, BinaryCountdownMachine.stackCells
        (StepCounting.runFor BinaryCountdownMachine.machine.step budget
          (initList BinaryCountdownMachine.machine (List.replicate 64 false ++ [true]))) ≤ 66 := by
  constructor
  · decide
  · intro budget
    have path := StepCounting.reaches_runFor BinaryCountdownMachine.machine.step budget
      (initList BinaryCountdownMachine.machine (List.replicate 64 false ++ [true]))
    simpa using BinaryCountdownMachine.reached_stack_cells_le (List.replicate 64 false ++ [true]) _ path

theorem smallChain : BinaryCountdownMachine.Chain [true, true] [false, false] 3 11 :=
  .step (middle := [false, true]) (by decide)
    (.step (middle := [true, false]) (by decide)
      (.step (middle := [false, false]) (by decide) (.refl _)))

theorem three_debits_have_the_charged_potential_identity :
    11 + 2 * BinaryCountdownMachine.zeros [false, false] =
      2 * BinaryCountdownMachine.zeros [true, true] + 5 * 3 := smallChain.amortized

theorem counter_value_and_width_are_independent_of_the_borrow_cost :
    BinaryStackArithmetic.value [true, true] = BinaryStackArithmetic.value [false, false] + 3 ∧
      (BinaryCountdownMachine.resume 0 [false, true]).length = ([false, true] : List Bool).length + 1 :=
  ⟨smallChain.value, BinaryCountdownMachine.resume_length _⟩

theorem pushing_the_big_endian_length_header_gives_the_counter_word (length : Nat) :
    (binaryBits length).reverse = BinaryStackArithmetic.naturalBits length := by
  simp [binaryBits, BinaryStackArithmetic.naturalBits, List.map_reverse]

theorem the_header_counter_has_the_exact_payload_length (length : Nat) :
    BinaryStackArithmetic.value (binaryBits length).reverse = length := by
  rw [pushing_the_big_endian_length_header_gives_the_counter_word, BinaryStackArithmetic.naturalBits_value]

theorem reading_the_header_with_the_wrong_endianness_changes_the_count :
    BinaryStackArithmetic.value (binaryBits 2) = 1 := by decide_cbv

theorem preparation_keeps_order_empty_fields_and_duplicate_occurrences :
    ((FiniteStackWorker.worker ICPreparedCheck.preparation
      (fun _word => Indexed.frame [[], [true, false, true], [true, false, true], [], [false]])).searcher []).result 134 =
      some (Indexed.frame [trList [0], trList [12], trList [12], trList [0], trList [1]]) := by
  have run := ICPreparedCheck.prepare_words [[], [true, false, true], [true, false, true], [], [false]]
  have observed := FiniteStackWorker.complete ICPreparedCheck.preparation
    (fun _word => Indexed.frame [[], [true, false, true], [true, false, true], [], [false]]) [] _ _ run
  simpa [NaturalWordEncoding.encode, Indexed.frame] using observed

abbrev source := PhysicalCheckControls.presentation

def normalized_extract : TM2OutputsInTime (ICSourceClock.machine source)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec [] [true, false])
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec [])) 266 :=
  ICSourceClock.outputs source PhysicalCheckControls.extract_run

def normalized_reconstruct : TM2OutputsInTime (ICSourceClock.machine source)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec [false] [])
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec [true, false])) 284 :=
  ICSourceClock.outputs source PhysicalCheckControls.reconstruct_run

theorem normalized_source_really_has_distinct_ports :
    (ICSourceClock.machine source).k₀ ≠ (ICSourceClock.machine source).k₁ := ICSourceClock.distinct_ports source

theorem normalized_source_recovers_the_original_computation :
    Nonempty (TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec [] [true, false])
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec [])) 266) :=
  ICSourceClock.reflects_outputs source normalized_extract

theorem the_prepared_body_publishes_from_original_words :
    ((FiniteStackWorker.worker (ICPreparedCheck.machine source)
      (fun _word => ICPreparedCheck.input [] [false] [true, false])).searcher []).result 4544 =
      some (FramedCompressionCheck.response true [] [false]) := by
  have run := ICPreparedCheck.outputs source PhysicalCheckControls.extract_run PhysicalCheckControls.reconstruct_run
  have observed := FiniteStackWorker.complete (ICPreparedCheck.machine source)
    (fun _word => ICPreparedCheck.input [] [false] [true, false]) [] _ _ run
  simpa [ICPhysicalCheck.result, FramedCompressionCheck.verdict, ICPreparedCheck.wordCost, ICPreparedCheck.input,
    Indexed.frame] using observed

theorem prepared_publication_is_bounded_by_the_normalized_source_clock :
    ((FiniteStackWorker.worker (ICPreparedCheck.machine source)
      (fun _word => ICPreparedCheck.input [] [false] [true, false])).searcher []).result
      (ICSourceClock.factor source * (266 + 284 + 1)) =
        some (FramedCompressionCheck.response true [] [false]) := by
  have run := ICSourceClock.prepared_outputs source normalized_extract normalized_reconstruct
  have observed := FiniteStackWorker.complete (ICPreparedCheck.machine source)
    (fun _word => ICPreparedCheck.input [] [false] [true, false]) [] _ _ run
  simpa [ICPhysicalCheck.result, FramedCompressionCheck.verdict] using observed

def step : CompressionStep PhysicalCheckControls.model [true, false] where
  featureProgram := [false]
  descriptiveProgram := []
  residual := []
  extracts := ConditionalSourceMachine.sound source PhysicalCheckControls.extract_run
  reconstructs := ConditionalSourceMachine.sound source PhysicalCheckControls.reconstruct_run
  compresses := by decide

theorem the_candidate_uses_the_complete_twelve_bit_pair_record : (pairCode [] [false]).length = 12 := by decide_cbv

theorem admitted_candidate_publication_uses_the_actual_prepared_worker :
    ((PreparedICSearch.worker source [true, false]).searcher (pairCode [] [false])).result
      (ICSourceClock.factor source * (266 + 284 + 1)) = some ([], [false]) :=
  PreparedICSearch.complete_from_source_clocks source step 266 284 normalized_extract normalized_reconstruct

theorem extensions_are_outside_the_declared_candidate_region : pairCodeTest (pairCode [] [false] ++ [true]) = false :=
  pairCodeTest_rejects_extension [] [false] [true] (by decide)

end Mettapedia.Examples.Compression.PreparedSourceControls
