import Mettapedia.Examples.Compression.PreparedSourceControls

/-!
# Literal E2 jobs and complete entry-worker controls

The literal fixtures are independent of the formatter. Valid, empty, duplicate,
malformed and large-announced-length jobs exercise the actual reader. Compiled
source witnesses then exercise the complete parser/preparation/checking path.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Mettapedia.Examples.Compression.E2EntryControls

open Turing StateTransition KolmogorovComplexity
open Mettapedia.Computability Mettapedia.Machines WordTemplateMachine
open Mettapedia.UniversalAI.TimeBoundedAIXI
open FeatureTheory.DyadicSearch

attribute [local implicit_reducible] E2PairMachine.machine BinaryCountdownMachine.machine

abbrev resultEquality : DecidableEq (E2PairMachine.machine.Γ E2PairMachine.machine.k₁) :=
  inferInstanceAs (DecidableEq (Option Bool))
abbrev phaseEquality : DecidableEq E2PairMachine.machine.Λ := inferInstanceAs (DecidableEq E2PairMachine.Phase)
attribute [local instance] resultEquality phaseEquality

def literalGood : List (Option Bool) :=
  [some true, some true, some false, some true, some false, some true, some false,
    some false, some true, some false, some true, some false, none, some true, some false, none]

theorem literal_job_is_the_existing_record : literalGood = E2PairMachine.job [] [false] [true, false] := by decide_cbv

theorem the_parser_needs_the_final_publication_transition :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => literalGood)).searcher []).result 41 = none := by decide

theorem literal_e2_job_executes_in_the_actual_reader :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => literalGood)).searcher []).result 42 =
      some [none, some false, none, some true, some false, none] := by decide

theorem empty_candidate_fields_keep_all_three_boundaries :
    ((FiniteStackWorker.worker E2PairMachine.machine
      (fun _word => [some true, some true, some false, some true, some false, some true, some false,
        some false, some false, none, none])).searcher []).result 29 = some [none, none, none] := by decide

theorem original_order_and_duplicate_fields_are_preserved :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => E2PairMachine.job [true, false] [true, false] [false, true])).searcher
      []).result (8 * ((E2PairMachine.job [true, false] [true, false] [false, true]).length + 1)) =
      some (Indexed.frame [[true, false], [true, false], [false, true]]) :=
  FiniteStackWorker.complete E2PairMachine.machine (fun _word => E2PairMachine.job [true, false] [true, false] [false, true]) [] _ _
    (E2PairMachine.outputs [true, false] [true, false] [false, true])

theorem wrong_count_header_never_publishes_in_the_control :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => some false :: literalGood.tail)).searcher []).result 100 = none := by decide

def missingCandidateBoundary : List (Option Bool) :=
  [some true, some true, some false, some true, some false, some true, some false,
    some false, some true, some false, some true, some false, some true, some false, none]

theorem a_missing_candidate_boundary_is_not_source_data :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => missingCandidateBoundary)).searcher []).result 100 = none := by decide

theorem a_missing_original_boundary_is_not_end_of_input :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => literalGood.dropLast)).searcher []).result 100 = none := by decide

theorem an_extra_original_field_is_not_ignored :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => literalGood ++ [none])).searcher []).result 100 = none := by decide

def noncanonicalHeader : List (Option Bool) :=
  (E2PairMachine.countHeader ++ [true, false, false, false]).map some ++ [none, none]

theorem a_redundant_zero_length_header_is_refused :
    ((FiniteStackWorker.worker E2PairMachine.machine (fun _word => noncanonicalHeader)).searcher []).result 100 = none := by decide

def enormousLength : List Bool := E2PairMachine.countHeader ++
  (List.replicate 65 true ++ false :: true :: List.replicate 64 false)
def enormousJob : List (Option Bool) := enormousLength.map some ++ [none, none]

theorem a_huge_announced_length_reaches_rejection_without_payload :
    let state := StepCounting.runFor E2PairMachine.machine.step 300 (initList E2PairMachine.machine enormousJob)
    state.l = some .reject ∧ (state.stk (.inl false)).length = 65 ∧
      (state.stk (.inl true)).length = 0 ∧ (state.stk (.inr .header)).length = 0 := by
  dsimp only
  decide

abbrev source := PreparedSourceControls.source

theorem the_complete_entry_accepts_a_compiled_source_witness :
    ((FiniteStackWorker.worker (ICEntryCheck.machine source)
      (fun _word => ICEntryCheck.input (pairCode [] [false]) [true, false])).searcher []).result 8512 =
      some (FramedCompressionCheck.response true [] [false]) := by
  have run := ICEntryCheck.outputs source PhysicalCheckControls.extract_run PhysicalCheckControls.reconstruct_run
  have observed := FiniteStackWorker.complete (ICEntryCheck.machine source)
    (fun _word => ICEntryCheck.input (pairCode [] [false]) [true, false]) [] _ _ run
  simpa [ICPhysicalCheck.result, FramedCompressionCheck.verdict, ICEntryCheck.wordCost,
    PreparedSourceControls.the_candidate_uses_the_complete_twelve_bit_pair_record] using observed

theorem code_extensions_never_complete_the_entry (budget : Nat) :
    ((FiniteStackWorker.worker (ICEntryCheck.machine source)
      (fun _word => ICEntryCheck.input (pairCode [] [false] ++ [true]) [true, false])).searcher []).result budget = none := by
  apply ICEntryCheck.no_publication_if_candidate_invalid
  have invalid := pairCodeTest_rejects_extension [] [false] [true] (by decide)
  change (parsePair (pairCode [] [false] ++ [true])).isSome = false at invalid
  cases parsed : parsePair (pairCode [] [false] ++ [true]) with
  | none => rfl
  | some fields => simp [parsed] at invalid

theorem complete_entry_publication_has_the_normalized_source_bound :
    ((PreparedICSearch.entryWorker source [true, false]).searcher (pairCode [] [false])).result
      (ICSourceClock.entryFactor source * (266 + 284 + 1)) = some ([], [false]) :=
  PreparedICSearch.entry_complete_from_source_clocks source PreparedSourceControls.step 266 284
    PreparedSourceControls.normalized_extract PreparedSourceControls.normalized_reconstruct

theorem every_finite_entry_observation_has_reconstruction_and_strict_decrease
    (count phase : Nat) {word residual feature : BinString}
    (emitted : (word, (residual, feature)) ∈ PrefixPortfolio.observations (PreparedICSearch.entryWorker source [true, false])
      pairCodeTest phase (PrefixPortfolio.runFrom pairCodeTest (PreparedICSearch.entryWorker source [true, false]).step 0 count
        (PreparedICSearch.entryWorker source [true, false]).initial)) :
    ∃ descriptive, parsePair word = some (descriptive, feature) ∧
      residual ∈ PhysicalCheckControls.model descriptive [true, false] ∧
      [true, false] ∈ PhysicalCheckControls.model feature residual ∧ feature.length + residual.length < 2 := by
  simpa using PreparedICSearch.entry_emitted_reconstructs source [true, false] count phase emitted

end Mettapedia.Examples.Compression.E2EntryControls
