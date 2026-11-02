import Mettapedia.Computability.KolmogorovComplexity.FeatureDyadicSearch
import Mettapedia.Examples.Compression.FeatureGlobalSearchControls

/-!
# Dyadic allocation, real-machine and codec controls

A shorter divergent worker competes with two terminating workers. Retained
execution reaches both, whereas resetting a worker changes the result. A
compiled successor machine needs nine actual four-stack transitions; its
initial input cannot be mistaken for a completed answer. Noncanonical output
codes and extra output values are refused.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureDyadicSearchControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open KolmogorovComplexity.FeatureTheory.DyadicSearch
open Mettapedia.Machines
open Mettapedia.UniversalAI.TimeBoundedAIXI

def controlCode (word : BinString) : Bool :=
  decide (word = [false] ∨ word = [true, false] ∨ word = [true, true])

theorem controlCode_prefixFree : PrefixFree {word | controlCode word = true} := by
  intro first one second two different isPrefix
  change decide (first = [false] ∨ first = [true, false] ∨ first = [true, true]) = true at one
  change decide (second = [false] ∨ second = [true, false] ∨ second = [true, true]) = true at two
  simp only [decide_eq_true_eq] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl <;>
    simp_all [List.prefix_iff_eq_take]

def counter : PrefixPortfolio.Worker Nat Nat where
  initial _word := 0
  step word state := if word = [false] ∨ state < 3 then some (state + 1) else none
  read word state := if word ≠ [false] ∧ 3 ≤ state then some state else none
  stopped word state answer found := by
    split at found
    · rename_i terminal
      simp [terminal.1, Nat.not_lt.mpr terminal.2]
    · cases found

theorem divergent_worker_does_not_hide_later_answers :
    PrefixPortfolio.observations counter controlCode 3
      (PrefixPortfolio.runFrom controlCode counter.step 0 4 counter.initial) =
        [([true, false], 3), ([true, true], 3)] := by decide

theorem divergent_worker_keeps_its_own_state :
    PrefixPortfolio.runFrom controlCode counter.step 0 4 counter.initial [false] = 7 := by decide

theorem resetting_changes_a_worker :
    PrefixPortfolio.runPhase controlCode counter.step 3 counter.initial [true, false] = 2 ∧
      PrefixPortfolio.runFrom controlCode counter.step 0 4 counter.initial [true, false] = 3 := by decide

theorem sliced_execution_keeps_the_phase_clock :
    PrefixPortfolio.runFrom controlCode counter.step 0 4 counter.initial =
      PrefixPortfolio.runFrom controlCode counter.step 1 3
        (PrefixPortfolio.runFrom controlCode counter.step 0 1 counter.initial) :=
  PrefixPortfolio.runFrom_add controlCode counter.step 1 3 0 counter.initial

theorem strict_and_inclusive_boundary_differ :
    [true, false] ∈ PrefixPortfolio.words controlCode 2 ∧
      [true, false] ∉ PrefixPortfolio.strictWords controlCode 2 ∧
      PrefixPortfolio.phaseCost controlCode 2 = 4 ∧
      PrefixPortfolio.strictPhaseCost controlCode 3 = 8 := by decide

def overlappingCode (word : BinString) : Bool := decide (word = [] ∨ word = [false])

theorem dropping_prefix_freeness_breaks_the_budget :
    PrefixPortfolio.phaseCost overlappingCode 1 = 3 ∧ ¬ (3 ≤ 2 ^ (1 : Nat)) := by decide

theorem framed_pair_is_not_raw_concatenation :
    (pairCode [true] [false]).length = 15 ∧ ([true] ++ [false] : BinString).length = 2 := by decide

theorem pair_fields_round_trip : parsePair (pairCode [true] [false]) = some ([true], [false]) :=
  parsePair_pairCode _ _

theorem pair_extension_is_refused : pairCodeTest (pairCode [true] [false] ++ [false]) = false :=
  pairCodeTest_rejects_extension _ _ _ (by decide)

theorem wrong_record_arity_is_refused :
    parsePair (Mettapedia.Algorithms.Compression.Framing.encode [[true]]) = none := by decide

theorem nonshrinking_completed_pair_is_rejected :
    autoencoder literalResidualAlgorithm (pairCode [] fourTrue) fourTrue = Part.some none := by
  simp [autoencoder, parsePair_pairCode, Part.coe_some, executePair, literalResidualAlgorithm, fourTrue]

theorem wrong_reconstruction_is_rejected :
    autoencoder literalResidualAlgorithm (pairCode [] [false]) fourTrue = Part.some none := by
  simp [autoencoder, parsePair_pairCode, Part.coe_some, executePair, literalResidualAlgorithm, fourTrue]

def successorWorker := PrefixMachine.worker (α := Nat) Turing.ToPartrec.Code.succ (fun _ => 0)

theorem successor_not_finished_at_eight : (successorWorker.searcher []).result 8 = none := by decide

theorem successor_finished_at_nine : (successorWorker.searcher []).result 9 = some 1 := by decide

theorem filtered_halt_is_not_a_candidate :
    (((successorWorker.filterMap (fun value => if value = 1 then none else some value)).searcher []).result 9) = none := by
  decide

theorem initial_tape_is_not_an_answer : PrefixMachine.readOutput (α := Nat)
    (Turing.PartrecToTM2.init Turing.ToPartrec.Code.succ [0]) = none := by decide

inductive Mark where
  | red
  | blue
  deriving DecidableEq

instance : Encodable Mark where
  encode mark := match mark with | .red => 0 | .blue => 1
  decode number := some (if number % 2 = 0 then .red else .blue)
  encodek mark := by cases mark <;> rfl

theorem ordinary_decode_is_not_a_canonicality_proof :
    Encodable.decode (α := Mark) 2 = some .red ∧ Encodable.encode Mark.red ≠ 2 := by decide

theorem canonical_machine_output_is_accepted :
    PrefixMachine.readOutput (α := Mark) (Turing.PartrecToTM2.halt [0]) = some .red := by decide

theorem noncanonical_machine_output_is_refused :
    PrefixMachine.readOutput (α := Mark) (Turing.PartrecToTM2.halt [2]) = none := by decide

theorem extra_machine_output_is_refused :
    PrefixMachine.readOutput (α := Nat) (Turing.PartrecToTM2.halt [0, 1]) = none := by decide

theorem redundant_binary_machine_output_is_refused :
    PrefixMachine.readSingleton [.bit0, .cons] = none := by decide

theorem finite_compression_has_an_actual_machine_search :
    ∃ code : Turing.ToPartrec.Code, ∃ work,
      let word := pairCode [true] [false]
      let phase := word.length + Nat.clog 2 work
      let worker := checkedWorker code fourTrue
      (word, ([], [false])) ∈ PrefixPortfolio.observations worker pairCodeTest phase
        (PrefixPortfolio.runFrom pairCodeTest worker.step 0 (phase + 1) worker.initial) ∧
      (PrefixPortfolio.family pairCodeTest pairCodeTest_prefixFree worker.searcher).cost (phase + 1) ≤
        4 * 2 ^ word.length * max work 1 := by
  obtain ⟨code, _codeSpec, finds⟩ := exists_transition_bounded_search FeatureGlobalSearchControls.finite_machine_effective
  obtain ⟨work, emitted⟩ := finds fourTrue finiteCompressionStep
  exact ⟨code, work, emitted⟩

#print axioms controlCode_prefixFree
#print axioms divergent_worker_does_not_hide_later_answers
#print axioms divergent_worker_keeps_its_own_state
#print axioms resetting_changes_a_worker
#print axioms sliced_execution_keeps_the_phase_clock
#print axioms strict_and_inclusive_boundary_differ
#print axioms dropping_prefix_freeness_breaks_the_budget
#print axioms framed_pair_is_not_raw_concatenation
#print axioms pair_fields_round_trip
#print axioms pair_extension_is_refused
#print axioms wrong_record_arity_is_refused
#print axioms nonshrinking_completed_pair_is_rejected
#print axioms wrong_reconstruction_is_rejected
#print axioms successor_not_finished_at_eight
#print axioms successor_finished_at_nine
#print axioms filtered_halt_is_not_a_candidate
#print axioms initial_tape_is_not_an_answer
#print axioms ordinary_decode_is_not_a_canonicality_proof
#print axioms canonical_machine_output_is_accepted
#print axioms noncanonical_machine_output_is_refused
#print axioms extra_machine_output_is_refused
#print axioms redundant_binary_machine_output_is_refused
#print axioms finite_compression_has_an_actual_machine_search

end Mettapedia.Examples.Compression.FeatureDyadicSearchControls
