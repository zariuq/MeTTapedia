import Mettapedia.Machines.ICPhysicalCheck

/-!
# Counted physical checking controls

The compiled source fixture has an independently specified conditional
meaning. A successful local compression and a wrong reconstruction exercise
the entire physical body. These finite controls do not assert universal
shortest features, native CeTTa speedups or held-out program-family utility.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Mettapedia.Examples.Compression.PhysicalCheckControls

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability Mettapedia.Machines WordTemplateMachine
open Mettapedia.UniversalAI.TimeBoundedAIXI

attribute [local implicit_reducible] FramedCompressionCheck.machine

abbrev checkEquality : DecidableEq (FramedCompressionCheck.machine.Γ FramedCompressionCheck.machine.k₁) :=
  inferInstanceAs (DecidableEq (Option Bool))
attribute [local instance] checkEquality

theorem the_last_checking_transition_is_required :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => FramedCompressionCheck.packet [true] [] [] [true])).searcher []).result 14 = none := by decide

theorem a_strict_reconstructing_candidate_is_published_with_both_empty_fields :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => FramedCompressionCheck.packet [true] [] [] [true])).searcher []).result 15 =
      some [some true, none, none] := by decide

theorem equal_word_cost_is_a_completed_refusal :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => FramedCompressionCheck.packet [true, false] [true] [false] [true, false])).searcher []).result 100 =
      some (FramedCompressionCheck.response false [false] [true]) := by decide

theorem wrong_reconstruction_refuses_even_when_shorter :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => FramedCompressionCheck.packet [false] [] [] [true])).searcher []).result 100 =
      some (FramedCompressionCheck.response false [] []) := by decide

theorem the_empty_original_has_no_strict_compression :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => FramedCompressionCheck.packet [] [] [] [])).searcher []).result 100 =
      some (FramedCompressionCheck.response false [] []) := by decide

theorem missing_the_final_delimiter_refuses :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => [some true, none, none, none, some true])).searcher []).result 100 =
      some (FramedCompressionCheck.response false [] []) := by decide

theorem an_extra_empty_field_is_not_ignored :
    ((FiniteStackWorker.worker FramedCompressionCheck.machine
      (fun _word => FramedCompressionCheck.packet [true] [] [] [true] ++ [none])).searcher []).result 100 =
      some (FramedCompressionCheck.response false [] []) := by decide

theorem stored_natural_field_lengths_do_not_determine_original_word_lengths :
    (trList [2]).length = (trList [3]).length ∧
      ([true] : List Bool).length < ([false, false] : List Bool).length := by decide

theorem physical_decoding_recovers_the_shorter_original_word :
    ((FiniteStackWorker.worker NaturalWordDecodingMachine.machine (fun _word => trList [2])).searcher []).result 48 =
      some [true] := by
  have observed := FiniteStackWorker.complete NaturalWordDecodingMachine.machine
    (fun _word => trList [NaturalWordEncoding.encode [true]]) [] [true] _
    (NaturalWordDecodingMachine.outputs [true])
  simpa [NaturalWordEncoding.encode] using observed

theorem physical_decoding_recovers_the_longer_original_word :
    ((FiniteStackWorker.worker NaturalWordDecodingMachine.machine (fun _word => trList [3])).searcher []).result 72 =
      some [false, false] := by
  have observed := FiniteStackWorker.complete NaturalWordDecodingMachine.machine
    (fun _word => trList [NaturalWordEncoding.encode [false, false]]) [] [false, false] _
    (NaturalWordDecodingMachine.outputs [false, false])
  simpa [NaturalWordEncoding.encode] using observed

theorem decoded_lengths_allow_the_actual_strict_reduction :
    FramedCompressionCheck.verdict [false, false] [] [true] [false, false] = true := by decide

theorem equal_decoded_cost_is_not_a_bit_field_shortening :
    FramedCompressionCheck.verdict [true, false] [false] [false] [true, false] = false := by decide

theorem missing_result_fields_do_not_decode_as_acceptance :
    ICPhysicalCheck.readResponse [some true, none] = none := by decide

theorem false_is_a_completed_result_not_unfinished_search :
    ICPhysicalCheck.readResponse (FramedCompressionCheck.response false [] []) = some none := by
  exact ICPhysicalCheck.read_response false [] []

def modelCode : ToPartrec.Code := .case (.comp .head .zero') (.comp .succ (.comp .succ (.comp .succ .succ)))

def model (program _condition : BinString) : Part BinString :=
  Part.some (if NaturalWordEncoding.encode program = 0 then []
    else NaturalWordEncoding.decode (NaturalWordEncoding.encode program + 3))

def presentation : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec model where
  code := modelCode
  correct program _condition := by
    cases encoded : NaturalWordEncoding.encode program <;>
      simp [modelCode, model, NaturalWordEncoding.codec, encoded,
        NaturalWordEncoding.encode_decode, NaturalWordEncoding.encode, Nat.add_assoc]

def raw_extract : EvalsToInTime (TM2.step tr) (init modelCode [0, 4]) (some (halt [0])) 256 := by
  have counted := FiniteStackWorker.executionWithin (TM2.step tr) 256 (init modelCode [0, 4])
  have final : StepCounting.runFor (TM2.step tr) 256 (init modelCode [0, 4]) = halt [0] := by
    let state := StepCounting.runFor (TM2.step tr) 256 (init modelCode [0, 4])
    have label : state.l = none := by decide
    have registers : state.var = none := by decide
    have contents : state.stk = K'.elim (trList [0]) [] [] [] := by funext key; cases key <;> decide
    calc state = TM2.Cfg.mk state.l state.var state.stk := rfl
      _ = halt [0] := by rw [label, registers, contents]; rfl
  simpa only [final] using counted

def raw_reconstruct : EvalsToInTime (TM2.step tr) (init modelCode [1, 0]) (some (halt [4])) 256 := by
  have counted := FiniteStackWorker.executionWithin (TM2.step tr) 256 (init modelCode [1, 0])
  have final : StepCounting.runFor (TM2.step tr) 256 (init modelCode [1, 0]) = halt [4] := by
    let state := StepCounting.runFor (TM2.step tr) 256 (init modelCode [1, 0])
    have label : state.l = none := by decide
    have registers : state.var = none := by decide
    have contents : state.stk = K'.elim (trList [4]) [] [] [] := by funext key; cases key <;> decide
    calc state = TM2.Cfg.mk state.l state.var state.stk := rfl
      _ = halt [4] := by rw [label, registers, contents]; rfl
  simpa only [final] using counted

def extract_run : TM2OutputsInTime (ConditionalSourceMachine.machine presentation)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec [] [true, false])
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec [])) 256 := by
  simpa only [ConditionalSourceMachine.machine, presentation, ConditionalSourceMachine.query,
    ConditionalSourceMachine.answer, NaturalWordEncoding.codec, NaturalWordEncoding.encode] using
    FiniteCompiledMachine.outputs modelCode raw_extract

def reconstruct_run : TM2OutputsInTime (ConditionalSourceMachine.machine presentation)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec [false] [])
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec [true, false])) 256 := by
  simpa only [ConditionalSourceMachine.machine, presentation, ConditionalSourceMachine.query,
    ConditionalSourceMachine.answer, NaturalWordEncoding.codec, NaturalWordEncoding.encode] using
    FiniteCompiledMachine.outputs modelCode raw_reconstruct

noncomputable def checked_run : TM2OutputsInTime (ICPhysicalCheck.machine presentation)
    (ICConditionalCalls.input NaturalWordEncoding.codec [] [false] [true, false])
    (some (ICPhysicalCheck.result [false] [true, false] [] [true, false])) 4096 :=
  ICPhysicalCheck.outputs presentation extract_run reconstruct_run

theorem a_compiled_source_yields_a_genuinely_checked_compression :
    ((FiniteStackWorker.worker (ICPhysicalCheck.machine presentation)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec [] [false] [true, false])).searcher []).result 4096 =
      some (FramedCompressionCheck.response true [] [false]) := by
  have observed := FiniteStackWorker.complete (ICPhysicalCheck.machine presentation)
    (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec [] [false] [true, false]) [] _ _ checked_run
  simpa [ICPhysicalCheck.result, FramedCompressionCheck.verdict] using observed

theorem the_published_result_has_the_mathematical_checker_meaning :
    some ([], [false]) ∈ FeatureTheory.DyadicSearch.executePair model (([], [false]), [true, false]) := by
  obtain ⟨outcome, read, meaning⟩ := ICPhysicalCheck.worker_sound presentation [] [false] [true, false]
    (FramedCompressionCheck.response true [] [false]) 4096 a_compiled_source_yields_a_genuinely_checked_compression
  have same : outcome = some ([], [false]) := by simpa [ICPhysicalCheck.read_response] using read.symm
  simpa only [same] using meaning

def raw_wrong_extract : EvalsToInTime (TM2.step tr) (init modelCode [0, 14]) (some (halt [0])) 256 := by
  have counted := FiniteStackWorker.executionWithin (TM2.step tr) 256 (init modelCode [0, 14])
  have final : StepCounting.runFor (TM2.step tr) 256 (init modelCode [0, 14]) = halt [0] := by
    let state := StepCounting.runFor (TM2.step tr) 256 (init modelCode [0, 14])
    have label : state.l = none := by decide
    have registers : state.var = none := by decide
    have contents : state.stk = K'.elim (trList [0]) [] [] [] := by funext key; cases key <;> decide
    calc state = TM2.Cfg.mk state.l state.var state.stk := rfl
      _ = halt [0] := by rw [label, registers, contents]; rfl
  simpa only [final] using counted

def wrong_extract_run : TM2OutputsInTime (ConditionalSourceMachine.machine presentation)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec [] [true, true, true])
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec [])) 256 := by
  simpa only [ConditionalSourceMachine.machine, presentation, ConditionalSourceMachine.query,
    ConditionalSourceMachine.answer, NaturalWordEncoding.codec, NaturalWordEncoding.encode] using
    FiniteCompiledMachine.outputs modelCode raw_wrong_extract

theorem a_completed_compiled_wrong_reconstruction_is_refused :
    ((FiniteStackWorker.worker (ICPhysicalCheck.machine presentation)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec [] [false] [true, true, true])).searcher []).result 8192 =
      some (FramedCompressionCheck.response false [] [false]) := by
  have run := ICPhysicalCheck.outputs presentation wrong_extract_run reconstruct_run
  have bounded : TM2OutputsInTime (ICPhysicalCheck.machine presentation)
      (ICConditionalCalls.input NaturalWordEncoding.codec [] [false] [true, true, true])
      (some (ICPhysicalCheck.result [false] [true, true, true] [] [true, false])) 8192 :=
    ⟨run.toEvalsTo, run.steps_le_m.trans (by decide)⟩
  have observed := FiniteStackWorker.complete (ICPhysicalCheck.machine presentation)
    (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec [] [false] [true, true, true]) [] _ _ bounded
  simpa [ICPhysicalCheck.result, FramedCompressionCheck.verdict] using observed

end Mettapedia.Examples.Compression.PhysicalCheckControls
