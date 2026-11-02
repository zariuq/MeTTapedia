import Mettapedia.Machines.ICConditionalCalls
import Mettapedia.Computability.NaturalWordDecodingMachine
import Mettapedia.Computability.FramedCompressionCheck
import Mettapedia.Computability.FramedWordDecoding
import Mettapedia.Computability.KolmogorovComplexity.FeatureDyadicSearch
import Mettapedia.Machines.FiniteStackWorker

/-!
# A physically checked two-call IC body

The same fixed conditional source performs extraction and reconstruction.
The returned four-field packet is physically decoded and checked for exact
reconstruction and strict word-length decrease. The output retains a Boolean
and both candidate words, distinguishing a completed refusal from unfinished
execution. This clock starts at an admitted encoded task, not at an unparsed
candidate description. Preparation and the full search clock remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ICPhysicalCheck

open Turing KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability WordTemplateMachine

variable {algorithm : ConditionalAlgorithm}

local instance (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    Fintype ((ICConditionalCalls.machine source).Γ (ICConditionalCalls.machine source).k₁) :=
  inferInstanceAs (Fintype (Option Γ'))
local instance (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    Inhabited ((ICConditionalCalls.machine source).Γ (ICConditionalCalls.machine source).k₁) :=
  inferInstanceAs (Inhabited (Option Γ'))
local instance : Fintype (NaturalWordDecodingMachine.vectorMachine.Γ NaturalWordDecodingMachine.vectorMachine.k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (NaturalWordDecodingMachine.vectorMachine.Γ NaturalWordDecodingMachine.vectorMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Bool))

def decoded (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : FinTM2 :=
  StackMachineComposition.machine (ICConditionalCalls.machine source)
    NaturalWordDecodingMachine.vectorMachine (Equiv.refl (Option Γ'))

local instance (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    Fintype ((decoded source).Γ (decoded source).k₁) := inferInstanceAs (Fintype (Option Bool))
local instance (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    Inhabited ((decoded source).Γ (decoded source).k₁) := inferInstanceAs (Inhabited (Option Bool))

def machine (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : FinTM2 :=
  StackMachineComposition.machine (decoded source) FramedCompressionCheck.machine (Equiv.refl (Option Bool))

attribute [local implicit_reducible] decoded machine ICConditionalCalls.machine
  NaturalWordDecodingMachine.vectorMachine FramedCompressionCheck.machine

def wordCost (descriptive feature original residual rebuilt : BinString) : Nat :=
  256 * (descriptive.length + feature.length + original.length + residual.length + rebuilt.length + 9)

def result (feature original residual rebuilt : BinString) : List (Option Bool) :=
  FramedCompressionCheck.response (FramedCompressionCheck.verdict rebuilt feature residual original) residual feature

noncomputable def outputs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) secondTime) :
    TM2OutputsInTime (machine source) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)
      (some (result feature original residual rebuilt))
      (firstTime + secondTime + wordCost descriptive feature original residual rebuilt) := by
  have called := ICConditionalCalls.outputs source extract reconstruct
  let encoded := ICConditionalCalls.result NaturalWordEncoding.codec feature original residual rebuilt
  let decodedWords := FramedCompressionCheck.packet rebuilt feature residual original
  have decodeRun := NaturalWordDecodingMachine.vector_outputs [rebuilt, feature, residual, original]
  change TM2OutputsInTime NaturalWordDecodingMachine.vectorMachine encoded (some decodedWords)
    (32 * encoded.length + 2) at decodeRun
  have first := StackMachineComposition.outputs (ICConditionalCalls.machine source)
    NaturalWordDecodingMachine.vectorMachine (Equiv.refl (Option Γ'))
    (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)
    encoded decodedWords _ _ called (by
      change TM2OutputsInTime NaturalWordDecodingMachine.vectorMachine (encoded.map id) _ _
      simpa only [List.map_id] using decodeRun)
  have checked := FramedCompressionCheck.outputs rebuilt feature residual original
  have joined := StackMachineComposition.outputs (decoded source) FramedCompressionCheck.machine (Equiv.refl (Option Bool))
    (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)
    decodedWords (result feature original residual rebuilt) _ _ first (by
      change TM2OutputsInTime FramedCompressionCheck.machine (decodedWords.map id) _ _
      simpa only [List.map_id, decodedWords, result] using checked)
  have sourceOverhead := ICConditionalCalls.dense_overhead_bound descriptive feature original residual rebuilt
  have f := NaturalWordMachine.field_length_bounds feature
  have x := NaturalWordMachine.field_length_bounds original
  have r := NaturalWordMachine.field_length_bounds residual
  have y := NaturalWordMachine.field_length_bounds rebuilt
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  change (firstTime + secondTime + ICConditionalCalls.overhead NaturalWordEncoding.codec
      descriptive feature original residual rebuilt + 2 * encoded.length + 2 + (32 * encoded.length + 2)) +
      2 * decodedWords.length + 2 + 4 * (decodedWords.length + 1) ≤
    firstTime + secondTime + wordCost descriptive feature original residual rebuilt
  simp only [wordCost, encoded, decodedWords, ICConditionalCalls.result, ICConditionalCalls.field,
    ConditionalSourceMachine.answer, FramedCompressionCheck.packet_length,
    Indexed.frame, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  simp only [NaturalWordEncoding.codec] at sourceOverhead f x r y ⊢
  omega

def readResponse : List (Option Bool) → Option (Option FeatureTheory.DyadicSearch.Candidate)
  | some accepted :: rest => (Indexed.decodeFrames rest).bind fun fields =>
      match fields with
      | [residual, feature] => some (if accepted then some (residual, feature) else none)
      | _ => none
  | _ => none

theorem read_response (accepted : Bool) (residual feature : BinString) :
    readResponse (FramedCompressionCheck.response accepted residual feature) =
      some (if accepted then some (residual, feature) else none) := by
  simp [readResponse, FramedCompressionCheck.response, Indexed.decodeFrames_frame]

/-- The physical result has the same conditional outcome as the mathematical
two-call checker. This law uses the actual two counted source executions. -/
theorem source_result_meaning (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) secondTime) :
    ∃ outcome, readResponse (result feature original residual rebuilt) = some outcome ∧
      outcome ∈ FeatureTheory.DyadicSearch.executePair algorithm ((descriptive, feature), original) := by
  have meanings := ICConditionalCalls.source_meanings source extract reconstruct
  let outcome := if rebuilt = original ∧ feature.length + residual.length < original.length
    then some (residual, feature) else none
  refine ⟨outcome, ?_, ?_⟩
  · rw [result, read_response]
    simp only [FramedCompressionCheck.verdict, Bool.and_eq_true, decide_eq_true_eq, outcome]
  · unfold FeatureTheory.DyadicSearch.executePair
    exact Part.mem_bind meanings.1
      (Part.mem_map (fun value => if value = original ∧ feature.length + residual.length < original.length
        then some (residual, feature) else none) meanings.2)

theorem eventually_checked (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString}
    (extracts : residual ∈ algorithm descriptive original) (reconstructs : rebuilt ∈ algorithm feature residual) :
    ∃ firstTime secondTime, Nonempty (TM2OutputsInTime (machine source)
      (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)
      (some (result feature original residual rebuilt))
      (firstTime + secondTime + wordCost descriptive feature original residual rebuilt)) := by
  obtain ⟨firstTime, ⟨firstRun⟩⟩ := ConditionalSourceMachine.complete source extracts
  obtain ⟨secondTime, ⟨secondRun⟩⟩ := ConditionalSourceMachine.complete source reconstructs
  exact ⟨firstTime, secondTime, ⟨outputs source firstRun secondRun⟩⟩

/-- One plain universal source code precedes every task and both calls. The
fixed body includes physical decoding, equality and strict shortening. -/
theorem fixed_universal_checked_body :
    ∃ source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec universalConditionalAlgorithm,
      ∀ descriptive feature original residual rebuilt : BinString,
        residual ∈ universalConditionalAlgorithm descriptive original →
        rebuilt ∈ universalConditionalAlgorithm feature residual →
        ∃ firstTime secondTime, Nonempty (TM2OutputsInTime (machine source)
          (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)
          (some (result feature original residual rebuilt))
          (firstTime + secondTime + wordCost descriptive feature original residual rebuilt)) := by
  obtain ⟨source⟩ := ConditionalSourceMachine.universal_has_fixed_source NaturalWordEncoding.codec
  exact ⟨source, fun _descriptive _feature _original _residual _rebuilt extracts reconstructs =>
    eventually_checked source extracts reconstructs⟩

/-- Any terminal wrapper trace contains the two actual conditional source
computations. Neither a successful reconstruction nor source totality is an
assumption of this reflection. -/
theorem terminal_computations (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original : BinString} {final : (machine source).Cfg} {time : Nat}
    (executed : StateTransition.EvalsToInTime (machine source).step
      (initList (machine source) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original))
      (some final) time) (stopped : final.l = none) :
    ∃ residual rebuilt : BinString, residual ∈ algorithm descriptive original ∧ rebuilt ∈ algorithm feature residual ∧
      Nonempty (TM2OutputsInTime (ConditionalSourceMachine.machine source)
        (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
        (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) time) ∧
      Nonempty (TM2OutputsInTime (ConditionalSourceMachine.machine source)
        (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
        (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) time) := by
  obtain ⟨decodedFinal, decodedStopped, ⟨decodedRun⟩⟩ := StackMachineComposition.terminal_first_halts
    (decoded source) FramedCompressionCheck.machine (Equiv.refl (Option Bool)) executed stopped
  obtain ⟨callsFinal, callsStopped, ⟨callsRun⟩⟩ := StackMachineComposition.terminal_first_halts
    (ICConditionalCalls.machine source) NaturalWordDecodingMachine.vectorMachine (Equiv.refl (Option Γ'))
    decodedRun decodedStopped
  exact ICConditionalCalls.terminal_computations source callsRun callsStopped

theorem clean_halts_at (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (descriptive feature original : BinString) (final : (machine source).Cfg)
    (path : StateTransition.Reaches (machine source).step
      (initList (machine source) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)) final)
    (stopped : final.l = none) :
    ∃ output, final = haltList (machine source) output := by
  obtain ⟨counted⟩ := StackMachineComposition.reaches_has_execution path
  let bounded : StateTransition.EvalsToInTime (machine source).step
      (initList (machine source) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original))
      (some final) counted.steps := ⟨counted, le_rfl⟩
  obtain ⟨residual, rebuilt, _extracts, _reconstructs, ⟨firstRun⟩, ⟨secondRun⟩⟩ :=
    terminal_computations source bounded stopped
  have expected := outputs source firstRun secondRun
  have actual : final ∈ StateTransition.eval (machine source).step
      (initList (machine source) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)) :=
    StateTransition.mem_eval.mpr ⟨path, (StackMachineComposition.source_step_none_iff (machine source) final).mpr stopped⟩
  have canonical : haltList (machine source) (result feature original residual rebuilt) ∈
      StateTransition.eval (machine source).step
        (initList (machine source) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches expected.toEvalsTo, by rfl⟩
  exact ⟨result feature original residual rebuilt, Part.mem_unique actual canonical⟩

/-- Every completed physical output decodes to the mathematical checker's
actual outcome, including a completed refusal. -/
theorem sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original : BinString} {returned : List (Option Bool)} {time : Nat}
    (executed : TM2OutputsInTime (machine source)
      (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original) (some returned) time) :
    ∃ outcome, readResponse returned = some outcome ∧
      outcome ∈ FeatureTheory.DyadicSearch.executePair algorithm ((descriptive, feature), original) := by
  obtain ⟨_residual, _rebuilt, _extracts, _reconstructs, ⟨firstRun⟩, ⟨secondRun⟩⟩ :=
    terminal_computations source executed rfl
  have same := StackMachineComposition.outputs_unique (outputs source firstRun secondRun).toTM2Outputs executed.toTM2Outputs
  obtain ⟨outcome, read, meaning⟩ := source_result_meaning source firstRun secondRun
  exact ⟨outcome, by rw [← same]; exact read, meaning⟩

theorem worker_sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (descriptive feature original : BinString) (returned : List (Option Bool)) (time : Nat)
    (read : ((FiniteStackWorker.worker (machine source)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)).searcher []).result time =
      some returned) :
    ∃ outcome, readResponse returned = some outcome ∧
      outcome ∈ FeatureTheory.DyadicSearch.executePair algorithm ((descriptive, feature), original) := by
  obtain ⟨executed⟩ := FiniteStackWorker.sound_at (machine source)
    (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original) []
    (clean_halts_at source descriptive feature original) returned time read
  exact sound source executed

theorem no_publication_if_extraction_diverges
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (descriptive feature original : BinString) (time : Nat)
    (diverges : algorithm descriptive original = Part.none) :
    ((FiniteStackWorker.worker (machine source)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)).searcher []).result time =
      none := by
  cases observed : ((FiniteStackWorker.worker (machine source)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)).searcher []).result time with
  | none => rfl
  | some returned =>
      exfalso
      obtain ⟨_outcome, _read, meaning⟩ := worker_sound source descriptive feature original returned time observed
      simp [FeatureTheory.DyadicSearch.executePair, diverges] at meaning

theorem no_publication_if_reconstruction_diverges
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (descriptive feature original residual : BinString) (time : Nat)
    (extracts : residual ∈ algorithm descriptive original)
    (diverges : algorithm feature residual = Part.none) :
    ((FiniteStackWorker.worker (machine source)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)).searcher []).result time =
      none := by
  cases observed : ((FiniteStackWorker.worker (machine source)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)).searcher []).result time with
  | none => rfl
  | some returned =>
      exfalso
      obtain ⟨_outcome, _read, meaning⟩ := worker_sound source descriptive feature original returned time observed
      obtain ⟨actual, extracted, rest⟩ := Part.mem_bind_iff.mp meaning
      have same : actual = residual := Part.mem_unique extracted extracts
      subst actual
      simp [diverges] at rest

end Mettapedia.Machines.ICPhysicalCheck
