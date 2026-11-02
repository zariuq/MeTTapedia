import Mettapedia.Machines.ICPreparedCheck
import Mettapedia.Computability.E2PairMachine

/-!
# The checked IC entry machine with physical candidate admission

The two input fields are the unchanged canonical candidate codeword and
original source word. The fixed E2 parser produces the original three-word
task, then the prepared checker encodes, executes and checks it. Candidate
parsing and every handoff are included in this worker-transition clock.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ICEntryCheck

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability WordTemplateMachine
open FeatureTheory.DyadicSearch

variable {algorithm : ConditionalAlgorithm}

local instance : Fintype (E2PairMachine.machine.Γ E2PairMachine.machine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (E2PairMachine.machine.Γ E2PairMachine.machine.k₁) := inferInstanceAs (Inhabited (Option Bool))

def machine (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : FinTM2 :=
  StackMachineComposition.machine E2PairMachine.machine (ICPreparedCheck.machine source) (Equiv.refl (Option Bool))

attribute [local implicit_reducible] machine E2PairMachine.machine ICPreparedCheck.machine

def input (word original : BinString) : List (Option Bool) := Indexed.frame [word, original]

def wordCost (descriptive feature original residual rebuilt : BinString) : Nat :=
  320 * ((pairCode descriptive feature).length + original.length + residual.length + rebuilt.length + 9)

theorem pair_contains_payloads (descriptive feature : BinString) :
    descriptive.length + feature.length ≤ (pairCode descriptive feature).length := by
  rw [pairCode_length]
  omega

noncomputable def outputs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) secondTime) :
    TM2OutputsInTime (machine source) (input (pairCode descriptive feature) original)
      (some (ICPhysicalCheck.result feature original residual rebuilt))
      (firstTime + secondTime + wordCost descriptive feature original residual rebuilt) := by
  have parsed := E2PairMachine.outputs descriptive feature original
  have checked := ICPreparedCheck.outputs source extract reconstruct
  have joined := StackMachineComposition.outputs E2PairMachine.machine (ICPreparedCheck.machine source) (Equiv.refl (Option Bool))
    (input (pairCode descriptive feature) original) (ICPreparedCheck.input descriptive feature original)
    (ICPhysicalCheck.result feature original residual rebuilt) _ _ parsed (by
      change TM2OutputsInTime (ICPreparedCheck.machine source) ((ICPreparedCheck.input descriptive feature original).map id) _ _
      simpa only [List.map_id] using checked)
  have payloads := pair_contains_payloads descriptive feature
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  change 8 * ((input (pairCode descriptive feature) original).length + 1) +
      2 * (ICPreparedCheck.input descriptive feature original).length + 2 +
      (firstTime + secondTime + ICPreparedCheck.wordCost descriptive feature original residual rebuilt) ≤ _
  simp only [input, ICPreparedCheck.input, ICPreparedCheck.wordCost, wordCost, Indexed.frame,
    List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {word original : BinString} {returned : List (Option Bool)} {time : Nat}
    (executed : TM2OutputsInTime (machine source) (input word original) (some returned) time) :
    ∃ outcome, ICPhysicalCheck.readResponse returned = some outcome ∧ outcome ∈ autoencoder algorithm word original := by
  obtain ⟨parserFinal, parserStopped, ⟨parserRun⟩⟩ := StackMachineComposition.terminal_first_halts
    E2PairMachine.machine (ICPreparedCheck.machine source) (Equiv.refl (Option Bool)) executed rfl
  obtain ⟨descriptive, feature, wordSame⟩ := E2PairMachine.terminal_fields word original parserRun parserStopped
  subst word
  obtain ⟨checked⟩ := StackMachineComposition.reflects_second_outputs E2PairMachine.machine (ICPreparedCheck.machine source)
    (Equiv.refl (Option Bool)) (E2PairMachine.outputs descriptive feature original) executed
  change TM2OutputsInTime (ICPreparedCheck.machine source) ((ICPreparedCheck.input descriptive feature original).map id) _ _ at checked
  simp only [List.map_id] at checked
  obtain ⟨outcome, read, meaning⟩ := ICPreparedCheck.sound source checked
  exact ⟨outcome, read, by simpa [autoencoder, parsePair_pairCode] using meaning⟩

theorem clean_halts_at (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (word original : BinString) (final : (machine source).Cfg)
    (path : Reaches (machine source).step (initList (machine source) (input word original)) final)
    (stopped : final.l = none) : ∃ output, final = haltList (machine source) output := by
  obtain ⟨counted⟩ := StackMachineComposition.reaches_has_execution path
  let bounded : EvalsToInTime (machine source).step (initList (machine source) (input word original))
      (some final) counted.steps := ⟨counted, le_rfl⟩
  obtain ⟨parserFinal, parserStopped, ⟨parserRun⟩⟩ := StackMachineComposition.terminal_first_halts
    E2PairMachine.machine (ICPreparedCheck.machine source) (Equiv.refl (Option Bool)) bounded stopped
  obtain ⟨descriptive, feature, wordSame⟩ := E2PairMachine.terminal_fields word original parserRun parserStopped
  subst word
  obtain ⟨after, same, ⟨bodyRun⟩⟩ := StackMachineComposition.terminal_after_known_first
    E2PairMachine.machine (ICPreparedCheck.machine source) (Equiv.refl (Option Bool))
    (E2PairMachine.outputs descriptive feature original) bounded stopped
  have bodyStopped : after.l = none :=
    (StackMachineComposition.secondConfig_halted_iff E2PairMachine.machine (ICPreparedCheck.machine source)
      (Equiv.refl (Option Bool)) after).mp (by rw [same]; exact stopped)
  change EvalsToInTime (ICPreparedCheck.machine source).step
    (initList (ICPreparedCheck.machine source) ((ICPreparedCheck.input descriptive feature original).map id))
    (some after) counted.steps at bodyRun
  simp only [List.map_id] at bodyRun
  obtain ⟨output, canonical⟩ := ICPreparedCheck.clean_halts_at source descriptive feature original after
    (StackMachineComposition.execution_reaches bodyRun.toEvalsTo) bodyStopped
  exact ⟨output, same.symm.trans ((congrArg (StackMachineComposition.secondConfig E2PairMachine.machine
    (ICPreparedCheck.machine source) (Equiv.refl (Option Bool))) canonical).trans
      (StackMachineComposition.second_halt_eq E2PairMachine.machine (ICPreparedCheck.machine source) (Equiv.refl (Option Bool)) output))⟩

theorem worker_sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (word original : BinString) (returned : List (Option Bool)) (time : Nat)
    (read : ((FiniteStackWorker.worker (machine source) (fun _word => input word original)).searcher []).result time = some returned) :
    ∃ outcome, ICPhysicalCheck.readResponse returned = some outcome ∧ outcome ∈ autoencoder algorithm word original := by
  obtain ⟨executed⟩ := FiniteStackWorker.sound_at (machine source) (fun _word => input word original) []
    (clean_halts_at source word original) returned time read
  exact sound source executed

theorem no_publication_if_candidate_invalid
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (word original : BinString) (time : Nat) (invalid : parsePair word = none) :
    ((FiniteStackWorker.worker (machine source) (fun _word => input word original)).searcher []).result time = none := by
  cases observed : ((FiniteStackWorker.worker (machine source) (fun _word => input word original)).searcher []).result time with
  | none => rfl
  | some returned =>
      exfalso
      obtain ⟨_outcome, _read, meaning⟩ := worker_sound source word original returned time observed
      simp [autoencoder, invalid] at meaning

end Mettapedia.Machines.ICEntryCheck
