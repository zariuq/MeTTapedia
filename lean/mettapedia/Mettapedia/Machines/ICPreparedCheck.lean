import Mettapedia.Machines.ICPhysicalCheck

/-!
# Charged preparation of original-word IC tasks

The input frame contains the original descriptive, feature and source words.
The existing finite encoder executes on every field and a physical handoff
delivers the resulting canonical task to the checked body. Preparation is in
the clock. Parsing a serialized candidate pair is a separate preceding stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ICPreparedCheck

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability WordTemplateMachine

local instance : Fintype (NaturalWordMachine.machine.Γ NaturalWordMachine.machine.k₁) := inferInstanceAs (Fintype Γ')
local instance : Inhabited (NaturalWordMachine.machine.Γ NaturalWordMachine.machine.k₁) := inferInstanceAs (Inhabited Γ')
local instance : Inhabited (NaturalWordMachine.machine.Γ NaturalWordMachine.machine.k₀) := inferInstanceAs (Inhabited Bool)

def preparation : FinTM2 := FramedWordMapping.machine NaturalWordMachine.machine

local instance : Fintype (preparation.Γ preparation.k₁) := inferInstanceAs (Fintype (Option Γ'))
local instance : Inhabited (preparation.Γ preparation.k₁) := inferInstanceAs (Inhabited (Option Γ'))

def input (descriptive feature original : BinString) : List (Option Bool) :=
  Indexed.frame [descriptive, feature, original]

noncomputable def prepare_words (words : List BinString) :
    TM2OutputsInTime preparation (Indexed.frame words)
      (some (Indexed.frame (words.map fun word => trList [NaturalWordEncoding.encode word])))
      (11 * (Indexed.frame words).length + 2) := by
  have run := FramedWordMapping.outputs NaturalWordMachine.machine id
    (fun word => trList [NaturalWordEncoding.encode word]) (fun word => 2 * word.length + 3)
    NaturalWordMachine.outputs words
  simp only [List.map_id] at run
  have bound : FramedWordMapping.totalClock NaturalWordMachine.machine id
      (fun word => trList [NaturalWordEncoding.encode word]) (fun word => 2 * word.length + 3) words ≤
      11 * (Indexed.frame words).length + 2 := by
    clear run
    rw [FramedWordMapping.totalClock_eq]
    induction words with
    | nil => simp [Indexed.frame]
    | cons word rest ih =>
        have cells := (NaturalWordMachine.field_length_bounds word).2
        simp only [List.map_cons, List.sum_cons, Indexed.frame, List.flatMap_cons, List.length_append,
          List.length_map, List.length_cons, List.length_nil] at ih ⊢
        dsimp only [id_eq] at ih ⊢
        omega
  exact ⟨run.toEvalsTo, run.steps_le_m.trans bound⟩

noncomputable def prepare_task (descriptive feature original : BinString) :
    TM2OutputsInTime preparation (input descriptive feature original)
      (some (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original))
      (11 * (input descriptive feature original).length + 2) :=
  prepare_words [descriptive, feature, original]

variable {algorithm : ConditionalAlgorithm}

def machine (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : FinTM2 :=
  StackMachineComposition.machine preparation (ICPhysicalCheck.machine source) (Equiv.refl (Option Γ'))

attribute [local implicit_reducible] preparation machine

def wordCost (descriptive feature original residual rebuilt : BinString) : Nat :=
  288 * (descriptive.length + feature.length + original.length + residual.length + rebuilt.length + 9)

noncomputable def outputs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) secondTime) :
    TM2OutputsInTime (machine source) (input descriptive feature original)
      (some (ICPhysicalCheck.result feature original residual rebuilt))
      (firstTime + secondTime + wordCost descriptive feature original residual rebuilt) := by
  have prepared := prepare_task descriptive feature original
  have checked := ICPhysicalCheck.outputs source extract reconstruct
  have joined := StackMachineComposition.outputs preparation (ICPhysicalCheck.machine source) (Equiv.refl (Option Γ'))
    (input descriptive feature original) (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original)
    (ICPhysicalCheck.result feature original residual rebuilt) _ _ prepared (by
      change TM2OutputsInTime (ICPhysicalCheck.machine source)
        ((ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original).map id) _ _
      simpa only [List.map_id] using checked)
  have g := (NaturalWordMachine.field_length_bounds descriptive).2
  have f := (NaturalWordMachine.field_length_bounds feature).2
  have x := (NaturalWordMachine.field_length_bounds original).2
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  change 11 * (input descriptive feature original).length + 2 +
      2 * (ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original).length + 2 +
      (firstTime + secondTime + ICPhysicalCheck.wordCost descriptive feature original residual rebuilt) ≤ _
  simp only [input, ICConditionalCalls.input, ICConditionalCalls.field, ConditionalSourceMachine.answer,
    NaturalWordEncoding.codec, Indexed.frame, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_map, List.length_cons, List.length_nil, ICPhysicalCheck.wordCost, wordCost]
  omega

theorem sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original : BinString} {returned : List (Option Bool)} {time : Nat}
    (executed : TM2OutputsInTime (machine source) (input descriptive feature original) (some returned) time) :
    ∃ outcome, ICPhysicalCheck.readResponse returned = some outcome ∧
      outcome ∈ FeatureTheory.DyadicSearch.executePair algorithm ((descriptive, feature), original) := by
  obtain ⟨checked⟩ := StackMachineComposition.reflects_second_outputs preparation (ICPhysicalCheck.machine source)
    (Equiv.refl (Option Γ')) (prepare_task descriptive feature original) executed
  change TM2OutputsInTime (ICPhysicalCheck.machine source)
    ((ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original).map id) _ _ at checked
  simp only [List.map_id] at checked
  exact ICPhysicalCheck.sound source checked

theorem clean_halts_at (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (descriptive feature original : BinString) (final : (machine source).Cfg)
    (path : Reaches (machine source).step (initList (machine source) (input descriptive feature original)) final)
    (stopped : final.l = none) : ∃ output, final = haltList (machine source) output := by
  obtain ⟨counted⟩ := StackMachineComposition.reaches_has_execution path
  let bounded : EvalsToInTime (machine source).step
      (initList (machine source) (input descriptive feature original)) (some final) counted.steps := ⟨counted, le_rfl⟩
  obtain ⟨after, same, ⟨checked⟩⟩ := StackMachineComposition.terminal_after_known_first preparation (ICPhysicalCheck.machine source)
    (Equiv.refl (Option Γ')) (prepare_task descriptive feature original) bounded stopped
  have bodyStopped : after.l = none :=
    (StackMachineComposition.secondConfig_halted_iff preparation (ICPhysicalCheck.machine source)
      (Equiv.refl (Option Γ')) after).mp (by rw [same]; exact stopped)
  change EvalsToInTime (ICPhysicalCheck.machine source).step
    (initList (ICPhysicalCheck.machine source)
      ((ICConditionalCalls.input NaturalWordEncoding.codec descriptive feature original).map id)) (some after) counted.steps at checked
  simp only [List.map_id] at checked
  obtain ⟨output, canonical⟩ := ICPhysicalCheck.clean_halts_at source descriptive feature original after
    (StackMachineComposition.execution_reaches checked.toEvalsTo) bodyStopped
  exact ⟨output, same.symm.trans ((congrArg (StackMachineComposition.secondConfig preparation
    (ICPhysicalCheck.machine source) (Equiv.refl (Option Γ'))) canonical).trans
      (StackMachineComposition.second_halt_eq preparation (ICPhysicalCheck.machine source) (Equiv.refl (Option Γ')) output))⟩

theorem worker_sound (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    (descriptive feature original : BinString) (returned : List (Option Bool)) (time : Nat)
    (read : ((FiniteStackWorker.worker (machine source) (fun _word => input descriptive feature original)).searcher []).result time =
      some returned) : ∃ outcome, ICPhysicalCheck.readResponse returned = some outcome ∧
      outcome ∈ FeatureTheory.DyadicSearch.executePair algorithm ((descriptive, feature), original) := by
  obtain ⟨executed⟩ := FiniteStackWorker.sound_at (machine source) (fun _word => input descriptive feature original) []
    (clean_halts_at source descriptive feature original) returned time read
  exact sound source executed

end Mettapedia.Machines.ICPreparedCheck
