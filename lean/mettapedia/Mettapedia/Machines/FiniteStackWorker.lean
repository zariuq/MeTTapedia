import Mettapedia.Machines.PrefixPortfolio
import Mettapedia.Computability.StackMachinePortTime

/-!
# Retained workers for actual finite stack machines

The worker exposes only halted output words. A counted original execution
supplies a readout within the same transition budget. Conversely, a readout
from a machine with clean halts supplies a counted original execution, not
just an unbounded reachability witness. The existing prefix portfolio then
uses the actual source-machine time directly.

Input construction and interpreting the returned physical word remain
separate operations; this interface assigns them no hidden unit cost.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.FiniteStackWorker

open Turing StateTransition
open Mettapedia.Computability
open Mettapedia.UniversalAI.TimeBoundedAIXI

variable {S : Type}

def executionWithin (step : S → Option S) : (count : Nat) → (state : S) →
    EvalsToInTime step state (some (StepCounting.runFor step count state)) count
  | 0, _state => ⟨⟨0, rfl⟩, Nat.zero_le _⟩
  | count + 1, state =>
      match advanced : step state with
      | none =>
          { steps := 0, steps_le_m := Nat.zero_le _,
            evals_in_steps := by simp only [Function.iterate_zero_apply, StepCounting.runFor, advanced] }
      | some next =>
          let tail := executionWithin step count next
          { steps := tail.steps + 1,
            steps_le_m := Nat.succ_le_succ tail.steps_le_m,
            evals_in_steps := by
              rw [Function.iterate_succ_apply]
              simpa only [Option.bind_eq_bind, flip, Option.bind_some, advanced, StepCounting.runFor] using tail.evals_in_steps }

theorem runFor_of_iteration (step : S → Option S) (count : Nat) (before after : S)
    (ran : (fun state : Option S => state.bind step)^[count] (some before) = some after) :
    StepCounting.runFor step count before = after := by
  induction count generalizing before with
  | zero => exact Option.some.inj ran
  | succ count ih =>
      simp only [Function.iterate_succ_apply, Option.bind_some] at ran
      cases advanced : step before with
      | none =>
          rw [advanced] at ran
          have empty : (fun state : Option S => state.bind step)^[count] none = none :=
            Function.iterate_fixed (by rfl) count
          rw [empty] at ran
          contradiction
      | some next =>
          rw [advanced] at ran
          simpa only [StepCounting.runFor, advanced] using ih next ran

def readOutput (machine : FinTM2) (state : machine.Cfg) : Option (List (machine.Γ machine.k₁)) :=
  match state.l with
  | some _label => none
  | none => some (state.stk machine.k₁)

theorem readOutput_halt (machine : FinTM2) (output : List (machine.Γ machine.k₁)) :
    readOutput machine (haltList machine output) = some output := by
  simp [readOutput, haltList]

theorem readOutput_stopped (machine : FinTM2) (state : machine.Cfg) (output : List (machine.Γ machine.k₁))
    (read : readOutput machine state = some output) : state.l = none := by
  cases label : state.l with
  | none => rfl
  | some label => simp [readOutput, label] at read

def worker (machine : FinTM2) (input : KolmogorovComplexity.BinString → List (machine.Γ machine.k₀)) :
    PrefixPortfolio.Worker machine.Cfg (List (machine.Γ machine.k₁)) where
  initial word := initList machine (input word)
  step _word := machine.step
  read _word := readOutput machine
  stopped _word state output read := by
    have halted := readOutput_stopped machine state output read
    cases state with
    | mk label registers contents =>
        dsimp only at halted
        subst label
        rfl

theorem complete (machine : FinTM2)
    (input : KolmogorovComplexity.BinString → List (machine.Γ machine.k₀))
    (word : KolmogorovComplexity.BinString) (output : List (machine.Γ machine.k₁)) (time : Nat)
    (executed : TM2OutputsInTime machine (input word) (some output) time) :
    ((worker machine input).searcher word).result time = some output := by
  have reached := runFor_of_iteration machine.step executed.steps
    (initList machine (input word)) (haltList machine output) executed.evals_in_steps
  have found : ((worker machine input).searcher word).result executed.steps = some output := by
    change readOutput machine (StepCounting.runFor machine.step executed.steps (initList machine (input word))) = some output
    rw [reached, readOutput_halt]
  exact ((worker machine input).searcher word).persists executed.steps_le_m found

theorem sound_at (machine : FinTM2)
    (input : KolmogorovComplexity.BinString → List (machine.Γ machine.k₀))
    (word : KolmogorovComplexity.BinString)
    (clean : ∀ (state : machine.Cfg),
      Reaches machine.step (initList machine (input word)) state → state.l = none →
        ∃ output : List (machine.Γ machine.k₁), state = haltList machine output)
    (output : List (machine.Γ machine.k₁)) (time : Nat)
    (found : ((worker machine input).searcher word).result time = some output) :
    Nonempty (TM2OutputsInTime machine (input word) (some output) time) := by
  let state := StepCounting.runFor machine.step time (initList machine (input word))
  have read : readOutput machine state = some output := found
  have stopped := readOutput_stopped machine state output read
  obtain ⟨actual, same⟩ := clean state
    (StepCounting.reaches_runFor machine.step time (initList machine (input word))) stopped
  have equal : actual = output := by
    rw [same, readOutput_halt] at read
    exact Option.some.inj read
  subst actual
  have bounded := executionWithin machine.step time (initList machine (input word))
  change EvalsToInTime machine.step (initList machine (input word)) (some state) time at bounded
  exact ⟨by simpa only [TM2OutputsInTime, Option.map_some, same] using bounded⟩

theorem sound (machine : FinTM2)
    (clean : ∀ (input : List (machine.Γ machine.k₀)) (state : machine.Cfg),
      Reaches machine.step (initList machine input) state → state.l = none →
        ∃ output : List (machine.Γ machine.k₁), state = haltList machine output)
    (input : KolmogorovComplexity.BinString → List (machine.Γ machine.k₀))
    (word : KolmogorovComplexity.BinString) (output : List (machine.Γ machine.k₁)) (time : Nat)
    (found : ((worker machine input).searcher word).result time = some output) :
    Nonempty (TM2OutputsInTime machine (input word) (some output) time) :=
  sound_at machine input word (clean (input word)) output time found

theorem readout_port_bounds (machine : FinTM2) (distinct : machine.k₀ ≠ machine.k₁)
    (clean : ∀ (input : List (machine.Γ machine.k₀)) (state : machine.Cfg),
      Reaches machine.step (initList machine input) state → state.l = none →
        ∃ output : List (machine.Γ machine.k₁), state = haltList machine output)
    (input : KolmogorovComplexity.BinString → List (machine.Γ machine.k₀))
    (word : KolmogorovComplexity.BinString) (output : List (machine.Γ machine.k₁)) (time : Nat)
    (found : ((worker machine input).searcher word).result time = some output) :
    (input word).length ≤ StackMachinePortTime.machinePopBound machine * time ∧
      output.length ≤ StackMachineSpaceGrowth.machinePushBound machine * time := by
  obtain ⟨executed⟩ := sound machine clean input word output time found
  exact StackMachinePortTime.io_lengths_le machine distinct executed

theorem retained_by_source_time (machine : FinTM2)
    (input : KolmogorovComplexity.BinString → List (machine.Γ machine.k₀))
    (accepts : KolmogorovComplexity.BinString → Bool)
    (free : KolmogorovComplexity.PrefixFree {word | accepts word = true})
    (word : KolmogorovComplexity.BinString) (valid : accepts word = true)
    (output : List (machine.Γ machine.k₁)) (time : Nat)
    (executed : TM2OutputsInTime machine (input word) (some output) time) :
    let phase := word.length + Nat.clog 2 time
    let retained := worker machine input
    (word, output) ∈ PrefixPortfolio.observations retained accepts phase
      (PrefixPortfolio.runFrom accepts retained.step 0 (phase + 1) retained.initial) ∧
      (PrefixPortfolio.family accepts free retained.searcher).cost (phase + 1) ≤
        4 * 2 ^ word.length * max time 1 :=
  PrefixPortfolio.retained_finds (worker machine input) accepts free word valid time output
    (complete machine input word output time executed)

end Mettapedia.Machines.FiniteStackWorker
