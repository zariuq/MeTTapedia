import Mettapedia.Computability.StackMachinePortTime
import Mettapedia.Computability.StackMachineCompositionReflection
import Mettapedia.Computability.WordHomomorphismMachine

/-!
# A physical, output-separated relay for original finite stack programs

The relay executes the source program, moves its output through the shared
two-pass handoff, and copies every symbol into a separate output arena. Its
time includes all transfer and copy transitions. In-place sources pay for
their possibly long returned input instead of receiving a fictitious
constant-time output-writing guarantee.

Completed runs reflect back to the original program when its halts are
canonical clean outputs. That premise is an explicit semantic condition,
not an assumed runtime inequality. No native execution bound is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineOutputRelay

open Turing StateTransition
open StackMachineSpaceGrowth StackMachinePortTime

variable (source : FinTM2) [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)]

def copy : FinTM2 := WordHomomorphismMachine.machine (fun symbol : source.Γ source.k₁ => [symbol])

def machine : FinTM2 := StackMachineComposition.machine source (copy source) (Equiv.refl _)

attribute [local implicit_reducible] copy machine

theorem distinct_ports : (machine source).k₀ ≠ (machine source).k₁ := by
  intro same
  cases same

def copy_outputs (word : List (source.Γ source.k₁)) :
    TM2OutputsInTime (copy source) word (some word) (4 * word.length + 2) := by
  have copied := WordHomomorphismMachine.outputs (fun symbol : source.Γ source.k₁ => [symbol]) word
  have same : TM2OutputsInTime (copy source) word (some word) (2 * word.length + 2 * word.length + 2) := by
    simpa only [copy, List.flatMap_singleton'] using copied
  exact ⟨same.toEvalsTo, same.steps_le_m.trans (by omega)⟩

/-- Every original completed execution has an actual relay execution. The
bound charges the full intermediate word, even for an in-place source. -/
def outputs {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source) input (some output) (time + 6 * output.length + 4) := by
  have mapped (word : List (source.Γ source.k₁)) : word.map (Equiv.refl (source.Γ source.k₁)) = word := by
    change word.map id = word
    exact List.map_id word
  have prepared : TM2OutputsInTime (copy source) (output.map (Equiv.refl (source.Γ source.k₁)))
      (some output) (4 * output.length + 2) :=
    Eq.mpr (congrArg (fun argument : List (source.Γ source.k₁) =>
      TM2OutputsInTime (copy source) argument (some output) (4 * output.length + 2)) (mapped output))
      (copy_outputs source output)
  have composed := StackMachineComposition.outputs source (copy source) (Equiv.refl _) input output output
    time (4 * output.length + 2) executed prepared
  exact ⟨composed.toEvalsTo, composed.steps_le_m.trans (by omega)⟩

def outputs_linear (distinct : source.k₀ ≠ source.k₁)
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source) input (some output) ((1 + 6 * machinePushBound source) * time + 4) := by
  have relayed := outputs source executed
  have size := (io_lengths_le source distinct executed).2
  exact ⟨relayed.toEvalsTo, relayed.steps_le_m.trans (by nlinarith)⟩

def outputs_with_input_charge
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source) input (some output)
      ((1 + 6 * machinePushBound source) * time + 6 * input.length + 4) := by
  have relayed := outputs source executed
  have size := StackMachineSpaceGrowth.output_length_le source executed
  exact ⟨relayed.toEvalsTo, relayed.steps_le_m.trans (by nlinarith)⟩

theorem relay_io_lengths
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime (machine source) input (some output) time) :
    input.length ≤ machinePopBound (machine source) * time ∧
      output.length ≤ machinePushBound (machine source) * time :=
  io_lengths_le (machine source) (distinct_ports source) executed

theorem clean_halts_at
    (input : List (source.Γ source.k₀)) (state : (machine source).Cfg)
    (clean : ∀ (state : source.Cfg), Reaches source.step (initList source input) state → state.l = none →
      ∃ output : List (source.Γ source.k₁), state = haltList source output)
    (path : Reaches (machine source).step (initList (machine source) input) state) (stopped : state.l = none) :
    ∃ output : List (source.Γ source.k₁), state = haltList (machine source) output := by
  obtain ⟨actual⟩ := StackMachineComposition.reaches_has_execution path
  let counted : EvalsToInTime (machine source).step (initList (machine source) input) (some state) actual.steps :=
    ⟨actual, le_rfl⟩
  obtain ⟨firstHalt, halted, ⟨firstRun⟩⟩ := StackMachineComposition.terminal_first_halts source (copy source)
    (Equiv.refl _) counted stopped
  obtain ⟨output, same⟩ := clean firstHalt
    (StackMachineComposition.execution_reaches firstRun.toEvalsTo) halted
  have original : TM2OutputsInTime source input (some output) actual.steps := by
    simpa only [TM2OutputsInTime, Option.map_some, same] using firstRun
  have expected := outputs source original
  have stateStopped : (machine source).step state = none := by
    cases state with
    | mk label registers contents =>
        dsimp only at stopped
        subst label
        rfl
  have actualValue : state ∈ StateTransition.eval (machine source).step (initList (machine source) input) :=
    StateTransition.mem_eval.mpr ⟨path, stateStopped⟩
  have canonical : haltList (machine source) output ∈
      StateTransition.eval (machine source).step (initList (machine source) input) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches expected.toEvalsTo, by rfl⟩
  exact ⟨output, Part.mem_unique actualValue canonical⟩

theorem clean_halts
    (clean : ∀ (input : List (source.Γ source.k₀)) (state : source.Cfg),
      Reaches source.step (initList source input) state → state.l = none →
        ∃ output : List (source.Γ source.k₁), state = haltList source output)
    (input : List (source.Γ source.k₀)) (state : (machine source).Cfg)
    (path : Reaches (machine source).step (initList (machine source) input) state) (stopped : state.l = none) :
    ∃ output : List (source.Γ source.k₁), state = haltList (machine source) output :=
  clean_halts_at source input state (clean input) path stopped

/-- A relay cannot turn divergence into a successful clean output. A clean
source halt is recovered from the actual composite trace, not postulated as
an independently successful evaluation. -/
theorem reflects_outputs_at
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (clean : ∀ (state : source.Cfg), Reaches source.step (initList source input) state → state.l = none →
      ∃ output : List (source.Γ source.k₁), state = haltList source output)
    (executed : TM2OutputsInTime (machine source) input (some output) time) :
    Nonempty (TM2OutputsInTime source input (some output) time) := by
  obtain ⟨after, stopped, ⟨prefixRun⟩⟩ := StackMachineComposition.outputs_first_halts source (copy source)
    (Equiv.refl _) executed
  obtain ⟨originalOutput, same⟩ := clean after (StackMachineComposition.execution_reaches prefixRun.toEvalsTo) stopped
  have original : TM2OutputsInTime source input (some originalOutput) time := by
    simpa only [TM2OutputsInTime, Option.map_some, same] using prefixRun
  have completed := outputs source original
  have equal := StackMachineComposition.outputs_unique completed.toTM2Outputs executed.toTM2Outputs
  subst originalOutput
  exact ⟨original⟩

theorem reflects_outputs
    (clean : ∀ (input : List (source.Γ source.k₀)) (state : source.Cfg),
      Reaches source.step (initList source input) state → state.l = none →
        ∃ output : List (source.Γ source.k₁), state = haltList source output)
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime (machine source) input (some output) time) :
    Nonempty (TM2OutputsInTime source input (some output) time) :=
  reflects_outputs_at source (clean input) executed

end Mettapedia.Computability.StackMachineOutputRelay
