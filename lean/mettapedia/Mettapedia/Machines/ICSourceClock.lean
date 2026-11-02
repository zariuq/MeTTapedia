import Mettapedia.Machines.ICPreparedCheck
import Mettapedia.Machines.ICEntryCheck
import Mettapedia.Computability.StackMachineOutputRelay

/-!
# Prepared checking in an explicit output-separated source clock

The reference clock executes the fixed original conditional source and copies
its result into a separate output arena. Real relay traces reflect original
source executions at admitted queries. Physical port laws then charge every
query and answer cell. This does not identify normalized time with an in-place
interpreter's original time, nor charge candidate-pair parsing for free.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ICSourceClock

open Turing StateTransition KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability

variable {algorithm : ConditionalAlgorithm}

local instance (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    Fintype ((ConditionalSourceMachine.machine source).Γ (ConditionalSourceMachine.machine source).k₁) :=
  inferInstanceAs (Fintype Γ')
local instance (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    Inhabited ((ConditionalSourceMachine.machine source).Γ (ConditionalSourceMachine.machine source).k₁) :=
  inferInstanceAs (Inhabited Γ')

def machine (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : FinTM2 :=
  StackMachineOutputRelay.machine (ConditionalSourceMachine.machine source)

attribute [local implicit_reducible] machine ConditionalSourceMachine.machine FiniteCompiledMachine.machine
  FiniteSupportMachine.machine StackMachineOutputRelay.machine StackMachineOutputRelay.copy

theorem distinct_ports (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) :
    (machine source).k₀ ≠ (machine source).k₁ := StackMachineOutputRelay.distinct_ports _

def outputs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {program condition output : BinString} {time : Nat}
    (executed : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec output)) time) :
    TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec output))
      (time + 6 * (ConditionalSourceMachine.answer NaturalWordEncoding.codec output).length + 4) :=
  StackMachineOutputRelay.outputs _ executed

theorem complete (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {program condition output : BinString} (computed : output ∈ algorithm program condition) :
    ∃ time, Nonempty (TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec output)) time) := by
  obtain ⟨_time, ⟨original⟩⟩ := ConditionalSourceMachine.complete source computed
  exact ⟨_, ⟨outputs source original⟩⟩

theorem reflects_outputs (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {program condition output : BinString} {time : Nat}
    (executed : TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec output)) time) :
    Nonempty (TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec output)) time) := by
  apply StackMachineOutputRelay.reflects_outputs_at (ConditionalSourceMachine.machine source) ?_ executed
  intro state path stopped
  obtain ⟨numbers, canonical⟩ := FiniteCompiledMachine.clean_halts_at_encoded_input source.code
    [NaturalWordEncoding.encode program, NaturalWordEncoding.encode condition] state path stopped
  exact ⟨trList numbers, canonical⟩

theorem io_word_bounds (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {program condition output : BinString} {time : Nat}
    (executed : TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec program condition)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec output)) time) :
    program.length + condition.length ≤ StackMachinePortTime.machinePopBound (machine source) * time ∧
      output.length ≤ StackMachineSpaceGrowth.machinePushBound (machine source) * time := by
  have ports := StackMachinePortTime.io_lengths_le (machine source) (distinct_ports source) executed
  have inputBits := (NaturalWordMachine.query_length_bounds program condition).1
  have outputBits := (NaturalWordMachine.field_length_bounds output).1
  change output.length + 1 ≤ (ConditionalSourceMachine.answer NaturalWordEncoding.codec output).length at outputBits
  constructor <;> omega

def factor (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : Nat :=
  2593 + 288 * (StackMachinePortTime.machinePopBound (machine source) +
    StackMachineSpaceGrowth.machinePushBound (machine source))

/-- One factor is fixed by the actual finite source before all task words.
Both normalized source clocks are observed executions, not assumed I/O bounds. -/
noncomputable def prepared_outputs
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) secondTime) :
    TM2OutputsInTime (ICPreparedCheck.machine source) (ICPreparedCheck.input descriptive feature original)
      (some (ICPhysicalCheck.result feature original residual rebuilt))
      (factor source * (firstTime + secondTime + 1)) := by
  let firstRun := Classical.choice (reflects_outputs source extract)
  let secondRun := Classical.choice (reflects_outputs source reconstruct)
  have checked := ICPreparedCheck.outputs source firstRun secondRun
  have firstBounds := io_word_bounds source extract
  have secondBounds := io_word_bounds source reconstruct
  have outputBound := Nat.mul_le_mul_left (StackMachineSpaceGrowth.machinePushBound (machine source))
    (show secondTime ≤ firstTime + secondTime + 1 by omega)
  refine ⟨checked.toEvalsTo, checked.steps_le_m.trans ?_⟩
  simp only [ICPreparedCheck.wordCost, factor]
  nlinarith

theorem pair_linear_length (descriptive feature : BinString) :
    (FeatureTheory.DyadicSearch.pairCode descriptive feature).length ≤
      3 * (descriptive.length + feature.length) + 13 := by
  have first := binaryBits_length descriptive.length
  have second := binaryBits_length feature.length
  have firstLog := Nat.log_le_self 2 descriptive.length
  have secondLog := Nat.log_le_self 2 feature.length
  rw [FeatureTheory.DyadicSearch.pairCode_length_framed_components, e2encode_length, e2encode_length]
  omega

def entryFactor (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm) : Nat := 4 * factor source

/-- Physical E2 admission, original-word preparation and checking share one
fixed normalized-source factor. The input is the actual candidate codeword. -/
noncomputable def entry_outputs
    (source : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec descriptive original)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (machine source)
      (ConditionalSourceMachine.query NaturalWordEncoding.codec feature residual)
      (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec rebuilt)) secondTime) :
    TM2OutputsInTime (ICEntryCheck.machine source)
      (ICEntryCheck.input (FeatureTheory.DyadicSearch.pairCode descriptive feature) original)
      (some (ICPhysicalCheck.result feature original residual rebuilt))
      (entryFactor source * (firstTime + secondTime + 1)) := by
  let firstRun := Classical.choice (reflects_outputs source extract)
  let secondRun := Classical.choice (reflects_outputs source reconstruct)
  have checked := ICEntryCheck.outputs source firstRun secondRun
  have firstBounds := io_word_bounds source extract
  have secondBounds := io_word_bounds source reconstruct
  have pairBound := pair_linear_length descriptive feature
  have outputBound := Nat.mul_le_mul_left (StackMachineSpaceGrowth.machinePushBound (machine source))
    (show secondTime ≤ firstTime + secondTime + 1 by omega)
  refine ⟨checked.toEvalsTo, checked.steps_le_m.trans ?_⟩
  simp only [ICEntryCheck.wordCost, entryFactor, factor]
  nlinarith

end Mettapedia.Machines.ICSourceClock
