import Mettapedia.Computability.BoundedTapeRuns
import Mettapedia.Computability.StreamingInput
import Mettapedia.Computability.FiniteBitStrings

/-!
# One-way probabilistic generators

A generator makes deterministic internal steps, reads the next input bit,
or emits an irrevocable output symbol. A staged transition may be unknown
at a finite evaluator cutoff. Established transitions must stay the same.
Truncated runs retain the output already emitted, even if the run never
returns. The independent streaming monitor stops as soon as it has read
enough output to confirm the requested prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.BitGenerator

open scoped ENNReal
open MeasureTheory Filter

variable {State Symbol : Type*}

/-- Silent, input and output instructions. No instruction means the current
stage cannot advance. The input instruction lists its false and true exits. -/
inductive Instruction (State Symbol : Type*) where
  | silent (next : State)
  | read (onFalse onTrue : State)
  | emit (symbol : Symbol) (next : State)
  deriving DecidableEq, Repr

abbrev Transition (State Symbol : Type*) := State → Option (Instruction State Symbol)

/-- Interpret a finite cut without requiring the machine to return. -/
def output (step : Transition State Symbol) : Nat → State → List Bool → List Symbol
  | 0, _, _ => []
  | fuel + 1, state, tape =>
    match step state with
    | none => []
    | some (.silent next) => output step fuel next tape
    | some (.read no yes) =>
      match tape with
      | [] => []
      | bit :: rest => output step fuel (if bit then yes else no) rest
    | some (.emit symbol next) => symbol :: output step fuel next tape

/-- More tape, more steps, and more known transitions preserve all emission
already observed. In particular an unavailable input never acts as a zero. -/
theorem output_prefix {first later : Transition State Symbol}
    (stable : ∀ {state action}, first state = some action → later state = some action)
    {fuel more : Nat} (budget : fuel ≤ more) (state : State)
    {tape extended : List Bool} (extension : tape <+: extended) :
    output first fuel state tape <+: output later more state extended := by
  induction fuel generalizing more state tape extended with
  | zero => exact List.nil_prefix
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      have smaller : fuel ≤ more := Nat.le_of_succ_le_succ budget
      cases action : first state with
      | none => simp [output, action]
      | some instruction =>
        have found := stable action
        cases instruction with
        | silent next =>
            simpa only [output, action, found] using ih smaller next extension
        | read no yes =>
            cases tape with
            | nil => simp [output, action]
            | cons bit tail =>
                obtain ⟨suffix, rfl⟩ := extension
                simpa only [output, action, found, List.cons_append] using
                  ih (tape := tail) (extended := tail ++ suffix) smaller
                    (if bit then yes else no) (List.prefix_append _ _)
        | emit symbol next =>
            simpa only [output, action, found, List.cons_prefix_cons, true_and] using
              ih smaller next extension

/-- A time-indexed, monotone implementation of one transition. Each action
observed at a finite cutoff agrees with every later cutoff. -/
structure Generator (State Symbol : Type*) where
  initial : State
  atStage : Nat → Transition State Symbol
  stable : ∀ {first later state instruction}, first ≤ later →
    atStage first state = some instruction → atStage later state = some instruction

/-- The actual finite prefix of the tape, in reading order. -/
def tapePrefix (tape : CantorSpace) (length : Nat) : List Bool :=
  List.ofFn fun i : Fin length => tape i

theorem tapePrefix_succ (tape : CantorSpace) (n : Nat) :
    tapePrefix tape (n + 1) = tapePrefix tape n ++ [tape n] := by
  unfold tapePrefix
  rw [List.ofFn_succ_last]
  rfl

theorem tapePrefix_mono (tape : CantorSpace) {n m : Nat} (bound : n ≤ m) :
    tapePrefix tape n <+: tapePrefix tape m := by
  induction bound with
  | refl => exact List.prefix_rfl
  | @step m bound ih =>
    rw [tapePrefix_succ]
    exact ih.trans (List.prefix_append _ _)

namespace Generator

variable (program : Generator State Symbol)

def cut (program : Generator State Symbol) (stage : Nat) (tape : List Bool) : List Symbol :=
  output (program.atStage stage) stage program.initial tape

def run (program : Generator State Symbol) [DecidableEq Symbol] (history : List Symbol) : BoundedRun :=
  fun tape fuel bits => if history.isPrefixOf (program.cut fuel (tapePrefix tape bits)) then some 1 else none

theorem run_readsPrefix [DecidableEq Symbol] (history : List Symbol) :
    (program.run history).ReadsPrefix := by
  intro first second fuel bits same
  have tapeEq : tapePrefix first bits = tapePrefix second bits := by
    unfold tapePrefix
    exact congrArg List.ofFn (funext fun i : Fin bits => same i i.isLt)
  simp only [run, tapeEq]

/-- The emitted prefix event on infinite fair tapes. -/
def event (history : List Symbol) : Set CantorSpace :=
  {tape | ∃ stage, history <+: program.cut stage (tapePrefix tape stage)}

theorem stage_mono {earlier later : Nat} (work : earlier ≤ later) (tape : CantorSpace) :
    program.cut earlier (tapePrefix tape earlier) <+:
      program.cut later (tapePrefix tape later) :=
  output_prefix (program.stable work) work program.initial (tapePrefix_mono tape work)

theorem run_stage_iff [DecidableEq Symbol] (history : List Symbol) (stage : Nat) (tape : CantorSpace) :
    tape ∈ (program.run history).stageSet 1 stage ↔
      history <+: program.cut stage (tapePrefix tape stage) := by
  constructor
  · rintro ⟨fuel, hf, bits, hb, success⟩
    apply List.IsPrefix.trans (l₂ := program.cut fuel (tapePrefix tape bits))
    · simpa [run] using success
    · exact output_prefix (program.stable hf) hf program.initial (tapePrefix_mono tape hb)
  · intro seen
    exact ⟨stage, le_rfl, stage, le_rfl, by simp [run, seen]⟩

theorem outputSet_eq_event [DecidableEq Symbol] (history : List Symbol) :
    (program.run history).outputSet 1 = program.event history := by
  rw [← (program.run history).iUnion_stageSet 1]
  ext tape
  simp only [Set.mem_iUnion, run_stage_iff, event, Set.mem_ofPred_eq]

theorem measurable_event [DecidableEq Symbol] (history : List Symbol) :
    MeasurableSet (program.event history) := by
  rw [← program.outputSet_eq_event]
  exact (program.run_readsPrefix history).measurableSet_outputSet 1

@[simp] theorem event_nil : program.event [] = Set.univ := by
  ext tape
  simp [event]

theorem event_mono {first later : List Symbol} (included : first <+: later) :
    program.event later ⊆ program.event first := by
  rintro tape ⟨stage, seen⟩
  exact ⟨stage, included.trans seen⟩

/-- Histories of the same length are incompatible unless they coincide. -/
theorem event_disjoint {left right : List Symbol} (length : left.length = right.length)
    (different : left ≠ right) : Disjoint (program.event left) (program.event right) := by
  refine Set.disjoint_left.mpr ?_
  rintro tape ⟨first, hLeft⟩ ⟨second, hRight⟩
  have leftPrefix := hLeft.trans (program.stage_mono (le_max_left first second) tape)
  have rightPrefix := hRight.trans (program.stage_mono (le_max_right first second) tape)
  apply different
  calc
    left = _ := List.prefix_iff_eq_take.mp leftPrefix
    _ = right := by rw [length, ← List.prefix_iff_eq_take.mp rightPrefix]

open Mettapedia.UniversalAI.TimeBoundedAIXI (bitstringsOfLength)
open KolmogorovComplexity.FiniteBitStrings (bitstringsOfLength_nodup bitstringsOfLength_length)

theorem countP_bitstrings_succ (accept : List Bool → Bool) (length : Nat) :
    (bitstringsOfLength (length + 1)).countP accept =
      (bitstringsOfLength length).countP (fun tape => accept (false :: tape)) +
      (bitstringsOfLength length).countP (fun tape => accept (true :: tape)) := by
  rw [bitstringsOfLength]
  generalize bitstringsOfLength length = tapes
  induction tapes with
  | nil => rfl
  | cons tape rest ih =>
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons, List.countP_nil, ih]
    omega

variable [DecidableEq State]

private def countPrefix [DecidableEq Symbol] (step : Transition State Symbol) :
    Nat → Nat → State → List Symbol → Nat
  | _, bits, _, [] => 2 ^ bits
  | 0, _, _, _ :: _ => 0
  | fuel + 1, bits, state, expected :: rest =>
    match step state with
    | none => 0
    | some (.silent next) => countPrefix step fuel bits next (expected :: rest)
    | some (.read no yes) =>
      match bits with
      | 0 => 0
      | bits + 1 =>
        if no = yes then 2 * countPrefix step fuel bits no (expected :: rest)
        else
          countPrefix step fuel bits no (expected :: rest) +
            countPrefix step fuel bits yes (expected :: rest)
    | some (.emit actual next) =>
      if expected = actual then countPrefix step fuel bits next rest else 0

private theorem countPrefix_eq [DecidableEq Symbol] (step : Transition State Symbol)
    (fuel bits : Nat) (state : State) (history : List Symbol) :
    countPrefix step fuel bits state history =
      (bitstringsOfLength bits).countP (fun tape => history.isPrefixOf (output step fuel state tape)) := by
  induction fuel generalizing bits state history with
  | zero => cases history <;> simp [countPrefix, output, bitstringsOfLength_length]
  | succ fuel ih =>
    cases history with
    | nil => simp [countPrefix, bitstringsOfLength_length]
    | cons expected rest =>
      cases found : step state with
      | none => simp [countPrefix, output, found]
      | some instruction =>
        cases instruction with
        | silent next =>
          simpa [countPrefix, output, found] using ih bits next (expected :: rest)
        | read no yes =>
          cases bits with
          | zero => simp [countPrefix, output, found, bitstringsOfLength]
          | succ bits =>
            rw [countPrefix, found, countP_bitstrings_succ]
            simp only [output, found, Bool.false_eq_true, if_false, if_true,
              ← ih bits no (expected :: rest), ← ih bits yes (expected :: rest)]
            split
            · rename_i same
              rw [same, two_mul]
            · rfl
        | emit actual next =>
          by_cases same : expected = actual
          · subst actual
            simpa [countPrefix, output, found] using ih bits next rest
          · have mismatch : (expected == actual) = false := decide_eq_false same
            simp [countPrefix, output, found, List.isPrefixOf_cons_cons, same, mismatch]

/-- Count all accepted tape words of the cutoff length. Equal read exits are
counted together. A completed prefix counts all its unread extensions at once. -/
def count [DecidableEq Symbol] (history : List Symbol) (stage : Nat) : Nat :=
  countPrefix (program.atStage stage) stage stage program.initial history

theorem count_eq_filter [DecidableEq Symbol] (history : List Symbol) (stage : Nat) :
    program.count history stage =
      ((bitstringsOfLength stage).filter fun tape => history.isPrefixOf (program.cut stage tape)).length := by
  rw [← List.countP_eq_length_filter]
  exact countPrefix_eq (program.atStage stage) stage stage program.initial history

private theorem finiteTapes (stage : Nat) :
    (Finset.univ : Finset (Fin stage → Bool)).image List.ofFn = (bitstringsOfLength stage).toFinset := by
  ext bits
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨tape, rfl⟩
    simpa only [List.length_ofFn] using
      Mettapedia.UniversalAI.TimeBoundedAIXI.mem_bitstringsOfLength_self (List.ofFn tape)
  · intro member
    have length := Mettapedia.UniversalAI.TimeBoundedAIXI.length_eq_of_mem_bitstringsOfLength member
    refine ⟨fun i => bits[i.val]'(length ▸ i.isLt), ?_⟩
    apply List.ext_getElem
    · simp [length]
    · intro i h1 h2
      simp

theorem count_eq_numerator [DecidableEq Symbol] (history : List Symbol) (stage : Nat) :
    program.count history stage = (program.run history).numerator 1 stage := by
  classical
  have full : ∀ bits : Fin stage → Bool,
      tapePrefix (completeTape bits) stage = List.ofFn bits := by
    intro bits
    unfold tapePrefix completeTape
    exact congrArg List.ofFn (funext fun i : Fin stage => dif_pos i.isLt)
  have agree : ∀ bits : Fin stage → Bool,
      (program.run history).accepts 1 stage bits = true ↔
        history.isPrefixOf (program.cut stage (List.ofFn bits)) = true := by
    intro bits
    rw [(program.run history).accepts_iff, program.run_stage_iff, full, List.isPrefixOf_iff_prefix]
  rw [program.count_eq_filter]
  unfold BoundedRun.numerator BoundedRun.acceptedPrefixes
  rw [← List.toFinset_card_of_nodup ((bitstringsOfLength_nodup stage).filter _)]
  rw [List.toFinset_filter, ← finiteTapes]
  let selected := (Finset.univ : Finset (Fin stage → Bool)).filter
    fun bits => (program.run history).accepts 1 stage bits = true
  have same :
      ((Finset.univ : Finset (Fin stage → Bool)).image List.ofFn).filter
          (fun tape => history.isPrefixOf (program.cut stage tape) = true) =
        selected.image List.ofFn := by
    ext tape
    simp only [selected, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨bits, rfl⟩, found⟩
      exact ⟨bits, (agree bits).mpr found, rfl⟩
    · rintro ⟨bits, passed, rfl⟩
      exact ⟨⟨bits, rfl⟩, (agree bits).mp passed⟩
  exact (congrArg Finset.card same).trans
    (Finset.card_image_of_injective _ List.ofFn_injective)

/-- Exact dyadic likelihood at a finite stage. -/
def stageMass [DecidableEq Symbol] (history : List Symbol) (stage : Nat) : ℚ :=
  (program.count history stage : ℚ) / (2 : ℚ) ^ stage

theorem stageMass_eq_fraction [DecidableEq Symbol] (history : List Symbol) (stage : Nat) :
    program.stageMass history stage = (program.run history).fraction 1 stage := by
  rw [stageMass, BoundedRun.fraction, program.count_eq_numerator]

theorem stageMass_mono [DecidableEq Symbol] (history : List Symbol) :
    Monotone (program.stageMass history) := by
  intro i j bound
  rw [program.stageMass_eq_fraction, program.stageMass_eq_fraction]
  exact (program.run_readsPrefix history).fraction_monotone 1 bound

theorem stageMass_tendsto [DecidableEq Symbol] (history : List Symbol) :
    Tendsto (fun stage => ENNReal.ofReal (program.stageMass history stage : ℝ)) atTop
      (nhds (coinMeasure (program.event history))) := by
  simpa only [program.stageMass_eq_fraction, program.outputSet_eq_event] using
    (program.run_readsPrefix history).fraction_tendsto 1

end Generator

/-! ## Verification against the one-way input machine -/

def monitor [DecidableEq Symbol] (step : Transition State Symbol) :
    StreamingInput.Machine (State × List Symbol) Bool where
  observe
    | (_, []) => .halt true
    | (state, expected :: rest) =>
      match step state with
      | none => .halt false
      | some (.silent next) => .step (next, expected :: rest)
      | some (.read no yes) => .read fun bit => (if bit then yes else no, expected :: rest)
      | some (.emit actual next) =>
        if actual = expected then .step (next, rest) else .halt false

/-- The streaming machine stops at the requested prefix and hands back the
unread tape. Counting its successes does not require the generator to halt. -/
theorem prefix_iff_monitor [DecidableEq Symbol] (step : Transition State Symbol) (fuel : Nat)
    (state : State) (history : List Symbol) (tape : List Bool) :
    history <+: output step fuel state tape ↔
      ∃ rest, StreamingInput.runFuel (monitor step) (fuel + 1) (state, history) tape =
        some (true, rest) := by
  induction fuel generalizing state history tape with
  | zero =>
    cases history with
    | nil => simp [output, StreamingInput.runFuel, monitor]
    | cons expected rest =>
      cases observe : step state with
      | none => simp [output, StreamingInput.runFuel, monitor, observe]
      | some action =>
        cases action with
        | silent next => simp [output, StreamingInput.runFuel, monitor, observe]
        | read no yes => cases tape <;> simp [output, StreamingInput.runFuel, monitor, observe]
        | emit actual next =>
            by_cases same : actual = expected <;>
              simp [output, StreamingInput.runFuel, monitor, observe, same]
  | succ fuel ih =>
    cases history with
    | nil => simp [StreamingInput.runFuel, monitor]
    | cons expected rest =>
      cases observe : step state with
      | none => simp [output, StreamingInput.runFuel, monitor, observe]
      | some action =>
        cases action with
        | silent next =>
            simpa only [output, StreamingInput.runFuel, monitor, observe] using
              ih next (expected :: rest) tape
        | read no yes =>
            cases tape with
            | nil => simp [output, StreamingInput.runFuel, monitor, observe]
            | cons bit tail =>
                simpa only [output, StreamingInput.runFuel, monitor, observe] using
                  ih (if bit then yes else no) (expected :: rest) tail
        | emit actual next =>
            by_cases same : actual = expected
            · subst actual
              rw [StreamingInput.runFuel,
                show (monitor step).observe (state, expected :: rest) = .step (next, rest) by
                  simp [monitor, observe]]
              simpa only [output, observe, List.cons_prefix_cons, true_and] using ih next rest tape
            · have reverse : expected ≠ actual := Ne.symm same
              simp [output, StreamingInput.runFuel, monitor, observe, same, reverse]

namespace Generator

variable (program : Generator State Symbol) (meaning : Transition State Symbol)
variable (sound : ∀ {stage state instruction}, program.atStage stage state = some instruction →
  meaning state = some instruction)
variable (complete : ∀ {state instruction}, meaning state = some instruction →
  ∃ stage, program.atStage stage state = some instruction)

include sound complete in
/-- Each fixed finite run only needs finitely many transition computations.
There is a cutoff at which all the transitions for that run are known. -/
theorem finite_run_eventually_exact (fuel : Nat) (state : State) (tape : List Bool) :
    ∃ threshold, ∀ stage ≥ threshold,
      output (program.atStage stage) fuel state tape = output meaning fuel state tape := by
  induction fuel generalizing state tape with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ fuel ih =>
    cases observed : meaning state with
    | none =>
      refine ⟨0, fun stage _ => ?_⟩
      have stalled : program.atStage stage state = none := by
        cases ready : program.atStage stage state with
        | none => rfl
        | some instruction =>
          have impossible := sound ready
          rw [observed] at impossible
          cases impossible
      simp only [output, observed, stalled]
    | some instruction =>
      obtain ⟨first, ready⟩ := complete observed
      have found : ∀ stage ≥ first, program.atStage stage state = some instruction :=
        fun _ bound => program.stable bound ready
      cases instruction with
      | silent next =>
        obtain ⟨second, rest⟩ := ih next tape
        refine ⟨max first second, fun stage bound => ?_⟩
        simp only [output, observed, found stage ((le_max_left _ _).trans bound),
          rest stage ((le_max_right _ _).trans bound)]
      | read no yes =>
        cases tape with
        | nil => exact ⟨first, fun stage bound => by simp only [output, observed, found stage bound]⟩
        | cons bit tail =>
          obtain ⟨second, rest⟩ := ih (if bit then yes else no) tail
          refine ⟨max first second, fun stage bound => ?_⟩
          simp only [output, observed, found stage ((le_max_left _ _).trans bound),
            rest stage ((le_max_right _ _).trans bound)]
      | emit symbol next =>
        obtain ⟨second, rest⟩ := ih next tape
        refine ⟨max first second, fun stage bound => ?_⟩
        simp only [output, observed, found stage ((le_max_left _ _).trans bound),
          rest stage ((le_max_right _ _).trans bound)]

include sound complete in
/-- The resulting probability is about the unbounded one-way semantics.
A successful monitor run is enough, even along a nonterminating generator. -/
theorem event_iff_monitor_runs [DecidableEq Symbol] (history : List Symbol) (tape : CantorSpace) :
    tape ∈ program.event history ↔
      ∃ bits rest, StreamingInput.Runs (monitor meaning)
        (program.initial, history) (tapePrefix tape bits) true rest := by
  constructor
  · rintro ⟨stage, seen⟩
    have recognized := seen.trans
      (output_prefix (first := program.atStage stage) (later := meaning) sound le_rfl
        program.initial (List.prefix_rfl (l := tapePrefix tape stage)))
    obtain ⟨rest, success⟩ := (prefix_iff_monitor meaning stage program.initial history _).mp recognized
    exact ⟨stage, rest, StreamingInput.runFuel_sound success⟩
  · rintro ⟨bits, rest, run⟩
    obtain ⟨fuel, execution⟩ := run.fuel
    cases fuel with
    | zero => simp [StreamingInput.runFuel] at execution
    | succ fuel =>
      have seen := (prefix_iff_monitor meaning fuel program.initial history _).mpr ⟨rest, execution⟩
      obtain ⟨threshold, exactAt⟩ :=
        program.finite_run_eventually_exact meaning sound complete fuel program.initial (tapePrefix tape bits)
      let stage := max threshold (max fuel bits)
      have hb : bits ≤ stage := (le_max_right _ _).trans (le_max_right _ _)
      have hf : fuel ≤ stage := (le_max_left _ _).trans (le_max_right _ _)
      refine ⟨stage, ?_⟩
      rw [← exactAt stage (le_max_left _ _)] at seen
      exact seen.trans
        (output_prefix (fun same => same) hf program.initial (tapePrefix_mono tape hb))

end Generator

end Mettapedia.Computability.BitGenerator
