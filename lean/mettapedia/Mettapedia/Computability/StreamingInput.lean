import Mathlib.Data.List.Basic

/-!
# One-way binary input

A computation chooses between returning a value, an internal step, and
requesting the next input bit. It cannot inspect the remaining tape or catch
exhaustion of that tape. Successful runs retain their exact unread suffix.
-/

namespace Mettapedia.Computability.StreamingInput

universe u v

abbrev Tape := List Bool

inductive Action (State : Type u) (Output : Type v) where
  | halt (value : Output)
  | step (next : State)
  | read (next : Bool → State)

structure Machine (State : Type u) (Output : Type v) where
  observe : State → Action State Output

inductive Runs {State : Type u} {Output : Type v}
    (machine : Machine State Output) : State → Tape → Output → Tape → Prop where
  | halt {state input value} (observed : machine.observe state = .halt value) :
      Runs machine state input value input
  | step {state next input value rest}
      (observed : machine.observe state = .step next)
      (later : Runs machine next input value rest) :
      Runs machine state input value rest
  | read {state next bit input value rest}
      (observed : machine.observe state = .read next)
      (later : Runs machine (next bit) input value rest) :
      Runs machine state (bit :: input) value rest

variable {State : Type u} {Output : Type v} {machine : Machine State Output}

theorem runs_step_iff {state next input value rest}
    (observed : machine.observe state = .step next) :
    Runs machine state input value rest ↔ Runs machine next input value rest := by
  constructor
  · intro run
    cases run with
    | halt other => rw [observed] at other; contradiction
    | step other later => rw [observed] at other; cases other; exact later
    | read other later => rw [observed] at other; contradiction
  · exact .step observed

theorem runs_halt_iff {state output input value rest}
    (observed : machine.observe state = .halt output) :
    Runs machine state input value rest ↔ value = output ∧ rest = input := by
  constructor
  · intro run
    cases run with
    | halt other => rw [observed] at other; cases other; exact ⟨rfl, rfl⟩
    | step other later => rw [observed] at other; contradiction
    | read other later => rw [observed] at other; contradiction
  · rintro ⟨rfl, rfl⟩
    exact .halt observed

theorem runs_read_iff {state next bit input value rest}
    (observed : machine.observe state = .read next) :
    Runs machine state (bit :: input) value rest ↔ Runs machine (next bit) input value rest := by
  constructor
  · intro run
    cases run with
    | halt other => rw [observed] at other; contradiction
    | step other later => rw [observed] at other; contradiction
    | read other later => rw [observed] at other; cases other; exact later
  · exact .read observed

theorem not_runs_read_empty {state next value rest}
    (observed : machine.observe state = .read next) : ¬ Runs machine state [] value rest := by
  intro run
  cases run with
  | halt other => rw [observed] at other; contradiction
  | step other later => rw [observed] at other; contradiction

/-- Advance only internal actions. An input request or return interrupts this
finite prefix instead of being mistaken for an internal transition. -/
def advance (machine : Machine State Output) : Nat → State → Option State
  | 0, state => some state
  | steps + 1, state =>
      match machine.observe state with
      | .step next => advance machine steps next
      | _ => none

theorem runs_advance_iff {steps state next input value rest}
    (advanced : advance machine steps state = some next) :
    Runs machine state input value rest ↔ Runs machine next input value rest := by
  induction steps generalizing state with
  | zero => simp only [advance, Option.some.injEq] at advanced; cases advanced; rfl
  | succ steps ih =>
      cases observed : machine.observe state with
      | halt output => simp [advance, observed] at advanced
      | read reader => simp [advance, observed] at advanced
      | step following =>
          simp only [advance, observed] at advanced
          exact (runs_step_iff observed).trans (ih advanced)

theorem Runs.deterministic {state input first firstRest second secondRest}
    (left : Runs machine state input first firstRest)
    (right : Runs machine state input second secondRest) :
    first = second ∧ firstRest = secondRest := by
  induction left generalizing second secondRest with
  | halt observed =>
      cases right with
      | halt other =>
          rw [observed] at other
          cases other
          exact ⟨rfl, rfl⟩
      | step other later => rw [observed] at other; contradiction
      | read other later => rw [observed] at other; contradiction
  | step observed later ih =>
      cases right with
      | halt other => rw [observed] at other; contradiction
      | step other later =>
          rw [observed] at other
          cases other
          exact ih later
      | read other later => rw [observed] at other; contradiction
  | read observed later ih =>
      cases right with
      | halt other => rw [observed] at other; contradiction
      | step other later => rw [observed] at other; contradiction
      | read other later =>
          rw [observed] at other
          cases other
          exact ih later

theorem Runs.append {state input value rest}
    (run : Runs machine state input value rest) (suffix : Tape) :
    Runs machine state (input ++ suffix) value (rest ++ suffix) := by
  induction run with
  | halt observed => exact .halt observed
  | step observed later ih => exact .step observed ih
  | read observed later ih => exact .read observed ih

theorem Runs.consumed {state input value rest}
    (run : Runs machine state input value rest) :
    ∃ consumed : Tape, input = consumed ++ rest ∧ Runs machine state consumed value [] := by
  induction run with
  | halt observed => exact ⟨[], rfl, .halt observed⟩
  | step observed later ih =>
      obtain ⟨consumed, same, exactRun⟩ := ih
      exact ⟨consumed, same, .step observed exactRun⟩
  | @read state next bit input value rest observed later ih =>
      obtain ⟨consumed, same, exactRun⟩ := ih
      exact ⟨bit :: consumed, by simp [same], .read observed exactRun⟩

theorem Runs.strip_suffix {state program suffix value}
    (run : Runs machine state (program ++ suffix) value suffix) :
    Runs machine state program value [] := by
  obtain ⟨consumed, same, exactRun⟩ := run.consumed
  have equal : program = consumed := List.append_cancel_right same
  simpa [equal] using exactRun

/-- Exact programs consist of all and only the bits consumed before return. -/
def HaltingPrograms (machine : Machine State Output) (initial : State) : Set Tape :=
  {program | ∃ value, Runs machine initial program value []}

theorem haltingPrograms_prefix_free (machine : Machine State Output) (initial : State)
    {first second : Tape} (left : first ∈ HaltingPrograms machine initial)
    (right : second ∈ HaltingPrograms machine initial) (isPrefix : first <+: second) :
    first = second := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  obtain ⟨firstValue, firstRun⟩ := left
  obtain ⟨secondValue, secondRun⟩ := right
  have same := (firstRun.append suffix).deterministic secondRun
  have empty : suffix = [] := by simpa using same.2
  simp [empty]

/-- Fuel bounds the number of observed actions, including the final return.
Exhaustion produces no successful result and is not observable by a program. -/
def runFuel (machine : Machine State Output) : Nat → State → Tape → Option (Output × Tape)
  | 0, _, _ => none
  | fuel + 1, state, input =>
      match machine.observe state with
      | .halt value => some (value, input)
      | .step next => runFuel machine fuel next input
      | .read next =>
          match input with
          | [] => none
          | bit :: rest => runFuel machine fuel (next bit) rest

theorem runFuel_sound {fuel state input value rest}
    (returned : runFuel machine fuel state input = some (value, rest)) :
    Runs machine state input value rest := by
  induction fuel generalizing state input with
  | zero => simp [runFuel] at returned
  | succ fuel ih =>
      cases observed : machine.observe state with
      | halt output =>
          simp [runFuel, observed] at returned
          obtain ⟨rfl, rfl⟩ := returned
          exact .halt observed
      | step next =>
          exact .step observed (ih (by simpa [runFuel, observed] using returned))
      | read next =>
          cases input with
          | nil => simp [runFuel, observed] at returned
          | cons bit input =>
              exact .read observed (ih (by simpa [runFuel, observed] using returned))

theorem Runs.fuel {state input value rest} (run : Runs machine state input value rest) :
    ∃ fuel, runFuel machine fuel state input = some (value, rest) := by
  induction run with
  | halt observed => exact ⟨1, by simp [runFuel, observed]⟩
  | step observed later ih =>
      obtain ⟨fuel, returned⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, observed, returned]⟩
  | read observed later ih =>
      obtain ⟨fuel, returned⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, observed, returned]⟩

theorem runs_iff_fuel {state input value rest} :
    Runs machine state input value rest ↔
      ∃ fuel, runFuel machine fuel state input = some (value, rest) :=
  ⟨Runs.fuel, fun ⟨_, returned⟩ => runFuel_sound returned⟩

theorem runFuel_monotone {fuel state input result}
    (returned : runFuel machine fuel state input = some result) :
    runFuel machine (fuel + 1) state input = some result := by
  induction fuel generalizing state input with
  | zero => simp [runFuel] at returned
  | succ fuel ih =>
      cases observed : machine.observe state with
      | halt value => simpa [runFuel, observed] using returned
      | step next =>
          simpa [runFuel, observed] using ih (by simpa [runFuel, observed] using returned)
      | read next =>
          cases input with
          | nil => simp [runFuel, observed] at returned
          | cons bit input =>
              simpa [runFuel, observed] using ih (by simpa [runFuel, observed] using returned)

end Mettapedia.Computability.StreamingInput
