import Mettapedia.Computability.StreamingInput

/-!
# Sequential composition of one-way input machines

The first machine returns a value and its unread input. That value selects the
second machine and its initial state; the unread input is passed on unchanged.
The final result retains both returned values.
-/

namespace Mettapedia.Computability.StreamingComposition

open StreamingInput

universe u v w x

variable {S : Type u} {A : Type v} {T : Type w} {B : Type x}

abbrev State (S : Type u) (A : Type v) (T : Type w) := Sum S (A × T)

/-- Run the first machine, then the machine selected by its output. -/
def sequential (first : Machine S A) (second : A → Machine T B)
    (start : A → T) : Machine (State S A T) (A × B) where
  observe
    | .inl state =>
        match first.observe state with
        | .halt value => .step (.inr (value, start value))
        | .step next => .step (.inl next)
        | .read next => .read (fun bit => .inl (next bit))
    | .inr (value, state) =>
        match (second value).observe state with
        | .halt result => .halt (value, result)
        | .step next => .step (.inr (value, next))
        | .read next => .read (fun bit => .inr (value, next bit))

variable {first : Machine S A} {second : A → Machine T B} {start : A → T}

theorem lift_second {value state input result rest}
    (run : StreamingInput.Runs (second value) state input result rest) :
    StreamingInput.Runs (sequential first second start)
      (.inr (value, state)) input (value, result) rest := by
  induction run with
  | halt observed => exact .halt (by simp [sequential, observed])
  | step observed later ih => exact .step (by simp [sequential, observed]) ih
  | @read state next bit input result rest observed later ih =>
      exact .read (next := fun bit => .inr (value, next bit))
        (by simp [sequential, observed]) ih

theorem join_runs {state input value middle result rest}
    (left : StreamingInput.Runs first state input value middle)
    (right : StreamingInput.Runs (second value) (start value) middle result rest) :
    StreamingInput.Runs (sequential first second start)
      (.inl state) input (value, result) rest := by
  induction left with
  | halt observed =>
      exact .step (by simp [sequential, observed]) (lift_second right)
  | step observed later ih =>
      exact .step (by simp [sequential, observed]) (ih right)
  | @read state next bit input value rest observed later ih =>
      exact .read (next := fun bit => .inl (next bit))
        (by simp [sequential, observed]) (ih right)

theorem runFuel_second (fuel : Nat) (value : A) (state : T) (input : Tape) :
    runFuel (sequential first second start) fuel (.inr (value, state)) input =
      (runFuel (second value) fuel state input).map
        (fun returned => ((value, returned.1), returned.2)) := by
  induction fuel generalizing state input with
  | zero => rfl
  | succ fuel ih =>
      cases observed : (second value).observe state with
      | halt result => simp [runFuel, sequential, observed]
      | step next => simpa [runFuel, sequential, observed] using ih next input
      | read next =>
          cases input with
          | nil => simp [runFuel, sequential, observed]
          | cons bit input =>
              simpa [runFuel, sequential, observed] using ih (next bit) input

theorem runs_second_iff {value state input returned rest} :
    StreamingInput.Runs (sequential first second start)
        (.inr (value, state)) input returned rest ↔
      returned.1 = value ∧
        StreamingInput.Runs (second value) state input returned.2 rest := by
  constructor
  · intro run
    obtain ⟨fuel, equal⟩ := run.fuel
    rw [runFuel_second] at equal
    cases observed : runFuel (second value) fuel state input with
    | none => simp [observed] at equal
    | some result =>
        simp [observed] at equal
        rcases result with ⟨result, resultRest⟩
        rcases returned with ⟨returnedFirst, returnedSecond⟩
        simp only [Prod.mk.injEq] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        exact ⟨rfl, runFuel_sound observed⟩
  · rintro ⟨equal, run⟩
    rcases returned with ⟨returnedFirst, returnedSecond⟩
    simp only at equal
    subst returnedFirst
    exact lift_second run

theorem split_first {state input returned rest}
    (run : StreamingInput.Runs (sequential first second start)
      (.inl state) input returned rest) :
    ∃ middle, StreamingInput.Runs first state input returned.1 middle ∧
      StreamingInput.Runs (second returned.1) (start returned.1)
        middle returned.2 rest := by
  obtain ⟨fuel, equal⟩ := run.fuel
  clear run
  induction fuel generalizing state input with
  | zero => simp [runFuel] at equal
  | succ fuel ih =>
      cases observed : first.observe state with
      | halt value =>
          have later : StreamingInput.Runs (sequential first second start)
              (.inr (value, start value)) input returned rest :=
            runFuel_sound (by simpa [runFuel, sequential, observed] using equal)
          obtain ⟨same, later⟩ := runs_second_iff.mp later
          subst value
          exact ⟨input, .halt observed, later⟩
      | step next =>
          obtain ⟨middle, left, right⟩ :=
            ih (by simpa [runFuel, sequential, observed] using equal)
          exact ⟨middle, .step observed left, right⟩
      | read next =>
          cases input with
          | nil => simp [runFuel, sequential, observed] at equal
          | cons bit input =>
              obtain ⟨middle, left, right⟩ :=
                ih (by simpa [runFuel, sequential, observed] using equal)
              exact ⟨middle, .read observed left, right⟩

/-- Sequential execution is exactly two successful runs sharing the unread tape. -/
theorem runs_sequential_iff {state input value result rest} :
    StreamingInput.Runs (sequential first second start)
        (.inl state) input (value, result) rest ↔
      ∃ middle, StreamingInput.Runs first state input value middle ∧
        StreamingInput.Runs (second value) (start value) middle result rest :=
  ⟨split_first, fun ⟨_, left, right⟩ => join_runs left right⟩

/-- An exact composite program splits into the exact programs consumed by its
two phases. The second phase can depend on the first returned value. -/
theorem runs_exact_iff {state program value result} :
    StreamingInput.Runs (sequential first second start)
        (.inl state) program (value, result) [] ↔
      ∃ left right, program = left ++ right ∧
        StreamingInput.Runs first state left value [] ∧
        StreamingInput.Runs (second value) (start value) right result [] := by
  constructor
  · intro run
    obtain ⟨right, firstRun, secondRun⟩ := runs_sequential_iff.mp run
    obtain ⟨left, equal, exactRun⟩ := firstRun.consumed
    exact ⟨left, right, equal, exactRun, secondRun⟩
  · rintro ⟨left, right, rfl, firstRun, secondRun⟩
    exact join_runs (by simpa using firstRun.append right) secondRun

theorem haltingPrograms_sequential_iff {state program} :
    program ∈ HaltingPrograms (sequential first second start) (.inl state) ↔
      ∃ left right value, program = left ++ right ∧
        StreamingInput.Runs first state left value [] ∧
        right ∈ HaltingPrograms (second value) (start value) := by
  constructor
  · rintro ⟨⟨value, result⟩, run⟩
    obtain ⟨left, right, equal, firstRun, secondRun⟩ := runs_exact_iff.mp run
    exact ⟨left, right, value, equal, firstRun, result, secondRun⟩
  · rintro ⟨left, right, value, equal, firstRun, result, secondRun⟩
    exact ⟨(value, result), runs_exact_iff.mpr
      ⟨left, right, equal, firstRun, secondRun⟩⟩

theorem haltingPrograms_sequential_prefix_free {state p q}
    (left : p ∈ HaltingPrograms (sequential first second start) (.inl state))
    (right : q ∈ HaltingPrograms (sequential first second start) (.inl state))
    (isPrefix : p <+: q) : p = q :=
  haltingPrograms_prefix_free _ _ left right isPrefix

universe y z

/-- Regrouping three sequential phases preserves their results and exact input
consumption. This compares executions rather than identifying the state types. -/
theorem runs_associative {U : Type y} {C : Type z}
    (third : A → B → Machine U C) (thirdStart : A → B → U)
    {state input a b c rest} :
    StreamingInput.Runs
        (sequential (sequential first second start)
          (fun ab => third ab.1 ab.2) (fun ab => thirdStart ab.1 ab.2))
        (.inl (.inl state)) input ((a, b), c) rest ↔
      StreamingInput.Runs
        (sequential first
          (fun a => sequential (second a) (third a) (thirdStart a))
          (fun a => .inl (start a)))
        (.inl state) input (a, (b, c)) rest := by
  constructor
  · intro run
    obtain ⟨middle, combined, last⟩ := runs_sequential_iff.mp run
    obtain ⟨earlier, firstRun, secondRun⟩ := runs_sequential_iff.mp combined
    exact join_runs firstRun (join_runs secondRun last)
  · intro run
    obtain ⟨earlier, firstRun, combined⟩ := runs_sequential_iff.mp run
    obtain ⟨middle, secondRun, last⟩ := runs_sequential_iff.mp combined
    exact join_runs (join_runs firstRun secondRun) last

namespace Controls

/-- A reader that returns its first bit and consumes exactly that bit. -/
def oneBit : Machine (Option Bool) Bool where
  observe
    | none => .read some
    | some bit => .halt bit

theorem oneBit_runs (bit : Bool) (rest : Tape) :
    StreamingInput.Runs oneBit none (bit :: rest) bit rest :=
  .read rfl (.halt rfl)

theorem oneBit_runs_iff {input bit rest} :
    StreamingInput.Runs oneBit none input bit rest ↔ input = bit :: rest := by
  constructor
  · intro run
    cases run with
    | halt observed => simp [oneBit] at observed
    | step observed later => simp [oneBit] at observed
    | @read state next readBit input value rest observed later =>
        simp only [oneBit, Action.read.injEq] at observed
        cases observed
        cases later with
        | halt observed =>
            simp only [oneBit, Action.halt.injEq] at observed
            cases observed
            rfl
        | step observed later => simp [oneBit] at observed
        | read observed later => simp [oneBit] at observed
  · rintro rfl
    exact oneBit_runs _ _

/-- Composition preserves bit order and passes the tail to the next reader. -/
theorem twoBit_runs_iff {input a b rest} :
    StreamingInput.Runs (sequential oneBit (fun _ => oneBit) (fun _ => none))
        (.inl none) input (a, b) rest ↔ input = a :: b :: rest := by
  simp only [runs_sequential_iff, oneBit_runs_iff]
  constructor
  · rintro ⟨middle, first, second⟩
    simpa [second] using first
  · intro equal
    exact ⟨b :: rest, equal, rfl⟩

theorem twoBit_cannot_run_on_one (bit a b : Bool) (rest : Tape) :
    ¬ StreamingInput.Runs (sequential oneBit (fun _ => oneBit) (fun _ => none))
      (.inl none) [bit] (a, b) rest := by
  rw [twoBit_runs_iff]
  simp

/-- The first output can select whether the second phase requests a bit. -/
def conditionalReader (request : Bool) : Machine (Option Bool) Bool :=
  if request then oneBit else { observe := fun _ => .halt false }

theorem conditional_false (suffix : Tape) :
    StreamingInput.Runs (sequential oneBit conditionalReader (fun _ => none))
      (.inl none) (false :: suffix) (false, false) suffix :=
  join_runs (oneBit_runs false suffix) (.halt rfl)

theorem conditional_true (bit : Bool) (suffix : Tape) :
    StreamingInput.Runs (sequential oneBit conditionalReader (fun _ => none))
      (.inl none) (true :: bit :: suffix) (true, bit) suffix :=
  join_runs (oneBit_runs true (bit :: suffix)) (oneBit_runs bit suffix)

end Controls

end Mettapedia.Computability.StreamingComposition
