import Mettapedia.Languages.TuringMachine.Configurations
import Mathlib.Tactic.IntervalCases

/-!
# Machines from the classic papers

Each machine below is a transition table of a few rows, hence a language
definition with twice as many rewrites.  Its classical facts are stated about
reduction in that language definition.

* **Turing (1936), §3, first example.**  The machine with the four states
  `𝔟`, `𝔠`, `𝔢`, `𝔣` prints the figures `0` and `1` alternately on every other
  square.  A round of four steps prints `0 _ 1 _`; for every number of rounds
  the machine reaches the tape with that many copies, and it never halts.
* **Radó (1962).**  The two-state table that halts after six steps with four
  ones on the tape.
* **Lin and Radó (1965).**  Two three-state tables: one halts with six ones,
  the other after twenty-one steps.
* **Brady (1983).**  The four-state table that halts after 107 steps with
  thirteen ones.

That these step counts and numbers of ones are the largest possible for
their number of states is the content of the cited papers and is not proved
here.  What is proved is the run of each table.

Symbols are numbered, and symbol zero is the blank.  In Turing's example the
figure `0` is symbol one and the figure `1` is symbol two.  A state without a
row in the table is a halting state.

## References

* Turing (1936). "On computable numbers, with an application to the
  Entscheidungsproblem", Proc. London Math. Soc. 42.
* Radó (1962). "On non-computable functions", Bell System Tech. J. 41.
* Lin and Radó (1965). "Computer studies of Turing machine problems",
  J. ACM 12.
* Brady (1983). "The determination of the value of Rado's noncomputable
  function Σ(k) for four-state Turing machines", Math. Comp. 40.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

/-! ## Turing's first example -/

/-- Turing's machine that prints `0 1 0 1 …` on every other square.  States
`𝔟`, `𝔠`, `𝔢`, `𝔣` are numbered zero to three. -/
def alternating : Machine where
  transitions :=
    [ { state := 0, read := 0, write := 1, move := .right, next := 1 },
      { state := 1, read := 0, write := 0, move := .right, next := 2 },
      { state := 2, read := 0, write := 2, move := .right, next := 3 },
      { state := 3, read := 0, write := 0, move := .right, next := 0 } ]

/-- It is an automatic machine: one row for each state and symbol. -/
theorem alternating_deterministic : alternating.Deterministic := by decide

/-- The cells to the left of the head after the given number of rounds,
nearest first. -/
def alternatingTape (rounds : Nat) : List Nat :=
  (List.replicate rounds [0, 2, 0, 1]).flatten

/-- One round of four steps prints `0 _ 1 _` and returns to the first state. -/
theorem alternating_round (written : List Nat) :
    alternating.runFor 4 ⟨0, written, 0, []⟩ = ⟨0, 0 :: 2 :: 0 :: 1 :: written, 0, []⟩ :=
  rfl

/-- **From the blank tape the machine reaches, for every number of rounds,
the tape with that many copies of `0 _ 1 _`.** -/
theorem alternating_reaches (rounds : Nat) :
    Reaches alternating Configuration.blank.term
      (⟨0, alternatingTape rounds, 0, []⟩ : Configuration).term := by
  induction rounds with
  | zero => exact .refl
  | succ rounds recurse =>
      have round := alternating.reaches_runFor 4 ⟨0, alternatingTape rounds, 0, []⟩
      rw [alternating_round] at round
      exact recurse.trans round

/-- The figures on that tape, read from left to right, are `0 1` repeated:
the sequence the machine computes. -/
theorem alternating_figures (rounds : Nat) :
    (alternatingTape rounds).reverse.filter (· ≠ 0) =
      (List.replicate rounds [1, 2]).flatten := by
  induction rounds with
  | zero => rfl
  | succ rounds recurse =>
      have unfolded : alternatingTape (rounds + 1) = [0, 2, 0, 1] ++ alternatingTape rounds := rfl
      rw [unfolded, List.reverse_append, List.filter_append, recurse, List.replicate_succ',
        List.flatten_append]
      rfl

/-- **The machine never halts.**  It always scans a blank at the right end of
what it has written, in one of its four states, and each of them has a row
for the blank. -/
theorem alternating_never_halts : ¬ HaltsFrom alternating Configuration.blank.term := by
  refine not_haltsFrom_of_invariant
    (fun configuration =>
      configuration.state < 4 ∧ configuration.scanned = 0 ∧ configuration.right = [])
    ?_ ?_ ⟨by decide, rfl, rfl⟩
  · rintro ⟨state, left, scanned, right⟩ ⟨-, rfl, rfl⟩ entry member -
    simp only [alternating, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [Configuration.after], rfl, rfl⟩
  · rintro ⟨state, left, scanned, right⟩ ⟨bound, rfl, rfl⟩
    simp only at bound
    interval_cases state
    · exact ⟨⟨0, 0, 1, .right, 1⟩, by decide, rfl, rfl⟩
    · exact ⟨⟨1, 0, 0, .right, 2⟩, by decide, rfl, rfl⟩
    · exact ⟨⟨2, 0, 2, .right, 3⟩, by decide, rfl, rfl⟩
    · exact ⟨⟨3, 0, 0, .right, 0⟩, by decide, rfl, rfl⟩

/-! ## Busy beavers -/

/-- The number of ones on the tape of a configuration. -/
def Configuration.ones (configuration : Configuration) : Nat :=
  (configuration.left ++ configuration.scanned :: configuration.right).count 1

/-- Radó's two-state table.  State two has no row. -/
def busyBeaver2 : Machine where
  transitions :=
    [ { state := 0, read := 0, write := 1, move := .right, next := 1 },
      { state := 0, read := 1, write := 1, move := .left, next := 1 },
      { state := 1, read := 0, write := 1, move := .left, next := 0 },
      { state := 1, read := 1, write := 1, move := .right, next := 2 } ]

/-- Where Radó's two-state table stops. -/
def busyBeaver2Final : Configuration := ⟨2, [1, 1], 1, [1]⟩

/-- **From the blank tape it halts after exactly six steps.** -/
theorem busyBeaver2_haltsAfter :
    busyBeaver2.HaltsAfter 6 Configuration.blank busyBeaver2Final := by decide +kernel

/-- In the language definition: the blank configuration reduces to the final
one, and no rule applies there. -/
theorem busyBeaver2_run :
    Reaches busyBeaver2 Configuration.blank.term busyBeaver2Final.term ∧
      Halted busyBeaver2 busyBeaver2Final.term :=
  Machine.haltsAfter_spec busyBeaver2_haltsAfter

/-- It leaves four ones. -/
theorem busyBeaver2_ones : busyBeaver2Final.ones = 4 := by decide

theorem busyBeaver2_deterministic : busyBeaver2.Deterministic := by decide

/-- The three-state table of Lin and Radó that leaves six ones.  State three
has no row. -/
def busyBeaver3Ones : Machine where
  transitions :=
    [ { state := 0, read := 0, write := 1, move := .right, next := 1 },
      { state := 0, read := 1, write := 1, move := .left, next := 2 },
      { state := 1, read := 0, write := 1, move := .left, next := 0 },
      { state := 1, read := 1, write := 1, move := .right, next := 1 },
      { state := 2, read := 0, write := 1, move := .left, next := 1 },
      { state := 2, read := 1, write := 1, move := .right, next := 3 } ]

def busyBeaver3OnesFinal : Configuration := ⟨3, [1, 1, 1, 1], 1, [1]⟩

/-- From the blank tape it halts after exactly thirteen steps. -/
theorem busyBeaver3Ones_haltsAfter :
    busyBeaver3Ones.HaltsAfter 13 Configuration.blank busyBeaver3OnesFinal := by decide +kernel

/-- It leaves six ones. -/
theorem busyBeaver3Ones_ones : busyBeaver3OnesFinal.ones = 6 := by decide

/-- The three-state table of Lin and Radó that runs for twenty-one steps. -/
def busyBeaver3Steps : Machine where
  transitions :=
    [ { state := 0, read := 0, write := 1, move := .right, next := 1 },
      { state := 0, read := 1, write := 1, move := .right, next := 3 },
      { state := 1, read := 0, write := 1, move := .left, next := 1 },
      { state := 1, read := 1, write := 0, move := .right, next := 2 },
      { state := 2, read := 0, write := 1, move := .left, next := 2 },
      { state := 2, read := 1, write := 1, move := .left, next := 0 } ]

def busyBeaver3StepsFinal : Configuration := ⟨3, [1, 1], 1, [1, 1]⟩

/-- **From the blank tape it halts after exactly twenty-one steps.** -/
theorem busyBeaver3Steps_haltsAfter :
    busyBeaver3Steps.HaltsAfter 21 Configuration.blank busyBeaver3StepsFinal := by
  decide +kernel

/-- It leaves five ones: one fewer than the table above, in more steps. -/
theorem busyBeaver3Steps_ones : busyBeaver3StepsFinal.ones = 5 := by decide

/-- Brady's four-state table.  State four has no row. -/
def busyBeaver4 : Machine where
  transitions :=
    [ { state := 0, read := 0, write := 1, move := .right, next := 1 },
      { state := 0, read := 1, write := 1, move := .left, next := 1 },
      { state := 1, read := 0, write := 1, move := .left, next := 0 },
      { state := 1, read := 1, write := 0, move := .left, next := 2 },
      { state := 2, read := 0, write := 1, move := .right, next := 4 },
      { state := 2, read := 1, write := 1, move := .left, next := 3 },
      { state := 3, read := 0, write := 1, move := .right, next := 3 },
      { state := 3, read := 1, write := 0, move := .right, next := 0 } ]

def busyBeaver4Final : Configuration :=
  ⟨4, [1], 0, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]⟩

/-- **From the blank tape it halts after exactly 107 steps.** -/
theorem busyBeaver4_haltsAfter :
    busyBeaver4.HaltsAfter 107 Configuration.blank busyBeaver4Final := by decide +kernel

/-- In the language definition: 107 steps of reduction end where no rule
applies. -/
theorem busyBeaver4_run :
    Reaches busyBeaver4 Configuration.blank.term busyBeaver4Final.term ∧
      Halted busyBeaver4 busyBeaver4Final.term :=
  Machine.haltsAfter_spec busyBeaver4_haltsAfter

/-- It leaves thirteen ones. -/
theorem busyBeaver4_ones : busyBeaver4Final.ones = 13 := by decide

/-! ## Controls -/

/-- The run of a halting table distinguishes step counts: Radó's table has
not halted after five steps. -/
theorem busyBeaver2_not_haltsAfter_five (final : Configuration) :
    ¬ busyBeaver2.HaltsAfter 5 Configuration.blank final := by
  rintro ⟨rfl, stopped, -⟩
  revert stopped
  decide +kernel

/-- Turing's machine and Radó's differ where it matters: one halts from the
blank tape and the other does not. -/
theorem busyBeaver2_halts_alternating_does_not :
    HaltsFrom busyBeaver2 Configuration.blank.term ∧
      ¬ HaltsFrom alternating Configuration.blank.term :=
  ⟨Machine.haltsFrom_of_haltsAfter busyBeaver2_haltsAfter, alternating_never_halts⟩

end Mettapedia.Languages.TuringMachine
