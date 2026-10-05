import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Execution
import Mettapedia.Languages.TuringMachine.ClassicMachines

/-!
# Equation-program execution controls

These examples retain actual tape contents and separate deterministic table
execution, missing rows, indefinite growth, and nondeterministic equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.TuringMachine
open Tables Execution

theorem busyBeaver_returns_four_ones :
    Returns busyBeaver2 Configuration.blank busyBeaver2Final ∧ busyBeaver2Final.ones = 4 :=
  ⟨⟨(equationReaches_iff _ _).mpr busyBeaver2_run.1,
    (equationNormal_iff _).mpr busyBeaver2_run.2⟩, busyBeaver2_ones⟩

/-- Reading another blank after every round does not impose a tape limit. -/
theorem arbitrarily_long_tape (rounds : Nat) :
    EquationReaches alternating Configuration.blank.term
      (⟨0, alternatingTape rounds, 0, []⟩ : Configuration).term :=
  (equationReaches_iff _ _).mpr (alternating_reaches rounds)

theorem alternating_does_not_halt : ¬ EquationHalts alternating Configuration.blank.term := by
  rw [equationHalts_iff]
  exact alternating_never_halts

/-- A single-row table with no choice about the new tape symbol. -/
def oneRow : Machine :=
  ⟨[⟨0, 0, 1, .right, 1⟩]⟩

theorem blank_edge_extends_the_tape :
    EquationStep oneRow Configuration.blank.term (⟨1, [1], 0, []⟩ : Configuration).term := by
  apply (equationStep_configuration_iff _ _).mpr
  exact ⟨⟨0, 0, 1, .right, 1⟩, by decide, ⟨rfl, rfl⟩, rfl⟩

theorem different_symbol_has_no_answer :
    EquationNormal oneRow (⟨0, [], 2, []⟩ : Configuration).term := by
  apply (equationNormal_iff _).mpr
  rw [halted_term_iff]
  intro entry member
  have same : entry = ⟨0, 0, 1, .right, 1⟩ := by simpa [oneRow] using member
  subst entry
  simp [Transition.Applies]

/-- Equation matching retains both choices instead of choosing the first
table row silently. -/
def twoChoices : Machine :=
  ⟨[⟨0, 0, 1, .right, 1⟩, ⟨0, 0, 2, .right, 1⟩]⟩

theorem two_answers_are_distinct :
    EquationStep twoChoices Configuration.blank.term (⟨1, [1], 0, []⟩ : Configuration).term ∧
    EquationStep twoChoices Configuration.blank.term (⟨1, [2], 0, []⟩ : Configuration).term ∧
    (⟨1, [1], 0, []⟩ : Configuration).term ≠ (⟨1, [2], 0, []⟩ : Configuration).term := by
  refine ⟨?_, ?_, ?_⟩
  · apply (equationStep_configuration_iff _ _).mpr
    exact ⟨⟨0, 0, 1, .right, 1⟩, by decide, ⟨rfl, rfl⟩, rfl⟩
  · apply (equationStep_configuration_iff _ _).mpr
    exact ⟨⟨0, 0, 2, .right, 1⟩, by decide, ⟨rfl, rfl⟩, rfl⟩
  · intro equal
    have configurations := Configuration.term_injective equal
    have cells := congrArg Configuration.left configurations
    cases cells

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Controls
