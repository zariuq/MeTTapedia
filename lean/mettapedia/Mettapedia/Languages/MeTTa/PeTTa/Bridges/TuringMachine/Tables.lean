import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleEvaluation
import Mettapedia.Languages.TuringMachine.Configurations

/-!
# Turing tapes in MeTTa's equation kernel

Each table row is loaded as its two existing MeTTaIL equations. `Run`, `At`
and `Cell` are ordinary ordered expression constructors. The existing PeTTa
equation judgment, including its real matcher and substitution, executes each
write-and-move operation. Tape ends produce blanks; no tape bound is imposed.

The correspondence reflects every equation answer from a represented
configuration, all finite reduction paths, and absence of a matching equation.
Iteration here is the reflexive-transitive closure of equation answers. It
does not identify that closure with a full runtime's recursive evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.TuringMachine

/-- The table is an equation program in the existing atomspace. -/
def program (machine : Machine) : PeTTaSpace :=
  MeTTaIL.RuleEvaluation.space (turingMachine machine)

/-- Equation answers use the existing PeTTa evaluation relation. -/
abbrev EquationStep (machine : Machine) (source target : Pattern) : Prop :=
  PeTTaEval (program machine) source [target]

/-- Iteration of equation answers, retaining every complete configuration. -/
abbrev EquationReaches (machine : Machine) : Pattern → Pattern → Prop :=
  Relation.ReflTransGen (EquationStep machine)

/-- A term with no equation answer. This is distinct from returning inert data
in a full evaluator's fallback branch. -/
def EquationNormal (machine : Machine) (source : Pattern) : Prop :=
  ∀ target, ¬ EquationStep machine source target

def EquationHalts (machine : Machine) (source : Pattern) : Prop :=
  ∃ final, EquationReaches machine source final ∧ EquationNormal machine final

theorem instruction_iff (machine : Machine) (source target : Pattern) :
    MeTTaStep (program machine) (.apply "eval" [source]) target ↔
      Step base (turingMachine machine) source target :=
  MeTTaIL.RuleEvaluation.evalInstruction_iff (rewrites_plain machine) source target

/-- No built-in or pass-through case invents an answer for a `Run` expression. -/
theorem equationStep_iff {machine : Machine} (configuration : Configuration)
    (target : Pattern) :
    EquationStep machine configuration.term target ↔
      Step base (turingMachine machine) configuration.term target := by
  constructor
  · intro equation
    generalize requestEq : configuration.term = request at equation
    cases equation <;> simp_all [Configuration.term, run]
    apply (step_iff_exists_match (rewrites_plain machine)).mpr
    exact ⟨_, by assumption, _, by assumption, by assumption⟩
  · exact MeTTaIL.RuleEvaluation.equationAnswer_of_step (rewrites_plain machine)

/-- The complete result is write-then-move, not just the next control state. -/
theorem equationStep_configuration_iff {machine : Machine}
    (configuration next : Configuration) :
    EquationStep machine configuration.term next.term ↔
      ∃ entry ∈ machine.transitions,
        entry.Applies configuration ∧ next = configuration.after entry :=
  (equationStep_iff configuration next.term).trans step_term_term_iff

theorem equationReaches_reflect {machine : Machine} {configuration : Configuration}
    {target : Pattern} (path : EquationReaches machine configuration.term target) :
    ∃ final : Configuration, target = final.term ∧
      Reaches machine configuration.term final.term := by
  induction path with
  | refl => exact ⟨configuration, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨current, rfl, previous⟩ := ih
      have authored := (equationStep_iff current _).mp step
      obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp authored
      exact ⟨current.after entry, rfl, previous.tail authored⟩

theorem equationReaches_preserve {machine : Machine} {configuration : Configuration}
    {target : Pattern} (path : Reaches machine configuration.term target) :
    ∃ final : Configuration, target = final.term ∧
      EquationReaches machine configuration.term final.term := by
  induction path with
  | refl => exact ⟨configuration, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨current, rfl, previous⟩ := ih
      obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp step
      exact ⟨current.after entry, rfl,
        previous.tail ((equationStep_iff current _).mpr step)⟩

theorem equationReaches_iff {machine : Machine} (configuration : Configuration)
    (target : Pattern) :
    EquationReaches machine configuration.term target ↔
      Reaches machine configuration.term target := by
  constructor
  · intro path
    obtain ⟨final, rfl, reflected⟩ := equationReaches_reflect path
    exact reflected
  · intro path
    obtain ⟨final, rfl, preserved⟩ := equationReaches_preserve path
    exact preserved

theorem equationNormal_iff {machine : Machine} (configuration : Configuration) :
    EquationNormal machine configuration.term ↔ Halted machine configuration.term := by
  simp only [EquationNormal, Halted, equationStep_iff]

theorem equationHalts_iff {machine : Machine} (configuration : Configuration) :
    EquationHalts machine configuration.term ↔ HaltsFrom machine configuration.term := by
  constructor
  · rintro ⟨target, path, normal⟩
    obtain ⟨final, rfl, reflected⟩ := equationReaches_reflect path
    exact ⟨final.term, reflected, (equationNormal_iff final).mp normal⟩
  · rintro ⟨target, path, halted⟩
    obtain ⟨final, rfl, preserved⟩ := equationReaches_preserve path
    exact ⟨final.term, preserved, (equationNormal_iff final).mpr halted⟩

theorem equationStep_unique {machine : Machine} (deterministic : machine.Deterministic)
    {configuration : Configuration} {first second : Pattern}
    (one : EquationStep machine configuration.term first)
    (two : EquationStep machine configuration.term second) : first = second :=
  step_unique deterministic ((equationStep_iff configuration first).mp one)
    ((equationStep_iff configuration second).mp two)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables
