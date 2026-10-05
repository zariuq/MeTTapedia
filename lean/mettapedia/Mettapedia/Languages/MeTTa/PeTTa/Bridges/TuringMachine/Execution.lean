import Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Tables
import Mettapedia.Languages.TuringMachine.MathlibBridge

/-!
# Terminal equation executions retain the Turing result

The relation below observes a complete terminal configuration, including both
half-tapes and the scanned symbol. For a deterministic table it is exactly
the established partial execution function. This supplies both output
preservation and reflection without a fuel bound or a second interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Execution

open Mettapedia.Languages.TuringMachine
open Tables

def Returns (machine : Machine) (initial final : Configuration) : Prop :=
  EquationReaches machine initial.term final.term ∧ EquationNormal machine final.term

/-- Every terminal equation execution corresponds to precisely this final
configuration of the source partial machine, and conversely. -/
theorem returns_iff {machine : Machine} (deterministic : machine.Deterministic)
    (initial final : Configuration) :
    Returns machine initial final ↔ final ∈ StateTransition.eval machine.next? initial := by
  constructor
  · rintro ⟨path, normal⟩
    obtain ⟨last, same, reached⟩ := MathlibBridge.reaches_next_reflect machine deterministic
      ((equationReaches_iff initial final.term).mp path)
    have sameConfiguration : final = last := Configuration.term_injective same
    subst last
    exact StateTransition.mem_eval.mpr ⟨reached,
      (MathlibBridge.next_none_iff_halted machine final).mpr
        ((equationNormal_iff final).mp normal)⟩
  · intro computed
    obtain ⟨reached, stopped⟩ := StateTransition.mem_eval.mp computed
    exact ⟨(equationReaches_iff initial final.term).mpr
      (MathlibBridge.reaches_next_forward machine reached),
      (equationNormal_iff final).mpr (Machine.halted_of_next?_eq_none stopped)⟩

theorem returns_unique {machine : Machine} (deterministic : machine.Deterministic)
    {initial first second : Configuration}
    (one : Returns machine initial first) (two : Returns machine initial second) :
    first = second :=
  Part.mem_unique ((returns_iff deterministic initial first).mp one)
    ((returns_iff deterministic initial second).mp two)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.TuringMachine.Execution
