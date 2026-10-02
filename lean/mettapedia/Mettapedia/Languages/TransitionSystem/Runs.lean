import Mettapedia.Languages.TransitionSystem.Contexts
import Mettapedia.GSLT.Contexts.Traces

/-!
# How long a state of a transition table runs

A height on a table assigns a number to every state so that every move
descends by at least one and every listed state of positive height has a
move that descends by exactly one.  A state then runs for exactly the lengths
up to its height, which is what the probe that sees reduction finds of it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TransitionSystem

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Table

variable {table : Table}

/-- A height on a table: every move descends by at least one, and a listed
state of positive height has a move that descends by exactly one. -/
structure Height (table : Table) (height : String → ℕ) : Prop where
  descends : ∀ move ∈ table.moves, height move.2.2 + 1 ≤ height move.2.1
  attained : ∀ label ∈ table.states, 0 < height label →
    ∃ move ∈ table.moves, move.2.1 = label ∧ height move.2.2 + 1 = height label

/-- **A state runs for exactly the lengths up to its height.** -/
theorem runsFor_iff (wellFormed : table.WellFormed) {height : String → ℕ}
    (heights : table.Height height) (count : ℕ) :
    ∀ {interface : Interface} (term : Term table.language interface) {label : String},
      term.1 = state label →
        ((theory wellFormed).RunsFor count term ↔ count ≤ height label) := by
  induction count with
  | zero =>
      intro interface term label shape
      exact ⟨fun _ => Nat.zero_le _, fun _ => True.intro⟩
  | succ count recurse =>
      intro interface term label shape
      constructor
      · rintro ⟨next, step, more⟩
        obtain ⟨move, moveMember, source, target⟩ := (rewrites_iff wellFormed).mp step
        have bound := (recurse next target).mp more
        have same : move.2.1 = label := state_injective (source.symm.trans shape)
        have descends := heights.descends move moveMember
        rw [same] at descends
        omega
      · intro bound
        obtain ⟨ofStates, listed⟩ := interface_of_state term shape
        obtain ⟨move, moveMember, rfl, deep⟩ := heights.attained label listed (by omega)
        refine ⟨stateTerm ofStates (wellFormed.2.2 move moveMember).2,
          (rewrites_iff wellFormed).mpr ⟨move, moveMember, shape, rfl⟩, ?_⟩
        exact (recurse _ rfl).mpr (by omega)

/-- **Two states of the same height have the same traces**, as the probe that
sees reduction finds them. -/
theorem traceEquivalent_of_height_eq (wellFormed : table.WellFormed) {height : String → ℕ}
    (heights : table.Height height) {interface : Interface}
    {left right : Term table.language interface} {leftLabel rightLabel : String}
    (leftShape : left.1 = state leftLabel) (rightShape : right.1 = state rightLabel)
    (same : height leftLabel = height rightLabel) :
    (theory wellFormed).reductionProbe.TraceEquivalent (index := interface) left right := by
  apply ContextTheory.reductionProbe_traceEquivalent_iff.mpr
  intro count
  rw [runsFor_iff wellFormed heights count left leftShape,
    runsFor_iff wellFormed heights count right rightShape, same]

end Table

end Mettapedia.Languages.TransitionSystem
