import Mettapedia.Machines.Checkpoint
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataDebt

/-!
# An actual bounded data region stops before its saved caller suffix

The generic checkpoint controller delegates all internal work to the existing
destination machine. Reaching its checkpoint earns the source data path and
the existing alias-return contract. Exhaustion and source refusal are not
checkpoint success, and no caller suffix is replayed during this region.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataCheckpoint

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open DestinationDataRecipe DestinationDataDebt

def stop {Context : Type} (older : List Goal) (cursor : Cursor Context) : Bool :=
  decide (cursor.control.goals = older)

def regionMachine {Context : Type} (program : SpaceSemantics.Program) (older : List Goal) :
    Machine (Cursor Context) Empty (Result × Cursor Context) (Unit ⊕ Boundary) :=
  Mettapedia.Machines.Checkpoint.machine (EagerDFS.Destination.machine .eagerValue program) (stop older)

theorem active_debt {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {cursor : Cursor Context}
    (held : Invariant program older destination argument cursor) (inside : stop older cursor = false) :
    ∃ goal remaining, cursor.control.goals = (goal :: remaining) ++ older ∧
      AllPure program (goal :: remaining) ∧
      Entails cursor.control.bindings (goal :: remaining) destination argument := by
  obtain ⟨debt, goals, pure, entailed⟩ := held
  cases debt with
  | nil => simp [stop, goals] at inside
  | cons goal remaining => exact ⟨goal, remaining, goals, pure, entailed⟩

theorem licensed {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {cursor : Cursor Context}
    (held : Invariant program older destination argument cursor) (inside : stop older cursor = false) :
    Source.Licensed cursor.control := by
  obtain ⟨goal, remaining, goals, pure, _entailed⟩ := active_debt held inside
  have kind := pure goal List.mem_cons_self
  cases kind with
  | @evaluate expression target data =>
      exact .evaluation expression target (remaining ++ older)
        (by simpa only [List.cons_append] using goals) data.not_scoped
  | equate expression target =>
      exact .equation expression target (remaining ++ older) (by simpa only [List.cons_append] using goals)

theorem no_publication {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (held : Invariant program older destination argument before) (inside : stop older before = false)
    (events : List Empty) :
    (EagerDFS.Destination.machine .eagerValue program).step before ≠ some (.publish events after) := by
  intro published
  obtain ⟨goal, remaining, goals, pure, _entailed⟩ := active_debt held inside
  have kind := pure goal List.mem_cons_self
  cases kind with
  | evaluate data =>
      simp only [EagerDFS.Destination.machine, goals, List.cons_append] at published
      cases published
  | equate expression target =>
      simp only [EagerDFS.Destination.machine, goals, List.cons_append] at published
      cases refined : refine before.control.bindings expression target <;>
        simp only [refined] at published <;> cases published

theorem interior_continues {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (held : Invariant program older destination argument before)
    (advanced : Mettapedia.Machines.Checkpoint.Interior
      (EagerDFS.Destination.machine .eagerValue program) (stop older) before after) :
    Continues program older before after := by
  rcases advanced with ⟨inside, silent | ⟨events, published⟩⟩
  · obtain ⟨goal, remaining, goals, _pure, _entailed⟩ := active_debt held inside
    refine ⟨?_, (Source.step_iff_source .eagerValue program before (licensed held inside) (.silent after)).mp silent⟩
    simp only [goals, List.length_append, List.length_cons]
    omega
  · exact (no_publication held inside events published).elim

theorem source_path {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (path : Relation.ReflTransGen (Mettapedia.Machines.Checkpoint.Interior
      (EagerDFS.Destination.machine .eagerValue program) (stop older)) before after)
    (held : Invariant program older destination argument before) :
    Relation.ReflTransGen (Continues program older) before after ∧
      Invariant program older destination argument after := by
  induction path with
  | refl => exact ⟨.refl, held⟩
  | tail previous advanced ih =>
      have actual := interior_continues ih.2 advanced
      exact ⟨.tail ih.1 actual, (step_invariant ih.2 actual).1⟩

/-- A checkpoint run, rather than an assumed source output, earns the read
and retains the exact world and opaque context. -/
theorem checkpoint_observation {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (fuel : Nat) (held : Invariant program older destination argument before)
    (reached : ((regionMachine program older).run fuel before).2 = .suspended (.inl ()) after)
    (environment : Environment) (resolved : resolve after.control.bindings = some environment) :
    read environment destination = read environment argument ∧ after.world = before.world ∧ after.context = before.context := by
  obtain ⟨path, stopped⟩ := Mettapedia.Machines.Checkpoint.boundary_path
    (EagerDFS.Destination.machine .eagerValue program) (stop older) fuel before after reached
  have actual := (source_path path held).1
  have atSuffix : after.control.goals = older := by simpa only [stop, decide_eq_true_eq] using stopped
  exact suffix_observation actual held atSuffix environment resolved

theorem checkpoint_alias {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (fuel : Nat) (held : Invariant program older destination argument before)
    (reached : ((regionMachine program older).run fuel before).2 = .suspended (.inl ()) after)
    (name : String) (root : before.control.destination = destination) (slot : destination = .var name) :
    ScopedReturnLocal.AliasHolds argument after.control := by
  obtain ⟨path, stopped⟩ := Mettapedia.Machines.Checkpoint.boundary_path
    (EagerDFS.Destination.machine .eagerValue program) (stop older) fuel before after reached
  have actual := (source_path path held).1
  have atSuffix : after.control.goals = older := by simpa only [stop, decide_eq_true_eq] using stopped
  exact suffix_alias actual held atSuffix name root slot

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataCheckpoint
