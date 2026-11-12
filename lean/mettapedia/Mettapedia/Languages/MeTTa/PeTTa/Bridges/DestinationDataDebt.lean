import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataRecipe
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnAliasEntry

/-!
# Pending constructor equations through actual local source steps

An entailment records what follows once the pending pure data equations
are discharged. It is not a completed-value certificate. Actual source
preparation expands that debt; actual successful unification pays one
equation. At the saved suffix, no debt remains and the reached read follows.

This local source component does not claim native plan adequacy or replace
the owned scope dispatcher with another evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataDebt

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open DestinationDataRecipe

def Entails (bindings : Equations) (debt : List Goal) (destination argument : Atom) : Prop :=
  ∀ environment, Solves environment bindings → AllSay environment debt →
    read environment destination = read environment argument

theorem initial (bindings : Equations) (recipe destination : Atom) :
    Entails bindings [.evaluate recipe destination] destination recipe := by
  intro environment _solved pending
  exact (pending _ List.mem_cons_self).symm

theorem clause_entry (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence : Nat) (equation : SpaceSemantics.Equation)
    (next : Control) (index : Nat) (argument recipe : Atom)
    (selected : ClauseChoice.attempt control head arguments destination older occurrence equation = some next)
    (actual : arguments[index]? = some argument) (formal : equation.arguments[index]? = some recipe) :
    Entails next.bindings
      [.evaluate (HE.Spec.Type.RuntimeRefinement.renameTypeVars
        (ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation)) recipe) destination]
      destination argument := by
  intro environment solved pending
  exact (pending _ List.mem_cons_self).symm.trans
    (ScopedReturnEntry.fresh_recipe_read control head arguments destination older occurrence equation next index
      argument recipe selected actual formal environment solved)

theorem prepared_debt {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) (control : Control) (target destination argument : Atom)
    (remaining : List Goal)
    (held : Entails control.bindings (.evaluate expression target :: remaining) destination argument) :
    Entails control.bindings (expansion program control expression target ++ remaining) destination argument := by
  intro environment solved pending
  apply held environment solved
  intro goal member
  rcases List.mem_cons.mp member with rfl | later
  · exact expansion_entails data control target environment
      (fun part present => pending part (List.mem_append_left _ present))
  · exact pending goal (List.mem_append_right _ later)

theorem refined_debt {before after : Equations} {expression target destination argument : Atom}
    (remaining : List Goal) (refined : Refinement before expression target (some after))
    (held : Entails before (.equate expression target :: remaining) destination argument) :
    Entails after remaining destination argument := by
  cases refined with
  | accepted witness old same =>
      intro environment solved pending
      have facts := (solves_append_equation _ _ _ _).mp solved
      apply held environment facts.1
      intro goal member
      rcases List.mem_cons.mp member with rfl | later
      · exact facts.2
      · exact pending goal later

theorem finished_debt {bindings : Equations} {destination argument : Atom}
    (held : Entails bindings [] destination argument) (environment : Environment)
    (solved : Solves environment bindings) : read environment destination = read environment argument :=
  held environment solved (by intro goal impossible; cases impossible)

/-- The debt is tied to an actual goal prefix. Keeping the suffix fixes its
physical extent; no convenient empty replacement may be chosen. -/
def Invariant {Context : Type} (program : SpaceSemantics.Program) (older : List Goal)
    (destination argument : Atom) (cursor : Cursor Context) : Prop :=
  ∃ debt, cursor.control.goals = debt ++ older ∧ AllPure program debt ∧
    Entails cursor.control.bindings debt destination argument

theorem debt_unique {Context : Type} {cursor : Cursor Context} {older first second : List Goal}
    (one : cursor.control.goals = first ++ older) (two : cursor.control.goals = second ++ older) : first = second := by
  simpa only [List.append_left_inj] using one.symm.trans two

theorem active_step {Context : Type} {program : SpaceSemantics.Program}
    (older remaining : List Goal) (goal : Goal) (destination argument : Atom)
    (before after : Cursor Context)
    (atGoal : before.control.goals = (goal :: remaining) ++ older)
    (pure : AllPure program (goal :: remaining))
    (held : Entails before.control.bindings (goal :: remaining) destination argument)
    (step : Source.Step .eagerValue program before (.silent after)) :
    Invariant program older destination argument after ∧ after.world = before.world ∧ after.context = before.context := by
  have kind := pure goal List.mem_cons_self
  have tailPure : AllPure program remaining := fun other member => pure other (List.mem_cons_of_mem _ member)
  cases kind with
  | @evaluate expression target data =>
      have actual := step.execution
      simp only [EagerDFS.Destination.machine, atGoal, List.cons_append] at actual
      have same := Transition.silent.inj (Option.some.inj actual)
      subst after
      refine ⟨⟨expansion program before.control expression target ++ remaining, ?_, ?_, ?_⟩, rfl, rfl⟩
      · simpa only [List.append_assoc] using expansion_suffix data before.control target (remaining ++ older)
      · intro next member
        rcases List.mem_append.mp member with fresh | pending
        · exact expansion_pure data before.control target next fresh
        · exact tailPure next pending
      · change Entails (prepare .eagerValue program before.control expression target (remaining ++ older)).bindings
          (expansion program before.control expression target ++ remaining) destination argument
        rw [(data.prepared before.control target (remaining ++ older)).retains_frame.1]
        exact prepared_debt data before.control target destination argument remaining held
  | equate expression target =>
      have actual := step.execution
      simp only [EagerDFS.Destination.machine, atGoal, List.cons_append] at actual
      cases refined : refine before.control.bindings expression target with
      | none => simp only [refined] at actual; cases actual
      | some bindings =>
          simp only [refined] at actual
          have same := Transition.silent.inj (Option.some.inj actual)
          subst after
          refine ⟨⟨remaining, rfl, tailPure, ?_⟩, rfl, rfl⟩
          exact refined_debt remaining ((refinement_iff _ _ _ _).mpr refined) held

/-- The region continues only while a goal remains before the saved suffix.
The transition itself is the existing independent source judgment. -/
def Continues {Context : Type} (program : SpaceSemantics.Program) (older : List Goal)
    (before after : Cursor Context) : Prop :=
  older.length < before.control.goals.length ∧ Source.Step .eagerValue program before (.silent after)

theorem step_invariant {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (held : Invariant program older destination argument before) (step : Continues program older before after) :
    Invariant program older destination argument after ∧ after.world = before.world ∧ after.context = before.context := by
  obtain ⟨debt, atGoals, pure, entailed⟩ := held
  cases debt with
  | nil =>
      have impossible := step.1
      rw [atGoals, List.nil_append] at impossible
      omega
  | cons goal remaining => exact active_step older remaining goal destination argument before after atGoals pure entailed step.2

theorem path_invariant {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (path : Relation.ReflTransGen (Continues program older) before after)
    (held : Invariant program older destination argument before) :
    Invariant program older destination argument after ∧ after.world = before.world ∧ after.context = before.context := by
  induction path with
  | refl => exact ⟨held, rfl, rfl⟩
  | tail previous advanced ih =>
      have next := step_invariant ih.1 advanced
      exact ⟨next.1, next.2.1.trans ih.2.1, next.2.2.trans ih.2.2⟩

theorem suffix_observation {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (path : Relation.ReflTransGen (Continues program older) before after)
    (held : Invariant program older destination argument before)
    (atSuffix : after.control.goals = older) (environment : Environment)
    (resolved : resolve after.control.bindings = some environment) :
    read environment destination = read environment argument ∧ after.world = before.world ∧ after.context = before.context := by
  obtain ⟨⟨debt, goals, _pure, entailed⟩, world, context⟩ := path_invariant path held
  have empty : debt = [] := by
    have length := congrArg List.length (atSuffix.symm.trans goals)
    simp only [List.length_append] at length
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst debt
  exact ⟨finished_debt entailed environment (resolve_sound resolved), world, context⟩

theorem path_destination {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {before after : Cursor Context} (path : Relation.ReflTransGen (Continues program older) before after) :
    after.control.destination = before.control.destination := by
  induction path with
  | refl => rfl
  | tail previous advanced ih => exact (ScopedReturnLocal.silent_destination advanced.2).trans ih

/-- A completed constructor leaf earns the existing alias contract. The
slot name belongs to the actual source control; no ghost equation is added. -/
theorem suffix_alias {Context : Type} {program : SpaceSemantics.Program} {older : List Goal}
    {destination argument : Atom} {before after : Cursor Context}
    (path : Relation.ReflTransGen (Continues program older) before after)
    (held : Invariant program older destination argument before)
    (atSuffix : after.control.goals = older) (name : String)
    (root : before.control.destination = destination) (slot : destination = .var name) :
    ScopedReturnLocal.AliasHolds argument after.control := by
  obtain ⟨⟨debt, goals, _pure, entailed⟩, _world, _context⟩ := path_invariant path held
  have empty : debt = [] := by
    have length := congrArg List.length (atSuffix.symm.trans goals)
    simp only [List.length_append] at length
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst debt
  have currentRoot := (path_destination path).trans root
  refine ⟨name, ?_, .inl ?_⟩
  · intro environment solved
    rw [← slot]
    exact finished_debt entailed environment solved
  · intro environment solved
    rw [currentRoot]
    exact finished_debt entailed environment solved

/-- An actual refused data step is the actual inconsistent source equation.
It cannot be inferred from exhaustion, a missing service or a timeout. -/
theorem refused_step {Context : Type} {program : SpaceSemantics.Program}
    (older remaining : List Goal) (goal : Goal) (before reached : Cursor Context) (bindings : Equations)
    (atGoal : before.control.goals = (goal :: remaining) ++ older)
    (pure : PureGoal program goal)
    (step : Source.Step .eagerValue program before (.finish (.noValue bindings, reached))) :
    reached = before ∧ bindings = before.control.bindings ∧
      ∃ expression target, goal = .equate expression target ∧
        ¬ ∃ environment, Solves environment before.control.bindings ∧
          read environment expression = read environment target := by
  cases pure with
  | evaluate data =>
      have actual := step.execution
      simp only [EagerDFS.Destination.machine, atGoal, List.cons_append] at actual
      cases actual
  | equate expression target =>
      have actual := step.execution
      simp only [EagerDFS.Destination.machine, atGoal, List.cons_append] at actual
      cases refined : refine before.control.bindings expression target with
      | some after => simp only [refined] at actual; cases actual
      | none =>
          simp only [refined] at actual
          have same := Transition.finish.inj (Option.some.inj actual)
          have pairs := Prod.mk.inj same
          have frames : reached = before := pairs.2.symm
          have bindingsSame : bindings = before.control.bindings := Result.noValue.inj pairs.1.symm
          have refused := (refinement_iff _ _ _ _).mpr refined
          cases refused with
          | refused noSolution => exact ⟨frames, bindingsSame, expression, target, rfl, noSolution⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataDebt
