import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataDebt

/-!
# Compound return recipes with unpaid constructor equations

A return may still be in its authored continuation, be partway through
the source preparer's pure constructor equations, or already be earned.
The middle case is deliberately not a value certificate. Its equations
must be paid by actual source steps before the destination can be read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnState

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnSyntax (Returns)
open ScopedReturnObligation (Pending AtHead)
open ScopedReturnLocal (Reads)
open DestinationDataRecipe
open DestinationDataDebt (Entails)
open RefinementTransport

theorem data_recipe_is_not_a_callable {program : SpaceSemantics.Program} {recipe : Atom}
    (data : Recipe program recipe) (head : String) (arguments : List Atom) (called : callable program head = true) :
    recipe ≠ .expression (.symbol head :: arguments) := by
  intro same
  cases data with
  | variableValue | symbol | grounded => cases same
  | named name fields ordinary localForm inert surface children =>
      have shape : name = head ∧ fields = arguments := by simpa using same
      rw [shape.1, called] at inert
      cases inert
  | tuple children noHead parts => exact noHead head arguments (Atom.expression.inj same)

/-- A physically present pure prefix owes the result equation. In particular,
neither arbitrary prefix work nor a guessed body result can serve as debt. -/
def Owes (program : SpaceSemantics.Program) (recipe : Atom) (control : Control) : Prop :=
  ∃ debt older, control.goals = debt ++ older ∧ AllPure program debt ∧
    Entails control.bindings debt control.destination recipe

def Holds (program : SpaceSemantics.Program) (recipe : Atom)
    (observation : Environment → Atom) (control : Control) : Prop :=
  Reads control.bindings recipe observation ∧
    (Reads control.bindings control.destination observation ∨
      Pending recipe control.destination control.goals ∨ Owes program recipe control)

theorem Owes.empty {recipe : Atom} {control : Control}
    {observation : Environment → Atom} (reads : Reads control.bindings recipe observation)
    (held : Entails control.bindings [] control.destination recipe) :
    Reads control.bindings control.destination observation := by
  intro environment solved
  exact (DestinationDataDebt.finished_debt held environment solved).trans (reads environment solved)

theorem Owes.head_or_paid {program : SpaceSemantics.Program} {recipe : Atom} {control : Control}
    {observation : Environment → Atom} {goal : Goal} {older : List Goal}
    (reads : Reads control.bindings recipe observation) (owes : Owes program recipe control)
    (atGoal : control.goals = goal :: older) :
    Reads control.bindings control.destination observation ∨ PureGoal program goal := by
  obtain ⟨debt, saved, goals, pure, entailed⟩ := owes
  cases debt with
  | nil => exact .inl (Owes.empty reads entailed)
  | cons first rest =>
      have same : first = goal := (List.cons.inj (by simpa using goals.symm.trans atGoal)).1
      exact .inr (same ▸ pure first List.mem_cons_self)

/-- Outside a pure data prefix, no unpaid constructor equation can hide at
the current operation. The remaining alternatives are the established
value and pending-continuation cases. -/
theorem Holds.outside_debt {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {control : Control} {goal : Goal} {older : List Goal}
    (held : Holds program recipe observation control) (atGoal : control.goals = goal :: older)
    (notPure : ¬ PureGoal program goal) :
    Reads control.bindings control.destination observation ∨ Pending recipe control.destination control.goals := by
  rcases held.2 with realized | pending | owes
  · exact .inl realized
  · exact .inr pending
  · rcases owes.head_or_paid held.1 atGoal with realized | pure
    · exact .inl realized
    · exact (notPure pure).elim

theorem Owes.silent_preserves {Context : Type} {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {before after : Cursor Context}
    (reads : Reads before.control.bindings recipe observation) (owes : Owes program recipe before.control)
    (step : Source.Step .eagerValue program before (.silent after)) :
    Reads after.control.bindings after.control.destination observation ∨ Owes program recipe after.control := by
  have extended : Extends before.control.bindings after.control.bindings :=
    local_step_extends step _ (by simp [localRecords])
  have destination := ScopedReturnLocal.silent_destination step
  obtain ⟨debt, older, goals, pure, entailed⟩ := owes
  cases debt with
  | nil =>
      left
      rw [destination]
      exact (Owes.empty reads entailed).extends extended
  | cons goal remaining =>
      obtain ⟨⟨following, afterGoals, afterPure, afterEntails⟩, _world, _context⟩ :=
        DestinationDataDebt.active_step older remaining goal before.control.destination recipe before after
          goals pure entailed step
      right
      exact ⟨following, older, afterGoals, afterPure, destination ▸ afterEntails⟩

/-- The actual preparer either retains a source return continuation or
expands a data leaf to its unpaid equations. -/
theorem prepared_return (program : SpaceSemantics.Program) (control next : Control)
    (recipe expression destination : Atom) (older : List Goal) (data : Recipe program recipe)
    (returns : Returns recipe expression) (ordinary : Source.scopedForm expression = false)
    (notSequence : ∀ pairs body, expression ≠ .expression [.symbol "let*", .expression pairs, body])
    (prepared : Source.Prepared .eagerValue program control destination older expression next) :
    Pending recipe destination next.goals ∨
      ∃ debt, next.goals = debt ++ older ∧ AllPure program debt ∧
        Entails next.bindings debt destination recipe := by
  rw [← prepared.execution]
  cases returns with
  | leaf =>
      right
      refine ⟨expansion program control recipe destination, expansion_suffix data control destination older,
        expansion_pure data control destination, ?_⟩
      rw [(data.prepared control destination older).retains_frame.1]
      intro environment _solved pending
      exact (expansion_entails data control destination environment pending).symm
  | empty => cases ordinary
  | emptyChoice => cases ordinary
  | @binding pattern producer body returns =>
      exact .inl (ScopedReturnObligation.binding_preparation returns program pattern producer
        (.var (freshName control 0)) older)
  | @sequential pairs body returns => exact (notSequence pairs body rfl).elim
  | @conditional condition yes no yesReturn noReturn =>
      exact .inl (ScopedReturnObligation.conditional_preparation yesReturn noReturn condition
        (.var (freshName control 0)) older)
  | @conditionalAbsent condition yes yesReturn =>
      exact .inl (ScopedReturnObligation.conditional_absent_preparation yesReturn condition
        (.var (freshName control 0)) older)
  | @query space pattern body returns =>
      left
      have arguments := ScopedReturnPreparation.match_arguments_are_source_recipes program space pattern body
        (.var (freshName control 0)) (.var (freshName control 1)) (.var (freshName control 2))
      have selected : callable program "match" = true := by simp [callable, StdLib.known]
      simpa [prepare, selected, freshSlots, List.range_succ, arguments, replace] using
        (Pending.readyQuery (.var (freshName control 0)) pattern body older returns).prepend_evaluation
          space (.var (freshName control 0))

/-- Compound leaves, arbitrary prefix preparation, branch selection, actual
unification and propagated-error delimiters all use the same source step. -/
theorem silent_preserves {Context : Type} {program : SpaceSemantics.Program} {recipe : Atom}
    {before after : Cursor Context} (observation : Environment → Atom) (data : Recipe program recipe)
    (holds : Holds program recipe observation before.control)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (step : Source.Step .eagerValue program before (.silent after)) :
    Holds program recipe observation after.control := by
  have extended : Extends before.control.bindings after.control.bindings :=
    local_step_extends step _ (by simp [localRecords])
  refine ⟨holds.1.extends extended, ?_⟩
  rcases holds.2 with realized | pending | owes
  · left
    rw [ScopedReturnLocal.silent_destination step]
    exact realized.extends extended
  · cases step with
    | restoring boundary older atGoal =>
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · cases head
        · exact .inr (.inl tail)
    | expanded expression destination older next atGoal ordinary prepared =>
        rw [prepared.retains_frame.2.1]
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · rcases head with ⟨same, returns⟩
          rcases prepared_return program before.control next recipe expression destination older data returns ordinary
              (fun pairs body identical => noSequence pairs body destination older (identical ▸ atGoal)) prepared with
              stillPending | ⟨debt, goals, pure, entailed⟩
          · exact .inr (.inl (same ▸ stillPending))
          · right; right
            refine ⟨debt, older, goals, pure, ?_⟩
            change Entails next.bindings debt next.destination recipe
            rw [prepared.retains_frame.2.1, ← same]
            exact entailed
        · exact .inr (.inl (tail.prepared_prefix prepared))
    | accepted expression destination older bindings atGoal matched =>
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · rcases head with ⟨same, identical⟩
          left
          change Reads bindings before.control.destination observation
          rw [← same]
          exact Reads.refined_destination holds.1 (identical ▸ matched)
        · exact .inr (.inl tail)
    | conditional condition yes no destination older environment atGoal resolved =>
        right; left
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · rcases head with ⟨same, yesReturn, noReturn⟩
          change Pending recipe before.control.destination
            (.evaluate (if read environment condition == Effects.boolean true then yes else no) destination :: older)
          rw [← same]
          apply Pending.evaluation
          split <;> assumption
        · exact tail.prepend_evaluation _ _
    | printed arguments destination older environment printed atGoal resolved readout =>
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · simp [AtHead] at head
        · exact .inr (.inl (tail.prepend_equation _ _))
    | argument expression destination younger older action atGoal returned =>
        cases returned with
        | ordinary environment resolved normal =>
            rcases pending.head_or_tail _ _ atGoal with head | tail
            · cases head
            · exact .inr (.inl tail)
        | propagated environment resolved error bindings matched =>
            exact .inr (.inl (pending.return_delimiter expression destination older.length (younger ++ older) older
              atGoal (callerSuffix?_split younger older)))
  · rcases owes.silent_preserves holds.1 step with realized | nextDebt
    · exact .inl realized
    · exact .inr (.inr nextDebt)

theorem terminal_reads {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {control : Control}
    (holds : Holds program recipe observation control) (terminal : control.goals = []) :
    Reads control.bindings control.destination observation := by
  rcases holds.2 with realized | pending | ⟨debt, older, goals, pure, entailed⟩
  · exact realized
  · exact (pending.nonempty terminal).elim
  · have empty : debt = [] := (List.append_eq_nil_iff.mp (goals.symm.trans terminal)).1
    subst debt
    exact Owes.empty holds.1 entailed

theorem terminal_observation {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {control : Control}
    (holds : Holds program recipe observation control) (terminal : control.goals = [])
    (environment : Environment) (resolved : resolve control.bindings = some environment) :
    read environment control.destination = observation environment :=
  terminal_reads holds terminal environment (resolve_sound resolved)

/-- The source invariant depends on actual constraints and pending work, not
reserved-name or cut metadata. Refinement keeps every already owed equation. -/
theorem Holds.refinement {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {before after : Control}
    (held : Holds program recipe observation before) (extended : Extends before.bindings after.bindings)
    (goals : after.goals = before.goals) (destination : after.destination = before.destination) :
    Holds program recipe observation after := by
  refine ⟨held.1.extends extended, ?_⟩
  rcases held.2 with realized | pending | ⟨debt, older, atGoals, pure, entailed⟩
  · left
    rw [destination]
    exact realized.extends extended
  · right; left
    rw [destination, goals]
    exact pending
  · right; right
    refine ⟨debt, older, goals.trans atGoals, pure, ?_⟩
    rw [destination]
    exact fun environment solved unpaid => entailed environment (extended environment solved) unpaid

/-- The earlier variable contract embeds without changing its observation,
its pending goals or the evaluator. -/
theorem variable_instance {program : SpaceSemantics.Program} {name : String}
    {observation : Environment → Atom} {control : Control}
    (holds : ScopedReturnLocal.Holds name observation control) :
    Holds program (.var name) observation control :=
  ⟨holds.1, holds.2.imp_right Or.inl⟩

theorem Owes.prepend_equation {program : SpaceSemantics.Program} {recipe : Atom} {control : Control}
    (owes : Owes program recipe control) (value destination : Atom) :
    Owes program recipe {control with goals := .equate value destination :: control.goals} := by
  obtain ⟨debt, older, goals, pure, entailed⟩ := owes
  refine ⟨.equate value destination :: debt, older, ?_, ?_, ?_⟩
  · simp only [List.cons_append, goals]
  · intro goal member
    rcases List.mem_cons.mp member with rfl | present
    · exact .equate _ _
    · exact pure goal present
  · exact fun environment solved pending => entailed environment solved
      (fun goal member => pending goal (List.mem_cons_of_mem _ member))

theorem Holds.prepend_equation {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {control : Control}
    (held : Holds program recipe observation control) (value destination : Atom) :
    Holds program recipe observation {control with goals := .equate value destination :: control.goals} := by
  refine ⟨held.1, ?_⟩
  rcases held.2 with realized | pending | owes
  · exact .inl realized
  · exact .inr (.inl (pending.prepend_equation value destination))
  · exact .inr (.inr (owes.prepend_equation value destination))

/-- Each selected occurrence carries its own fresh source recipe. The alias
relates reached reads, not a frozen copy of an open input's entry value. -/
def AliasHolds (program : SpaceSemantics.Program) (argument : Atom) (control : Control) : Prop :=
  ∃ recipe, Recipe program recipe ∧ Holds program recipe (fun environment => read environment argument) control

theorem AliasHolds.refinement {program : SpaceSemantics.Program} {argument : Atom} {before after : Control}
    (held : AliasHolds program argument before) (extended : Extends before.bindings after.bindings)
    (goals : after.goals = before.goals) (destination : after.destination = before.destination) :
    AliasHolds program argument after := by
  obtain ⟨recipe, data, returning⟩ := held
  exact ⟨recipe, data, returning.refinement extended goals destination⟩

theorem variable_alias_instance {program : SpaceSemantics.Program} {argument : Atom} {control : Control}
    (held : ScopedReturnLocal.AliasHolds argument control) : AliasHolds program argument control := by
  obtain ⟨name, returning⟩ := held
  exact ⟨.var name, .variableValue name, variable_instance returning⟩

theorem alias_observation_congr {program : SpaceSemantics.Program} (control : Control) (left right : Atom)
    (same : ∀ environment, Solves environment control.bindings → read environment left = read environment right)
    (held : AliasHolds program left control) : AliasHolds program right control := by
  obtain ⟨recipe, data, protectedRead, returning⟩ := held
  refine ⟨recipe, data, ?_, ?_⟩
  · exact fun environment solved => (protectedRead environment solved).trans (same environment solved)
  · rcases returning with realized | pending | debt
    · exact .inl (fun environment solved => (realized environment solved).trans (same environment solved))
    · exact .inr (.inl pending)
    · exact .inr (.inr debt)

/-- A materialized operand is related back to its original source recipe
using the reached constraints, including later bindings of open variables. -/
theorem original_recipe_alias {program : SpaceSemantics.Program} (before : Equations) (environment : Environment)
    (resolved : resolve before = some environment) (control : Control) (recipe : Atom)
    (extended : Extends before control.bindings) (held : AliasHolds program (read environment recipe) control) :
    AliasHolds program recipe control :=
  alias_observation_congr control (read environment recipe) recipe
    (fun candidate solved => resolve_read_preserved_by_extension resolved extended candidate solved recipe) held

/-- Only a terminal control can re-enter the earlier alias API through its
actual output slot. The input recipe is not replaced and no equation is added. -/
theorem terminal_slot_alias {program : SpaceSemantics.Program} {argument : Atom} {control : Control}
    (held : AliasHolds program argument control) (terminal : control.goals = [])
    (name : String) (slot : control.destination = .var name) : ScopedReturnLocal.AliasHolds argument control := by
  obtain ⟨recipe, data, returning⟩ := held
  have earned := terminal_reads returning terminal
  refine ⟨name, ?_, .inl earned⟩
  intro environment solved
  rw [← slot]
  exact earned environment solved

theorem alias_silent_preserves {Context : Type} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (argument : Atom) (held : AliasHolds program argument before.control)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (step : Source.Step .eagerValue program before (.silent after)) : AliasHolds program argument after.control := by
  obtain ⟨recipe, data, returns⟩ := held
  exact ⟨recipe, data, silent_preserves _ data returns noSequence step⟩

theorem terminal_alias_observation {program : SpaceSemantics.Program} {argument : Atom} {control : Control}
    (held : AliasHolds program argument control) (terminal : control.goals = [])
    (environment : Environment) (resolved : resolve control.bindings = some environment) :
    read environment control.destination = read environment argument := by
  obtain ⟨recipe, data, returns⟩ := held
  exact terminal_observation returns terminal environment resolved

/-- A sequence of actual local steps, after the outer owner has handled
sequential-let entry. The path does not promise termination or success. -/
def LocalAdvance {Context : Type} (program : SpaceSemantics.Program) (before after : Cursor Context) : Prop :=
  (∀ pairs body destination older,
    before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older) ∧
    Source.Step .eagerValue program before (.silent after)

theorem local_path_preserves {Context : Type} {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {before after : Cursor Context}
    (data : Recipe program recipe)
    (path : Relation.ReflTransGen (LocalAdvance program) before after)
    (held : Holds program recipe observation before.control) : Holds program recipe observation after.control := by
  induction path with
  | refl => exact held
  | tail previous step ih => exact silent_preserves observation data ih step.1 step.2

theorem local_path_alias {Context : Type} {program : SpaceSemantics.Program} {argument : Atom}
    {before after : Cursor Context} (path : Relation.ReflTransGen (LocalAdvance program) before after)
    (held : AliasHolds program argument before.control) : AliasHolds program argument after.control := by
  obtain ⟨recipe, data, returns⟩ := held
  exact ⟨recipe, data, local_path_preserves data path returns⟩

theorem local_path_terminal_read {Context : Type} {program : SpaceSemantics.Program} {argument : Atom}
    {before after : Cursor Context} (path : Relation.ReflTransGen (LocalAdvance program) before after)
    (held : AliasHolds program argument before.control) (terminal : after.control.goals = [])
    (environment : Environment) (resolved : resolve after.control.bindings = some environment) :
    read environment after.control.destination = read environment argument :=
  terminal_alias_observation (local_path_alias path held) terminal environment resolved

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnState
