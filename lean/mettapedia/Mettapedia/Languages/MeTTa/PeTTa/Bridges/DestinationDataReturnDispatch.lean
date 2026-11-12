import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnState
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDispatch

/-!
# Owned dispatch around compound return recipes

The surrounding source operations preserve a pending compound return.
They do not execute its template in a host service or replace a selected
record by its entry record. Constructor debt is absent at non-data heads;
saved collection callers retain their own original continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnSyntax (Returns)
open ScopedReturnObligation (Pending AtHead)
open ScopedReturnLocal (Reads)
open DestinationDataRecipe
open DestinationDataReturnState
open RefinementTransport

theorem not_surface_recipe {program : SpaceSemantics.Program} {recipe : Atom}
    (data : Recipe program recipe) (head : String) (arguments : List Atom)
    (surface : head = "let*" ∨ head = "case") : recipe ≠ .expression (.symbol head :: arguments) := by
  intro same
  cases data with
  | variableValue | symbol | grounded => cases same
  | named name fields ordinary localForm inert excluded children =>
      have shape : name = head ∧ fields = arguments := by simpa using same
      rcases shape with ⟨rfl, rfl⟩
      rcases surface with rfl | rfl
      · exact excluded.1 rfl
      · exact excluded.2 rfl
  | tuple children noHead parts => exact noHead head arguments (Atom.expression.inj same)

theorem not_scoped_recipe {program : SpaceSemantics.Program} {recipe expression : Atom}
    (data : Recipe program recipe) (owned : Source.scopedForm expression = true) : recipe ≠ expression := by
  intro same
  have no := data.not_scoped
  rw [same, owned] at no
  cases no

theorem sequence_body_returns {program : SpaceSemantics.Program} {recipe : Atom}
    (data : Recipe program recipe) (pairs : List Atom) (body : Atom)
    (returns : Returns recipe (.expression [.symbol "let*", .expression pairs, body])) :
    Returns recipe body := by
  generalize shape : Atom.expression [.symbol "let*", .expression pairs, body] = expression at returns
  cases returns <;> try simp_all
  exact (not_surface_recipe data "let*" [.expression pairs, body] (.inl rfl) shape.symm).elim

theorem case_not_return {program : SpaceSemantics.Program} {recipe : Atom}
    (data : Recipe program recipe) (key : Atom) (rows : List Atom) :
    ¬ Returns recipe (.expression [.symbol "case", key, .expression rows]) := by
  intro returns
  generalize shape : Atom.expression [.symbol "case", key, .expression rows] = expression at returns
  cases returns <;> try simp_all
  exact (not_surface_recipe data "case" [key, .expression rows] (.inr rfl) shape.symm).elim

theorem collapse_not_return {program : SpaceSemantics.Program} {recipe : Atom}
    (data : Recipe program recipe) (child : Atom) :
    ¬ Returns recipe (.expression [.symbol "collapse", child]) := by
  intro returns
  generalize shape : Atom.expression [.symbol "collapse", child] = expression at returns
  cases returns <;> try simp_all
  exact (not_scoped_recipe data (expression := .expression [.symbol "collapse", child]) rfl shape.symm).elim

theorem choice_not_return {program : SpaceSemantics.Program} {recipe : Atom}
    (data : Recipe program recipe) (first : Atom) (rest : List Atom) :
    ¬ Returns recipe (.expression [.symbol "superpose", .expression (first :: rest)]) := by
  intro returns
  generalize shape : Atom.expression [.symbol "superpose", .expression (first :: rest)] = expression at returns
  cases returns <;> try simp_all
  exact (not_scoped_recipe data (expression := .expression [.symbol "superpose", .expression (first :: rest)]) rfl
    shape.symm).elim

/-- All record changes below are the source's actual constraint extensions.
This helper transfers only the already-earned and still-pending cases. -/
theorem nondata_transition {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} {before after : Control} {goal : Goal} {older : List Goal}
    (held : Holds program recipe observation before) (atGoal : before.goals = goal :: older)
    (notPure : ¬ PureGoal program goal) (extended : Extends before.bindings after.bindings)
    (destination : after.destination = before.destination)
    (pending : Pending recipe before.destination before.goals → Pending recipe after.destination after.goals) :
    Holds program recipe observation after := by
  refine ⟨held.1.extends extended, ?_⟩
  rcases held.outside_debt atGoal notPure with realized | awaiting
  · left
    rw [destination]
    exact realized.extends extended
  · exact .inr (.inl (pending awaiting))

theorem sequence_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (data : Recipe program recipe) (control : Control) (pairs : List Atom) (body nested destination : Atom)
    (older : List Goal) (held : Holds program recipe observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (lowered : Eval.nestedLets pairs body = some nested) :
    Holds program recipe observation {control with goals := .evaluate nested destination :: older} := by
  apply nondata_transition held atGoal
  · intro pure
    cases pure with
    | evaluate data => exact not_surface_recipe data "let*" [.expression pairs, body] (.inl rfl) rfl
  · exact fun _ solved => solved
  · rfl
  · intro pending
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨same, returns⟩
      rw [← same]
      exact .evaluation nested older (ScopedReturnSyntax.sequence_lowering_returns
        (sequence_body_returns data pairs body returns) _ _ lowered)
    · exact tail.prepend_evaluation nested destination

theorem case_key_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (data : Recipe program recipe) (control : Control) (key destination : Atom) (rows : List Atom)
    (older : List Goal) (held : Holds program recipe observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "case", key, .expression rows]) destination :: older) :
    Holds program recipe observation {control with goals :=
      [.evaluate key (.var (freshName control 0)),
        .invoke "case" [.var (freshName control 0), .expression rows] destination] ++ older} := by
  apply nondata_transition held atGoal
  · intro pure
    cases pure with
    | evaluate data => exact not_surface_recipe data "case" [key, .expression rows] (.inr rfl) rfl
  · exact fun _ solved => solved
  · rfl
  · intro pending
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · exact (case_not_return data key rows head.2).elim
    · exact tail.prepend _ rfl

theorem query_selected_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (control : Control) (space pattern body destination : Atom) (older : List Goal)
    (rows : List Atom) (start : Nat) (selected : List (Nat × Control))
    (held : Holds program recipe observation control)
    (atGoal : control.goals = .query space pattern body destination :: older)
    (source : QueryFrontier control pattern body destination older start rows selected) :
    ∀ chosen ∈ selected, Holds program recipe observation chosen.2 := by
  intro chosen present
  apply nondata_transition held atGoal (by intro impossible; cases impossible)
    (query_frontier_good source chosen present)
    (ScopedReturnDispatch.query_selected_destination source chosen present)
  intro pending
  rw [ScopedReturnDispatch.query_selected_destination source chosen present,
    MatchSource.selected_template_is_original_recipe source chosen present]
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · rcases head with ⟨same, returns⟩
    rw [← same]
    exact .evaluation body older returns
  · exact tail.prepend_evaluation body destination

theorem captured_query_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (control : Control) (space pattern readPattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × Control))
    (held : Holds program recipe observation control)
    (atGoal : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (source : ScopedQuerySource.Choices control readPattern body destination older offset rows selected) :
    ∀ chosen ∈ selected, Holds program recipe observation chosen.2 := by
  intro chosen present
  have fields := source.frames chosen present
  obtain ⟨suffix, record⟩ := fields.2.2.2.2.2.2.1
  apply nondata_transition held atGoal (by intro impossible; cases impossible)
    (record ▸ append_extends _ suffix) fields.2.2.2.1
  intro pending
  rw [fields.2.2.2.1, fields.2.2.1]
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · rcases head with ⟨same, returns⟩
    rw [← same]
    exact .evaluation body older returns
  · exact tail.prepend_evaluation body destination

theorem query_ready_to_owned {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (control : Control) (space pattern body destination : Atom) (older : List Goal)
    (held : Holds program recipe observation control)
    (atGoal : control.goals = .invoke "match" [space, pattern, body] destination :: older) :
    Holds program recipe observation {control with goals := .query space pattern body destination :: older} := by
  apply nondata_transition (after := {control with goals := .query space pattern body destination :: older})
    held atGoal (by intro impossible; cases impossible) (fun _ solved => solved) rfl
  intro pending
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · rcases head with ⟨same, returns⟩
    rw [← same]
    exact .query space pattern body older returns
  · exact tail.prepend [.query space pattern body destination] rfl

theorem case_body_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (control : Control) (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (older : List Goal) (choice : ScopedCaseSelection.Choice) (held : Holds program recipe observation control)
    (atGoal : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (parsed : Eval.readCases rows = some cases)
    (selected : ScopedCaseSelection.Selection control.bindings key 0 cases (some choice)) :
    Holds program recipe observation
      {control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older} := by
  apply nondata_transition
    (after := {control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older})
    held atGoal (by intro impossible; cases impossible)
    (ScopedCaseSelection.selected_record selected).1 rfl
  intro pending
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · rcases head with ⟨same, authored, authoredParsed, returns⟩
    have sameCases := Option.some.inj (authoredParsed.symm.trans parsed)
    subst authored
    rw [← same]
    exact .evaluation _ older (ScopedCaseSelection.selected_body_property _ returns selected)
  · exact tail.prepend_evaluation _ destination

theorem collapse_saved_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (data : Recipe program recipe) (control : Control) (child destination : Atom) (older : List Goal)
    (held : Holds program recipe observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", child]) destination :: older) :
    Holds program recipe observation {control with goals := older} := by
  apply nondata_transition held atGoal
  · intro pure
    cases pure with
    | evaluate data => exact not_scoped_recipe data (expression := .expression [.symbol "collapse", child]) rfl rfl
  · exact fun _ solved => solved
  · rfl
  · intro pending
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · exact (collapse_not_return data child head.2).elim
    · exact tail

theorem superpose_choices_return {Context : Type} {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} (data : Recipe program recipe) (control : Control)
    (context : Context) (origins : List Nat) (alternatives : List Atom) (destination : Atom) (older : List Goal)
    (held : Holds program recipe observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    ∀ work ∈ superposeWork control context origins alternatives destination older,
      Holds program recipe observation work.1 := by
  intro work present
  cases alternatives with
  | nil => simp [superposeWork] at present
  | cons first rest =>
      obtain ⟨⟨expression, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
      apply nondata_transition held atGoal
      · intro pure
        cases pure with
        | evaluate data =>
            exact not_scoped_recipe data
              (expression := .expression [.symbol "superpose", .expression (first :: rest)]) rfl rfl
      · exact fun _ solved => solved
      · rfl
      · intro pending
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · exact (choice_not_return data first rest head.2).elim
        · exact tail.prepend_evaluation expression destination

theorem primitive_choices_with_tail {Context : Type} {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} (control : Control) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) (values : List Atom)
    (held : Holds program recipe observation control)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (tail : Pending recipe control.destination control.goals → Pending recipe control.destination older) :
    ∀ work ∈ primitiveWork control context origins destination older values,
      Holds program recipe observation work.1 := by
  intro work present
  obtain ⟨⟨value, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
  apply nondata_transition (after := {control with goals := .equate value destination :: older})
    held atGoal (by intro impossible; cases impossible) (fun _ solved => solved) rfl
  exact fun pending => (tail pending).prepend_equation value destination

theorem equation_choice_with_tail {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence retained : Nat) (next : Control)
    (held : Holds program recipe observation control)
    (atGoal : ∃ sourceArguments, control.goals = .invoke head sourceArguments destination :: older)
    (tail : Pending recipe control.destination control.goals → Pending recipe control.destination older)
    (decision : ClauseChoice.Decision program control head arguments destination older occurrence (some next)) :
    Holds program recipe observation (predicateEntry retained next) := by
  obtain ⟨sourceArguments, atCall⟩ := atGoal
  cases decision with
  | selected equation bindings row sameHead matched =>
      apply nondata_transition
        (after := predicateEntry retained {control with bindings := bindings, goals := .evaluate (ClauseChoice.freshBody control occurrence equation) destination :: older})
        held atCall (by intro impossible; cases impossible) (accepted_extends matched) rfl
      exact fun pending => (tail pending).prepend
        [.evaluate (ClauseChoice.freshBody control occurrence equation) destination, .restoreCommit control.cutBoundary] rfl

theorem equation_frontier_with_tail {program : SpaceSemantics.Program} {recipe : Atom}
    {observation : Environment → Atom} (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (positions : List Nat) (selected : List (Nat × Control))
    (retained : Nat) (held : Holds program recipe observation control)
    (atGoal : ∃ sourceArguments, control.goals = .invoke head sourceArguments destination :: older)
    (tail : Pending recipe control.destination control.goals → Pending recipe control.destination older)
    (frontier : ClauseChoice.Frontier program control head arguments destination older positions selected) :
    ∀ chosen ∈ selected, Holds program recipe observation (predicateEntry retained chosen.2) := by
  induction frontier with
  | nil => simp
  | skip decision rest ih => exact ih
  | @keep occurrence remaining next answers decision rest ih =>
      intro chosen present
      rcases List.mem_cons.mp present with rfl | later
      · exact equation_choice_with_tail control head arguments destination older occurrence retained next held atGoal tail decision
      · exact ih chosen later

theorem open_commit_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (control : Control) (older : List Goal) (boundary : Nat) (held : Holds program recipe observation control)
    (atGoal : control.goals = .openCommit :: older) :
    Holds program recipe observation {control with goals := older, cutBoundary := boundary} := by
  apply nondata_transition (after := {control with goals := older, cutBoundary := boundary})
    held atGoal (by intro impossible; cases impossible) (fun _ solved => solved) rfl
  intro pending
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · cases head
  · exact tail

theorem commit_return {program : SpaceSemantics.Program} {recipe : Atom} {observation : Environment → Atom}
    (control : Control) (older : List Goal) (held : Holds program recipe observation control)
    (atGoal : control.goals = .commit :: older) :
    Holds program recipe observation {control with goals := older} := by
  apply nondata_transition (after := {control with goals := older})
    held atGoal (by intro impossible; cases impossible) (fun _ solved => solved) rfl
  intro pending
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · cases head
  · exact tail

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnDispatch
