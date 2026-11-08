import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnLocal

/-!
# Return obligations through the owned source dispatch operations

These laws concern actual selected records and original source recipes.
They preserve the pending return across macro entry and per-row selection;
they do not replace a query body or callee with a returned-value oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open EagerDFSStreaming.Scoped.ProtectedContinuation
open ScopedReturnSyntax (Returns)
open ScopedReturnObligation (Pending AtHead)
open ScopedReturnLocal (Holds Reads)
open RefinementTransport

theorem sequence_body_returns (name : String) (pairs : List Atom) (body : Atom)
    (returns : Returns (.var name) (.expression [.symbol "let*", .expression pairs, body])) :
    Returns (.var name) body := by
  generalize shape : Atom.expression [.symbol "let*", .expression pairs, body] = expression at returns
  cases returns <;> simp_all

theorem case_is_not_a_return_recipe (name : String) (key : Atom) (rows : List Atom) :
    ¬ Returns (.var name) (.expression [.symbol "case", key, .expression rows]) := by
  intro returns
  generalize shape : Atom.expression [.symbol "case", key, .expression rows] = expression at returns
  cases returns <;> simp_all

theorem sequence_return (name : String) (observation : Environment → Atom) (control : Control)
    (pairs : List Atom) (body nested destination : Atom) (older : List Goal)
    (holds : Holds name observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (lowered : Eval.nestedLets pairs body = some nested) :
    Holds name observation {control with goals := .evaluate nested destination :: older} := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · right
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨same, returns⟩
      rw [← same]
      apply Pending.evaluation
      exact ScopedReturnSyntax.sequence_lowering_returns (sequence_body_returns name pairs body returns) _ _ lowered
    · exact tail.prepend_evaluation nested destination

theorem case_key_return (name : String) (observation : Environment → Atom) (control : Control)
    (key destination : Atom) (rows : List Atom) (older : List Goal)
    (holds : Holds name observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "case", key, .expression rows]) destination :: older) :
    Holds name observation {control with goals :=
      [.evaluate key (.var (freshName control 0)),
        .invoke "case" [.var (freshName control 0), .expression rows] destination] ++ older} := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · right
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨_, returns⟩
      exact False.elim (case_is_not_a_return_recipe name key rows returns)
    · exact tail.prepend _ rfl

theorem case_body_return (name : String) (observation : Environment → Atom) (control : Control)
    (key destination : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
    (choice : ScopedCaseSelection.Choice) (holds : Holds name observation control)
    (atGoal : control.goals = .invoke "case" [key, .expression rows] destination :: older)
    (parsed : Eval.readCases rows = some cases)
    (selected : ScopedCaseSelection.Selection control.bindings key 0 cases (some choice)) :
    Holds name observation {control with bindings := choice.bindings, goals := .evaluate choice.body destination :: older} := by
  have extended := (ScopedCaseSelection.selected_record selected).1
  refine ⟨holds.1.extends extended, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl (realized.extends extended)
  · right
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨same, authored, authoredParsed, returns⟩
      have sameCases := Option.some.inj (authoredParsed.symm.trans parsed)
      subst authored
      rw [← same]
      exact .evaluation _ older (ScopedCaseSelection.selected_body_property _ returns selected)
    · exact tail.prepend_evaluation _ destination

theorem query_selected_destination {control : Control} {pattern body destination : Atom}
    {older : List Goal} {start : Nat} {rows : List Atom} {selected : List (Nat × Control)}
    (source : QueryFrontier control pattern body destination older start rows selected) :
    ∀ chosen ∈ selected, chosen.2.destination = control.destination := by
  induction source with
  | nil => simp
  | selected start row rest bindings tail accepted following ih =>
      intro chosen member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact ih chosen later
  | refused start row rest tail rejected following ih => exact ih

theorem query_selected_return (name : String) (observation : Environment → Atom) (control : Control)
    (space pattern body destination : Atom) (older : List Goal)
    (rows : List Atom) (start : Nat) (selected : List (Nat × Control))
    (holds : Holds name observation control)
    (atGoal : control.goals = .query space pattern body destination :: older)
    (source : QueryFrontier control pattern body destination older start rows selected) :
    ∀ chosen ∈ selected, Holds name observation chosen.2 := by
  intro chosen present
  have extended := query_frontier_good source chosen present
  have sameDestination := query_selected_destination source chosen present
  have goals := MatchSource.selected_template_is_original_recipe source chosen present
  refine ⟨holds.1.extends extended, ?_⟩
  rcases holds.2 with realized | pending
  · left
    rw [sameDestination]
    exact realized.extends extended
  · right
    rw [sameDestination, goals]
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨same, returns⟩
      rw [← same]
      exact .evaluation body older returns
    · exact tail.prepend_evaluation body destination

theorem query_ready_to_owned (name : String) (observation : Environment → Atom) (control : Control)
    (space pattern body destination : Atom) (older : List Goal) (holds : Holds name observation control)
    (atGoal : control.goals = .invoke "match" [space, pattern, body] destination :: older) :
    Holds name observation {control with goals := .query space pattern body destination :: older} := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · right
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨same, returns⟩
      rw [← same]
      exact .query space pattern body older returns
    · simpa only [List.singleton_append] using
        tail.prepend [.query space pattern body destination] rfl

theorem captured_query_return (name : String) (observation : Environment → Atom) (control : Control)
    (space pattern readPattern body destination : Atom) (older : List Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × Control))
    (holds : Holds name observation control)
    (atGoal : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (source : ScopedQuerySource.Choices control readPattern body destination older offset rows selected) :
    ∀ chosen ∈ selected, Holds name observation chosen.2 := by
  intro chosen present
  have fields := source.frames chosen present
  obtain ⟨suffix, record⟩ := fields.2.2.2.2.2.2.1
  have extended : Extends control.bindings chosen.2.bindings := record ▸ append_extends _ suffix
  refine ⟨holds.1.extends extended, ?_⟩
  rcases holds.2 with realized | pending
  · left
    rw [fields.2.2.2.1]
    exact realized.extends extended
  · right
    rw [fields.2.2.2.1, fields.2.2.1]
    rcases pending.head_or_tail _ _ atGoal with head | tail
    · rcases head with ⟨same, returns⟩
      rw [← same]
      exact .evaluation body older returns
    · exact tail.prepend_evaluation body destination

theorem ordinary_invocation_keeps_tail {recipe target : Atom} {control : Control}
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (pending : Pending recipe target control.goals)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (notQuery : head ≠ "match") (notCase : head ≠ "case") : Pending recipe target older := by
  rcases pending.head_or_tail _ _ atGoal with head | tail
  · simp [AtHead, notQuery, notCase] at head
  · exact tail

theorem primitive_choices_return {Context : Type} (name : String) (observation : Environment → Atom)
    (control : Control) (context : Context) (origins : List Nat) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (values : List Atom)
    (holds : Holds name observation control)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (notQuery : head ≠ "match") (notCase : head ≠ "case") :
    ∀ work ∈ primitiveWork control context origins destination older values, Holds name observation work.1 := by
  intro work present
  obtain ⟨⟨value, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · exact .inr ((ordinary_invocation_keeps_tail head arguments destination older pending atGoal notQuery notCase).prepend_equation value destination)

theorem equation_choice_return {program : SpaceSemantics.Program} (name : String)
    (observation : Environment → Atom) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence retained : Nat) (next : Control)
    (holds : Holds name observation control)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (notQuery : head ≠ "match") (notCase : head ≠ "case")
    (decision : ClauseChoice.Decision program control head arguments destination older occurrence (some next)) :
    Holds name observation (predicateEntry retained next) := by
  cases decision with
  | selected equation bindings row sameHead matched =>
      have extended := accepted_extends matched
      refine ⟨holds.1.extends extended, ?_⟩
      rcases holds.2 with realized | pending
      · exact .inl (realized.extends extended)
      · right
        have tail := ordinary_invocation_keeps_tail head arguments destination older pending atGoal notQuery notCase
        exact tail.prepend [.evaluate (ClauseChoice.freshBody control occurrence equation) destination,
          .restoreCommit control.cutBoundary] rfl

theorem equation_frontier_return {program : SpaceSemantics.Program} (name : String)
    (observation : Environment → Atom) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (positions : List Nat) (selected : List (Nat × Control))
    (retained : Nat) (holds : Holds name observation control)
    (atGoal : control.goals = .invoke head arguments destination :: older)
    (notQuery : head ≠ "match") (notCase : head ≠ "case")
    (frontier : ClauseChoice.Frontier program control head arguments destination older positions selected) :
    ∀ chosen ∈ selected, Holds name observation (predicateEntry retained chosen.2) := by
  induction frontier with
  | nil => simp
  | skip decision rest ih => exact ih
  | @keep occurrence remaining next answers decision rest ih =>
      intro chosen present
      rcases List.mem_cons.mp present with rfl | later
      · exact equation_choice_return name observation control head arguments destination older occurrence retained next
          holds atGoal notQuery notCase decision
      · exact ih chosen later

theorem collapse_is_not_a_return_recipe (name : String) (child : Atom) :
    ¬ Returns (.var name) (.expression [.symbol "collapse", child]) := by
  intro returns
  generalize shape : Atom.expression [.symbol "collapse", child] = expression at returns
  cases returns <;> simp_all

theorem collapse_saved_return (name : String) (observation : Environment → Atom)
    (control : Control) (child destination : Atom) (older : List Goal)
    (holds : Holds name observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", child]) destination :: older) :
    Holds name observation {control with goals := older} := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · rcases pending.head_or_tail _ _ atGoal with head | tail
    · exact False.elim (collapse_is_not_a_return_recipe name child head.2)
    · exact .inr tail

theorem nonempty_choice_is_not_a_return_recipe (name : String) (first : Atom) (rest : List Atom) :
    ¬ Returns (.var name) (.expression [.symbol "superpose", .expression (first :: rest)]) := by
  intro returns
  generalize shape : Atom.expression [.symbol "superpose", .expression (first :: rest)] = expression at returns
  cases returns <;> simp_all

theorem superpose_choices_return {Context : Type} (name : String) (observation : Environment → Atom)
    (control : Control) (context : Context) (origins : List Nat) (alternatives : List Atom)
    (destination : Atom) (older : List Goal) (holds : Holds name observation control)
    (atGoal : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    ∀ work ∈ superposeWork control context origins alternatives destination older, Holds name observation work.1 := by
  intro work present
  cases alternatives with
  | nil => simp [superposeWork] at present
  | cons first rest =>
      obtain ⟨⟨expression, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
      refine ⟨holds.1, ?_⟩
      rcases holds.2 with realized | pending
      · exact .inl realized
      · rcases pending.head_or_tail _ _ atGoal with head | tail
        · exact False.elim (nonempty_choice_is_not_a_return_recipe name first rest head.2)
        · exact .inr (tail.prepend_evaluation expression destination)

theorem open_commit_keeps_return (name : String) (observation : Environment → Atom)
    (control : Control) (older : List Goal) (boundary : Nat) (holds : Holds name observation control)
    (atGoal : control.goals = .openCommit :: older) :
    Holds name observation {control with goals := older, cutBoundary := boundary} := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · rcases pending.head_or_tail _ _ atGoal with head | tail
    · cases head
    · exact .inr tail

theorem commit_keeps_return (name : String) (observation : Environment → Atom)
    (control : Control) (older : List Goal) (holds : Holds name observation control)
    (atGoal : control.goals = .commit :: older) :
    Holds name observation {control with goals := older} := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · rcases pending.head_or_tail _ _ atGoal with head | tail
    · cases head
    · exact .inr tail

theorem allocated_collection_return {Context : Type} (name : String) (observation : Environment → Atom)
    (copies : List (Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Token × (Atom × List Atom)))
    (caller : CollectionCaller Context) (holds : Holds name observation caller.1) :
    Holds name observation (allocatedWork copies caller).1 := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · exact .inr (pending.prepend_equation _ _)

theorem copied_collection_return {Context : Type} (name : String) (observation : Environment → Atom)
    (boundary : Finset String) (answers : List CollectedAnswer) (caller : CollectionCaller Context)
    (holds : Holds name observation caller.1) :
    Holds name observation (copiedWork boundary answers caller).1 := by
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · exact .inr (pending.prepend_equation _ _)

theorem primitive_choices_with_tail {Context : Type} (name : String) (observation : Environment → Atom)
    (control : Control) (context : Context) (origins : List Nat) (destination : Atom)
    (older : List Goal) (values : List Atom) (holds : Holds name observation control)
    (tail : Pending (.var name) control.destination control.goals → Pending (.var name) control.destination older) :
    ∀ work ∈ primitiveWork control context origins destination older values, Holds name observation work.1 := by
  intro work present
  obtain ⟨⟨value, occurrence⟩, _present, rfl⟩ := List.mem_map.mp present
  refine ⟨holds.1, ?_⟩
  rcases holds.2 with realized | pending
  · exact .inl realized
  · exact .inr ((tail pending).prepend_equation value destination)

theorem equation_choice_with_tail {program : SpaceSemantics.Program} (name : String)
    (observation : Environment → Atom) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (occurrence retained : Nat) (next : Control)
    (holds : Holds name observation control)
    (tail : Pending (.var name) control.destination control.goals → Pending (.var name) control.destination older)
    (decision : ClauseChoice.Decision program control head arguments destination older occurrence (some next)) :
    Holds name observation (predicateEntry retained next) := by
  cases decision with
  | selected equation bindings row sameHead matched =>
      have extended := accepted_extends matched
      refine ⟨holds.1.extends extended, ?_⟩
      rcases holds.2 with realized | pending
      · exact .inl (realized.extends extended)
      · exact .inr ((tail pending).prepend
          [.evaluate (ClauseChoice.freshBody control occurrence equation) destination,
            .restoreCommit control.cutBoundary] rfl)

theorem equation_frontier_with_tail {program : SpaceSemantics.Program} (name : String)
    (observation : Environment → Atom) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) (positions : List Nat) (selected : List (Nat × Control))
    (retained : Nat) (holds : Holds name observation control)
    (tail : Pending (.var name) control.destination control.goals → Pending (.var name) control.destination older)
    (frontier : ClauseChoice.Frontier program control head arguments destination older positions selected) :
    ∀ chosen ∈ selected, Holds name observation (predicateEntry retained chosen.2) := by
  induction frontier with
  | nil => simp
  | skip decision rest ih => exact ih
  | @keep occurrence remaining next answers decision rest ih =>
      intro chosen present
      rcases List.mem_cons.mp present with rfl | later
      · exact equation_choice_with_tail name observation control head arguments destination older occurrence retained next
          holds tail decision
      · exact ih chosen later

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDispatch
