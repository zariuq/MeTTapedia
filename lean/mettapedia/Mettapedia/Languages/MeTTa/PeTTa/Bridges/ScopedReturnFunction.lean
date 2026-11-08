import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRun

/-!
# Checked function frontiers and their complete source answer prefixes

The check reads the actual equation table, requires a declared head, and
checks every row of that head. Execution uses the existing complete ordered
clause scan. Duplicate equations remain distinct source occurrences.
This slice covers variable formal recipes; constructor recipes are not
silently admitted by this check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnFunction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS (World)
open EagerDFS.Destination
open ScopedReturnPublication

def clauseReturnsAt (index fuel : Nat) (equation : SpaceSemantics.Equation) : Bool :=
  match equation.arguments[index]? with
  | some (.var name) => ScopedReturnSyntax.checksSurfaceReturn (.var name) fuel equation.body
  | _ => false

def checksHead (program : SpaceSemantics.Program) (head : String) (index fuel : Nat) : Bool :=
  program.equations.any (fun equation => equation.head == head) &&
    program.equations.all (fun equation => equation.head != head || clauseReturnsAt index fuel equation)

theorem checked_has_head (program : SpaceSemantics.Program) (head : String) (index fuel : Nat)
    (checked : checksHead program head index fuel = true) :
    ∃ equation ∈ program.equations, equation.head = head := by
  have found := (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨equation, member, named⟩ := List.any_eq_true.mp found
  exact ⟨equation, member, by simpa using named⟩

theorem checked_row (program : SpaceSemantics.Program) (head : String) (index fuel : Nat)
    (checked : checksHead program head index fuel = true) (equation : SpaceSemantics.Equation)
    (member : equation ∈ program.equations) (named : equation.head = head) :
    ∃ name, equation.arguments[index]? = some (.var name) ∧
      ScopedReturnSyntax.checksSurfaceReturn (.var name) fuel equation.body = true := by
  have rows := (Bool.and_eq_true_iff.mp checked).2
  have accepted := List.all_eq_true.mp rows equation member
  simp only [named, bne_self_eq_false, Bool.false_or] at accepted
  unfold clauseReturnsAt at accepted
  split at accepted
  · exact ⟨_, by assumption, accepted⟩
  · cases accepted

theorem checked_frontier_aliases (program : SpaceSemantics.Program) (head : String)
    (index inspectionFuel : Nat) (checked : checksHead program head index inspectionFuel = true)
    (control : Control) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination) :
    ∀ choice ∈ ClauseChoice.choices program control head arguments destination [],
      ScopedReturnLocal.AliasHolds argument (predicateEntry 0 choice.2) := by
  intro choice present
  obtain ⟨equation, row, selected⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp present
  have named : equation.head = head := by
    by_contra different
    rw [ClauseChoice.wrong_head_not_selected control head arguments destination [] choice.1 equation different] at selected
    cases selected
  obtain ⟨name, formal, returns⟩ := checked_row program head index inspectionFuel checked equation
    (List.mem_of_getElem? row) named
  have entered := ScopedReturnAliasEntry.selected_variable_alias_contract control head arguments destination []
    choice.1 equation choice.2 index argument name inspectionFuel selected actual formal target returns
  exact ScopedReturnAliasEntry.predicate_entry_alias argument choice.2 _ destination [] 0 entered
    (ClauseChoice.attempt_preserves_caller control head arguments destination [] choice.1 equation choice.2 selected).2.2.1

/-- All accepted equation occurrences run through the actual source driver.
There is no assumption that a body terminates, succeeds, or implements its
claimed return. Arbitrary recursion in prefix computations is retained. -/
theorem checked_function_run {Context : Type} (program : SpaceSemantics.Program) (head : String)
    (index inspectionFuel : Nat) (checked : checksHead program head index inspectionFuel = true)
    (control : Control) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (allocator : Allocator) (world : World) (context : Context) (origins : List Nat) (fuel : Nat) :
    let selected := ClauseChoice.choices program control head arguments destination []
    let work := selected.map fun choice => (predicateEntry 0 choice.2, context, origins ++ [choice.1])
    ∀ packet ∈ ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨work, [], none⟩]⟩)).1,
      ∃ environment, resolve packet.bindings = some environment ∧
        packet.value = read environment argument := by
  dsimp only
  have frontier := checked_frontier_aliases program head index inspectionFuel checked control arguments argument destination actual target
  have allPackets := ScopedReturnRun.run_packets_read_input (fun _ : Context => argument) program fuel
    (allocator, ⟨world, [⟨(ClauseChoice.choices program control head arguments destination []).map
      (fun choice => (predicateEntry 0 choice.2, context, origins ++ [choice.1])), [], none⟩]⟩)
    (.root _ _) (.root _ (by
      intro work member
      obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
      exact frontier choice present))
  intro packet present
  obtain ⟨_context, environment, resolved, observed⟩ := allPackets packet present
  exact ⟨environment, resolved, observed⟩

theorem checked_ground_function_run {Context : Type} (program : SpaceSemantics.Program) (head : String)
    (index inspectionFuel : Nat) (checked : checksHead program head index inspectionFuel = true)
    (control : Control) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (allocator : Allocator) (world : World) (context : Context) (origins : List Nat) (fuel : Nat)
    (ground : (encode argument).isGround) :
    let selected := ClauseChoice.choices program control head arguments destination []
    let work := selected.map fun choice => (predicateEntry 0 choice.2, context, origins ++ [choice.1])
    let packets := ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨work, [], none⟩]⟩)).1
    packets.map CollectedAnswer.value = List.replicate packets.length argument := by
  dsimp only
  apply List.map_eq_replicate_iff.mpr
  intro packet present
  obtain ⟨environment, _resolved, observed⟩ := checked_function_run program head index inspectionFuel checked
    control arguments argument destination actual target allocator world context origins fuel packet present
  exact observed.trans (ProtectedSlots.read_ground environment argument ground)

namespace Controls

private def declaration (name : String) (body : Atom) : SpaceSemantics.Equation := ⟨"keep", [.var name], body⟩
private def first : SpaceSemantics.Equation := declaration "x" (.var "x")
private def second : SpaceSemantics.Equation := declaration "other" (.var "other")

theorem duplicate_equations_are_checked_not_erased :
    checksHead {equations := [first, first, second], declarations := []} "keep" 0 2 = true := by decide +kernel

theorem unknown_head_is_not_vacuously_certified :
    checksHead {equations := [], declarations := []} "keep" 0 2 = false := by decide +kernel

theorem one_wrong_body_rejects_the_head :
    checksHead {equations := [first, declaration "x" (.symbol "wrong")], declarations := []} "keep" 0 2 = false := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnFunction
