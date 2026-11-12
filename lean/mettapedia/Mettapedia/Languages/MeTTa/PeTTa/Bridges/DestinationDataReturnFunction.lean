import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRun

/-!
# Executable source certificates for compound-return function frontiers

The data check is sound and complete for the existing independent Recipe
judgment. The head check then reads every actual equation of the named head.
It retains duplicate equations and rejects absent heads, missing formals,
interpreted recipes and wrong return bodies. Native plan and symbol-table
authority is not identified with this source checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnFunction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open DestinationDataRecipe (Recipe)

def dataHead (program : SpaceSemantics.Program) (children : List Atom) : Bool :=
  match children with
  | .symbol head :: _ =>
      !Source.lexicalForm (.expression children) && !Source.scopedForm (.expression children) &&
        !callable program head && decide (head ≠ "let*" ∧ head ≠ "case")
  | _ => true

def checksData (program : SpaceSemantics.Program) : Atom → Bool
  | .expression children => dataHead program children && children.attach.all (fun child => checksData program child.1)
  | _ => true
termination_by expression => sizeOf expression
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem child.property) (by omega)

theorem checksData_sound (program : SpaceSemantics.Program) (expression : Atom)
    (checked : checksData program expression = true) : Recipe program expression := by
  cases shape : expression with
  | var name => exact .variableValue name
  | symbol name => exact .symbol name
  | grounded value => exact .grounded value
  | expression children =>
      rw [shape, checksData] at checked
      have headGood := (Bool.and_eq_true_iff.mp checked).1
      have parts := (Bool.and_eq_true_iff.mp checked).2
      have every : ∀ child ∈ children, Recipe program child := by
        intro child member
        exact checksData_sound program child (List.all_eq_true.mp parts ⟨child, member⟩ (by simp))
      cases children with
      | nil => exact .tuple [] (by intro head arguments same; cases same) every
      | cons first rest =>
          cases first with
          | symbol head =>
              have fields : Source.lexicalForm (.expression (.symbol head :: rest)) = false ∧
                  Source.scopedForm (.expression (.symbol head :: rest)) = false ∧ callable program head = false ∧
                  (head ≠ "let*" ∧ head ≠ "case") := by
                simpa only [dataHead, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, and_assoc] using headGood
              exact .named head rest fields.1 fields.2.1 fields.2.2.1 fields.2.2.2
                (fun child member => every child (List.mem_cons_of_mem _ member))
          | var | grounded | expression =>
              exact .tuple _ (by intro head arguments same; cases same) every
termination_by sizeOf expression
decreasing_by
  exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by simp [shape])

theorem checksData_complete {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) : checksData program expression = true := by
  induction data with
  | variableValue | symbol | grounded => simp only [checksData]
  | named head arguments ordinary localForm inert surface children ih =>
      rw [checksData]
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp [dataHead, ordinary, localForm, inert, surface], ?_⟩
      apply List.all_eq_true.mpr
      rintro ⟨child, present⟩ member
      rcases List.mem_cons.mp present with rfl | later
      · simp only [checksData]
      · exact ih child later
  | tuple children noHead parts ih =>
      rw [checksData]
      apply Bool.and_eq_true_iff.mpr
      constructor
      · cases shape : children with
        | nil => rfl
        | cons first rest =>
            cases first with
            | symbol head => exact (noHead head rest shape).elim
            | var | grounded | expression => rfl
      · apply List.all_eq_true.mpr
        intro child member
        exact ih child.1 child.property

theorem checksData_iff (program : SpaceSemantics.Program) (expression : Atom) :
    checksData program expression = true ↔ Recipe program expression :=
  ⟨checksData_sound program expression, checksData_complete⟩

def clauseReturnsAt (program : SpaceSemantics.Program) (index fuel : Nat) (equation : SpaceSemantics.Equation) : Bool :=
  match equation.arguments[index]? with
  | some recipe => checksData program recipe && ScopedReturnSyntax.checksSurfaceReturn recipe fuel equation.body
  | none => false

def checksHead (program : SpaceSemantics.Program) (head : String) (index fuel : Nat) : Bool :=
  program.equations.any (fun equation => equation.head == head) &&
    program.equations.all (fun equation => equation.head != head || clauseReturnsAt program index fuel equation)

theorem checked_has_head (program : SpaceSemantics.Program) (head : String) (index fuel : Nat)
    (checked : checksHead program head index fuel = true) :
    program.equations.any (fun equation => equation.head == head) = true := (Bool.and_eq_true_iff.mp checked).1

theorem checked_row (program : SpaceSemantics.Program) (head : String) (index fuel : Nat)
    (checked : checksHead program head index fuel = true) (equation : SpaceSemantics.Equation)
    (member : equation ∈ program.equations) (named : equation.head = head) :
    ∃ recipe, equation.arguments[index]? = some recipe ∧ Recipe program recipe ∧
      ScopedReturnSyntax.checksSurfaceReturn recipe fuel equation.body = true := by
  have accepted := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 equation member
  simp only [named, bne_self_eq_false, Bool.false_or] at accepted
  unfold clauseReturnsAt at accepted
  split at accepted
  · exact ⟨_, by assumption, checksData_sound _ _ (Bool.and_eq_true_iff.mp accepted).1,
      (Bool.and_eq_true_iff.mp accepted).2⟩
  · cases accepted

theorem checked_frontier_aliases (program : SpaceSemantics.Program) (head : String)
    (index inspectionFuel retained : Nat) (checked : checksHead program head index inspectionFuel = true)
    (control : Control) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination) :
    ∀ choice ∈ ClauseChoice.choices program control head arguments destination [],
      DestinationDataReturnState.AliasHolds program argument (predicateEntry retained choice.2) := by
  intro choice present
  obtain ⟨equation, row, selected⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp present
  have named : equation.head = head := by
    by_contra different
    rw [ClauseChoice.wrong_head_not_selected control head arguments destination [] choice.1 equation different] at selected
    cases selected
  obtain ⟨recipe, formal, data, returns⟩ := checked_row program head index inspectionFuel checked equation
    (List.mem_of_getElem? row) named
  exact DestinationDataReturnEntry.selected_predicate_entry program control head arguments destination [] choice.1 retained
    equation choice.2 index argument recipe inspectionFuel selected actual formal data returns target

theorem checked_function_run {Context : Type} (program : SpaceSemantics.Program) (head : String)
    (index inspectionFuel : Nat) (checked : checksHead program head index inspectionFuel = true)
    (control : Control) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (allocator : Allocator) (world : EagerDFS.World) (context : Context) (origins : List Nat) (fuel : Nat) :
    let selected := ClauseChoice.choices program control head arguments destination []
    let work := selected.map fun choice => (predicateEntry 0 choice.2, context, origins ++ [choice.1])
    ∀ packet ∈ ((ScopedQuerySource.ownedMachine .eagerValue program).run fuel
      (allocator, ⟨world, [⟨work, [], none⟩]⟩)).1,
      ∃ environment, resolve packet.bindings = some environment ∧ packet.value = read environment argument := by
  dsimp only
  have frontier := checked_frontier_aliases program head index inspectionFuel 0 checked control arguments argument destination actual target
  have allPackets := DestinationDataReturnRun.run_packets_read_input (fun _ : Context => argument) program fuel
    (allocator, ⟨world, [⟨(ClauseChoice.choices program control head arguments destination []).map
      (fun choice => (predicateEntry 0 choice.2, context, origins ++ [choice.1])), [], none⟩]⟩)
    (.root _ _) (.root _ (by
      intro work member
      obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
      exact frontier choice present))
  intro packet present
  obtain ⟨_context, environment, resolved, observed⟩ := allPackets packet present
  exact ⟨environment, resolved, observed⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnFunction
