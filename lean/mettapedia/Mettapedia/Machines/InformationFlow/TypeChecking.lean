import Mettapedia.Machines.InformationFlow.CheckedRegion

/-!
# Executable security type checking and checked command construction

The checker decides the syntax-directed judgment for the finite machine core.
Checked constructors preserve that judgment while building a program. Its
execution uses the independent check-free evaluator with actual read effects;
the typing certificate is a proposition and has no executable flow checks.

This is a compilation interface for the modeled fragment. It does not infer
dependencies of arbitrary MeTTa closures, authenticate a space policy, or prove
a wall-clock bound for native operations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InformationFlow.TypeChecking

open FloatingLabel CheckedRegion

universe u

variable {Label : Type u} [SemilatticeSup Label] [OrderBot Label] [DecidableLE Label]

def checkPrimitive (spaceLabel : Nat → Label) (bound : Label) : Primitive Label → Bool
  | .write space => decide (bound ≤ spaceLabel space)
  | .emit destination => decide (bound ≤ destination)
  | _ => true

def checkCommand (spaceLabel : Nat → Label) (bound : Label) : Command Label → Bool
  | .skip => true
  | .primitive operation => checkPrimitive spaceLabel bound operation
  | .seq first second =>
      checkCommand spaceLabel bound first &&
        checkCommand spaceLabel (bound ⊔ readLabel spaceLabel first) second
  | .ifEmpty yes no => checkCommand spaceLabel bound yes && checkCommand spaceLabel bound no

omit [OrderBot Label] in
theorem checkPrimitive_iff (spaceLabel : Nat → Label) (bound : Label)
    (operation : Primitive Label) :
    checkPrimitive spaceLabel bound operation = true ↔ Admissible spaceLabel bound operation := by
  cases operation with
  | literal value => exact ⟨fun _ => .literal value, fun _ => rfl⟩
  | query space predicate => exact ⟨fun _ => .query space predicate, fun _ => rfl⟩
  | count => exact ⟨fun _ => .count, fun _ => rfl⟩
  | write space =>
      simp only [checkPrimitive, decide_eq_true_eq]
      constructor
      · exact Admissible.write space
      · intro allowed; cases allowed with | write _ flows => exact flows
  | emit destination =>
      simp only [checkPrimitive, decide_eq_true_eq]
      constructor
      · exact Admissible.emit destination
      · intro allowed; cases allowed with | emit _ flows => exact flows

/-- Both directions are proved against the inductive judgment; the checker
does not call the judgment or an interpreter as its implementation. -/
theorem checkCommand_iff (spaceLabel : Nat → Label) (bound : Label)
    (command : Command Label) :
    checkCommand spaceLabel bound command = true ↔ WellTyped spaceLabel bound command := by
  induction command generalizing bound with
  | skip => exact ⟨fun _ => .skip _, fun _ => rfl⟩
  | primitive operation =>
      rw [checkCommand, checkPrimitive_iff]
      constructor
      · exact WellTyped.primitive bound operation
      · intro typed; cases typed with | primitive _ _ allowed => exact allowed
  | seq first second ihFirst ihSecond =>
      simp only [checkCommand, Bool.and_eq_true, ihFirst, ihSecond]
      constructor
      · rintro ⟨firstTyped, secondTyped⟩
        exact .seq _ _ _ firstTyped secondTyped
      · intro typed
        cases typed with | seq _ _ _ firstTyped secondTyped => exact ⟨firstTyped, secondTyped⟩
  | ifEmpty yes no ihYes ihNo =>
      simp only [checkCommand, Bool.and_eq_true, ihYes, ihNo]
      constructor
      · rintro ⟨yesTyped, noTyped⟩
        exact .ifEmpty _ _ _ yesTyped noTyped
      · intro typed
        cases typed with | ifEmpty _ _ _ yesTyped noTyped => exact ⟨yesTyped, noTyped⟩

structure CheckedCommand (spaceLabel : Nat → Label) (bound : Label) where
  command : Command Label
  typing : WellTyped spaceLabel bound command

/-- Entry to a checked region carries the bound required by its construction. -/
structure BoundedState (bound : Label) where
  state : State Label
  current_le : state.current ≤ bound

def check (spaceLabel : Nat → Label) (bound : Label) (command : Command Label) :
    Option (CheckedCommand spaceLabel bound) :=
  if accepted : checkCommand spaceLabel bound command = true then
    some ⟨command, (checkCommand_iff _ _ _).mp accepted⟩
  else none

theorem check_isSome_iff (spaceLabel : Nat → Label) (bound : Label)
    (command : Command Label) :
    (check spaceLabel bound command).isSome = true ↔ WellTyped spaceLabel bound command := by
  unfold check
  split
  · rename_i accepted
    simp [(checkCommand_iff _ _ _).mp accepted]
  · rename_i rejected
    simp [← checkCommand_iff, rejected]

namespace CheckedCommand

variable {spaceLabel : Nat → Label} {bound : Label}

def literal (value : List Nat) : CheckedCommand spaceLabel bound :=
  ⟨.primitive (.literal value), .primitive _ _ (.literal value)⟩

def query (space : Nat) (predicate : Nat → Bool) : CheckedCommand spaceLabel bound :=
  ⟨.primitive (.query space predicate), .primitive _ _ (.query space predicate)⟩

def count : CheckedCommand spaceLabel bound :=
  ⟨.primitive .count, .primitive _ _ .count⟩

def write (space : Nat) (flows : bound ≤ spaceLabel space) : CheckedCommand spaceLabel bound :=
  ⟨.primitive (.write space), .primitive _ _ (.write space flows)⟩

def emit (destination : Label) (flows : bound ≤ destination) : CheckedCommand spaceLabel bound :=
  ⟨.primitive (.emit destination), .primitive _ _ (.emit destination flows)⟩

def seq (first : CheckedCommand spaceLabel bound)
    (second : CheckedCommand spaceLabel (bound ⊔ readLabel spaceLabel first.command)) :
    CheckedCommand spaceLabel bound :=
  ⟨.seq first.command second.command, .seq _ _ _ first.typing second.typing⟩

def ifEmpty (yes no : CheckedCommand spaceLabel bound) : CheckedCommand spaceLabel bound :=
  ⟨.ifEmpty yes.command no.command, .ifEmpty _ _ _ yes.typing no.typing⟩

/-- Execute a constructed program without dynamic write/output flow checks.
The input type establishes admission, and the actual read effect reconstructs
the precise current label on return. -/
def execute (program : CheckedCommand spaceLabel bound) (s : BoundedState bound) : State Label :=
  reconstitute s.state.current (effectRun spaceLabel program.command (erase s.state))

theorem execute_correct (program : CheckedCommand spaceLabel bound)
    (s : BoundedState bound) :
    program.execute s = run spaceLabel program.command s.state :=
  reconstitute_effectRun_eq program.typing s.state s.current_le

theorem continuation_exact (program : CheckedCommand spaceLabel bound)
    (s : BoundedState bound) (continuation : Command Label) :
    run spaceLabel continuation (program.execute s) =
      run spaceLabel (.seq program.command continuation) s.state :=
  monitored_continuation_exact program.typing s.state s.current_le continuation

end CheckedCommand

namespace Controls

def policy (space : Nat) : Nat := if space = 0 then 0 else 1

/-- Query, count, and publish within the private compartment. Every composition
is constructed with its required input bound. -/
def privateAggregate : CheckedCommand policy 0 :=
  CheckedCommand.seq (CheckedCommand.query 1 (fun _ => true))
    (CheckedCommand.seq CheckedCommand.count (CheckedCommand.emit 1 (by decide)))

def initial : State Nat :=
  ⟨0, [], fun space => if space = 1 then [7, 9, 11] else [], []⟩

def initialBounded : BoundedState 0 := ⟨initial, by decide⟩

theorem constructed_private_aggregate_computes :
    (privateAggregate.execute initialBounded).trace = [(1, [3])] ∧
      (privateAggregate.execute initialBounded).current = 1 := by
  decide

theorem checker_accepts_private_aggregate :
    checkCommand policy 0 privateAggregate.command = true := by decide

theorem checker_rejects_public_count_release :
    checkCommand policy 0
      (.seq (.primitive (.query 1 (fun _ => true)))
        (.seq (.primitive .count) (.primitive (.emit 0)))) = false := by
  decide

end Controls

end Mettapedia.Machines.InformationFlow.TypeChecking
