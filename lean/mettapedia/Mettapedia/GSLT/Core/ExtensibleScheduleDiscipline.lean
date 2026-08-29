import Mettapedia.GSLT.Core.InferenceControl

/-!
# Extensible schedule-discipline libraries

An open schedule command should identify reusable implementation structure
separately from authored policy parameters.  A discipline library therefore
has dependent commands `(plan, parameter)`: the plan is suitable for a native
cache key, while the parameter may change ranking, direction, weights, or
other policy data without compiling a new physical queue implementation.

Libraries extend by coproduct.  Existing commands retain exactly their old
interpretation, while a new primitive family becomes available through the
other injection.  An authored GSLT-IL or other surface language may target
these commands after its decoder and admission proof are supplied; no surface
syntax is selected here.

Every interpretation returns an occurrence-preserving `Scheduler`.  Thus a
live-added policy may reorder authorized work, but a primitive which drops,
duplicates, or invents occurrences cannot inhabit this interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ExtensibleScheduleDiscipline

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

universe uNode uPlan uParameter uAnswer uMemory

/-- A family of reusable physical selection plans with plan-specific authored
parameters. -/
structure Library (Node : Type uNode) where
  Plan : Type uPlan
  Parameter : Plan -> Type uParameter
  scheduler : (plan : Plan) -> Parameter plan -> Scheduler Node

namespace Library

variable {Node : Type uNode}

/-- One authored discipline command: a reusable plan plus its parameters. -/
abbrev Command (library : Library.{uNode, uPlan, uParameter} Node) :=
  (plan : library.Plan) × library.Parameter plan

def planOf (library : Library.{uNode, uPlan, uParameter} Node)
    (command : library.Command) : library.Plan :=
  command.1

/-- Interpret a command through the implementation associated with its plan
key. -/
def interpret (library : Library.{uNode, uPlan, uParameter} Node) :
    library.Command -> Scheduler Node
  | ⟨plan, parameter⟩ => library.scheduler plan parameter

/-- Extend two primitive libraries without changing either interpretation. -/
def coproduct
    (left right : Library.{uNode, uPlan, uParameter} Node) :
    Library.{uNode, uPlan, uParameter} Node where
  Plan := Sum left.Plan right.Plan
  Parameter
    | .inl plan => left.Parameter plan
    | .inr plan => right.Parameter plan
  scheduler
    | .inl plan => left.scheduler plan
    | .inr plan => right.scheduler plan

def includeLeft
    (left right : Library.{uNode, uPlan, uParameter} Node)
    (command : left.Command) : (left.coproduct right).Command :=
  ⟨Sum.inl command.1, command.2⟩

def includeRight
    (left right : Library.{uNode, uPlan, uParameter} Node)
    (command : right.Command) : (left.coproduct right).Command :=
  ⟨Sum.inr command.1, command.2⟩

@[simp] theorem interpret_includeLeft
    (left right : Library.{uNode, uPlan, uParameter} Node)
    (command : left.Command) :
    (left.coproduct right).interpret (left.includeLeft right command) =
      left.interpret command := by
  cases command
  rfl

@[simp] theorem interpret_includeRight
    (left right : Library.{uNode, uPlan, uParameter} Node)
    (command : right.Command) :
    (left.coproduct right).interpret (left.includeRight right command) =
      right.interpret command := by
  cases command
  rfl

/-- A library revision is part of native cache identity.  Changing authored
parameters inside one plan retains the plan component; changing the library's
primitive semantics requires a new revision. -/
structure Revisioned (Node : Type uNode) where
  revision : Nat
  library : Library.{uNode, uPlan, uParameter} Node

namespace Revisioned

variable {Answer : Type uAnswer} {Memory : Type uMemory}

abbrev Command (revisioned : Revisioned.{uNode, uPlan, uParameter} Node) :=
  revisioned.library.Command

def cacheKey (revisioned : Revisioned.{uNode, uPlan, uParameter} Node)
    (command : revisioned.Command) : Nat × revisioned.library.Plan :=
  (revisioned.revision, revisioned.library.planOf command)

/-- Realize an authored schedule program through the current revisioned
discipline library. -/
def realize
    (revisioned : Revisioned.{uNode, uPlan, uParameter} Node)
    (program : Controller.Program Node Answer revisioned.Command Memory) :
    Controller Node Answer Memory :=
  program.realize revisioned.library.interpret

end Revisioned

end Library

/-! ## Executable positive and negative controls -/

namespace Canary

inductive QueuePlan where
  | queue
deriving DecidableEq, Repr

/-- One queue implementation plan accepts an authored direction parameter. -/
def queueLibrary : Library Nat where
  Plan := QueuePlan
  Parameter
    | .queue => Bool
  scheduler
    | .queue, false => Scheduler.breadthFirst
    | .queue, true => Scheduler.reverseBreadthFirst

def forwardCommand : queueLibrary.Command :=
  ⟨.queue, false⟩

def reverseCommand : queueLibrary.Command :=
  ⟨.queue, true⟩

/-- Distinct authored policies share the same native implementation plan. -/
theorem direction_parameters_share_plan :
    queueLibrary.planOf forwardCommand =
      queueLibrary.planOf reverseCommand :=
  rfl

def queueRevision : Library.Revisioned Nat where
  revision := 7
  library := queueLibrary

/-- Revision and plan, rather than the policy parameter, form the reusable
native cache key. -/
theorem direction_parameters_share_cacheKey :
    queueRevision.cacheKey forwardCommand =
      queueRevision.cacheKey reverseCommand :=
  rfl

/-- The shared plan still permits genuinely different policy behavior. -/
theorem direction_parameters_change_order :
    (queueLibrary.interpret forwardCommand).reorder [0, 1] = [0, 1] /\
      (queueLibrary.interpret reverseCommand).reorder [0, 1] = [1, 0] := by
  decide

/-- A live program may change policy parameters after each authorized
expansion without changing its command type or native plan. -/
def alternatingProgram :
    Controller.Program Nat Unit queueRevision.Command Bool where
  initialMemory := false
  command reverse := if reverse then reverseCommand else forwardCommand
  advance reverse _ _ _ := !reverse

theorem alternatingProgram_changes_policy :
    (queueRevision.realize alternatingProgram).scheduler false =
        Scheduler.breadthFirst /\
      (queueRevision.realize alternatingProgram).scheduler true =
        Scheduler.reverseBreadthFirst := by
  constructor <;> rfl

inductive StackPlan where
  | stack
deriving DecidableEq, Repr

def stackLibrary : Library Nat where
  Plan := StackPlan
  Parameter
    | .stack => Unit
  scheduler
    | .stack, () => Scheduler.depthFirst

def stackCommand : stackLibrary.Command :=
  ⟨.stack, ()⟩

def extendedLibrary : Library Nat :=
  queueLibrary.coproduct stackLibrary

/-- Adding a new primitive family by coproduct preserves every old command's
meaning exactly. -/
theorem extension_preserves_queue_command :
    extendedLibrary.interpret
        (queueLibrary.includeLeft stackLibrary reverseCommand) =
      queueLibrary.interpret reverseCommand :=
  queueLibrary.interpret_includeLeft stackLibrary reverseCommand

/-- The same extension makes the new primitive available without modifying
the old library. -/
theorem extension_interprets_stack_command :
    extendedLibrary.interpret
        (queueLibrary.includeRight stackLibrary stackCommand) =
      Scheduler.depthFirst := by
  rfl

/-- Negative control: a primitive which discards a generated occurrence
cannot be interpreted as an occurrence-preserving scheduler. -/
theorem generated_occurrence_drop_is_unrepresentable :
    Not (Exists fun scheduler : Scheduler Nat =>
      scheduler.integrate [] [0] = []) := by
  rintro ⟨scheduler, drops⟩
  have sameLength := (scheduler.integrate_complete [] [0]).length_eq
  rw [drops] at sameLength
  simp at sameLength

end Canary

#print axioms Library.interpret_includeLeft
#print axioms Library.interpret_includeRight
#print axioms Canary.direction_parameters_share_plan
#print axioms Canary.direction_parameters_share_cacheKey
#print axioms Canary.direction_parameters_change_order
#print axioms Canary.alternatingProgram_changes_policy
#print axioms Canary.extension_preserves_queue_command
#print axioms Canary.extension_interprets_stack_command
#print axioms Canary.generated_occurrence_drop_is_unrepresentable

end Mettapedia.GSLT.Core.ExtensibleScheduleDiscipline
