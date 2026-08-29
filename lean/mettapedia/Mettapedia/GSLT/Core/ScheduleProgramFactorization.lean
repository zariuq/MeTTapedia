import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.PolicyFamilySufficiency

/-!
# Exact factorization of open schedule programs

`Controller.Program` is already the open semantic interface for a schedule:
its command type is supplied by the client, its memory may change after every
selected occurrence, and the command interpreter is the only place where a
concrete selection discipline enters.

This module characterizes when a richer schedule memory can be replaced by a
readout.  A sufficient readout must determine both:

* the command issued now; and
* the readout of every possible next memory.

The second requirement is load-bearing.  Preserving only the current command
can merge memories whose future schedules diverge.  The dependent policy
family below requests every command and update coordinate, so its canonical
vector is the least sufficient schedule-state representation by the existing
`PolicyFamily` universal property.

An executable realization compiles to another ordinary `Controller.Program`.
The run-commutation theorem proves exact equality of event streams, live
frontiers, and compressed controller memory for every finite prefix.  It does
not assume a queue order, score carrier, fairness property, or physical
continuation representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ScheduleProgramFactorization

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

universe uNode uAnswer uCommand uView uMemory

variable {Node : Type uNode} {Answer : Type uAnswer}
variable {Command : Type uCommand} {View : Type uView}
variable {Memory : Type uMemory}

/-- The observations of controller memory required to reproduce an open
schedule program.  Update coordinates range over every observation that the
branching authority may present to the controller. -/
inductive Coordinate (Node : Type uNode) (Answer : Type uAnswer) where
  | command
  | advance (selected : Node) (emission : Option Answer)
      (generated : List Node)

/-- Result type of one schedule coordinate.  Current commands retain their
open authored type; next states retain only the proposed memory readout. -/
def CoordinateResult (Command : Type uCommand) (View : Type uView) :
    Coordinate Node Answer -> Type (max uCommand uView)
  | .command => ULift.{uView} Command
  | .advance _ _ _ => ULift.{uCommand} View

/-- The complete family of observations which a memory readout must support
to reproduce a schedule program. -/
def observationFamily
    (program : Controller.Program Node Answer Command Memory)
    (readout : Memory -> View) : PolicyFamily Memory where
  Policy := Coordinate Node Answer
  Result := CoordinateResult Command View
  decide
    | .command => fun memory => ULift.up (program.command memory)
    | .advance selected emission generated =>
        fun memory =>
          ULift.up
            (readout (program.advance memory selected emission generated))

abbrev Realization
    (program : Controller.Program Node Answer Command Memory)
    (readout : Memory -> View) :=
  (observationFamily program readout).ReadoutRealization readout

namespace Realization

/-- Compile an admitted schedule-memory readout to an ordinary open schedule
program.  The result carries no copy of the richer memory. -/
def compile
    {program : Controller.Program Node Answer Command Memory}
    {readout : Memory -> View}
    (realization : Realization program readout) :
    Controller.Program Node Answer Command View where
  initialMemory := readout program.initialMemory
  command view := (realization.run .command view).down
  advance view selected emission generated :=
    (realization.run (.advance selected emission generated) view).down

@[simp] theorem compile_initialMemory
    {program : Controller.Program Node Answer Command Memory}
    {readout : Memory -> View}
    (realization : Realization program readout) :
    realization.compile.initialMemory = readout program.initialMemory :=
  rfl

/-- The compiled schedule issues exactly the source command at every related
memory state. -/
theorem compile_command_agrees
    {program : Controller.Program Node Answer Command Memory}
    {readout : Memory -> View}
    (realization : Realization program readout) (memory : Memory) :
    realization.compile.command (readout memory) = program.command memory := by
  exact congrArg ULift.down (realization.agrees .command memory)

/-- The compiled update is exactly the readout of the source update. -/
theorem compile_advance_agrees
    {program : Controller.Program Node Answer Command Memory}
    {readout : Memory -> View}
    (realization : Realization program readout) (memory : Memory)
    (selected : Node) (emission : Option Answer) (generated : List Node) :
    realization.compile.advance (readout memory) selected emission generated =
      readout (program.advance memory selected emission generated) := by
  exact congrArg ULift.down
    (realization.agrees (.advance selected emission generated) memory)

end Realization

/-- Replace only controller memory in a resumable snapshot.  Events and the
live frontier remain definitionally unchanged. -/
def compressSnapshot
    (readout : Memory -> View)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    InferenceControl.Snapshot Node Answer View where
  search := snapshot.search
  memory := readout snapshot.memory

@[simp] theorem compressSnapshot_search
    (readout : Memory -> View)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    (compressSnapshot readout snapshot).search = snapshot.search :=
  rfl

@[simp] theorem compressSnapshot_memory
    (readout : Memory -> View)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    (compressSnapshot readout snapshot).memory = readout snapshot.memory :=
  rfl

/-- One compiled schedule step commutes with memory compression.  This is an
exact state equality, not only an answer-bag theorem. -/
theorem compressSnapshot_tick
    (system : BranchingSystem Node Answer)
    (program : Controller.Program Node Answer Command Memory)
    (interpret : Command -> Scheduler Node)
    (readout : Memory -> View)
    (realization : Realization program readout)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    compressSnapshot readout
        (InferenceControl.Snapshot.tick system
          (program.realize interpret) snapshot) =
      InferenceControl.Snapshot.tick system
        (realization.compile.realize interpret)
        (compressSnapshot readout snapshot) := by
  rw [InferenceControl.Snapshot.tick]
  rw [InferenceControl.Snapshot.tick]
  simp only [compressSnapshot_search, compressSnapshot_memory,
    Controller.Program.realize]
  rw [realization.compile_command_agrees snapshot.memory]
  cases selected :
      (interpret (program.command snapshot.memory)).reorder
        snapshot.search.frontier with
  | nil => rfl
  | cons node pending =>
      simp only [compressSnapshot]
      rw [realization.compile_advance_agrees snapshot.memory node
        (system.emit node) (system.successors node)]

/-- Every finite compiled prefix is exactly the compression of the source
prefix.  Consequently the two programs emit the same ordered stream and
retain the same live frontier, not merely the same completed bag. -/
theorem compressSnapshot_run
    (system : BranchingSystem Node Answer)
    (program : Controller.Program Node Answer Command Memory)
    (interpret : Command -> Scheduler Node)
    (readout : Memory -> View)
    (realization : Realization program readout)
    (fuel : Nat)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) :
    compressSnapshot readout
        (InferenceControl.Snapshot.run system
          (program.realize interpret) fuel snapshot) =
      InferenceControl.Snapshot.run system
        (realization.compile.realize interpret) fuel
        (compressSnapshot readout snapshot) := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [InferenceControl.Snapshot.run]
      rw [compressSnapshot_tick, inductionHypothesis]

/-- The identity readout always has a direct executable realization. -/
def identityRealization
    {IdentityMemory : Type uMemory}
    (program : Controller.Program Node Answer Command IdentityMemory) :
    Realization program (id : IdentityMemory -> IdentityMemory) where
  run
    | .command => fun memory => ULift.up (program.command memory)
    | .advance selected emission generated =>
        fun memory =>
          ULift.up (program.advance memory selected emission generated)
  agrees := by
    intro coordinate memory
    cases coordinate <;> rfl

/-- The observation vector is the least sufficient representation of the
schedule state: it is sufficient itself, and every other sufficient readout
has a fixed map onto it. -/
theorem observationVector_isLeastSufficient
    (program : Controller.Program Node Answer Command Memory)
    (readout : Memory -> View) :
    (observationFamily program readout).SupportsReadout
        (observationFamily program readout).vector /\
      forall (OtherView : Type*) (otherReadout : Memory -> OtherView),
        (observationFamily program readout).SupportsReadout otherReadout ->
          NonFactorization.Factors otherReadout
            (observationFamily program readout).vector :=
  (observationFamily program readout).vector_isLeastSufficient

/-! ## Executable positive and negative controls -/

namespace Canary

/-- Rich schedule memory contains one visible control bit and an irrelevant
diagnostic counter. -/
def compressibleProgram :
    Controller.Program Unit Unit Bool (Bool × Nat) where
  initialMemory := (false, 0)
  command memory := memory.1
  advance memory _ _ _ := (!memory.1, memory.2 + 1)

def visibleBit : Bool × Nat -> Bool := Prod.fst

/-- The visible bit determines both the current command and every next visible
state, so the diagnostic counter is erasable. -/
def visibleBitRealization :
    Realization compressibleProgram visibleBit where
  run
    | .command => fun visible => ULift.up visible
    | .advance _ _ _ => fun visible => ULift.up (!visible)
  agrees := by
    intro coordinate memory
    cases coordinate <;> rfl

theorem visibleBit_compile_command (memory : Bool × Nat) :
    visibleBitRealization.compile.command (visibleBit memory) =
      compressibleProgram.command memory :=
  visibleBitRealization.compile_command_agrees memory

/-- Current commands can agree across a readout fibre even though a later
update exposes a hidden distinction. -/
def futureSensitiveProgram :
    Controller.Program Unit Unit Bool (Bool × Bool) where
  initialMemory := (false, false)
  command memory := memory.1
  advance memory _ _ _ := (memory.2, memory.2)

def firstBit : Bool × Bool -> Bool := Prod.fst

theorem current_command_constant_on_collision :
    futureSensitiveProgram.command (false, false) =
      futureSensitiveProgram.command (false, true) :=
  rfl

/-- Preserving the current command alone is insufficient: after one possible
controller update, the proposed readout must distinguish the two memories. -/
theorem firstBit_refuses_futureSensitiveProgram :
    Not (Nonempty (Realization futureSensitiveProgram firstBit)) := by
  intro supported
  have refused :
      Not ((observationFamily futureSensitiveProgram firstBit
        ).SupportsReadout firstBit) := by
    apply (observationFamily futureSensitiveProgram firstBit
      ).not_supportsReadout_of_policy_collision firstBit
        (first := (false, false)) (second := (false, true)) rfl
        (.advance () none [])
    change (ULift.up false : ULift Bool) ≠ ULift.up true
    decide
  exact refused supported

end Canary

#print axioms Realization.compile_command_agrees
#print axioms Realization.compile_advance_agrees
#print axioms compressSnapshot_tick
#print axioms compressSnapshot_run
#print axioms observationVector_isLeastSufficient
#print axioms Canary.visibleBit_compile_command
#print axioms Canary.firstBit_refuses_futureSensitiveProgram

end Mettapedia.GSLT.Core.ScheduleProgramFactorization
