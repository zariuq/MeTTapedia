import Mettapedia.Languages.MeTTa.SpaceTheory.HEControlOnTransform

/-!
# Ordered argument demand

With an `Atom` demand an argument is delivered, not executed. When the
incoming activation also leaves the data as written, each such argument
extends the argument packet once. A newly produced failure, in contrast,
skips the rest of its own branch and preserves the other alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEArgumentPaths

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.GSLT.Ultrainfinite (Route)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentRequest ArgumentStopped Frame Policy Result WorldEnvironment argumentScope argumentPrepend_packet)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open HEFocused (Focus Leaf Parent)
open HEControlOnTransform (Shows source source_of_focus)

variable {Context World : Type}

def atomRequests (values : List Entry.Value) : List ArgumentRequest := values.map (·, Atom.atomType)

def focusAt (world : World) (active : Context) (parents : List (Parent Context)) (seen : List Result)
    (leaf : Leaf) (stack : List Continuation) : Focus Context World :=
  ⟨world, active, leaf, stack, parents, seen⟩

section Execution

variable (env : WorldEnvironment Context World) (p : Policy)
variable (world : World) (active : Context) (parents : List (Parent Context)) (seen : List Result)

local notation "At" => focusAt world active parents seen
local notation "StateAt" => fun leaf stack => HEFocused.restore (At leaf stack)

private theorem schedule {task : Task} {leaf : Leaf} {front : List Continuation} (stack : List Continuation)
    (plan : HEApplicationEntry.Plan task leaf front) :
    (source env p).Step (StateAt (.work task) stack) (StateAt leaf (front ++ stack)) :=
  source_of_focus env p (HEControlOnTransform.covered_application task world active stack parents seen plan.covered)
    ((HEApplicationEntry.step_iff env p task plan.covered world active stack parents seen _).mpr ⟨leaf, front, plan, rfl⟩)

private theorem consume {frame : Continuation} {batch : List Result} {leaf : Leaf} {front : List Continuation}
    (stack : List Continuation) (plan : HEReturnEntry.Plan p frame batch leaf front) :
    (source env p).Step (StateAt (.returning batch) (frame :: stack)) (StateAt leaf (front ++ stack)) :=
  source_of_focus env p (HEControlOnTransform.covered_return frame world active batch stack parents seen)
    ((HEReturnEntry.step_iff env p frame plan.covered batch world active stack parents seen _).mpr ⟨leaf, front, plan, rfl⟩)

/-- A witness of the exact number of semantic transitions, not a bound
on the cost of representing the argument packet or traversing its values. -/
theorem atom_arguments_path (values : List Entry.Value) (frame : Frame)
    (unchanged : ∀ value ∈ values, frame.read p value = value)
    (live : List Atom) (scope : List String) (stack : List Continuation) :
    ∃ path : ExecutionPath (source env p)
      (StateAt (.work (.arguments live scope (atomRequests values) frame)) stack)
      (StateAt (.returning [(Entry.Value.argumentPacket values, frame)]) stack),
      path.length = 8 * values.length + 1 := by
  induction values generalizing live stack with
  | nil =>
    refine ⟨.cons ⟨schedule env p world active parents seen stack
      (HEApplicationEntry.Plan.argumentsEnd (live := live) (scope := scope) (frame := frame))⟩ (.refl _), rfl⟩
  | cons head tail ih =>
    let requests := atomRequests tail
    let request : HEAtomEntry.Request := ⟨argumentScope requests ++ live, scope, head, Atom.atomType, frame⟩
    let receive := Continuation.arguments live scope head requests
    let batch : List Result := [(head, frame)]
    let branch := Task.argumentBranches live scope head requests
    let pending := branch []
    let tailStack := .argumentTail head :: .append pending :: stack
    have deliver : (source env p).Step (StateAt (.work request.task) (receive :: stack))
        (StateAt (.returning batch) (receive :: stack)) := by
      apply source_of_focus env p
      · exact HEControlOnTransform.covered_atom request _ _ _ _ _
      · apply (HEAtomEntry.atom_demand_iff env p request rfl world active (receive :: stack) parents seen _).mpr
        simp [focusAt, request, batch, HEAtomEntry.Request.read, unchanged head List.mem_cons_self]
    have requestHead : (source env p).Step
        (StateAt (.work (.arguments live scope (atomRequests (head :: tail)) frame)) stack)
        (StateAt (.work request.task) (receive :: stack)) :=
      schedule env p world active parents seen stack .argumentsNext
    have received : (source env p).Step (StateAt (.returning batch) (receive :: stack))
        (StateAt (.work (branch batch)) stack) :=
      consume env p world active parents seen stack .arguments
    have tailStep : (source env p).Step (StateAt (.work (branch batch)) stack)
        (StateAt (.work (.arguments (head.erase :: live) scope requests frame)) tailStack) :=
      schedule env p world active parents seen stack
        (.argumentBranchesNext (fun stopped : ArgumentStopped head (head, frame) => stopped.2 rfl))
    obtain ⟨runTail, lengthTail⟩ := ih (fun value present => unchanged value (List.mem_cons_of_mem _ present))
      (head.erase :: live) tailStack
    let combined : List Result := [(Entry.Value.argumentPacket (head :: tail), frame)]
    have assemble := consume env p world active parents seen (.append pending :: stack)
      (HEReturnEntry.Plan.argumentTail (policy := p) (head := head)
        (results := [(Entry.Value.argumentPacket tail, frame)]))
    have assembled : (source env p).Step
        (StateAt (.returning [(Entry.Value.argumentPacket tail, frame)]) tailStack)
        (StateAt (.returning combined) (.append pending :: stack)) := by
      simpa only [List.map_cons, List.map_nil, List.nil_append, argumentPrepend_packet, tailStack, combined] using assemble
    have pendingStep : (source env p).Step (StateAt (.returning combined) (.append pending :: stack))
        (StateAt (.work pending) (.prepend combined :: stack)) :=
      consume env p world active parents seen stack .append
    have finished : (source env p).Step (StateAt (.work pending) (.prepend combined :: stack))
        (StateAt (.returning []) (.prepend combined :: stack)) :=
      schedule env p world active parents seen (.prepend combined :: stack) .argumentBranchesEnd
    have resume : (source env p).Step (StateAt (.returning []) (.prepend combined :: stack))
        (StateAt (.returning combined) stack) :=
      consume env p world active parents seen stack .prepend
    let suffix : ExecutionPath (source env p)
        (StateAt (.returning [(Entry.Value.argumentPacket tail, frame)]) tailStack)
        (StateAt (.returning combined) stack) :=
      .cons ⟨assembled⟩ (.cons ⟨pendingStep⟩ (.cons ⟨finished⟩ (.cons ⟨resume⟩ (.refl _))))
    refine ⟨.cons ⟨requestHead⟩ (.cons ⟨deliver⟩ (.cons ⟨received⟩ (.cons ⟨tailStep⟩ (runTail.append suffix)))), ?_⟩
    change (runTail.append suffix).length + 1 + 1 + 1 + 1 = 8 * (tail.length + 1) + 1
    have joined : (runTail.append suffix).length = runTail.length + suffix.length := Route.length_append runTail suffix
    have small : suffix.length = 4 := rfl
    omega

theorem atom_arguments_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (code : HENativeOnTransform.Presentation Context World) (values : List Entry.Value) (frame : Frame)
    (unchanged : ∀ value ∈ values, frame.read p value = value)
    (live : List Atom) (scope : List String) (stack : List Continuation) {start : SState O}
    (shown : Shows code (StateAt (.work (.arguments live scope (atomRequests values) frame)) stack) start) :
    ∃ final, ∃ path : ExecutionPath (HEControlOnTransform.theory O code env p) start final,
      Shows code (StateAt (.returning [(Entry.Value.argumentPacket values, frame)]) stack) final ∧
      path.length = 8 * values.length + 1 := by
  obtain ⟨path, size⟩ := atom_arguments_path env p world active parents seen values frame unchanged live scope stack
  obtain ⟨final, compiled, done, length⟩ := HEControlOnTransform.realize_path env p code shown path
  exact ⟨final, compiled, done, length.trans size⟩

theorem stopped_branch_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (code : HENativeOnTransform.Presentation Context World)
    (live : List Atom) (scope : List String) (original : Entry.Value) (requests : List ArgumentRequest)
    (first : Result) (rest : List Result) (stack : List Continuation)
    (stopped : ArgumentStopped original first) {start : SState O}
    (shown : Shows code (StateAt (.work (.argumentBranches live scope original requests (first :: rest))) stack) start) :
    ∃ final, (HEControlOnTransform.theory O code env p).Step start final ∧
      ∀ next, (HEControlOnTransform.theory O code env p).Step start next →
        Shows code (StateAt (.work (.argumentBranches live scope original requests rest))
          (.prepend [first] :: stack)) next := by
  let task := Task.argumentBranches live scope original requests (first :: rest)
  let kept := Leaf.work (.argumentBranches live scope original requests rest)
  let plan : HEApplicationEntry.Plan task kept [.prepend [first]] := .argumentBranchesStop stopped
  have sourceStep := schedule env p world active parents seen stack plan
  obtain ⟨final, fires, _⟩ := HEControlOnTransform.realize_step env p code shown sourceStep
  refine ⟨final, fires, ?_⟩
  intro next advanced
  obtain ⟨reached, ⟨_, move⟩, readBack⟩ := HEControlOnTransform.reflect_step env p code shown advanced
  have focused := HEFocused.focus_step move
  rw [HEFocused.focus_restore] at focused
  obtain ⟨leaf, frames, scheduled, same⟩ :=
    (HEApplicationEntry.step_iff env p task plan.covered world active stack parents seen _).mp focused
  obtain ⟨rfl, rfl⟩ := scheduled.functional plan
  have exactState : reached = StateAt kept (.prepend [first] :: stack) :=
    HEFocused.focusing.injective (same.trans (HEFocused.focus_restore _).symm)
  exact exactState ▸ readBack

end Execution

end Mettapedia.Languages.MeTTa.SpaceTheory.HEArgumentPaths
