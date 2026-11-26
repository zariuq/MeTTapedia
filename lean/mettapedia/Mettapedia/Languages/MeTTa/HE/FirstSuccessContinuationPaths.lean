import Mathlib.Data.List.Forall2
import Mathlib.Logic.Relation
import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
import Mettapedia.Machines.OrderedOutput

/-!
# Retained continuations in ordered first-success paths

A local path specifies the frames it owns on each side, and runs under
every caller stack and publication history. The append traversal consumes
each physical result block before collecting its suffix. Admitting a task
or consuming a frame is justified by the selected worker's own relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessContinuationPaths

open RecursiveTasks
open FirstSuccessRecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A top-level reply record of the first-success worker. -/
def returning (space : Space) (rows emitted : ResultSet) : Configuration :=
  ⟨space, .returning rows, [], emitted⟩

def rawOutput (space : Space) (dispatch : GroundedDispatch) (policy : TypePolicy) :
    Machine.OrderedOutput (FirstSuccessRecursiveExecution.machine dispatch policy) where
  returning := returning space
  verdict := returning space []
  finish _ := rfl
  publish _ _ _ := rfl

def checkedOutput (space : Space) (dispatch : GroundedDispatch) (policy : TypePolicy) :
    Machine.OrderedOutput (Checked.machine dispatch policy) where
  returning := returning space
  verdict := returning space []
  finish _ := rfl
  publish _ _ _ := rfl

variable {step : Configuration → Configuration → Prop} {space : Space}

abbrev FramedPath (step : Configuration → Configuration → Prop) (space : Space)
    (before : Control) (frames : List Frame) (after : Control) (remaining : List Frame) : Prop :=
  ∀ stack emitted, Relation.ReflTransGen step
    ⟨space, before, frames ++ stack, emitted⟩
    ⟨space, after, remaining ++ stack, emitted⟩

abbrev Realizes (step : Configuration → Configuration → Prop) (space : Space)
    (task : Task) (results : ResultSet) : Prop :=
  FramedPath step space (.work task) [] (.returning results) []

theorem FramedPath.trans {before middle after : Control} {first second third : List Frame}
    (left : FramedPath step space before first middle second)
    (right : FramedPath step space middle second after third) :
    FramedPath step space before first after third :=
  fun stack emitted => (left stack emitted).trans (right stack emitted)

/-- Extend both ends by the same retained frames below the local frames. -/
theorem FramedPath.under {before after : Control} {first last : List Frame}
    (path : FramedPath step space before first after last) (saved : List Frame) :
    FramedPath step space before (first ++ saved) after (last ++ saved) := by
  intro stack emitted
  simpa only [List.append_assoc] using path (saved ++ stack) emitted

/-- An entered child returns under its own saved receiver. Consuming that
frame keeps the outer stack and the full publication history. -/
theorem FramedPath.receive {before after : Control} {first last : List Frame}
    {child : Task} {receiver : Frame} {rows : ResultSet}
    (enter : FramedPath step space before first (.work child) [receiver])
    (run : Realizes step space child rows)
    (resume : FramedPath step space (.returning rows) [receiver] after last) :
    FramedPath step space before first after last :=
  enter.trans ((run.under [receiver]).trans resume)

structure AppendFrames (step : Configuration → Configuration → Prop) (space : Space) : Prop where
  resumeTail (rest : Task) (head : ResultSet) :
    FramedPath step space (.returning head) [.append rest] (.work rest) [.prepend head]
  restoreHead (head tail : ResultSet) :
    FramedPath step space (.returning tail) [.prepend head] (.returning (head ++ tail)) []

theorem AppendFrames.collect (frames : AppendFrames step space) (rest : Task)
    (head tail : ResultSet) (finish : Realizes step space rest tail) :
    FramedPath step space (.returning head) [.append rest] (.returning (head ++ tail)) [] :=
  (frames.resumeTail rest head).trans ((finish.under [.prepend head]).trans
    (frames.restoreHead head tail))

/-- The append frame feeds the rest of the exact request list back to the
same worker, then prepends the whole block returned by its head. -/
theorem AppendFrames.traverse (frames : AppendFrames step space) {Row : Type}
    (batch : List Row → Task) (empty : Realizes step space (batch []) [])
    {source : List Row} {blocks : List ResultSet}
    (rows : List.Forall₂ (fun row block => ∀ rest,
      FramedPath step space (.work (batch (row :: rest))) [] (.returning block)
        [.append (batch rest)]) source blocks) :
    Realizes step space (batch source) blocks.flatten := by
  induction rows with
  | nil => exact empty
  | @cons item block rest blocks head _ ih =>
      exact (head rest).trans (frames.collect (batch rest) block blocks.flatten ih)

/-- A traversal whose head enters a child request under the actual saved
append frame. The caller supplies the child's own derivation for each row. -/
theorem AppendFrames.traverseTasks (frames : AppendFrames step space) {Row : Type}
    (batch : List Row → Task) (child : Row → Task)
    (empty : Realizes step space (batch []) [])
    (enter : ∀ row rest, FramedPath step space (.work (batch (row :: rest))) []
      (.work (child row)) [.append (batch rest)])
    {source : List Row} {blocks : List ResultSet}
    (rows : List.Forall₂ (fun row block => Realizes step space (child row) block) source blocks) :
    Realizes step space (batch source) blocks.flatten :=
  frames.traverse batch empty (List.Forall₂.imp (fun row _ next rest =>
    (enter row rest).trans (next.under [.append (batch rest)])) rows)

theorem AppendFrames.traverseMap (frames : AppendFrames step space) {Row : Type}
    (batch : List Row → Task) (emit : Row → ResultSet)
    (empty : Realizes step space (batch []) []) (source : List Row)
    (each : ∀ row ∈ source, ∀ rest,
      FramedPath step space (.work (batch (row :: rest))) [] (.returning (emit row))
        [.append (batch rest)]) :
    Realizes step space (batch source) (source.flatMap emit) := by
  rw [List.flatMap_def]
  exact frames.traverse batch empty (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr each))

/-- A row either returns as received or runs its child under a receiver.
The receiver reads that child's replies before the saved suffix is resumed. -/
structure BranchPlan where
  batch : ResultSet → Task
  stopped : ResultPair → Bool
  child : ResultPair → Task
  receiver : ResultPair → Frame
  readout : ResultPair → ResultSet → ResultSet

def BranchPlan.RowResult (plan : BranchPlan) (step : Configuration → Configuration → Prop)
    (space : Space) (row : ResultPair) (results : ResultSet) : Prop :=
  if plan.stopped row then results = [row]
  else ∃ replies, Realizes step space (plan.child row) replies ∧ results = plan.readout row replies

theorem BranchPlan.rowResults_map (plan : BranchPlan) (rows : ResultSet)
    (replies : ResultPair → ResultSet)
    (children : ∀ row ∈ rows, plan.stopped row = false →
      Realizes step space (plan.child row) (replies row)) :
    List.Forall₂ (plan.RowResult step space) rows
      (rows.map fun row => if plan.stopped row then [row] else plan.readout row (replies row)) := by
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro row member
  cases stopped : plan.stopped row with
  | true => simp only [RowResult, stopped, if_true]
  | false =>
      simp only [RowResult, stopped, Bool.false_eq_true, if_false]
      exact ⟨replies row, children row member stopped, rfl⟩

/-- The stopped branch contributes one physical row and does not demand a
child execution. The other branch collects under its own retained receiver. -/
theorem AppendFrames.traverseBranches (frames : AppendFrames step space) (plan : BranchPlan)
    (empty : Realizes step space (plan.batch []) [])
    (stop : ∀ row rest, plan.stopped row = true →
      FramedPath step space (.work (plan.batch (row :: rest))) [] (.returning [row])
        [.append (plan.batch rest)])
    (descend : ∀ row rest, plan.stopped row = false →
      FramedPath step space (.work (plan.batch (row :: rest))) [] (.work (plan.child row))
        [plan.receiver row, .append (plan.batch rest)])
    (receive : ∀ row replies, FramedPath step space (.returning replies) [plan.receiver row]
      (.returning (plan.readout row replies)) [])
    {rows : ResultSet} {blocks : List ResultSet}
    (children : List.Forall₂ (plan.RowResult step space) rows blocks) :
    Realizes step space (plan.batch rows) blocks.flatten := by
  refine frames.traverse plan.batch empty (List.Forall₂.imp ?_ children)
  intro row block given rest
  cases stopped : plan.stopped row with
  | true =>
      have same : block = [row] := by simpa only [BranchPlan.RowResult, stopped, if_true] using given
      subst block
      exact stop row rest stopped
  | false =>
      simp only [BranchPlan.RowResult, stopped, Bool.false_eq_true, if_false] at given
      obtain ⟨replies, run, rfl⟩ := given
      exact (descend row rest stopped).trans
        ((run.under [plan.receiver row, .append (plan.batch rest)]).trans
          ((receive row replies).under [.append (plan.batch rest)]))

end Mettapedia.Languages.MeTTa.HE.FirstSuccessContinuationPaths
