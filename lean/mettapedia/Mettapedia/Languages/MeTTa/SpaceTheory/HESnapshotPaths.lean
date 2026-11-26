import Mettapedia.Languages.MeTTa.SpaceTheory.HEControlOnTransform

/-!
# Binding snapshot traversals on Transform

The completed capture and restore judgments describe finite batches
independently of the evaluator's control. Their execution preserves
order, retains duplicate occurrences, and never restores a former
program world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotPaths

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (Frame Policy Result WorldEnvironment SnapshotServices CaptureRowsRel RestoreRowsRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task Continuation)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open HEFocused (Focus Leaf Parent)
open HEControlOnTransform (Shows source source_of_focus)

variable {Context World : Type}

def here (world : World) (active : Context) (stack : List Continuation) (parents : List (Parent Context))
    (seen : List Result) (leaf : Leaf) : Focus Context World :=
  ⟨world, active, leaf, stack, parents, seen⟩

section Execution

variable (env : WorldEnvironment Context World) (p : Policy) (active : Context)
variable (stack : List Continuation) (parents : List (Parent Context)) (seen : List Result)

private theorem step {world next : World} {task : Task} {leaf : Leaf} {frames : List Continuation}
    (plan : HESnapshotEntry.Plan env.services p world active task next leaf frames) :
    (source env p).Step (HEFocused.restore (here world active stack parents seen (.work task)))
      (HEFocused.restore (here next active (frames ++ stack) parents seen leaf)) :=
  source_of_focus env p (HEControlOnTransform.all_covered _)
    ((HESnapshotEntry.step_iff env p task plan.covered world active stack parents seen _).mpr ⟨next, leaf, frames, plan, rfl⟩)

theorem capture_path {world next : World} {answers : List Result} {saved : List Entry.Value} {packed : Entry.Value}
    {snapshots : SnapshotServices Context World} (enabled : env.services.snapshots = some snapshots) (caller : Frame)
    (capture : CaptureRowsRel snapshots active world answers saved packed next) :
    ∃ path : ExecutionPath (source env p)
      (HEFocused.restore (here world active stack parents seen (.work (.capture answers saved caller))))
      (HEFocused.restore (here next active stack parents seen (.returning [(packed, caller)]))),
      path.length = answers.length + 1 := by
  induction capture with
  | nil =>
    exact ⟨.cons ⟨step env p active stack parents seen (.packed enabled)⟩ (.refl _), rfl⟩
  | empty empty _ ih =>
    obtain ⟨tail, n⟩ := ih
    exact ⟨.cons ⟨step env p active stack parents seen (.skipEmpty enabled empty)⟩ tail,
      congrArg (· + 1) n⟩
  | cons keep stored _ ih =>
    obtain ⟨tail, n⟩ := ih
    exact ⟨.cons ⟨step env p active stack parents seen (.capture enabled keep stored)⟩ tail,
      congrArg (· + 1) n⟩

theorem restore_path {world : World} {pairs : List Entry.Value} {saved results : List Result}
    {snapshots : SnapshotServices Context World} (enabled : env.services.snapshots = some snapshots) (caller : Frame)
    (restore : RestoreRowsRel snapshots active world p caller pairs saved results) :
    ∃ path : ExecutionPath (source env p)
      (HEFocused.restore (here world active stack parents seen (.work (.restore pairs saved caller))))
      (HEFocused.restore (here world active stack parents seen (.returning results))),
      path.length = pairs.length + 1 := by
  induction restore with
  | nil =>
    exact ⟨.cons ⟨step env p active stack parents seen (.exhausted enabled)⟩ (.refl _), rfl⟩
  | cons stored merged _ ih =>
    obtain ⟨tail, n⟩ := ih
    exact ⟨.cons ⟨step env p active stack parents seen (.restore enabled stored merged)⟩ tail,
      congrArg (· + 1) n⟩
  | rejected stored rejected _ ih =>
    obtain ⟨tail, n⟩ := ih
    exact ⟨.cons ⟨step env p active stack parents seen (.reject enabled stored rejected)⟩ tail,
      congrArg (· + 1) n⟩

theorem collect_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (code : HENativeOnTransform.Presentation Context World)
    {world next : World} {answers : List Result} {packed : Entry.Value}
    {snapshots : SnapshotServices Context World} (enabled : env.services.snapshots = some snapshots) (caller : Frame)
    (capture : CaptureRowsRel snapshots active world answers [] packed next) {start : SState O}
    (shown : Shows code (HEFocused.restore (here world active (.collect caller :: stack) parents seen (.returning answers))) start) :
    ∃ final, ∃ path : ExecutionPath (HEControlOnTransform.theory O code env p) start final,
      Shows code (HEFocused.restore (here next active stack parents seen (.returning [(packed, caller)]))) final ∧
      path.length = answers.length + 2 := by
  have beginCollect :
      (source env p).Step (HEFocused.restore (here world active (.collect caller :: stack) parents seen (.returning answers)))
        (HEFocused.restore (here world active stack parents seen (.work (.capture answers [] caller)))) :=
    source_of_focus env p (HEControlOnTransform.all_covered _)
      ((HESnapshotEntry.collect_iff env p caller answers world active stack parents seen _).mpr ⟨⟨_, enabled⟩, rfl⟩)
  obtain ⟨tail, n⟩ := capture_path env p active stack parents seen enabled caller capture
  obtain ⟨final, path, done, same⟩ := HEControlOnTransform.realize_path env p code shown (.cons ⟨beginCollect⟩ tail)
  exact ⟨final, path, done, same.trans (congrArg (· + 1) n)⟩

theorem restore_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (code : HENativeOnTransform.Presentation Context World) {world : World}
    {pairs : List Entry.Value} {saved results : List Result}
    {snapshots : SnapshotServices Context World} (enabled : env.services.snapshots = some snapshots) (caller : Frame)
    (restore : RestoreRowsRel snapshots active world p caller pairs saved results) {start : SState O}
    (shown : Shows code (HEFocused.restore (here world active stack parents seen (.work (.restore pairs saved caller)))) start) :
    ∃ final, ∃ path : ExecutionPath (HEControlOnTransform.theory O code env p) start final,
      Shows code (HEFocused.restore (here world active stack parents seen (.returning results))) final ∧
      path.length = pairs.length + 1 := by
  obtain ⟨tail, n⟩ := restore_path env p active stack parents seen enabled caller restore
  obtain ⟨final, path, done, same⟩ := HEControlOnTransform.realize_path env p code shown tail
  exact ⟨final, path, done, same.trans n⟩

end Execution

end Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotPaths
