import Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotPaths
import Mettapedia.Languages.MeTTa.SpaceTheory.HENativeTransformExamples

/-!
# Collection preserves occurrences and restoration keeps the reached space

The fixture captures two equal occurrences separated by an Empty result,
edits the program while keeping their snapshot handles, then restores them
in the edited world. A missing handle is not a failed merge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotExamples

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.GSLT.Ultrainfinite (Route)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.ContextualData (framesData framesData_injective)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (Frame SnapshotServices Result WorldEnvironment CaptureRowsRel RestoreRowsRel)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Task)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (exists_reads)
open HEFocused (Focus)
open HEControlOnTransform (Shows)
open HESnapshotPaths (here)

abbrev Base := Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.World
abbrev World := Base × List Frame

def snapshots : SnapshotServices Bool World := SnapshotServices.appendModel Bool Base

def env : WorldEnvironment Bool World where
  view world label := ⟨world.1 label⟩
  arguments := Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.environment.arguments
  dispatch := Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.environment.dispatch
  lookup := Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.environment.lookup
  services := {
    contextPayload := Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls.services.contextPayload
    nativeCall := fun _ _ _ _ _ _ _ _ => False
    snapshots := some snapshots }

def code : HENativeOnTransform.Presentation Bool World where
  context := HENativeTransformExamples.code.context
  context_injective := HENativeTransformExamples.code.context_injective
  world world := .expression [HENativeTransformExamples.code.world world.1, framesData world.2]
  world_injective := by
    intro first second same
    have fields := List.cons.inj (Atom.expression.inj same)
    exact Prod.ext (HENativeTransformExamples.code.world_injective fields.1)
      (framesData_injective (List.cons.inj fields.2).1)

private def original : Base := fun _ => []
private def changed : Base :=
  Function.update original true [.expression [.symbol "=", .symbol "example", .symbol "new"]]
private def before : World := (original, [])
private def once : World := (original, [Frame.empty])
private def twice : World := (original, [Frame.empty, Frame.empty])
private def reached : World := (changed, twice.2)

private def datum : Result := (.symbol "value", Frame.empty)
private def vacant : Result := (Entry.Value.ofAtom Atom.empty, Frame.empty)
private def batch : List Result := [datum, vacant, datum]

private def pairAt (position : Int) : Entry.Value :=
  .expression .active [datum.1, .grounded (.int position)]

private def pairs : List Entry.Value := [pairAt 0, pairAt 1]
private def packed : Entry.Value := .expression .active pairs

private theorem capture :
    CaptureRowsRel snapshots true before batch [] packed twice := by
  have keep : datum.1.erase ≠ Atom.empty := by simp [datum, Entry.Value.erase, Atom.empty]
  refine .cons (nextWorld := once) (payload := .int 0) keep ?_ (.empty ?_ (.cons (payload := .int 1) keep ?_ .nil))
  · exact ⟨rfl, rfl⟩
  · exact Entry.Value.erase_ofAtom _
  · exact ⟨rfl, rfl⟩

private theorem restore :
    RestoreRowsRel snapshots true reached .unmarked Frame.empty pairs [] [datum, datum] := by
  have first : snapshots.restore true reached (.int 0) Frame.empty := ⟨0, rfl, rfl⟩
  have second : snapshots.restore true reached (.int 1) Frame.empty := ⟨1, rfl, rfl⟩
  exact .cons first (.emptyCaller _ _) (.cons second (.emptyCaller _ _) .nil)

private def waiting : Focus Bool World :=
  here before true [.collect Frame.empty] [] [] (.returning batch)

private def collectingDone : Focus Bool World :=
  here twice true [] [] [] (.returning [(packed, Frame.empty)])

private def restoring : Focus Bool World :=
  here reached true [] [] [] (.work (.restore pairs [] Frame.empty))

private def restoringDone : Focus Bool World :=
  here reached true [] [] [] (.returning [datum, datum])

/-- Hold two equal values under distinct handles, omitting only Empty. -/
theorem collects_both_copies :
    ∃ start final, Shows code (HEFocused.restore waiting) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code env .unmarked) start final,
        Shows code (HEFocused.restore collectingDone) final ∧ path.length = 5 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code waiting}
  have initial : Shows code (HEFocused.restore waiting) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  obtain ⟨final, path, done, length⟩ := HESnapshotPaths.collect_on_transform env .unmarked true [] [] []
    code rfl Frame.empty capture initial
  exact ⟨start, final, initial, path, done, length.trans rfl⟩

/-- Both stored activations are valid after the edit. Restoring them
uses the new program world, not the one from collection. -/
theorem restores_both_in_edited_space :
    ∃ start final, Shows code (HEFocused.restore restoring) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code env .unmarked) start final,
        Shows code (HEFocused.restore restoringDone) final ∧ path.length = 3 := by
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code restoring}
  have initial : Shows code (HEFocused.restore restoring) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  obtain ⟨final, path, done, length⟩ := HESnapshotPaths.restore_on_transform env .unmarked true [] [] []
    code rfl Frame.empty restore initial
  exact ⟨start, final, initial, path, done, length.trans rfl⟩

private def withoutSnapshots : WorldEnvironment Bool World :=
  { env with services := { env.services with snapshots := none } }

theorem collection_requires_snapshot_service {start final}
    (shown : Shows code (HEFocused.restore waiting) start) :
    ¬ (HEControlOnTransform.theory Nat code withoutSnapshots .unmarked).Step start final := by
  intro firing
  obtain ⟨_, ⟨_, stepped⟩, _⟩ :=
    HEControlOnTransform.reflect_step withoutSnapshots .unmarked code shown firing
  have moved := HEFocused.focus_step stepped
  rw [HEFocused.focus_restore] at moved
  obtain ⟨⟨_, contradiction⟩, _⟩ :=
    (HESnapshotEntry.collect_iff withoutSnapshots .unmarked Frame.empty batch before true [] [] [] _).mp moved
  cases contradiction

private def literal : Task := .minimal [] [] none datum.1 Frame.empty

private def collapse : Task :=
  .minimal [] [] none (.expression .active [.symbol "collapse-bind", datum.1]) Frame.empty

private def begun : Focus Bool World := here before true [] [] [] (.work collapse)

private def singletonDone : Focus Bool World :=
  here once true [] [] [] (.returning [(.expression .active [pairAt 0], Frame.empty)])

/-- Starting at the language instruction reaches its packed value through
ordinary literal delivery and the live collection service. -/
theorem collapse_of_literal_executes :
    ∃ start final, Shows code (HEFocused.restore begun) start ∧
      ∃ path : ExecutionPath (HEControlOnTransform.theory Nat code env .unmarked) start final,
        Shows code (HEFocused.restore singletonDone) final ∧ path.length = 5 := by
  open HEControlOnTransform (source source_of_focus) in
  let entered := here before true [.collect Frame.empty] [] [] (.work literal)
  let childDone := here before true [.collect Frame.empty] [] [] (.returning [datum])
  have enter : (source env .unmarked).Step (HEFocused.restore begun) (HEFocused.restore entered) :=
    source_of_focus env .unmarked (HEControlOnTransform.all_covered _)
      ((HESnapshotEntry.step_iff env .unmarked collapse rfl before true [] [] [] entered).mpr
        ⟨before, .work literal, [.collect Frame.empty], .openCollapse (snapshots := snapshots) rfl, rfl⟩)
  have deliver : (source env .unmarked).Step (HEFocused.restore entered) (HEFocused.restore childDone) :=
    source_of_focus env .unmarked (HEControlOnTransform.all_covered _)
      ((HEMinimalEntry.step_iff env .unmarked literal rfl rfl rfl rfl before true [.collect Frame.empty] [] []
        childDone).mpr ⟨.returning [datum], [], .data (by simp [datum, Entry.Value.erase,
          Minimal.embeddedInstruction]), rfl⟩)
  have one : CaptureRowsRel snapshots true before [datum] [] (.expression .active [pairAt 0]) once := by
    exact .cons (payload := .int 0) (by simp [datum, Entry.Value.erase, Atom.empty]) ⟨rfl, rfl⟩ .nil
  obtain ⟨start, read⟩ := exists_reads {HEControlOnTransform.encodeFocus code begun}
  have initial : Shows code (HEFocused.restore begun) start := by
    simpa only [Shows, HEFocused.focus_restore] using read
  let prefixPath : ExecutionPath (source env .unmarked) (HEFocused.restore begun) (HEFocused.restore childDone) :=
    .cons ⟨enter⟩ (.cons ⟨deliver⟩ (.refl _))
  obtain ⟨_, firstPath, middle, firstSize⟩ := HEControlOnTransform.realize_path env .unmarked code initial prefixPath
  obtain ⟨final, tail, done, secondSize⟩ := HESnapshotPaths.collect_on_transform env .unmarked true [] [] []
    code rfl Frame.empty one middle
  have adds : (firstPath.append tail).length = firstPath.length + tail.length := Route.length_append firstPath tail
  exact ⟨start, final, initial, firstPath.append tail, done,
    adds.trans (congrArg₂ Nat.add (firstSize.trans rfl) (secondSize.trans rfl))⟩

private def missing : Task := .restore [pairAt 2] [] Frame.empty

private theorem not_stored {service : SnapshotServices Bool World} {frame : Frame}
    (chosen : env.services.snapshots = some service) (loaded : service.restore true reached (.int 2) frame) : False := by
  obtain rfl : snapshots = service := Option.some.inj chosen
  obtain ⟨index, identity, saved⟩ := loaded
  have value := Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue.int.inj identity
  have same : index = 2 := by omega
  subst index
  simp [reached, twice] at saved

theorem missing_handle_cannot_restore {start final}
    (shown : Shows code (HEFocused.restore (here reached true [] [] [] (.work missing))) start) :
    ¬ (HEControlOnTransform.theory Nat code env .unmarked).Step start final := by
  intro firing
  obtain ⟨_, ⟨_, stepped⟩, _⟩ := HEControlOnTransform.reflect_step env .unmarked code shown firing
  have moved := HEFocused.focus_step stepped
  rw [HEFocused.focus_restore] at moved
  obtain ⟨_, _, _, plan, _⟩ :=
    (HESnapshotEntry.step_iff env .unmarked missing rfl reached true [] [] [] _).mp moved
  cases plan with
  | restore chosen loaded _ => exact not_stored chosen loaded
  | reject chosen loaded _ => exact not_stored chosen loaded

end Mettapedia.Languages.MeTTa.SpaceTheory.HESnapshotExamples
