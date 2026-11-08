import Mettapedia.Languages.MeTTa.HE.CollectionStdlibSource
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# The collection append helper on earned closed values

The helper loads the saved binding record, restores the paired value, and
appends it. It does not merge that record into the current caller. On the
closed values produced by the range/square program, binding application
leaves the entire annotated value unchanged. The accumulator's root mark is
retained, as in cloning its expression and pushing a child. Open values are
not claimed by this admitted primitive profile.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionClosedAppend

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation

inductive Step {Context World : Type} (snapshots : SnapshotServices Context World) (policy : Policy)
    (label : Context) (world : World) : Entry.Value → GroundedResult Entry.Value → Prop where
  | append {callMark listMark pairMark values value payload captured} :
      snapshots.restore label world payload captured → TypeSubst.typeVars value.erase = [] →
      Step snapshots policy label world
        (.expression callMark [.symbol CollectionStdlibSource.appendName, .expression listMark values,
          .expression pairMark [value, .grounded payload]])
        (.ok [(.expression listMark (values ++ [captured.read policy value]), Bindings.empty)])

theorem closed_read (policy : Policy) (frame : Frame) (value : Entry.Value)
    (closed : TypeSubst.typeVars value.erase = []) : frame.read policy value = value := by
  apply Frame.read_variable_free
  intro name occurs
  have member := Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
  simp only [closed, List.not_mem_nil] at member

/-- One actual saved pair earns exactly one append, without supplying an
already accumulated result as an evaluator oracle. -/
theorem append_of_stored {Context World : Type} (snapshots : SnapshotServices Context World)
    (policy : Policy) (label : Context) (world : World) (row : Result) (pair : Entry.Value)
    (stored : StoredPairRel snapshots label world row pair)
    (closed : TypeSubst.typeVars row.1.erase = []) (callMark listMark : Entry.Status) (values : List Entry.Value) :
    Step snapshots policy label world
      (.expression callMark [.symbol CollectionStdlibSource.appendName, .expression listMark values, pair])
      (.ok [(.expression listMark (values ++ [row.1]), Bindings.empty)]) := by
  obtain ⟨payload, rfl, loaded⟩ := stored
  simpa only [closed_read policy row.2 row.1 closed] using
    Step.append (policy := policy) (callMark := callMark) (listMark := listMark) (pairMark := .active) (values := values) loaded closed

theorem output_root_mark {Context World : Type} {snapshots : SnapshotServices Context World}
    {policy label world callMark listMark pairMark values value payload outcome}
    (advanced : Step snapshots policy label world
      (.expression callMark [.symbol CollectionStdlibSource.appendName, .expression listMark values,
        .expression pairMark [value, .grounded payload]]) outcome) :
    ∃ captured, snapshots.restore label world payload captured ∧
      outcome = .ok [(.expression listMark (values ++ [value]), Bindings.empty)] := by
  cases advanced with
  | @append _ _ _ _ _ _ captured restored closed =>
      exact ⟨captured, restored, by rw [closed_read policy captured value closed]⟩

theorem open_value_is_outside_profile {Context World : Type} (snapshots : SnapshotServices Context World)
    (policy : Policy) (label : Context) (world : World) (name : String)
    (callMark listMark pairMark : Entry.Status) (values : List Entry.Value) (payload : GroundedValue) (outcome : GroundedResult Entry.Value) :
    ¬Step snapshots policy label world
      (.expression callMark [.symbol CollectionStdlibSource.appendName, .expression listMark values,
        .expression pairMark [.var name, .grounded payload]]) outcome := by
  intro source
  cases source with
  | append _ closed => simp [Entry.Value.erase, TypeSubst.typeVars] at closed

theorem closed_error_is_kept (policy : Policy) (frame : Frame) (readiness : Entry.Status) :
    frame.read policy (.expression readiness [.symbol "Error", .symbol "input", .symbol "BadType"]) =
      .expression readiness [.symbol "Error", .symbol "input", .symbol "BadType"] :=
  closed_read policy frame _ (by simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionClosedAppend
