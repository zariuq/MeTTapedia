import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceInvocation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionWorld

/-! The real collection world's local services discharge the authored fold
invocation. Closed saved values make binding readback policy-independent;
this does not assert equivalence of whole evaluation/publication policies. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldWorldServices

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment snapshots)

theorem append_policy {Context World : Type} (snapshotService : SnapshotServices Context World)
    (first second : Policy) (label : Context) (world : World) (input : Entry.Value) (outcome : GroundedResult Entry.Value)
    (source : HECollectionClosedAppend.Step snapshotService first label world input outcome) :
    HECollectionClosedAppend.Step snapshotService second label world input outcome := by
  cases source with
  | @append callMark listMark pairMark values value payload captured restored closed =>
      simpa only [HECollectionClosedAppend.closed_read first captured value closed,
        HECollectionClosedAppend.closed_read second captured value closed] using
        (HECollectionClosedAppend.Step.append (policy := second) (callMark := callMark) (listMark := listMark)
          (pairMark := pairMark) (values := values) restored closed)

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem emitter (world : World) :
    HECollectionFoldNativeEntry.Emitter current sourceSpace world (HECollectionWorld.hidden world) := by
  constructor
  · simp [environment, HECollectionWorld.dispatch]
  · intro _; rfl
  · intro arguments
    simp [environment, HECollectionWorld.dispatch, CollectionStdlibSource.foldName, CollectionStdlibSource.appendName]
  · intro live scope before items init left right operation context
    exact ⟨rfl, HECollectionWorld.Primitive.fold items init left right operation context⟩

theorem marked_emitter (world : World) :
    HECollectionFoldNativeEntry.MarkedEmitter current sourceSpace world (HECollectionWorld.hidden world) := by
  refine ⟨emitter minimal nativePolicy external active primitive subtypes world, ?_⟩
  intro live scope before items init left right operation context itemsMark
  exact ⟨rfl, HECollectionWorld.Primitive.fold (itemsMark := itemsMark) items init left right operation context⟩

theorem append_interface (world : World) (policy : Policy) :
    HECollectionAppendSource.Interface current snapshots policy sourceSpace world := by
  constructor
  · rfl
  · intro names before expected
    exact HECollectionInferredQueries.closed_head ops external names before CollectionStdlibSource.appendName _ _ rfl rfl
  · simp [environment, HECollectionWorld.dispatch]
  · intro _; rfl
  · intro _; simp [environment, HECollectionWorld.dispatch]
  · intro live scope before input outcome source
    exact ⟨rfl, HECollectionWorld.Primitive.append (append_policy snapshots policy nativePolicy sourceSpace world input outcome source)⟩

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots sourceSpace world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    ∃ after mark, Stateful.MinimalRel current sourceSpace world live scope caller
      (.expression .active [.symbol "eval", HEFoldParameterCapture.query pairs (.expression .active []) left right]) before
      [(.expression mark (rows.map Prod.fst), after)] world (policy := policy) :=
  HEFoldSourceInvocation.eval_source current snapshots policy sourceSpace world (HECollectionWorld.hidden world) rfl
    (emitter minimal nativePolicy external active primitive subtypes world)
    (append_interface minimal nativePolicy external active primitive subtypes world policy)
    (fun arguments => HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "foldl-atom" arguments (by simp))
    before live scope caller left right different leftFresh rightFresh rows pairs stored closed

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldWorldServices
