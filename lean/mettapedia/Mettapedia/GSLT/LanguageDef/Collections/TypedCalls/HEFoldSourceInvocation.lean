import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceFrontier
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionAppendSource

/-! The authored fold equation joins its earned fresh frame to the actual
function body and local primitives. This is a source invocation, not a body
correctness premise. The full collection space and its live world are explicit. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceInvocation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HEFoldParameterCapture (query)

theorem query_read (policy : Policy) (before : Frame) (pairs : List Entry.Value) (init : Entry.Value)
    (left right : String) (leftFresh : left ∉ specBindingVars before.bindings)
    (rightFresh : right ∉ specBindingVars before.bindings)
    (pairsClosed : TypeSubst.typeVarsList (pairs.map Entry.Value.erase) = [])
    (initClosed : TypeSubst.typeVars init.erase = []) :
    before.read policy (query pairs init left right) = query pairs init left right := by
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  simp only [query, HECollectionFoldSourceLoop.operation, Entry.Value.erase, List.map_cons, List.map_nil,
    TypeSubst.typeVars, TypeSubst.typeVarsList, pairsClosed, initClosed, List.nil_append, List.append_nil,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at occurs
  have first := HEFreshSyntaxBinding.resolve_fresh before left leftFresh
  have second := HEFreshSyntaxBinding.resolve_fresh before right rightFresh
  aesop

theorem invocation {Context World : Type} (environment : WorldEnvironment Context World)
    (snapshots : SnapshotServices Context World) (policy : Policy) (label : Context) (world : World)
    (hidden : List String)
    (sourceView : environment.view world label = HECollectionSpaceExtension.space)
    (emitter : HECollectionFoldNativeEntry.Emitter environment label world hidden)
    (appendInterface : HECollectionAppendSource.Interface environment snapshots policy label world)
    (ordinary : ∀ arguments, NonGroundedCallRel environment.dispatch (.expression (.symbol "foldl-atom" :: arguments)))
    (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots label world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (mark : Entry.Status) (values : List Entry.Value)
    (valuesClosed : TypeSubst.typeVarsList (values.map Entry.Value.erase) = []) :
    ∃ after finalMark, Stateful.InvocationRel environment label world live scope caller
      (query pairs (.expression mark values) left right) before
      [(.expression finalMark (values ++ rows.map Prod.fst), after)] world (policy := policy) := by
  have pairsClosed := HECollectionFoldSourceLoop.pairs_closed stored closed
  have initClosed : TypeSubst.typeVars (.expression mark values : Entry.Value).erase = [] := by
    simpa only [Entry.Value.erase, TypeSubst.typeVars] using valuesClosed
  obtain ⟨work, after, a, b, spaceName, frontier, bindings, unified, bodyRead, differentAB, differentAS, differentBS, aFixed, bFixed⟩ :=
    HEFoldSourceFrontier.complete_frame policy live before pairs (.expression mark values) left right different
      leftFresh rightFresh pairsClosed initClosed
  obtain ⟨finalMark, executed⟩ := HECollectionFoldFunction.source emitter policy after
    (HECollectionAppendSource.append_calls appendInterface after) a b spaceName .active differentAB (Or.inr rfl)
    differentAS differentBS aFixed bFixed rows pairs stored closed live scope
    (some (query pairs (.expression mark values) left right).erase) mark values valuesClosed
  refine ⟨after, finalMark, Stateful.InvocationRel.equations (works := [work]) ?_ ?_ (by simp) ?_⟩
  · simpa only [query, Entry.Value.erase, List.map_cons, List.map_nil] using
      ordinary [(.expression .active pairs : Entry.Value).erase, (.expression mark values : Entry.Value).erase,
        .var left, .var right, (HECollectionFoldSourceLoop.operation .active left right).erase]
  · simpa only [sourceView] using frontier
  · simpa only [List.append_nil] using
      (Stateful.InvocationEquationsRel.cons bindings unified
        (by
          rw [bodyRead]
          exact Stateful.BoundaryRel.producerFunction
            (by
              refine ⟨?_, Or.inr rfl⟩
              simp [HECollectionFoldFunction.function, Entry.Value.erase, Minimal.IsFunction]) executed)
        Stateful.InvocationEquationsRel.nil)

theorem eval_source {Context World : Type} (environment : WorldEnvironment Context World)
    (snapshots : SnapshotServices Context World) (policy : Policy) (label : Context) (world : World)
    (hidden : List String)
    (sourceView : environment.view world label = HECollectionSpaceExtension.space)
    (emitter : HECollectionFoldNativeEntry.Emitter environment label world hidden)
    (appendInterface : HECollectionAppendSource.Interface environment snapshots policy label world)
    (ordinary : ∀ arguments, NonGroundedCallRel environment.dispatch (.expression (.symbol "foldl-atom" :: arguments)))
    (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots label world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    ∃ after finalMark, Stateful.MinimalRel environment label world live scope caller
      (.expression .active [.symbol "eval", query pairs (.expression .active []) left right]) before
      [(.expression finalMark (rows.map Prod.fst), after)] world (policy := policy) := by
  obtain ⟨after, finalMark, executed⟩ := invocation environment snapshots policy label world hidden sourceView emitter appendInterface
    ordinary before live scope caller left right different leftFresh rightFresh rows pairs stored closed .active [] rfl
  refine ⟨after, finalMark, Stateful.MinimalRel.eval ?_⟩
  rw [query_read policy before pairs (.expression .active []) left right leftFresh rightFresh
    (HECollectionFoldSourceLoop.pairs_closed stored closed) (by simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])]
  simpa only [List.nil_append] using executed

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceInvocation
