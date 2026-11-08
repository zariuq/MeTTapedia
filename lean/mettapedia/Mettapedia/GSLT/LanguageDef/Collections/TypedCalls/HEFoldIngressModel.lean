import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceInvocation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldControls

/-! The collection fold is invoked through its authored equation in the
extended collection space. Local snapshot/native services are the existing
fold instance; only this source slice's closed operator query is required.
This does not identify the stored-type reader with every HE type-query role. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldIngressModel

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open HECollectionFoldModel (World snapshots)
open HEFoldParameterCapture (query)

def environment (policy : Policy) : WorldEnvironment Unit World :=
  { HECollectionFoldModel.environment policy with view := fun _ _ => HECollectionSpaceExtension.space }

theorem append_query (names : List String) (frame : Frame) (expected : Atom) :
    scopedLookup names HECollectionSpaceExtension.space frame.bindings (.symbol CollectionStdlibSource.appendName) expected
      [HECollectionAppendSource.signature.functionType] := by
  have declared : getAtomTypes HECollectionSpaceExtension.space (.symbol CollectionStdlibSource.appendName) =
      [HECollectionAppendSource.signature.functionType] := rfl
  refine ⟨[HECollectionAppendSource.signature.functionType], ?_, .cons ?_ (.nil _)⟩
  · simpa only [declared] using FirstSuccessSourceReplies.source_types HECollectionSpaceExtension.space (.symbol CollectionStdlibSource.appendName)
  · exact ⟨id, Function.injective_id, by simp,
      by simp [HECollectionAppendSource.signature, CompletedDelivery.arrowType, TypeSubst.typeVars,
        TypeSubst.typeVarsList, Atom.expressionType, Atom.atomType]⟩

theorem emitter (policy : Policy) (world : World) :
    HECollectionFoldNativeEntry.Emitter (environment policy) () world (HECollectionFoldModel.hidden world) := by
  have old := HECollectionFoldModel.emitter policy world
  exact ⟨old.executable, old.raw, old.emitted, old.step⟩

theorem append_interface (policy : Policy) (world : World) :
    HECollectionAppendSource.Interface (environment policy) snapshots policy () world := by
  have old := HECollectionFoldModel.append_interface policy world
  exact ⟨old.kind, append_query, old.executable, old.raw, old.completed, old.primitive⟩

theorem ordinary (policy : Policy) (arguments : List Atom) :
    NonGroundedCallRel (environment policy).dispatch (.expression (.symbol "foldl-atom" :: arguments)) := by
  simp [NonGroundedCallRel, Minimal.HostCall, environment, HECollectionFoldModel.environment,
    HECollectionFoldModel.dispatch, Minimal.embeddedInstruction, CollectionStdlibSource.foldName, CollectionStdlibSource.appendName]

theorem source (policy : Policy) (world : World) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right : String)
    (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots () world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    ∃ after finalMark, Stateful.MinimalRel (environment policy) () world live scope caller
      (.expression .active [.symbol "eval", query pairs (.expression .active []) left right]) before
      [(.expression finalMark (rows.map Prod.fst), after)] world (policy := policy) :=
  HEFoldSourceInvocation.eval_source (environment policy) snapshots policy () world (HECollectionFoldModel.hidden world)
    rfl (emitter policy world) (append_interface policy world) (ordinary policy) before live scope caller left right different
    leftFresh rightFresh rows pairs stored closed

theorem retained_run (policy : Policy) (world : World) (before : Frame)
    (live : List Atom) (scope : List String) (caller : Option Atom) (left right : String)
    (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots () world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (stack : List Continuation) (emitted : List Result) :
    ∃ after finalMark, WorldSteps (environment policy).view (environment policy).services (environment policy).dispatch
      (environment policy).lookup policy
      ⟨world, (), .work (.minimal live scope caller (.expression .active [.symbol "eval",
        query pairs (.expression .active []) left right]) before), stack, emitted⟩
      ⟨world, (), .returning [(.expression finalMark (rows.map Prod.fst), after)], stack, emitted⟩
      (admission := (environment policy).arguments) := by
  obtain ⟨after, finalMark, run⟩ := source policy world before live scope caller left right different leftFresh rightFresh
    rows pairs stored closed
  exact ⟨after, finalMark, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.minimal_complete run stack) emitted⟩

theorem missing_equation_refuses (policy : Policy) (before : Frame) (world : World)
    (pairs : List Entry.Value) (init : Entry.Value) (left right : String) :
    Stateful.InvocationRel (HECollectionFoldModel.environment policy) () world [] [] none
      (query pairs init left right) before [(.symbol "NotReducible", before)] world (policy := policy) := by
  apply Stateful.InvocationRel.absent
  · simpa only [query, Entry.Value.erase, List.map_cons, List.map_nil, environment] using
      ordinary policy [(.expression .active pairs : Entry.Value).erase, init.erase, .var left, .var right,
        (HECollectionFoldSourceLoop.operation .active left right).erase]
  · change EquationFrontierRel HECollectionFoldModel.space [] (query pairs init left right).erase before.bindings []
    have scanned : EquationFrontierRel HECollectionFoldModel.space [] (query pairs init left right).erase before.bindings
        ([[]] : List (List EquationWork)).flatten := by
      apply EquationFrontierRel.completed
      exact .cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _) .nil
    simpa only [List.flatten_cons, List.flatten_nil, List.nil_append] using scanned

namespace Controls

open HECollectionFoldControls (policy world callerFrame rows pairs values)

theorem duplicates_and_error_source :
    ∃ after mark, Stateful.MinimalRel (environment policy) () world [] [] none
      (.expression .active [.symbol "eval", query pairs (.expression .active []) "acc" "item"]) callerFrame
      [(.expression mark values, after)] world (policy := policy) := by
  simpa only [HECollectionFoldControls.row_values] using source policy world callerFrame [] [] none "acc" "item"
    (by decide) (by decide) (by decide) rows pairs HECollectionFoldControls.stored HECollectionFoldControls.closed

theorem empty_source :
    ∃ after mark, Stateful.MinimalRel (environment policy) () world [] [] none
      (.expression .active [.symbol "eval", query [] (.expression .active []) "acc" "item"]) callerFrame
      [(.expression mark [], after)] world (policy := policy) := by
  simpa only [List.map_nil] using source policy world callerFrame [] [] none "acc" "item"
    (by decide) (by decide) (by decide) [] [] .nil (by simp)

theorem equal_parameters_break_template :
    HECollectionFoldEmission.rewritten [] (.grounded (.int 0)) (.grounded (.int 1)) "same" "same"
        (HECollectionFoldSourceLoop.operation .active "same" "same") =
      .expression .active [.symbol CollectionStdlibSource.appendName, .grounded (.int 0), .grounded (.int 0)] ∧
    HECollectionFoldEmission.rewritten [] (.grounded (.int 0)) (.grounded (.int 1)) "same" "same"
        (HECollectionFoldSourceLoop.operation .active "same" "same") ≠
      .expression .active [.symbol CollectionStdlibSource.appendName, .grounded (.int 0), .grounded (.int 1)] := by
  simp [HECollectionFoldEmission.rewritten, HECollectionFoldSourceLoop.operation,
    Entry.Value.substitute, Entry.Value.rebuildStatus]

end Controls
end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldIngressModel
