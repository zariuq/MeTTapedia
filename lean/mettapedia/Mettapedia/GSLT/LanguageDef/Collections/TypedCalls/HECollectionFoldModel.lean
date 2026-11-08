import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionAppendSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldFunction

/-! An explicit local service instance for the collection fold body.
Snapshots use the existing append-store model. The two primitive operations
are one hygienic source emission and one saved-pair append. This is not a
native instruction-lowering proof or the full standard-library environment. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldModel

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation

abbrev World := Unit × List Frame
def snapshots : SnapshotServices Unit World := SnapshotServices.appendModel Unit Unit

def hidden (world : World) : List String := world.2.flatMap (fun frame => specBindingVars frame.bindings)

inductive Primitive (policy : Policy) (world : World) (live : List Atom) (scope : List String) (frame : Frame) :
    Entry.Value → GroundedResult Entry.Value → Prop where
  | fold (items init left right operation context) :
      Primitive policy world live scope frame
        (HECollectionFoldEmission.call items init left right operation context)
        (.ok [(HECollectionFoldEmission.emission (hidden world) live scope frame items init left right operation context,
          Bindings.empty)])
  | append {input outcome} : HECollectionClosedAppend.Step snapshots policy () world input outcome →
      Primitive policy world live scope frame input outcome

def services (policy : Policy) : WorldServices Unit World where
  contextPayload _ := .int (-1)
  nativeCall _ _ _ _ _ _ _ _ := False
  snapshots := some snapshots
  scopedGroundedCall := some (fun _ world live scope frame input outcome after =>
    after = world ∧ Primitive policy world live scope frame input outcome)

def dispatch : Spec.Eval.GroundedDispatch where
  executable operator := operator = .symbol CollectionStdlibSource.foldName ∨ operator = .symbol CollectionStdlibSource.appendName
  outcome operator arguments result := ∃ policy world live scope frame input output,
    input.erase = .expression (operator :: arguments) ∧ output.map Entry.Value.erase = result ∧
      Primitive policy world live scope frame input output
  valueProvenance operator _ := if operator = .symbol CollectionStdlibSource.foldName then .emitted else .completed

def space : Space := Space.ofList
  [.expression [.symbol ":", .symbol CollectionStdlibSource.appendName, HECollectionAppendSource.signature.functionType]]

def environment (policy : Policy) : WorldEnvironment Unit World where
  view _ _ := space
  services := services policy
  dispatch := dispatch
  lookup := scopedLookup
  arguments := kindArgumentService

theorem hidden_covers (world : World) (frame : Frame) (stored : frame ∈ world.2) (name : String)
    (present : name ∈ specBindingVars frame.bindings) : name ∈ hidden world :=
  List.mem_flatMap.mpr ⟨frame, stored, present⟩

theorem append_query (names : List String) (frame : Frame) (expected : Atom) :
    scopedLookup names space frame.bindings (.symbol CollectionStdlibSource.appendName) expected
      [HECollectionAppendSource.signature.functionType] := by
  refine ⟨[HECollectionAppendSource.signature.functionType], ?_, .cons ?_ (.nil _)⟩
  · simpa [space, Space.ofList, getAtomTypes, getAnnotatedTypes,
      CollectionStdlibSource.appendName] using FirstSuccessSourceReplies.source_types space (.symbol CollectionStdlibSource.appendName)
  · exact ⟨id, Function.injective_id, by simp,
      by simp [HECollectionAppendSource.signature, CompletedDelivery.arrowType, TypeSubst.typeVars,
        TypeSubst.typeVarsList, Atom.expressionType, Atom.atomType]⟩

theorem emitter (policy : Policy) (world : World) :
    HECollectionFoldNativeEntry.Emitter (environment policy) () world (hidden world) := by
  constructor
  · exact Or.inl rfl
  · intro _; rfl
  · intro arguments
    simp [environment, dispatch]
  · intro live scope frame items init left right operation context
    exact ⟨rfl, Primitive.fold items init left right operation context⟩

theorem append_interface (policy : Policy) (world : World) :
    HECollectionAppendSource.Interface (environment policy) snapshots policy () world := by
  constructor
  · rfl
  · exact append_query
  · exact Or.inr rfl
  · intro _; rfl
  · intro arguments
    simp [environment, dispatch, CollectionStdlibSource.appendName, CollectionStdlibSource.foldName]
  · intro live scope frame input outcome executed
    exact ⟨rfl, Primitive.append executed⟩

theorem source (policy : Policy) (world : World) (frame : Frame)
    (left right spaceName : String) (different : left ≠ right)
    (leftDifferent : left ≠ spaceName) (rightDifferent : right ≠ spaceName)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots () world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    ∃ mark, Stateful.MinimalRel (environment policy) () world live scope caller
      (HECollectionFoldFunction.function pairs (.expression .active []) left right spaceName .active) frame
      [(.expression mark (rows.map Prod.fst), frame)] world (policy := policy) := by
  simpa only [List.nil_append] using HECollectionFoldFunction.source (emitter policy world) policy frame
    (HECollectionAppendSource.append_calls (append_interface policy world) frame) left right spaceName .active
    different (Or.inr rfl) leftDifferent rightDifferent leftFixed rightFixed rows pairs stored closed live scope caller .active [] rfl

theorem retained_run (policy : Policy) (world : World) (frame : Frame)
    (left right spaceName : String) (different : left ≠ right)
    (leftDifferent : left ≠ spaceName) (rightDifferent : right ≠ spaceName)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots () world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (live : List Atom) (scope : List String) (caller : Option Atom)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ mark, RecursiveMachine.Contextual.WorldSteps (environment policy).view (environment policy).services
      (environment policy).dispatch (environment policy).lookup policy
      ⟨world, (), .work (.minimal live scope caller
        (HECollectionFoldFunction.function pairs (.expression .active []) left right spaceName .active) frame), stack, emitted⟩
      ⟨world, (), .returning [(.expression mark (rows.map Prod.fst), frame)], stack, emitted⟩
      (admission := (environment policy).arguments) := by
  obtain ⟨mark, executed⟩ := source policy world frame left right spaceName different leftDifferent rightDifferent
    leftFixed rightFixed rows pairs stored closed live scope caller
  exact ⟨mark, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.minimal_complete executed stack) emitted⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldModel
