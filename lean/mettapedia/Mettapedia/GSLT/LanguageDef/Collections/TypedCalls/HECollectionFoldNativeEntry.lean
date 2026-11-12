import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldReadback

/-! The minimal fold helper enters the existing invocation boundary and
returns exactly one emitted instruction. This entry does not execute the
fold or assume its final value. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldNativeEntry

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open HECollectionFoldEmission HECollectionFoldReadback

structure Emitter {Context World : Type} (environment : WorldEnvironment Context World)
    (label : Context) (world : World) (hidden : List String) : Prop where
  executable : environment.dispatch.executable (.symbol CollectionStdlibSource.foldName)
  raw : ∀ arguments, environment.dispatch.bindingMode (.symbol CollectionStdlibSource.foldName) arguments = .raw
  emitted : ∀ arguments, environment.dispatch.valueProvenance (.symbol CollectionStdlibSource.foldName) arguments = .emitted
  step : ∀ live scope frame items init left right operation context,
    environment.services.groundedAt label world live scope frame (call items init left right operation context)
      (.ok [(emission hidden live scope frame items init left right operation context, Bindings.empty)]) world

/-- The primitive reads the input container as data at every root readiness.
It still emits one instruction; it is not a completed-fold oracle. -/
structure MarkedEmitter {Context World : Type} (environment : WorldEnvironment Context World)
    (label : Context) (world : World) (hidden : List String) : Prop extends Emitter environment label world hidden where
  stepMarked : ∀ live scope frame items init left right operation context itemsMark,
    environment.services.groundedAt label world live scope frame
      (call items init left right operation context (itemsMark := itemsMark))
      (.ok [(emission hidden live scope frame items init left right operation context, Bindings.empty)]) world

theorem emission_not_function (policy : Policy) (hidden : List String) (live : List Atom)
    (scope : List String) (frame : Frame) (items : List Entry.Value) (init : Entry.Value)
    (left right : String) (operation context : Entry.Value) :
    ¬FunctionPending policy (emission hidden live scope frame items init left right operation context) := by
  cases items <;> simp [emission, step, FunctionPending, Minimal.IsFunction, Entry.Value.erase]

theorem invocation_of_step {Context World : Type} {environment : WorldEnvironment Context World}
    {label world hidden} (emitter : Emitter environment label world hidden)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (frame : Frame) (items : List Entry.Value) (init : Entry.Value) (left right : String)
    (operation context : Entry.Value) (itemsMark : Entry.Status)
    (primitive : environment.services.groundedAt label world live scope frame
      (call items init left right operation context (itemsMark := itemsMark))
      (.ok [(emission hidden live scope frame items init left right operation context, Bindings.empty)]) world) :
    Stateful.InvocationRel environment label world live scope caller
      (call items init left right operation context (itemsMark := itemsMark)) frame
      [(emission hidden live scope frame items init left right operation context, frame)] world (policy := policy) := by
  let arguments := [.expression (items.map Entry.Value.erase), init.erase, .var left, .var right, operation.erase, context.erase]
  let output := emission hidden live scope frame items init left right operation context
  have prepared : NativeRowsRel policy environment.dispatch (.symbol CollectionStdlibSource.foldName)
      arguments frame [(output, Bindings.empty)] [(output, frame)] := by
    simpa only [nativeValue, emitter.raw, Prod.fst, Prod.snd] using
      (NativeRowsRel.cons (dispatch := environment.dispatch) (operator := .symbol CollectionStdlibSource.foldName)
        (arguments := arguments) (head := (output, Bindings.empty)) (Frame.NativeRenewRel.empty policy frame) .nil)
  refine .groundedResume (operator := .symbol CollectionStdlibSource.foldName) (arguments := arguments)
    (outcome := .ok [(output, Bindings.empty)]) (rows := [(output, frame)]) (world1 := world)
    ?_ emitter.executable primitive
    (.success prepared) ?_
  · simp only [call, Entry.Value.erase, List.map_cons, List.map_nil, arguments]
  · rw [emitter.emitted]
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .nativeEmittedRaw (.producerRaw (emission_not_function policy hidden live scope frame items init left right operation context))

theorem invocation {Context World : Type} {environment : WorldEnvironment Context World}
    {label world hidden} (emitter : Emitter environment label world hidden)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (frame : Frame) (items : List Entry.Value) (init : Entry.Value) (left right : String)
    (operation context : Entry.Value) :
    Stateful.InvocationRel environment label world live scope caller
      (call items init left right operation context) frame
      [(emission hidden live scope frame items init left right operation context, frame)] world (policy := policy) :=
  invocation_of_step emitter policy live scope caller frame items init left right operation context .active
    (emitter.step live scope frame items init left right operation context)

theorem eval_entry {Context World : Type} {environment : WorldEnvironment Context World}
    {label world hidden} (emitter : Emitter environment label world hidden)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (frame : Frame) (items : List Entry.Value) (init : Entry.Value) (left right : String)
    (context : Entry.Value) (operationMark : Entry.Status)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (initClosed : TypeSubst.typeVars init.erase = [])
    (itemsClosed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = [])
    (contextClosed : TypeSubst.typeVars context.erase = [])
    (operatorName : String := CollectionStdlibSource.appendName) :
    let operation := Entry.Value.expression operationMark [.symbol operatorName, .var left, .var right]
    Stateful.MinimalRel environment label world live scope caller
      (.expression .active [.symbol "eval", call items init left right operation context]) frame
      [(emission hidden live scope frame items init left right operation context, frame)] world (policy := policy) := by
  dsimp only
  apply Stateful.MinimalRel.eval
  rw [call_read (operatorName := operatorName) policy frame items init left right context operationMark leftFixed rightFixed initClosed itemsClosed contextClosed]
  exact invocation emitter policy live scope caller frame items init left right _ context


theorem marked_invocation {Context World : Type} {environment : WorldEnvironment Context World}
    {label world hidden} (emitter : MarkedEmitter environment label world hidden)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (frame : Frame) (items : List Entry.Value) (init : Entry.Value) (left right : String)
    (operation context : Entry.Value) (itemsMark : Entry.Status) :
    Stateful.InvocationRel environment label world live scope caller
      (call items init left right operation context (itemsMark := itemsMark)) frame
      [(emission hidden live scope frame items init left right operation context, frame)] world (policy := policy) :=
  invocation_of_step emitter.toEmitter policy live scope caller frame items init left right operation context itemsMark
    (emitter.stepMarked live scope frame items init left right operation context itemsMark)

theorem marked_eval_entry {Context World : Type} {environment : WorldEnvironment Context World}
    {label world hidden} (emitter : MarkedEmitter environment label world hidden)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (frame : Frame) (items : List Entry.Value) (init : Entry.Value) (left right : String)
    (context : Entry.Value) (operationMark : Entry.Status)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (initClosed : TypeSubst.typeVars init.erase = [])
    (itemsClosed : TypeSubst.typeVarsList (items.map Entry.Value.erase) = [])
    (contextClosed : TypeSubst.typeVars context.erase = [])
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) :
    let operation := Entry.Value.expression operationMark [.symbol operatorName, .var left, .var right]
    Stateful.MinimalRel environment label world live scope caller
      (.expression .active [.symbol "eval", call items init left right operation context (itemsMark := itemsMark)]) frame
      [(emission hidden live scope frame items init left right operation context, frame)] world (policy := policy) := by
  dsimp only
  apply Stateful.MinimalRel.eval
  rw [call_read (operatorName := operatorName) (itemsMark := itemsMark) policy frame items init left right context operationMark
    leftFixed rightFixed initClosed itemsClosed contextClosed]
  exact marked_invocation emitter policy live scope caller frame items init left right _ context itemsMark


end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldNativeEntry
