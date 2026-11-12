import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldWorldServices
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionArithmetic

/-!
# The authored numeric fold consumer

The same minimal-fold emitter and fresh equation capture used by collection
append now execute addition. Each iteration derives an actual typed arithmetic
call and resumes the emitted chain; no complete fold result is a service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericFold

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionFoldEmission HECollectionFoldReadback HECollectionFoldNativeEntry

def number (value : Int) : Entry.Value := .grounded (.int value)
def numbers (values : List Int) : List Entry.Value := values.map number

theorem number_closed (value : Int) : TypeSubst.typeVars (number value).erase = [] := by
  simp [number, Entry.Value.erase, TypeSubst.typeVars]

theorem numbers_closed (values : List Int) : TypeSubst.typeVarsList ((numbers values).map Entry.Value.erase) = [] := by
  induction values with
  | nil => rfl
  | cons head tail ih => simpa only [numbers, List.map_cons, TypeSubst.typeVarsList, number_closed, List.nil_append] using ih

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem finish_emission (world : World) (policy : Policy) (frame : Frame) (left right : String)
    (different : left ≠ right)
    (leftFixed : frame.read policy (.var left) = .var left) (rightFixed : frame.read policy (.var right) = .var right)
    (values : List Int) (init : Int) (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.BoundaryRel current sourceSpace world live scope caller .body
      (emission (HECollectionWorld.hidden world) live scope frame (numbers values) (number init) left right
        (HECollectionFoldSourceLoop.operation .active left right (operatorName := "+"))
        (.grounded (minimal.contextPayload sourceSpace))) frame
      [(.expression .active [.symbol "return", number (values.foldl (· + ·) init)], frame)] world (policy := policy) := by
  induction values generalizing init live scope caller with
  | nil =>
    have fixed := HECollectionClosedAppend.closed_read policy frame
      (.expression .active [.symbol "return", number init]) (by
        simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, number])
    simpa only [numbers, List.map_nil, List.foldl_nil, emission, fixed] using
      (Stateful.BoundaryRel.bodyTerminal (environment := current) (policy := policy) (frame := frame)
        (value := .expression .active [.symbol "return", number init])
        (by rw [fixed]; simp [Entry.Value.erase, Minimal.embeddedInstruction]))
  | cons head tail ih =>
    let context := Entry.Value.grounded (minimal.contextPayload sourceSpace)
    let op := HECollectionFoldSourceLoop.operation .active left right (operatorName := "+")
    let avoid := protectedNames (HECollectionWorld.hidden world) live scope frame (numbers (head :: tail)) (number init) left right op context
    let nextName := chainName avoid op
    let emitted := step avoid (number head) (numbers tail) (number init) left right op context
    have contextClosed : TypeSubst.typeVars context.erase = [] := by simp [context, Entry.Value.erase, TypeSubst.typeVars]
    have nextDistinct : left ≠ nextName ∧ right ≠ nextName :=
      chain_distinct_from_parameters (HECollectionWorld.hidden world) live scope frame (numbers (head :: tail))
        (number init) left right op context
    have fixed : frame.read policy emitted = emitted :=
      protected_step_read (operatorName := "+") policy frame (HECollectionWorld.hidden world) live scope
        (number head) (numbers tail) (number init) left right context .active different leftFixed rightFixed
        (number_closed init) (number_closed head) (numbers_closed tail) contextClosed
    have added := HECollectionArithmetic.addition_source minimal nativePolicy external active primitive subtypes world policy frame
      (emitted.erase :: live) scope init head
    have rewrittenStep : rewritten avoid (number init) (number head) left right op =
        HEBinaryNumericSource.addition.call init head := by
      simpa only [op, HECollectionFoldSourceLoop.operation, HEBinaryNumericSource.Operation.call,
        HEBinaryNumericSource.addition, number] using
        collapse_template (operatorName := "+") avoid (number init) (number head) left right different .active
    have finish := ih (init + head) live scope caller
    apply Stateful.BoundaryRel.bodyResume
    · change Minimal.embeddedInstruction (frame.read policy emitted).erase = true
      rw [fixed]
      exact step_is_minimal_instruction avoid (number head) (numbers tail) (number init) left right op context
    · change Stateful.BodyRel current sourceSpace world live scope caller (frame.read policy emitted) frame _ world (policy := policy)
      rw [fixed]
      refine Stateful.BodyRel.run (world1 := world)
        (raw := [(emission (HECollectionWorld.hidden world) live scope frame (numbers tail) (number (init + head)) left right op context, frame)]) ?_ ?_
      · apply Stateful.MinimalRel.chain (world1 := world) (selected := [(number (init + head), frame)])
        · apply Stateful.MinimalRel.metta
          convert added using 1 <;>
            simp [emitted, step, Atom.undefinedType, Entry.Value.erase, number]
        · apply Stateful.BoundaryBatchRel.single_iff.mpr
          apply Stateful.BoundaryRel.chain
          rw [HECollectionClosedAppend.closed_read policy frame (number (init + head)) (number_closed _)]
          have substituted : substituteBinder policy nextName (number (init + head))
              (.expression .active [.symbol "eval", call (numbers tail) (.var nextName) left right op context]) =
              .expression .active [.symbol "eval", call (numbers tail) (number (init + head)) left right op context] := by
            simpa only [nextName, op, HECollectionFoldSourceLoop.operation] using
              next_call_substitution (operatorName := "+") policy nextName left right (number (init + head)) context
                (numbers tail) .active nextDistinct.1 nextDistinct.2 (numbers_closed tail) contextClosed
          rw [substituted]
          exact eval_entry (operatorName := "+")
            (HECollectionFoldWorldServices.emitter minimal nativePolicy external active primitive subtypes world)
            policy live scope caller frame (numbers tail) (number (init + head)) left right context .active
            leftFixed rightFixed (number_closed _) (numbers_closed tail) contextClosed
      · apply Stateful.BoundaryBatchRel.single_iff.mpr
        exact finish

theorem function_source (world : World) (policy : Policy) (frame : Frame) (left right spaceName : String)
    (different : left ≠ right) (leftSpace : left ≠ spaceName) (rightSpace : right ≠ spaceName)
    (leftFixed : frame.read policy (.var left) = .var left) (rightFixed : frame.read policy (.var right) = .var right)
    (values : List Int) (init : Int) (live : List Atom) (scope : List String) (caller : Option Atom)
    (itemsMark : Entry.Status := .active) :
    Stateful.MinimalRel current sourceSpace world live scope caller
      (HECollectionFoldFunction.function (numbers values) (number init) left right spaceName .active (operatorName := "+") (itemsMark := itemsMark)) frame
      [(number (values.foldl (· + ·) init), frame)] world (policy := policy) := by
  let op := HECollectionFoldSourceLoop.operation .active left right (operatorName := "+")
  let context := Entry.Value.grounded (minimal.contextPayload sourceSpace)
  let body := HECollectionFoldFunction.body (numbers values) (number init) left right spaceName .active (operatorName := "+") (itemsMark := itemsMark)
  let functionLive := (.expression [.symbol "function", body.erase]) :: live
  let functionCaller : Option Atom := some (.expression [.symbol "function", body.erase])
  have contextClosed : TypeSubst.typeVars context.erase = [] := by simp [context, Entry.Value.erase, TypeSubst.typeVars]
  have finished := finish_emission minimal nativePolicy external active primitive subtypes world policy frame left right different
    leftFixed rightFixed values init functionLive scope functionCaller
  apply Stateful.MinimalRel.function (world1 := world)
    (raw := [(.expression .active [.symbol "return", number (values.foldl (· + ·) init)], frame)]) rfl
  · refine Stateful.BodyRel.run (world1 := world)
      (raw := [(emission (HECollectionWorld.hidden world) functionLive scope frame (numbers values) (number init) left right op context, frame)]) ?_ ?_
    · apply Stateful.MinimalRel.chain (world1 := world) (selected := [(context, frame)])
      · exact .contextSpace
      · apply Stateful.BoundaryBatchRel.single_iff.mpr
        apply Stateful.BoundaryRel.chain
        rw [HECollectionClosedAppend.closed_read policy frame context contextClosed]
        have substituted : substituteBinder policy spaceName context
            (.expression .active [.symbol "eval", call (numbers values) (number init) left right op (.var spaceName) (itemsMark := itemsMark)]) =
            .expression .active [.symbol "eval", call (numbers values) (number init) left right op context (itemsMark := itemsMark)] := by
          simpa only [op, HECollectionFoldSourceLoop.operation] using
            context_substitution (operatorName := "+") (itemsMark := itemsMark) policy spaceName left right context (number init) (numbers values) .active
              leftSpace rightSpace (numbers_closed values) (number_closed init)
        rw [substituted]
        exact marked_eval_entry (operatorName := "+") (itemsMark := itemsMark)
          (HECollectionFoldWorldServices.marked_emitter minimal nativePolicy external active primitive subtypes world)
          policy functionLive scope functionCaller frame (numbers values) (number init) left right context .active
          leftFixed rightFixed (number_closed init) (numbers_closed values) contextClosed
    · exact Stateful.BoundaryBatchRel.single_iff.mpr finished
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .functionReturn

theorem invocation (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (caller : Option Atom) (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (values : List Int) (init : Int) (itemsMark : Entry.Status := .active) :
    ∃ after, Stateful.InvocationRel current sourceSpace world live scope caller
      (HEFoldParameterCapture.query (numbers values) (number init) left right (operatorName := "+") (itemsMark := itemsMark)) before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  obtain ⟨work, after, a, b, spaceName, frontier, bindings, unified, read, differentAB, differentAS, differentBS, aFixed, bFixed⟩ :=
    HEFoldSourceFrontier.complete_frame (operatorName := "+") (itemsMark := itemsMark) policy live before (numbers values) (number init) left right
      different leftFresh rightFresh (numbers_closed values) (number_closed init)
  have executed := function_source (itemsMark := itemsMark) minimal nativePolicy external active primitive subtypes world policy after a b spaceName
    differentAB differentAS differentBS aFixed bFixed values init live scope
      (some (HEFoldParameterCapture.query (numbers values) (number init) left right (operatorName := "+") (itemsMark := itemsMark)).erase)
  refine ⟨after, Stateful.InvocationRel.equations (works := [work]) ?_ frontier (by simp) ?_⟩
  · simpa only [HEFoldParameterCapture.query, Entry.Value.erase, List.map_cons, List.map_nil] using
      HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "foldl-atom"
        [(.expression itemsMark (numbers values) : Entry.Value).erase, (number init).erase, .var left, .var right,
          (HECollectionFoldSourceLoop.operation .active left right (operatorName := "+")).erase] (by simp)
  · simpa only [List.append_nil] using
      (Stateful.InvocationEquationsRel.cons bindings unified
        (by
          rw [read]
          exact Stateful.BoundaryRel.producerFunction (by
            refine ⟨?_, Or.inr rfl⟩
            simp [HECollectionFoldFunction.function, Entry.Value.erase, Minimal.IsFunction]) executed) .nil)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericFold
