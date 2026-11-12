import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericFold
import Mettapedia.Languages.MeTTa.HE.DeliveredArgumentPackets

/-!
# Typed source ingress for the authored numeric fold

The Expression, Atom and Variable formals have their actual held deliveries.
The selected source equation then captures those operands and runs the common
minimal-fold control. Addition executes at each iteration; the Undefined
return still takes its ordinary numeric return cast.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number numbers number_closed numbers_closed)
open Mettapedia.Machines.OrderedProtocol.Completion

def query (values : List Int) (init : Int) (left right : String) (itemsMark : Entry.Status := .active) : Entry.Value :=
  HEFoldParameterCapture.query (numbers values) (number init) left right (operatorName := "+") (itemsMark := itemsMark)

def requests (values : List Int) (init : Int) (left right : String) (itemsMark : Entry.Status := .active) : List ArgumentRequest :=
  [(.expression itemsMark (numbers values), Atom.expressionType), (number init, Atom.atomType),
   (.var left, Atom.variableType), (.var right, Atom.variableType),
   (HECollectionFoldSourceLoop.operation .active left right (operatorName := "+"), Atom.atomType)]

def signature : SelectedTypePolicy := ⟨CollectionStdlibSource.foldType,
  [Atom.expressionType, Atom.atomType, Atom.variableType, Atom.variableType, Atom.atomType], Atom.undefinedType, rfl⟩

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes

theorem query_read (policy : Policy) (before : Frame) (values : List Int) (init : Int) (left right : String)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) (itemsMark : Entry.Status := .active) :
    before.read policy (query values init left right (itemsMark := itemsMark)) = query values init left right (itemsMark := itemsMark) := by
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  simp only [query, HEFoldParameterCapture.query, HECollectionFoldSourceLoop.operation, Entry.Value.erase,
    List.map_cons, List.map_nil, TypeSubst.typeVars, TypeSubst.typeVarsList, numbers_closed, number_closed,
    List.nil_append, List.append_nil] at occurs
  have first := HECollectionFoldReadback.resolve_of_fixed policy before left leftFixed
  have second := HECollectionFoldReadback.resolve_of_fixed policy before right rightFixed
  aesop

theorem arguments (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (left right : String)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) (itemsMark : Entry.Status := .active) :
    Stateful.ArgumentsRel current sourceSpace world live scope (requests values init left right (itemsMark := itemsMark)) before
      [(Entry.Value.argumentPacket ((requests values init left right (itemsMark := itemsMark)).map Prod.fst), before)] world (policy := policy) := by
  have tupleFixed : before.read policy (.expression itemsMark (numbers values)) = .expression itemsMark (numbers values) :=
    HECollectionClosedAppend.closed_read policy before _ (by
      simpa only [Entry.Value.erase, TypeSubst.typeVars] using numbers_closed values)
  have numFixed := HECollectionClosedAppend.closed_read policy before (number init) (number_closed init)
  have opFixed : before.read policy (HECollectionFoldSourceLoop.operation .active left right (operatorName := "+")) =
      HECollectionFoldSourceLoop.operation .active left right (operatorName := "+") := by
    have first := HECollectionFoldReadback.resolve_of_fixed policy before left leftFixed
    have second := HECollectionFoldReadback.resolve_of_fixed policy before right rightFixed
    simp only [HECollectionFoldSourceLoop.operation, Frame.read, Entry.Value.substitute, first, second,
      List.map_cons, List.map_nil, HEFreshEquationFrames.Range.active_rebuild]
  apply DeliveredArgumentPackets.source current policy sourceSpace world scope before (requests values init left right (itemsMark := itemsMark))
  · intro request member
    simp only [requests, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact tupleFixed
    · exact numFixed
    · exact leftFixed
    · exact rightFixed
    · exact opFixed
  · intro request member
    simp only [requests, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · by_cases stopped : IsEmptyOrErrorRel (.expression itemsMark (numbers values) : Entry.Value).erase
      · exact .stopped stopped
      · exact .pass stopped (by simp only [Entry.Value.erase]; exact .expression _) (Or.inr (Or.inl rfl))
    · exact .pass (by simp [number, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simpa only [number, Entry.Value.erase] using MetaTypeRel.grounded (.int init)) (Or.inl rfl)
    · exact .pass (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simpa only [Entry.Value.erase] using MetaTypeRel.variable left) (Or.inr (Or.inl rfl))
    · exact .pass (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simpa only [Entry.Value.erase] using MetaTypeRel.variable right) (Or.inr (Or.inl rfl))
    · exact .pass (by simp [HECollectionFoldSourceLoop.operation, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simp only [HECollectionFoldSourceLoop.operation, Entry.Value.erase]; exact .expression _) (Or.inl rfl)

theorem selection (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (left right : String) (itemsMark : Entry.Status := .active) :
    (current).arguments.selection sourceSpace (current).lookup policy live scope (query values init left right (itemsMark := itemsMark)).erase
      (.symbol "foldl-atom") Atom.undefinedType before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (query values init left right (itemsMark := itemsMark)).erase Atom.undefinedType before.bindings
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (query values init left right (itemsMark := itemsMark)).erase 1 ((requests values init left right (itemsMark := itemsMark)).map (fun request => request.1.erase))
      signature.argumentTypes [before] [before] [] := by
    simp only [requests, signature, List.map_cons, List.map_nil, Entry.Value.erase]
    exact .cons (AdmissionFramesRel.single (.kind (.expression _) .expression))
      (.cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _))
        (.cons (AdmissionFramesRel.single (.kind (.variable left) .variable))
          (.cons (AdmissionFramesRel.single (.kind (.variable right) .variable))
            (.cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _)) .nil))))
  refine ⟨[signature.functionType], HECollectionInferredQueries.closed_head ops external names before "foldl-atom" _ _ rfl rfl,
    .selected (errors := []) ?_ (by simp)⟩
  simpa [signature, requests, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := (query values init left right (itemsMark := itemsMark)).erase)
      (expected := Atom.undefinedType) (selected := signature) (before := before) (operator := .symbol "foldl-atom")
      (arguments := (requests values init left right (itemsMark := itemsMark)).map (fun request => request.1.erase))
      (by simp [query, HEFoldParameterCapture.query, requests, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedLeft _ _)))) .nil)

theorem called_fixed (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (left right : String) (different : left ≠ right)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) (itemsMark : Entry.Status := .active) :
    ∃ after, Stateful.CallRel current sourceSpace world live scope (query values init left right (itemsMark := itemsMark)) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  obtain ⟨work, after, a, b, spaceName, frontier, bindings, unified, read, differentAB, differentAS, differentBS, aFixed, bFixed⟩ :=
    HEFoldSourceFrontier.complete_fixed_frame (operatorName := "+") (itemsMark := itemsMark) policy (Atom.undefinedType :: live) before (numbers values) (number init)
      left right different leftFixed rightFixed (numbers_closed values) (number_closed init)
  have executed := HECollectionNumericFold.function_source (itemsMark := itemsMark) minimal nativePolicy external active primitive subtypes world policy after a b spaceName
    differentAB differentAS differentBS aFixed bFixed values init (Atom.undefinedType :: live) scope (some (query values init left right (itemsMark := itemsMark)).erase)
  have returned : Stateful.ReturnRel current sourceSpace world live scope (query values init left right (itemsMark := itemsMark)) Atom.undefinedType
      (number (values.foldl (· + ·) init)) after [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
    apply Stateful.ReturnRel.evaluate
    · simp [number, Entry.Value.erase, Atom.notReducible]
    · simp [number, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact HECollectionArithmetic.number_undefined minimal nativePolicy external active primitive subtypes world policy live scope after _
  refine ⟨after, Stateful.CallRel.equations (works := [work]) ?_ ?_ frontier (by simp) ?_⟩
  · simp [query, HEFoldParameterCapture.query, Entry.Value.erase, IsErrorRel]
  · simpa only [query, HEFoldParameterCapture.query, Entry.Value.erase, List.map_cons, List.map_nil] using
      HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "foldl-atom"
        [(.expression itemsMark (numbers values) : Entry.Value).erase, (number init).erase, .var left, .var right,
          (HECollectionFoldSourceLoop.operation .active left right (operatorName := "+")).erase] (by simp)
  · simpa only [List.append_nil, query] using
      (Stateful.EquationBodiesRel.cons bindings unified
        (by
          rw [read]
          exact Stateful.BoundaryRel.producerFunction (by
            refine ⟨?_, Or.inr rfl⟩
            simp [HECollectionFoldFunction.function, Entry.Value.erase, Minimal.IsFunction]) executed)
        (Stateful.BoundaryBatchRel.single_iff.mpr (.returned returned)) .nil)

theorem called (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings) (itemsMark : Entry.Status := .active) :
    ∃ after, Stateful.CallRel current sourceSpace world live scope (query values init left right (itemsMark := itemsMark)) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  have leftFixed : before.read policy (.var left) = .var left := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before left leftFresh
  have rightFixed : before.read policy (.var right) = .var right := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before right rightFresh
  exact called_fixed minimal nativePolicy external active primitive subtypes world policy before live scope
    values init left right different leftFixed rightFixed itemsMark

theorem source_fixed (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (left right : String) (different : left ≠ right)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) (itemsMark : Entry.Status := .active) :
    ∃ after, Stateful.AtomRel current sourceSpace world live scope (query values init left right (itemsMark := itemsMark)) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  obtain ⟨after, callRun⟩ := called_fixed (itemsMark := itemsMark) minimal nativePolicy external active primitive subtypes world policy before live scope values init left right
    different leftFixed rightFixed
  let output := number (values.foldl (· + ·) init)
  have originalRead := query_read (itemsMark := itemsMark) policy before values init left right leftFixed rightFixed
  have outputRead := HECollectionClosedAppend.closed_read policy after output (number_closed _)
  have calls : Stateful.CallsRel current sourceSpace world live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket ((requests values init left right (itemsMark := itemsMark)).map Prod.fst), before)].map
        (functionAssemble (.symbol "foldl-atom"))) [(output, after)] world (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.expressionType, Atom.undefinedType, functionAssemble, query, requests,
      HEFoldParameterCapture.query, output] using Stateful.CallsRel.cons callRun Stateful.CallsRel.nil
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      ([(output, after)].map (readResult policy)) [(output, after)] := by
    simpa only [List.map_cons, List.map_nil, readResult, outputRead] using HECollectionAppendSource.singleton_priority (output, after)
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy sourceSpace world world world world live scope
    (query values init left right (itemsMark := itemsMark)) Atom.undefinedType before before before .active (.symbol "foldl-atom") (.symbol "foldl-atom")
    ((requests values init left right (itemsMark := itemsMark)).map Prod.fst) signature
    [(Entry.Value.argumentPacket ((requests values init left right (itemsMark := itemsMark)).map Prod.fst), before)] [(output, after)] [(output, after)]
    (by
      rw [originalRead]
      simp only [query, HEFoldParameterCapture.query, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
    (by rw [originalRead]; rfl)
    (by simpa only [originalRead, Entry.Value.erase, environment, id_eq] using
      selection (itemsMark := itemsMark) minimal nativePolicy external active primitive subtypes policy before live scope values init left right)
    rfl (HECollectionArithmetic.closed_operator minimal nativePolicy external active primitive subtypes world policy _ _ before
      "foldl-atom" signature.functionType (by decide) (by decide) (by decide) rfl rfl)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (by simpa [signature, requests, invocationReturnType, Atom.expressionType, Atom.undefinedType, Entry.Value.erase] using
      (arguments (itemsMark := itemsMark) minimal nativePolicy external active primitive subtypes world policy before
        (Atom.symbol "foldl-atom" :: Atom.undefinedType :: live) scope values init left right leftFixed rightFixed)) calls priority
  refine ⟨after, ?_⟩
  simpa [originalRead, publishResult, Entry.Value.publish, Entry.Value.withStatus, output, number] using complete

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings) (itemsMark : Entry.Status := .active) :
    ∃ after, Stateful.AtomRel current sourceSpace world live scope (query values init left right (itemsMark := itemsMark)) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  have leftFixed : before.read policy (.var left) = .var left := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before left leftFresh
  have rightFixed : before.read policy (.var right) = .var right := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before right rightFresh
  exact source_fixed minimal nativePolicy external active primitive subtypes world policy before live scope
    values init left right different leftFixed rightFixed itemsMark


end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionNumericSource
