import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetCapture

/-!
# The authored let instruction binds the collected tuple before evaluation

All four operands of unify enter at Atom, including the literal Empty arm.
The local unifier earns the reached frame; the successful template then
enters the actual typed numeric fold in that same frame and world.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionUnifySource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number numbers number_closed numbers_closed)
open HECollectionLetCapture (template instruction)
open Mettapedia.Machines.OrderedProtocol.Completion

def operands (values : List Int) (init : Int) (patternName left right : String) (itemsMark : Entry.Status) : List Entry.Value :=
  [.expression itemsMark (numbers values), .var patternName, template patternName left right init, Entry.Value.ofAtom Atom.empty]

def requests (values : List Int) (init : Int) (patternName left right : String) (itemsMark : Entry.Status) : List ArgumentRequest :=
  (operands values init patternName left right itemsMark).map fun operand => (operand, Atom.atomType)

def signature : SelectedTypePolicy := ⟨CollectionStdlibSource.arrow
  [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType] Atom.undefinedType,
  [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType], Atom.undefinedType, rfl⟩

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes

theorem instruction_read (policy : Policy) (before : Frame) (values : List Int) (init : Int)
    (patternName left right : String) (itemsMark : Entry.Status)
    (patternFixed : before.read policy (.var patternName) = .var patternName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) :
    before.read policy (instruction values init patternName left right itemsMark) =
      instruction values init patternName left right itemsMark := by
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  simp only [instruction, template, HECollectionFoldSourceLoop.operation, Entry.Value.erase, Entry.Value.erase_ofAtom,
    List.map_cons, List.map_nil, TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.empty,
    numbers_closed, number_closed, List.nil_append, List.append_nil] at occurs
  have first := HECollectionFoldReadback.resolve_of_fixed policy before patternName patternFixed
  have second := HECollectionFoldReadback.resolve_of_fixed policy before left leftFixed
  have third := HECollectionFoldReadback.resolve_of_fixed policy before right rightFixed
  aesop

theorem called (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (patternName left right : String) (itemsMark : Entry.Status)
    (patternLeft : patternName ≠ left) (patternRight : patternName ≠ right) (different : left ≠ right)
    (patternFixed : before.read policy (.var patternName) = .var patternName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) :
    ∃ after, Stateful.CallRel current sourceSpace world live scope
      (instruction values init patternName left right itemsMark) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  let tuple := Entry.Value.expression itemsMark (numbers values)
  have closed : TypeSubst.typeVars tuple.erase = [] := by
    simpa only [tuple, Entry.Value.erase, TypeSubst.typeVars] using numbers_closed values
  obtain ⟨bound, reachedEnvironment, candidate, unified⟩ := ContextualUnificationFrame.bind_fixed policy before patternName tuple patternFixed closed
  have kept (name : String) (apart : name ≠ patternName) (fixed : before.read policy (.var name) = .var name) :
      bound.read policy (.var name) = .var name := by
    have resolved : Entry.Value.resolve before.environment name = .var name := by
      simpa only [Frame.read, Entry.Value.substitute] using fixed
    simp only [Frame.read, Entry.Value.substitute, reachedEnvironment]
    rw [ContextualAlias.resolve_bind_other policy.rebuilding before.environment patternName name tuple apart]
    rw [resolved]
    simp only [Entry.Value.substitute, Entry.Value.resolve, List.lookup_cons,
      beq_eq_false_iff_ne.mpr apart, List.lookup_nil, Option.getD_none]
  have leftRead := kept left (Ne.symm patternLeft) leftFixed
  have rightRead := kept right (Ne.symm patternRight) rightFixed
  have tupleRead : bound.read policy (.var patternName) = tuple := by
    simp only [Frame.read, Entry.Value.substitute, reachedEnvironment, Entry.Value.bind, Entry.Value.resolve,
      List.lookup_cons, beq_self_eq_true, Option.getD_some]
    exact HEFreshSyntaxBinding.ground_substitution policy.rebuilding _ tuple closed
  have templateRead : bound.read policy (template patternName left right init) =
      HECollectionNumericSource.query values init left right (itemsMark := itemsMark) := by
    have resolved (name : String) (value : Entry.Value) (read : bound.read policy (.var name) = value) :
        Entry.Value.resolve bound.environment name = value := by
      simpa only [Frame.read, Entry.Value.substitute] using read
    simp only [template, HECollectionNumericSource.query, HEFoldParameterCapture.query,
      HECollectionFoldSourceLoop.operation, Frame.read, Entry.Value.substitute,
      resolved _ _ tupleRead, resolved _ _ leftRead, resolved _ _ rightRead,
      HEFreshSyntaxBinding.ground_substitution policy.rebuilding _ (number init) (number_closed init),
      List.map_cons, List.map_nil, HEFreshEquationFrames.Range.active_rebuild, tuple]
  obtain ⟨after, executed⟩ := HECollectionNumericSource.source_fixed (itemsMark := itemsMark)
    minimal nativePolicy external active primitive subtypes world policy bound live scope values init left right different leftRead rightRead
  have returned : Stateful.ReturnRel current sourceSpace world live scope
      (instruction values init patternName left right itemsMark) Atom.undefinedType
      (bound.read policy (template patternName left right init)) bound
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
    rw [templateRead]
    exact .evaluate (by simp [HECollectionNumericSource.query, HEFoldParameterCapture.query, Entry.Value.erase, Atom.notReducible])
      (by simp [HECollectionNumericSource.query, HEFoldParameterCapture.query, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) executed
  have noHost : ¬Minimal.HostCall (current).dispatch (instruction values init patternName left right itemsMark).erase := by
    simp [instruction, Entry.Value.erase, Minimal.HostCall, environment, HECollectionWorld.dispatch,
      CollectionStdlibSource.foldName, CollectionStdlibSource.appendName]
  have embedded : Minimal.embeddedInstruction (instruction values init patternName left right itemsMark).erase = true := by
    simp [instruction, Entry.Value.erase, Minimal.embeddedInstruction]
  refine ⟨after, Stateful.CallRel.embedded ?_ noHost embedded
    (Stateful.InvocationRel.embedded noHost embedded ?_) (Stateful.BoundaryBatchRel.single_iff.mpr (.returned returned))⟩
  · simp [instruction, Entry.Value.erase, IsErrorRel]
  · apply Stateful.MinimalRel.unifyYes
    · simpa only [tuple, Entry.Value.erase] using candidate
    · exact unified

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (values : List Int) (init : Int) (patternName left right : String) (itemsMark : Entry.Status)
    (patternLeft : patternName ≠ left) (patternRight : patternName ≠ right) (different : left ≠ right)
    (patternFixed : before.read policy (.var patternName) = .var patternName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) :
    ∃ after, Stateful.AtomRel current sourceSpace world live scope
      (instruction values init patternName left right itemsMark) Atom.undefinedType before
      [(number (values.foldl (· + ·) init), after)] world (policy := policy) := by
  obtain ⟨after, callRun⟩ := called minimal nativePolicy external active primitive subtypes world policy before live scope
    values init patternName left right itemsMark patternLeft patternRight different patternFixed leftFixed rightFixed
  let query := instruction values init patternName left right itemsMark
  let input := operands values init patternName left right itemsMark
  let output := number (values.foldl (· + ·) init)
  have queryRead : before.read policy query = query :=
    instruction_read policy before values init patternName left right itemsMark patternFixed leftFixed rightFixed
  have selection : (current).arguments.selection sourceSpace (current).lookup policy live scope query.erase
      (.symbol "unify") Atom.undefinedType before (.selected signature [before]) := by
    let names := invocationTypeScope scope live query.erase Atom.undefinedType before.bindings
    have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy query.erase 1
        (input.map Entry.Value.erase) signature.argumentTypes [before] [before] [] :=
      .cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _))
        (.cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _))
          (.cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _))
            (.cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _)) .nil)))
    refine ⟨[signature.functionType], HECollectionInferredQueries.closed_head ops external names before "unify" _ _ rfl rfl,
      .selected (errors := []) ?_ (by simp)⟩
    simpa [signature, checkedFrames, checkedFailures, names] using
      AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := query.erase)
        (expected := Atom.undefinedType) (selected := signature) (before := before) (operator := .symbol "unify")
        (arguments := input.map Entry.Value.erase) (by simp [query, instruction, input, operands, Entry.Value.erase]) args
        (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedLeft _ _)))) .nil)
  have operandsFixed : ∀ value ∈ input, before.read policy value = value := by
    intro value member
    simp only [input, operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact HECollectionClosedAppend.closed_read policy before _ (by simpa only [Entry.Value.erase, TypeSubst.typeVars] using numbers_closed values)
    · exact patternFixed
    · exact HECollectionLetCapture.template_read policy before _ _ _ _ init patternFixed leftFixed rightFixed
    · exact HECollectionClosedAppend.closed_read policy before _ (by simp [Entry.Value.erase_ofAtom, Atom.empty, TypeSubst.typeVars])
  have arguments : ∀ nestedLive, Stateful.ArgumentsRel current sourceSpace world nestedLive scope (requests values init patternName left right itemsMark) before
      [(Entry.Value.argumentPacket input, before)] world (policy := policy) := by
    intro nestedLive
    apply DeliveredArgumentPackets.source current policy sourceSpace world scope before (requests values init patternName left right itemsMark)
    · intro request member
      change request ∈ input.map (fun operand => (operand, Atom.atomType)) at member
      obtain ⟨value, present, equality⟩ := List.mem_map.mp member
      subst request
      exact operandsFixed value present
    · intro request member
      change request ∈ input.map (fun operand => (operand, Atom.atomType)) at member
      obtain ⟨value, _member, rfl⟩ := List.mem_map.mp member
      exact Entry.atom_demand _ _ _
  have calls : Stateful.CallsRel current sourceSpace world live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket input, before)].map (functionAssemble (.symbol "unify"))) [(output, after)] world (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.atomType, Atom.expressionType, Atom.undefinedType,
      functionAssemble, input, operands, query, instruction, output] using Stateful.CallsRel.cons callRun Stateful.CallsRel.nil
  have outputRead := HECollectionClosedAppend.closed_read policy after output (number_closed _)
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      ([(output, after)].map (readResult policy)) [(output, after)] := by
    simpa only [List.map_cons, List.map_nil, readResult, outputRead] using HECollectionAppendSource.singleton_priority (output, after)
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy sourceSpace world world world world live scope
    query Atom.undefinedType before before before .active (.symbol "unify") (.symbol "unify") input signature
    [(Entry.Value.argumentPacket input, before)] [(output, after)] [(output, after)]
    (by
      rw [queryRead]
      simp only [query, instruction, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
    (by rw [queryRead]; rfl)
    (by simpa only [queryRead, Entry.Value.erase, environment, id_eq] using selection)
    rfl (HECollectionArithmetic.closed_operator minimal nativePolicy external active primitive subtypes world policy _ _ before
      "unify" signature.functionType (by decide) (by decide) (by decide) rfl rfl)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (by simpa [signature, requests, invocationReturnType, Atom.expressionType, Atom.undefinedType, Entry.Value.erase, input, operands] using
      (arguments (Atom.symbol "unify" :: Atom.undefinedType :: live))) calls priority
  refine ⟨after, ?_⟩
  simpa [queryRead, publishResult, Entry.Value.publish, Entry.Value.withStatus, output, number] using complete

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionUnifySource
