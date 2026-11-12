import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionHeldTypeRead

/-!
# The authored collection probe, from typed ingress through its consumer

The middle let argument executes the authored collapse and reaches a new
snapshot world. Its pending template protects the caller's three names.
The assembled let call then binds that same collected tuple and runs its
numeric fold. Every source equation and child execution is derived locally.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionNumericFold (number numbers number_closed numbers_closed)
open HECollectionLetCapture (template)
open Mettapedia.Machines.OrderedProtocol.Completion

def squareValues (lower : Int) (count : Nat) : List Int :=
  (List.range count).map fun (index : Nat) => (lower + index) * (lower + index)

theorem numbers_squares (lower : Int) (count : Nat) :
    numbers (squareValues lower count) = HECollectionSquareRange.squares lower count := by
  simp [numbers, number, squareValues, HECollectionSquareRange.squares, List.map_map]

theorem numeric_tuple_not_stopped (mark : Entry.Status) (values : List Int) :
    ¬IsEmptyOrErrorRel (Entry.Value.expression mark (numbers values)).erase := by
  cases values <;> simp [numbers, number, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

def query (lower upper init : Int) (listName left right : String) : Entry.Value :=
  .expression .active [.symbol "let", .var listName, HECollectionCollapseFrontier.call lower upper,
    template listName left right init]

def requests (lower upper init : Int) (listName left right : String) : List ArgumentRequest :=
  [(.var listName, Atom.atomType), (HECollectionCollapseFrontier.call lower upper, Atom.undefinedType),
    (template listName left right init, Atom.atomType)]

def signature : SelectedTypePolicy := ⟨CollectionStdlibSource.letType,
  [Atom.atomType, Atom.undefinedType, Atom.atomType], Atom.undefinedType, rfl⟩

theorem authored_probe_erasure (upper : Int) : (query 0 upper 0 "l" "a" "b").erase = CollectionStdlibSource.probe upper := by
  simp [query, template, HECollectionCollapseFrontier.call, HECollectionSquareRange.call,
    HERangeUntypedEntry.rangeCall, HECollectionFoldSourceLoop.operation, number, Entry.Value.erase,
    CollectionStdlibSource.probe, CollectionStdlibSource.collection, CollectionStdlibSource.app]

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes

theorem collapse_type_query (scope : List String) (before : Frame) (lower upper : Int) :
    (current).lookup scope sourceSpace before.bindings (HECollectionCollapseFrontier.call lower upper).erase Atom.undefinedType [Atom.atomType] := by
  let subject := (HECollectionCollapseFrontier.call lower upper).erase
  let supply : TypeReadSupply.Supply := ⟨invocationTypeScope scope [] subject Atom.undefinedType before.bindings, 0⟩
  refine ⟨rfl, supply, 2, fun _ member => member, ?_⟩
  change (NativeTypeScopedReads.evaluate
    { HERangeTypeReadApplications.ops external active primitive subtypes with
      annotationPolicy := .supplement (fun left right => RetainedTypePayloads.observe external left == RetainedTypePayloads.observe external right) }
    HECollectionTypeReadPrimitives.source external 2 (.infer true subject) supply).1 = _
  rw [HECollectionTypeReadApplications.current_policy_agrees]
  simpa only [subject, HECollectionCollapseFrontier.call, Entry.Value.erase, List.map_cons, List.map_nil, Atom.atomType] using
    HECollectionHeldTypeRead.unary external active primitive subtypes "collapse" "Atom" 0 supply
      (HECollectionSquareRange.call lower upper).erase
      (by simp [HECollectionSquareRange.call, HERangeUntypedEntry.rangeCall, Entry.Value.erase, atomVariables, atomListVariables])
      (by rw [HECollectionTypeReadPrimitives.declarations_eq]; rfl) rfl

theorem selection (scope : List String) (live : List Atom) (policy : Policy) (before : Frame)
    (lower upper init : Int) (listName left right : String) :
    (current).arguments.selection sourceSpace (current).lookup policy live scope (query lower upper init listName left right).erase
      (.symbol "let") Atom.undefinedType before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (query lower upper init listName left right).erase Atom.undefinedType before.bindings
  have middle : KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (query lower upper init listName left right).erase (HECollectionCollapseFrontier.call lower upper).erase Atom.undefinedType 2 before [before] [] := by
    apply HEArgumentMetatypeRole.singleton_inferred
    · intro kind _ cut
      have success := HEArgumentMetatypeRole.native_cut cut
      have absent : TypeScopeMatcher.metaCheckAtom Atom.undefinedType kind = none := rfl
      rw [absent] at success
      cases success
    · exact collapse_type_query minimal nativePolicy external active primitive subtypes names before lower upper
    · exact .unchanged (before.preserved_type_match policy (.undefinedLeft _ _))
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (query lower upper init listName left right).erase 1
      ((requests lower upper init listName left right).map (fun request => request.1.erase))
      signature.argumentTypes [before] [before] [] :=
    .cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _))
      (.cons (AdmissionFramesRel.single middle)
        (.cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _)) .nil))
  refine ⟨[signature.functionType], HECollectionInferredQueries.closed_head ops external names before "let" _ _ rfl rfl,
    .selected (errors := []) ?_ (by simp)⟩
  simpa [signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := (query lower upper init listName left right).erase)
      (expected := Atom.undefinedType) (selected := signature) (before := before) (operator := .symbol "let")
      (arguments := (requests lower upper init listName left right).map (fun request => request.1.erase))
      (by simp [query, requests, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedLeft _ _)))) .nil)

theorem query_read (policy : Policy) (before : Frame) (lower upper init : Int) (listName left right : String)
    (listFixed : before.read policy (.var listName) = .var listName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) :
    before.read policy (query lower upper init listName left right) = query lower upper init listName left right := by
  apply Entry.Value.substitute_of_fixed_variables
  intro name occurs
  simp only [query, template, HECollectionFoldSourceLoop.operation, Entry.Value.erase,
    List.map_cons, List.map_nil, TypeSubst.typeVars, TypeSubst.typeVarsList,
    HECollectionCollapseFrontier.call_closed, number_closed, List.nil_append, List.append_nil] at occurs
  have first := HECollectionFoldReadback.resolve_of_fixed policy before listName listFixed
  have second := HECollectionFoldReadback.resolve_of_fixed policy before left leftFixed
  have third := HECollectionFoldReadback.resolve_of_fixed policy before right rightFixed
  aesop

theorem arguments (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper init : Int) (listName left right : String)
    (listFresh : listName ∉ specBindingVars before.bindings)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings) :
    ∃ afterWorld after mark,
      Stateful.ArgumentsRel current sourceSpace world live scope (requests lower upper init listName left right) before
        [(Entry.Value.argumentPacket [.var listName, .expression mark (numbers (squareValues lower (upper - lower).toNat)),
          template listName left right init], after)] afterWorld (policy := policy) ∧
      after.read policy (.var listName) = .var listName ∧
      after.read policy (.var left) = .var left ∧ after.read policy (.var right) = .var right := by
  let pending := template listName left right init
  let collapseLive := argumentScope [(pending, Atom.atomType)] ++ ((.var listName : Atom) :: live)
  obtain ⟨afterWorld, after, mark, collapseRun, preserved⟩ := HECollectionCollapseSource.source_scoped
    minimal nativePolicy external active primitive subtypes world policy before collapseLive scope lower upper
  have freshAfter (name : String) (occurs : name ∈ TypeSubst.typeVars pending.erase)
      (oldFresh : name ∉ specBindingVars before.bindings) : name ∉ specBindingVars after.bindings := by
    apply preserved name ⟨pending.erase, ?_, (atomOccurs_iff_mem_typeVars pending.erase name).mpr occurs⟩ oldFresh
    simp [collapseLive, argumentScope]
  have freshList := freshAfter listName (by simp [pending, template, HECollectionFoldSourceLoop.operation,
    Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]) listFresh
  have freshLeft := freshAfter left (by simp [pending, template, HECollectionFoldSourceLoop.operation,
    Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]) leftFresh
  have freshRight := freshAfter right (by simp [pending, template, HECollectionFoldSourceLoop.operation,
    Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]) rightFresh
  have fixed (frame : Frame) (name : String) (fresh : name ∉ specBindingVars frame.bindings) :
      frame.read policy (.var name) = .var name := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh frame name fresh
  have templateFixed : after.read policy pending = pending := HECollectionLetCapture.template_read policy after _ _ _ _ init
    (fixed after listName freshList) (fixed after left freshLeft) (fixed after right freshRight)
  let tuple := Entry.Value.expression mark (numbers (squareValues lower (upper - lower).toNat))
  have finalArgument : Stateful.ArgumentsRel current sourceSpace afterWorld
      (tuple.erase :: (.var listName : Atom) :: live) scope [(pending, Atom.atomType)] after
      [(Entry.Value.argumentPacket [pending], after)] afterWorld (policy := policy) := by
    apply DeliveredArgumentPackets.source current policy sourceSpace afterWorld scope after [(pending, Atom.atomType)]
    · intro request member
      have same : request = (pending, Atom.atomType) := List.mem_singleton.mp member
      subst request
      exact templateFixed
    · intro request member
      have same : request = (pending, Atom.atomType) := List.mem_singleton.mp member
      subst request
      exact Entry.atom_demand _ _ _
  have middleArguments : Stateful.ArgumentsRel current sourceSpace world ((.var listName : Atom) :: live) scope
      [(HECollectionCollapseFrontier.call lower upper, Atom.undefinedType), (pending, Atom.atomType)] before
      [(Entry.Value.argumentPacket [tuple, pending], after)] afterWorld (policy := policy) := by
    apply Stateful.ArgumentsRel.cons
    · simpa only [collapseLive, tuple, numbers_squares] using collapseRun
    · simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet, tuple, numbers_squares] using
        (Stateful.ArgumentBranchesRel.continuing (original := HECollectionCollapseFrontier.call lower upper) (head := (tuple, after))
          (fun stopped => numeric_tuple_not_stopped mark _ stopped.1) finalArgument .nil)
  have firstArgument : Stateful.AtomRel current sourceSpace world
      (argumentScope [(HECollectionCollapseFrontier.call lower upper, Atom.undefinedType), (pending, Atom.atomType)] ++ live)
      scope (.var listName) Atom.atomType before [(.var listName, before)] world (policy := policy) := by
    simpa only [fixed before listName listFresh] using
      (Stateful.AtomRel.delivered (environment := current) (label := sourceSpace) (world0 := world)
        (value := .var listName) (frame := before) (policy := policy)
        (by rw [fixed before listName listFresh]; exact Entry.atom_demand _ _ _))
  refine ⟨afterWorld, after, mark, ?_, fixed after listName freshList, fixed after left freshLeft, fixed after right freshRight⟩
  apply Stateful.ArgumentsRel.cons firstArgument
  have continuation : Stateful.ArgumentsRel current sourceSpace world
      ((Entry.Value.var listName).erase :: live) scope
      [(HECollectionCollapseFrontier.call lower upper, Atom.undefinedType), (pending, Atom.atomType)] before
      [(Entry.Value.argumentPacket [tuple, pending], after)] afterWorld (policy := policy) := by
    simpa only [Entry.Value.erase] using middleArguments
  have branches := Stateful.ArgumentBranchesRel.continuing (original := .var listName)
    (head := (.var listName, before)) (heads := []) (rest := [])
    (by simp [ArgumentStopped]) continuation Stateful.ArgumentBranchesRel.nil
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet, pending, tuple] using branches

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper init : Int) (listName left right : String)
    (listLeft : listName ≠ left) (listRight : listName ≠ right) (different : left ≠ right)
    (listFresh : listName ∉ specBindingVars before.bindings)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings) :
    ∃ afterWorld after, Stateful.AtomRel current sourceSpace world live scope (query lower upper init listName left right)
      Atom.undefinedType before [(number ((squareValues lower (upper - lower).toNat).foldl (· + ·) init), after)] afterWorld (policy := policy) := by
  let argumentLive := Atom.symbol "let" :: Atom.undefinedType :: live
  obtain ⟨afterWorld, collected, mark, argumentsRun, listFixed, leftFixed, rightFixed⟩ :=
    arguments minimal nativePolicy external active primitive subtypes world policy before argumentLive scope lower upper init listName left right listFresh leftFresh rightFresh
  obtain ⟨after, called⟩ := HECollectionLetSource.called minimal nativePolicy external active primitive subtypes afterWorld policy collected live scope
    (squareValues lower (upper - lower).toNat) init listName left right mark listLeft listRight different listFixed leftFixed rightFixed
  let output := number ((squareValues lower (upper - lower).toNat).foldl (· + ·) init)
  let values := [Entry.Value.var listName, HECollectionCollapseFrontier.call lower upper, template listName left right init]
  let packet := Entry.Value.argumentPacket [Entry.Value.var listName,
    .expression mark (numbers (squareValues lower (upper - lower).toNat)), template listName left right init]
  have originalFixed (name : String) (fresh : name ∉ specBindingVars before.bindings) :
      before.read policy (.var name) = .var name := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before name fresh
  have originalRead := query_read policy before lower upper init listName left right
    (originalFixed listName listFresh) (originalFixed left leftFresh) (originalFixed right rightFresh)
  have calls : Stateful.CallsRel current sourceSpace afterWorld live scope (invocationReturnType signature)
      ([(packet, collected)].map (functionAssemble (.symbol "let"))) [(output, after)] afterWorld (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.atomType, Atom.expressionType, Atom.undefinedType,
      functionAssemble, packet, HECollectionLetCapture.call, output] using Stateful.CallsRel.cons called Stateful.CallsRel.nil
  have outputRead := HECollectionClosedAppend.closed_read policy after output (number_closed _)
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      ([(output, after)].map (readResult policy)) [(output, after)] := by
    simpa only [List.map_cons, List.map_nil, readResult, outputRead] using HECollectionAppendSource.singleton_priority (output, after)
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy sourceSpace world world afterWorld afterWorld live scope
    (query lower upper init listName left right) Atom.undefinedType before before before .active (.symbol "let") (.symbol "let") values signature
    [(packet, collected)] [(output, after)] [(output, after)]
    (by
      rw [originalRead]
      simp only [query, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
    (by rw [originalRead]; rfl)
    (by simpa only [originalRead, Entry.Value.erase, environment, id_eq] using
      selection minimal nativePolicy external active primitive subtypes scope live policy before lower upper init listName left right)
    rfl (HECollectionArithmetic.closed_operator minimal nativePolicy external active primitive subtypes world policy _ _ before
      "let" signature.functionType (by decide) (by decide) (by decide) rfl rfl)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (by simpa [signature, requests, invocationReturnType, Atom.expressionType, Atom.undefinedType, Entry.Value.erase, values, packet, argumentLive] using argumentsRun)
    calls priority
  refine ⟨afterWorld, after, ?_⟩
  simpa [originalRead, publishResult, Entry.Value.publish, Entry.Value.withStatus, output, number] using complete

theorem retained_run (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper init : Int) (listName left right : String)
    (listLeft : listName ≠ left) (listRight : listName ≠ right) (different : left ≠ right)
    (listFresh : listName ∉ specBindingVars before.bindings)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ afterWorld after, RecursiveMachine.Contextual.WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.atom live scope (query lower upper init listName left right) Atom.undefinedType before), stack, emitted⟩
      ⟨afterWorld, sourceSpace, .returning [(number ((squareValues lower (upper - lower).toNat).foldl (· + ·) init), after)], stack, emitted⟩
      (admission := (current).arguments) := by
  obtain ⟨afterWorld, after, executed⟩ := source minimal nativePolicy external active primitive subtypes world policy before live scope
    lower upper init listName left right listLeft listRight different listFresh leftFresh rightFresh
  exact ⟨afterWorld, after, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.atom_complete executed stack) emitted⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionProbeSource
