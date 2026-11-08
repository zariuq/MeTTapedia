import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorEdge
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedPublication
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedReadInterface
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadPrimitives
import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeConditionalActivation

/-!
# The demanded constructor through one inferred reader service

The fixture's head and scalar reads come from the existing occurrence-scoped
inference driver. Its source rows finish subtype closure without additions.
Fresh arrow variables are the actual names returned at those read occurrences;
neither operator recasting nor argument delivery changes to a raw lookup.
The imported reader is the explicit historical annotation-override instance.
Successful producer queries do not read the annotated final expression; its
historical late-cast control is separate from current supplement semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorInferred

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Spec.Bindings.ScopeObservation
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open HEDemandedConstructorEdge (space packet inferredLookup)
open HERepeatedFormalSource (signature)

def world : RetainedTypePayloads.ExternalView := fun tag key => .grounded (.custom tag key)
abbrev ops := HEConstructorDeclarationGuard.Controls.sourceOps
abbrev rangeDemand := HEDemandedConstructorEdge.demand

theorem no_subtype_rows : ∀ row ∈ (packet space).rows, ScopedSubtypeReads.possibleRow row = false := by
  have checked : (packet space).rows.all (fun row => !ScopedSubtypeReads.possibleRow row) = true := by decide
  intro row member
  simpa using List.all_eq_true.mp checked row member

theorem closure_finished (seeds : List Atom) (supply : Supply) :
    (ScopedSubtypeReads.completeTypes world (packet space).rows (packet space).subtypeFresh
      (packet space).alpha (packet space).subtypeBudget seeds supply).1 = some seeds :=
  HERangeTypeReadPrimitives.no_edge_closure world (packet space).rows no_subtype_rows
    (packet space).subtypeFresh (packet space).alpha 3 seeds supply

theorem symbol_read (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations (packet space) world (.symbol name) = [type]) :
    (NativeTypeScopedReads.evaluate ops (packet space) world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [(TypeReadSupply.fresh (TypeReadSupply.remember supply [.symbol name]) type).1]) := by
  simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.closeTypes, NativeTypeCallGraph.finishTypes,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList, List.isEmpty_cons,
    Bool.false_eq_true, ite_false, ite_true, closure_finished, Option.map_some, NativeTypeRecursiveDriver.completed]

theorem pair_declared : rawDeclarations (packet space) world (.symbol "OtherDemandPair") =
    [(signature "t").functionType] := by
  have observed : RetainedTypePayloads.observeList world space.atoms = space.atoms :=
    TypeDependencyAdmission.observeList_resourceFree world space.atoms (by decide)
  simp only [rawDeclarations, packet, TypeDependencyAdmission.observedSpace, observed,
    show RetainedTypePayloads.observeList world [] = [] from rfl]
  rfl

theorem pair_head_read (scope : List String) (before : Frame) (expected : Atom) :
    ∃ name,
      inferredLookup scope space before.bindings (.symbol "OtherDemandPair") expected [(signature name).functionType] ∧
      name ∉ invocationTypeScope scope [] (.symbol "OtherDemandPair") expected before.bindings := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol "OtherDemandPair") expected before.bindings, 0⟩
  let prepared := TypeReadSupply.remember supply [Atom.symbol "OtherDemandPair"]
  let original := (signature "t").functionType
  let name := instanceName prepared.used (atomVariables original).eraseDups prepared.next "t"
  have declared : rawDeclarations (packet space) world (.symbol "OtherDemandPair") = [original] := pair_declared
  have shape : (TypeReadSupply.fresh prepared original).1 = (signature name).functionType := by
    simp [TypeReadSupply.fresh, instantiateTypeSignature, original, signature,
      CompletedDelivery.arrowType, renameAtom, renameAtomList, name]
  have observed := symbol_read 7 supply "OtherDemandPair" original declared
  refine ⟨name, ?_, ?_⟩
  · change NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate ops (packet space) world 8 (.infer true (.symbol "OtherDemandPair")) supply).1 = _
    rw [observed]
    change some [(TypeReadSupply.fresh prepared original).1] = some [(signature name).functionType]
    exact congrArg (fun type => some [type]) shape
  · exact instanceName_not_mem prepared.used (atomVariables original).eraseDups prepared.next "t"

theorem number_read (scope : List String) (before : Frame) (value : Int) (expected : Atom) :
    inferredLookup scope space before.bindings (.grounded (.int value)) expected [.symbol "Number"] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.grounded (.int value)) expected before.bindings, 0⟩
  have observed := HERangeTypeReadPrimitives.number_read ops (packet space) world 7 value supply
  exact congrArg (fun result => NativeTypeRecursiveDriver.publishTypes result.1) observed

def environment (minimal : Minimal.Services) : WorldEnvironment Space Unit :=
  { HEDemandedConstructorEdge.environment minimal with
    lookup := inferredLookup
    arguments := kindArgumentService }

set_option maxHeartbeats 1200000 in
theorem historical_producer_head (scope : List String) (before : Frame) (expected : Atom) :
    inferredLookup scope space before.bindings (.symbol "other-demand-result") expected
      [CompletedDelivery.arrowType [] rangeDemand] := by cbv

def historicalReads : HEDemandedReadInterface.Reads where
  lookup := inferredLookup
  pair := pair_head_read
  number := number_read
  producer := HEDemandedConstructorEdge.producer_inferred
  consumerHead := HEDemandedConstructorEdge.consumer_head_inferred
  producerHead := historical_producer_head

theorem selection_of_reads (reads : HEDemandedReadInterface.Reads) (policy : Policy) (live : List Atom) (scope : List String) :
    ∃ name after,
      kindArgumentService.selection space reads.lookup policy live scope HERepeatedFormalSource.call
        (.symbol "OtherDemandPair") rangeDemand Frame.empty (.selected (signature name) [after]) ∧
      after.bindings = Bindings.empty.assign name (.symbol "Number") ∧
      after.bindings.classValues name = [.symbol "Number"] := by
  let names := invocationTypeScope scope live HERepeatedFormalSource.call rangeDemand Frame.empty.bindings
  obtain ⟨name, queried, _⟩ := reads.pair names Frame.empty Atom.undefinedType
  obtain ⟨after, bindings, firstRenew, classes⟩ := HERepeatedFormalSource.first_number_frame policy name
  have first : KindArgumentAdmissionRel space (reads.lookup names space) policy HERepeatedFormalSource.call
      (.grounded (.int 1)) (.var name) 1 Frame.empty [after] [] := by
    apply KindArgumentAdmissionRel.inferred
    · intro kind _ cut
      cases cut
    · simpa [checkedFrames, checkedFailures] using
        (ArgumentChecksRel.cons (expression := HERepeatedFormalSource.call) (position := 1)
          (reads.number names Frame.empty 1 (.var name)) (.cons (TypeCheckRel.accepted firstRenew) .nil) .nil)
  have second : KindArgumentAdmissionRel space (reads.lookup names space) policy HERepeatedFormalSource.call
      (.grounded (.int 2)) (.var name) 2 after [after] [] := by
    apply KindArgumentAdmissionRel.inferred
    · intro kind _ cut
      cases cut
    · simpa [checkedFrames, checkedFailures] using
        (ArgumentChecksRel.cons (expression := HERepeatedFormalSource.call) (position := 2)
          (reads.number names after 2 (.var name))
          (.cons (TypeCheckRel.accepted (HEAssignedRangeReturn.number_class_renewal policy after name classes)) .nil) .nil)
  have same := HEContextualArithmeticSource.same_symbol_match "DemandRange" after.bindings (by decide) (by decide)
  refine ⟨name, after, ⟨[(signature name).functionType], queried, .selected (errors := []) ?_ (by simp)⟩,
    bindings, classes⟩
  simpa [names, signature, HERepeatedFormalSource.call, rangeDemand, HEDemandedConstructorEdge.demand, checkedFrames, checkedFailures] using
    (AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := HERepeatedFormalSource.call) (expected := rangeDemand) (selected := signature name)
      (before := Frame.empty) (operator := .symbol "OtherDemandPair")
      (arguments := [.grounded (.int 1), .grounded (.int 2)]) rfl
      (.cons (AdmissionFramesRel.single first) (.cons (AdmissionFramesRel.single second) .nil))
      (.cons (TypeCheckRel.accepted (.unchanged (after.preserved_type_match policy same))) .nil))

theorem selection (policy : Policy) (live : List Atom) (scope : List String) :
    ∃ name after,
      kindArgumentService.selection space inferredLookup policy live scope HERepeatedFormalSource.call
        (.symbol "OtherDemandPair") rangeDemand Frame.empty (.selected (signature name) [after]) ∧
      after.bindings = Bindings.empty.assign name (.symbol "Number") ∧
      after.bindings.classValues name = [.symbol "Number"] :=
  selection_of_reads historicalReads policy live scope

theorem operator_source_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (policy : Policy) (live : List Atom) (scope : List String)
    (before : Frame) (left : String)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number")) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope (.symbol "OtherDemandPair")
        (signature left).functionType before [(.symbol "OtherDemandPair", after)] () (policy := policy) ∧
      after.bindings.classValues left = [.symbol "Number"] := by
  obtain ⟨right, queried, fresh⟩ := reads.pair
    (invocationTypeScope scope live (.symbol "OtherDemandPair") (signature left).functionType before.bindings)
    before (signature left).functionType
  have bindingFresh : right ∉ specBindingVars before.bindings := by
    intro present
    exact fresh (by simp [invocationTypeScope, present])
  have sourceMatch := HERepeatedFormalSource.arrow_source_match before left right isolated assigned bindingFresh
  have model := HEFreshRangeAlias.alias_model before left right bindingFresh
  have policyMatch : policy.matching.Rel (signature left).functionType (signature right).functionType before.bindings
      (before.bindings.addEquality left right) := by
    cases policy.matching with
    | raw => exact sourceMatch
    | finite => exact ⟨sourceMatch, model⟩
  obtain ⟨after, bindings, evaluated⟩ := HERangeConditionalActivation.operator_cast (HEDemandedReadInterface.environment reads minimal) policy
    space () live scope before "OtherDemandPair" (signature left).functionType (signature right).functionType
    (before.bindings.addEquality left right) (by decide)
    (by simp [signature, CompletedDelivery.arrowType, Atom.atomType])
    (by simp [signature, CompletedDelivery.arrowType, Atom.symbolType]) queried policyMatch model
  refine ⟨after, evaluated, ?_⟩
  rw [bindings]
  exact HEFreshRangeAlias.alias_class_singleton before.bindings left right (.symbol "Number") isolated assigned bindingFresh

theorem operator_source (minimal : Minimal.Services) (policy : Policy) (live : List Atom) (scope : List String)
    (before : Frame) (left : String)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number")) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope (.symbol "OtherDemandPair")
        (signature left).functionType before [(.symbol "OtherDemandPair", after)] () (policy := policy) ∧
      after.bindings.classValues left = [.symbol "Number"] :=
  operator_source_of_reads historicalReads minimal policy live scope before left isolated assigned

theorem number_at_private_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (policy : Policy) (live : List Atom) (scope : List String)
    (before : Frame) (name : String) (value : Int)
    (classes : before.bindings.classValues name = [.symbol "Number"]) :
    Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope (.grounded (.int value)) (.var name) before
      [(.grounded (.int value), before)] () (policy := policy) := by
  have queried := reads.number
    (invocationTypeScope scope live (.grounded (.int value)) (.var name) before.bindings) before value (.var name)
  have read : before.read policy (.grounded (.int value)) = .grounded (.int value) := by
    simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.grounded (.int value), before.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.groundedType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.grounded (.int value)
    · simp [Atom.atomType, Atom.groundedType, Atom.variableType]
    · exact Or.inr (Or.inl ⟨.int value, by simp [Entry.Value.erase]⟩)
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, Entry.Value.erase, id_eq] using
      (TypeCastBatchRel.success (space := space) (earlierTypes := []) (laterTypes := []) queried rfl (by simp)
        (before.preserved_type_match policy (HEAssignedRangeReturn.number_class_match before.bindings name classes)))
  · rw [read]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase], .same before, by simp [Entry.Value.erase]⟩ .nil

theorem number_at_private (minimal : Minimal.Services) (policy : Policy) (live : List Atom) (scope : List String)
    (before : Frame) (name : String) (value : Int)
    (classes : before.bindings.classValues name = [.symbol "Number"]) :
    Stateful.AtomRel (environment minimal) space () live scope (.grounded (.int value)) (.var name) before
      [(.grounded (.int value), before)] () (policy := policy) :=
  number_at_private_of_reads historicalReads minimal policy live scope before name value classes

theorem arguments_source_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (policy : Policy) (scope : List String)
    (before : Frame) (name : String) (values : List Int) (live : List Atom)
    (classes : before.bindings.classValues name = [.symbol "Number"]) :
    Stateful.ArgumentsRel (HEDemandedReadInterface.environment reads minimal) space () live scope
      (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name)) before
      [(Entry.Value.argumentPacket (values.map fun value => Entry.Value.grounded (.int value)), before)] ()
      (policy := policy) := by
  induction values generalizing live with
  | nil => exact .nil
  | cons value values ih =>
      have child := number_at_private_of_reads reads minimal policy
        (argumentScope (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name)) ++ live)
        scope before name value classes
      have rest : Stateful.ArgumentBranchesRel (HEDemandedReadInterface.environment reads minimal) space () live scope
          (.grounded (.int value)) (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name))
          [] [] () (policy := policy) := .nil
      have branches := Stateful.ArgumentBranchesRel.continuing
        (head := (Entry.Value.grounded (.int value), before)) (by simp [ArgumentStopped])
        (ih ((Entry.Value.grounded (.int value)).erase :: live)) rest
      apply Stateful.ArgumentsRel.cons child
      simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using branches

theorem arguments_source (minimal : Minimal.Services) (policy : Policy) (scope : List String)
    (before : Frame) (name : String) (values : List Int) (live : List Atom)
    (classes : before.bindings.classValues name = [.symbol "Number"]) :
    Stateful.ArgumentsRel (environment minimal) space () live scope
      (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name)) before
      [(Entry.Value.argumentPacket (values.map fun value => Entry.Value.grounded (.int value)), before)] ()
      (policy := policy) :=
  arguments_source_of_reads historicalReads minimal policy scope before name values live classes

/-- The actual fresh inferred head reads, kind-qualified argument checks,
operator recast and both scalar deliveries now use one environment. -/
theorem constructor_published_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (policy : Policy)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope HERepeatedFormalSource.contextualCall rangeDemand Frame.empty
        [HESelectedConstructorSource.published policy HERepeatedFormalSource.call "OtherDemandPair"
          [.grounded (.int 1), .grounded (.int 2)] after] () (policy := policy) := by
  obtain ⟨name, selected, selectionRun, bindings, _⟩ := selection_of_reads reads policy live scope
  have isolated : name ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    simp [Bindings.assign, Bindings.empty, Bindings.eqVarsInOrder]
  have assigned : selected.bindings.lookup name = some (.symbol "Number") := by
    rw [bindings]
    simp [Bindings.assign, Bindings.empty, Bindings.lookup, Bindings.isBound]
  let headLive := (signature name).functionType ::
    [.grounded (.int 1), .grounded (.int 2)] ++ invocationReturnType (signature name) :: live
  let headScope := scope ++ expectedApplicationScope HERepeatedFormalSource.call rangeDemand
  obtain ⟨after, operatorRun, classes⟩ := operator_source_of_reads reads minimal policy headLive headScope selected name isolated assigned
  have delivered := arguments_source_of_reads reads minimal policy scope after name [1, 2]
    (.symbol "OtherDemandPair" :: invocationReturnType (signature name) :: live) classes
  have source : Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope HERepeatedFormalSource.contextualCall
      rangeDemand Frame.empty
      [HESelectedConstructorSource.published policy HERepeatedFormalSource.call "OtherDemandPair"
        [.grounded (.int 1), .grounded (.int 2)] after] () (policy := policy) := by
    have erased : (Frame.empty.read policy HERepeatedFormalSource.contextualCall).erase = HERepeatedFormalSource.call := by
      simp [Frame.read_empty, HERepeatedFormalSource.contextualCall, HERepeatedFormalSource.call, Entry.Value.erase]
    rw [← erased]
    apply HESelectedConstructorSource.source_from_parts (HEDemandedReadInterface.environment reads minimal) policy space () () () live scope
      HERepeatedFormalSource.contextualCall rangeDemand Frame.empty selected after after .active
      (.symbol "OtherDemandPair") "OtherDemandPair"
      [.grounded (.int 1), .grounded (.int 2)] [.grounded (.int 1), .grounded (.int 2)] (signature name)
    · simp only [Frame.read_empty, HERepeatedFormalSource.contextualCall, Entry.Value.status, Entry.Value.erase,
        List.map_cons, List.map_nil]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simp [rangeDemand, HEDemandedConstructorEdge.demand, Atom.atomType, Atom.expressionType, Atom.variableType])
        (Or.inr rfl)
    · rw [Frame.read_empty]; rfl
    · simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, Frame.read_empty,
        HERepeatedFormalSource.contextualCall, HERepeatedFormalSource.call, Entry.Value.erase, List.map_cons, List.map_nil, id_eq] using selectionRun
    · rfl
    · simpa only [headLive, headScope, HERepeatedFormalSource.contextualCall, HERepeatedFormalSource.call,
        Entry.Value.erase, List.map_cons, List.map_nil] using operatorRun
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact delivered
    · decide
    · simp [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, NonGroundedCallRel,
        Minimal.HostCall, Completed.Controls.typedDispatch, HESelectedConstructorSource.assembled, Entry.Value.erase,
        Minimal.embeddedInstruction]
    · change HEConstructorAdmission.headAbsent space "OtherDemandPair" = true
      decide
  exact ⟨after, source⟩

theorem constructor_published (minimal : Minimal.Services) (policy : Policy)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope HERepeatedFormalSource.contextualCall rangeDemand Frame.empty
        [HESelectedConstructorSource.published policy HERepeatedFormalSource.call "OtherDemandPair"
          [.grounded (.int 1), .grounded (.int 2)] after] () (policy := policy) :=
  constructor_published_of_reads historicalReads minimal policy live scope

/-- Both publication profiles earn the constructor's completion mark from
its unchanged successful result, not from a global result-marking premise. -/
theorem constructor_source_with_marking_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope HERepeatedFormalSource.contextualCall rangeDemand Frame.empty
        [(HEDemandedConstructorEdge.heldResult, after)] () (policy := HEDemandedPublication.policy marking) := by
  obtain ⟨after, ran⟩ := constructor_published_of_reads reads minimal (HEDemandedPublication.policy marking) live scope
  have read : after.read (HEDemandedPublication.policy marking)
      (HESelectedConstructorSource.assembled "OtherDemandPair" [.grounded (.int 1), .grounded (.int 2)]) =
      HERepeatedFormalSource.contextualCall := by
    simp [HESelectedConstructorSource.assembled, Frame.read, Entry.Value.substitute,
      HERepeatedFormalSource.contextualCall, HEDemandedPublication.policy, Policy.ready, Entry.Value.rebuildStatus]
  have publication := HEDemandedPublication.unchanged marking supported HERepeatedFormalSource.call
    HERepeatedFormalSource.contextualCall after.source
    (by simp [HERepeatedFormalSource.call, HERepeatedFormalSource.contextualCall, Entry.Value.erase])
    (by simp [HERepeatedFormalSource.contextualCall, Entry.Value.erase, isErrorAtom])
  have pair : HESelectedConstructorSource.published (HEDemandedPublication.policy marking)
      HERepeatedFormalSource.call "OtherDemandPair" [.grounded (.int 1), .grounded (.int 2)] after =
      (HEDemandedConstructorEdge.heldResult, after) := by
    change (Entry.Value.publish marking HERepeatedFormalSource.call after.source
      (after.read (HEDemandedPublication.policy marking)
        (HESelectedConstructorSource.assembled "OtherDemandPair" [.grounded (.int 1), .grounded (.int 2)])), after) = _
    rw [read, publication]
    rfl
  exact ⟨after, by simpa only [pair] using ran⟩

theorem constructor_source_with_marking (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope HERepeatedFormalSource.contextualCall rangeDemand Frame.empty
        [(HEDemandedConstructorEdge.heldResult, after)] () (policy := HEDemandedPublication.policy marking) :=
  constructor_source_with_marking_of_reads historicalReads minimal marking supported live scope

theorem constructor_source (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope HERepeatedFormalSource.contextualCall rangeDemand Frame.empty
        [(HEDemandedConstructorEdge.heldResult, after)] () (policy := Policy.ready) :=
  constructor_source_with_marking minimal .successes (Or.inl rfl) live scope

theorem consumer_selection_of_reads (reads : HEDemandedReadInterface.Reads) (policy : Policy) (live : List Atom) (scope : List String) :
    kindArgumentService.selection space reads.lookup policy live scope HEDemandedConstructorEdge.consumer
      (.symbol "use-demand") rangeDemand Frame.empty
      (.selected HEDemandedConstructorEdge.consumerSignature [Frame.empty]) := by
  let names := invocationTypeScope scope live HEDemandedConstructorEdge.consumer rangeDemand Frame.empty.bindings
  have same := HEContextualArithmeticSource.same_symbol_match "DemandRange" Frame.empty.bindings (by decide) (by decide)
  have accepted : TypeCheckRel policy rangeDemand Frame.empty rangeDemand (.inr Frame.empty) :=
    .accepted (.unchanged (Frame.empty.preserved_type_match policy same))
  have argument : KindArgumentAdmissionRel space (reads.lookup names space) policy HEDemandedConstructorEdge.consumer
      HEDemandedConstructorEdge.producer rangeDemand 1 Frame.empty [Frame.empty] [] := by
    apply KindArgumentAdmissionRel.inferred
    · intro kind _ cut
      have admitted := HEArgumentMetatypeRole.native_cut cut
      have refused : TypeScopeMatcher.metaCheckAtom rangeDemand kind = none := rfl
      rw [refused] at admitted
      cases admitted
    · simpa [checkedFrames, checkedFailures] using
        (ArgumentChecksRel.cons (expression := HEDemandedConstructorEdge.consumer) (position := 1)
          (reads.producer names Frame.empty rangeDemand) (.cons accepted .nil) .nil)
  refine ⟨[HEDemandedConstructorEdge.consumerSignature.functionType],
    reads.consumerHead names Frame.empty _, .selected (errors := []) ?_ (by simp)⟩
  simpa [names, HEDemandedConstructorEdge.consumer, HEDemandedConstructorEdge.consumerSignature,
    rangeDemand, HEDemandedConstructorEdge.demand, checkedFrames, checkedFailures] using
    (AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := HEDemandedConstructorEdge.consumer) (expected := rangeDemand)
      (selected := HEDemandedConstructorEdge.consumerSignature) (before := Frame.empty)
      (operator := .symbol "use-demand") (arguments := [HEDemandedConstructorEdge.producer]) rfl
      (.cons (AdmissionFramesRel.single argument) .nil) (.cons accepted .nil))

theorem consumer_selection (policy : Policy) (live : List Atom) (scope : List String) :
    kindArgumentService.selection space inferredLookup policy live scope HEDemandedConstructorEdge.consumer
      (.symbol "use-demand") rangeDemand Frame.empty
      (.selected HEDemandedConstructorEdge.consumerSignature [Frame.empty]) :=
  consumer_selection_of_reads historicalReads policy live scope

theorem demanded_reentry_with_marking_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy) (frame : Frame) (live : List Atom) (scope : List String) :
    Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope HEDemandedConstructorEdge.heldResult rangeDemand frame
      [(HEDemandedConstructorEdge.heldResult, frame)] () (policy := (HEDemandedPublication.policy marking)) := by
  have entry : Entry.Rel (HEDemandedPublication.policy marking).reentry
      (frame.read (HEDemandedPublication.policy marking) HEDemandedConstructorEdge.heldResult).status
      (frame.read (HEDemandedPublication.policy marking) HEDemandedConstructorEdge.heldResult).erase rangeDemand .deliver := by
    simp only [HEDemandedPublication.read, HEDemandedConstructorEdge.held_read]
    simp only [HEDemandedConstructorEdge.heldResult, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil, HEDemandedPublication.policy, Policy.ready]
    apply Entry.Rel.held
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simp [rangeDemand, HEDemandedConstructorEdge.demand, Atom.atomType, Atom.expressionType, Atom.variableType]
    · rfl
    · rfl
  have delivered := Stateful.AtomRel.delivered (environment := HEDemandedReadInterface.environment reads minimal) (label := space)
    (world0 := ()) (live := live) (scope := scope) (value := HEDemandedConstructorEdge.heldResult) (expected := rangeDemand)
    (frame := frame) (policy := (HEDemandedPublication.policy marking)) entry
  simpa only [HEDemandedPublication.read, HEDemandedConstructorEdge.held_read] using delivered

theorem demanded_reentry_with_marking (minimal : Minimal.Services) (marking : Entry.MarkPolicy) (frame : Frame) (live : List Atom) (scope : List String) :
    Stateful.AtomRel (environment minimal) space () live scope HEDemandedConstructorEdge.heldResult rangeDemand frame
      [(HEDemandedConstructorEdge.heldResult, frame)] () (policy := (HEDemandedPublication.policy marking)) :=
  demanded_reentry_with_marking_of_reads historicalReads minimal marking frame live scope

theorem demanded_reentry (minimal : Minimal.Services) (frame : Frame) (live : List Atom) (scope : List String) :
    Stateful.AtomRel (environment minimal) space () live scope HEDemandedConstructorEdge.heldResult rangeDemand frame
      [(HEDemandedConstructorEdge.heldResult, frame)] () (policy := Policy.ready) :=
  demanded_reentry_with_marking minimal .successes frame live scope

/-- One historical inferred service supplies source admission and constructor
execution. Reuse keeps the earned result; its old final-syntax override cast
rejects at the same frame. This is not the current supplement reader. -/
theorem uniform_producer_edge (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    kindArgumentService.selection space inferredLookup Policy.ready live scope HEDemandedConstructorEdge.consumer
      (.symbol "use-demand") rangeDemand Frame.empty
      (.selected HEDemandedConstructorEdge.consumerSignature [Frame.empty]) ∧
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope HERepeatedFormalSource.contextualCall rangeDemand Frame.empty
        [(HEDemandedConstructorEdge.heldResult, after)] () (policy := Policy.ready) ∧
      Stateful.AtomRel (environment minimal) space () live scope HEDemandedConstructorEdge.heldResult rangeDemand after
        [(HEDemandedConstructorEdge.heldResult, after)] () (policy := Policy.ready) ∧
      NativeCompletedReturnRel space (inferredLookup [] space) Policy.ready HEDemandedConstructorEdge.heldResult rangeDemand after
        [(Entry.Value.ofAtom HEDemandedConstructorEdge.lateError, after)] := by
  obtain ⟨after, produced⟩ := constructor_source minimal live scope
  exact ⟨consumer_selection Policy.ready live scope, after, produced, demanded_reentry minimal after live scope,
    HEDemandedConstructorEdge.fresh_final_cast_rejects after⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorInferred
