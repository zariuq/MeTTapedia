import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorInferred
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeEquationFrontiers

/-!
# The authored nullary producer's complete source frontier

Every physical equation row of the demanded-constructor fixture is visited.
The producer's ground rule needs no new term-variable names, while the
consumer's differently headed rule remains a miss under every fresh variant.
The body then runs through the already checked shared-formal constructor.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge
open HEDemandedConstructorEdge (space producer heldResult)
open HEDemandedConstructorInferred (environment rangeDemand)

def producerCall : Entry.Value := Entry.Value.ofAtom producer
def work : EquationWork :=
  ⟨3, producer, HERepeatedFormalSource.call, producer, HERepeatedFormalSource.call, Bindings.empty⟩

theorem producer_alpha (live : List Atom) :
    AlphaVariantRel live producer Bindings.empty producer HERepeatedFormalSource.call producer HERepeatedFormalSource.call := by
  refine ⟨id, Function.injective_id,
    .expression (.cons (.symbol "other-demand-result") .nil),
    .expression (.cons (.symbol "OtherDemandPair") (.cons (.grounded (.int 1)) (.cons (.grounded (.int 2)) .nil))), ?_⟩
  intro name occurs
  rcases occurs with left | right
  · have used := atomOccurs_mem_typeVars left
    simp [producer, TypeSubst.typeVars, TypeSubst.typeVarsList] at used
  · have used := atomOccurs_mem_typeVars right
    simp [HERepeatedFormalSource.call, TypeSubst.typeVars, TypeSubst.typeVarsList] at used

theorem producer_frontier (live : List Atom) : EquationFrontierRel space live producer Bindings.empty [work] := by
  have matching : MatchRel equalityGroundedSemantic producer producer Bindings.empty :=
    .expression (.cons (.symSym "other-demand-result" semanticLoopFree_empty)
      (.mk (by simp [constraints, Bindings.empty]) .nil) .nil) semanticLoopFree_empty
  have merged : LogicalMergeRel Bindings.empty Bindings.empty Bindings.empty :=
    ⟨BindingSourceAgreement.refl _, Frame.empty.certified.satisfiable⟩
  have hit : EquationRowResultsRel live producer Bindings.empty 3
      (.expression [.symbol "=", producer, HERepeatedFormalSource.call]) [work] :=
    .hit 3 producer HERepeatedFormalSource.call producer HERepeatedFormalSource.call Bindings.empty Bindings.empty
      (producer_alpha live) matching merged
  have scanned : EquationFrontierRel space live producer Bindings.empty
      ([[], [], [], [work], [], []] : List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [space, Space.ofList, List.zipIdx_cons, List.zipIdx_nil]
    exact .cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
      (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
        (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
          (.cons hit (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
            (.cons (HERangeEquationFrontiers.different_head_miss live Bindings.empty 5
              "other-demand-result" "use-demand" [] [.var "value"] (.var "value") (by decide)) .nil)))))
  simpa using scanned

/-- The wrapper's selected equation actually evaluates the constructor at
the retained DemandRange. Its emitted body is not assumed to have run. -/
theorem producer_call_with_marking_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.CallRel (HEDemandedReadInterface.environment reads minimal) space () live scope producerCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
  obtain ⟨after, bodyRun⟩ := HEDemandedConstructorInferred.constructor_source_with_marking_of_reads reads minimal marking supported live scope
  have unified : Entry.Value.UnifyRel (HEDemandedPublication.policy marking).rebuilding Frame.empty.environment producerCall
      (Entry.Value.ofAtom work.pattern) Frame.empty.environment := .ordinary (.identical rfl)
  have produced : Stateful.BoundaryRel (HEDemandedReadInterface.environment reads minimal) space () (rangeDemand :: live) scope
      (some producerCall.erase) .producer
      (Frame.empty.read (HEDemandedPublication.policy marking) (Entry.Value.ofAtom work.body)) Frame.empty
      [(HERepeatedFormalSource.contextualCall, Frame.empty)] () (policy := (HEDemandedPublication.policy marking)) := by
    simpa [work, Frame.read_empty, Entry.Value.ofAtom, HERepeatedFormalSource.call, HERepeatedFormalSource.contextualCall] using
      (Stateful.BoundaryRel.producerRaw (environment := HEDemandedReadInterface.environment reads minimal)
        (label := space) (world0 := ()) (live := rangeDemand :: live) (scope := scope)
        (caller := some producerCall.erase) (value := HERepeatedFormalSource.contextualCall) (frame := Frame.empty)
        (policy := (HEDemandedPublication.policy marking))
        (by simp [FunctionPending, Minimal.IsFunction, HERepeatedFormalSource.contextualCall, Entry.Value.erase]))
  have returned : Stateful.BoundaryBatchRel (HEDemandedReadInterface.environment reads minimal) space () live scope none
      (.returned producerCall rangeDemand) [(HERepeatedFormalSource.contextualCall, Frame.empty)]
      [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .returned (.evaluate (by simp [HERepeatedFormalSource.contextualCall, Entry.Value.erase, Atom.notReducible])
      (by simp [HERepeatedFormalSource.contextualCall, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) bodyRun)
  refine ⟨after, ?_⟩
  apply Stateful.CallRel.equations (works := [work])
  · simp [producerCall, producer, Entry.Value.erase_ofAtom, IsErrorRel]
  · simp [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, NonGroundedCallRel,
      Minimal.HostCall, Completed.Controls.typedDispatch, producerCall, producer, Entry.Value.erase_ofAtom,
      Minimal.embeddedInstruction]
  · simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, id_eq,
      producerCall, Entry.Value.erase_ofAtom, Frame.empty] using producer_frontier (rangeDemand :: live)
  · simp
  · simpa only [List.append_nil] using
      (Stateful.EquationBodiesRel.cons (output := Frame.empty) (produced := [(HERepeatedFormalSource.contextualCall, Frame.empty)])
        rfl unified produced returned Stateful.EquationBodiesRel.nil)

theorem producer_call_with_marking (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.CallRel (environment minimal) space () live scope producerCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) :=
  producer_call_with_marking_of_reads HEDemandedConstructorInferred.historicalReads minimal marking supported live scope

theorem producer_call (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.CallRel (environment minimal) space () live scope producerCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) :=
  producer_call_with_marking minimal .successes (Or.inl rfl) live scope

def producerSignature : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [] rangeDemand, [], rangeDemand, rfl⟩

theorem producer_head_read (scope : List String) (before : Frame) (expected : Atom) :
    HEDemandedConstructorEdge.inferredLookup scope space before.bindings (.symbol "other-demand-result") expected
      [producerSignature.functionType] := by
  let supply : TypeReadSupply.Supply :=
    ⟨invocationTypeScope scope [] (.symbol "other-demand-result") expected before.bindings, 0⟩
  have observedRows : RetainedTypePayloads.observeList HEDemandedConstructorInferred.world space.atoms = space.atoms :=
    TypeDependencyAdmission.observeList_resourceFree _ space.atoms (by decide)
  have declared : NativeTypeSourcePorts.rawDeclarations (HEDemandedConstructorEdge.packet space)
      HEDemandedConstructorInferred.world (.symbol "other-demand-result") = [producerSignature.functionType] := by
    simp only [NativeTypeSourcePorts.rawDeclarations, HEDemandedConstructorEdge.packet,
      TypeDependencyAdmission.observedSpace, observedRows,
      show RetainedTypePayloads.observeList HEDemandedConstructorInferred.world [] = [] from rfl]
    rfl
  have queried := HEDemandedConstructorInferred.symbol_read 7 supply "other-demand-result" producerSignature.functionType declared
  have fresh : (TypeReadSupply.fresh (TypeReadSupply.remember supply [Atom.symbol "other-demand-result"])
      producerSignature.functionType).1 = producerSignature.functionType := by
    simp [TypeReadSupply.fresh, instantiateTypeSignature, producerSignature, rangeDemand,
      HEDemandedConstructorEdge.demand, CompletedDelivery.arrowType, renameAtom, renameAtomList]
  change NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate HEDemandedConstructorInferred.ops (HEDemandedConstructorEdge.packet space)
      HEDemandedConstructorInferred.world 8 (.infer true (.symbol "other-demand-result")) supply).1 = _
  rw [queried, fresh]
  rfl

theorem producer_selection_with_policy_of_reads (reads : HEDemandedReadInterface.Reads) (policy : Policy) (live : List Atom) (scope : List String) :
    kindArgumentService.selection space reads.lookup policy live scope producer
      (.symbol "other-demand-result") rangeDemand Frame.empty (.selected producerSignature [Frame.empty]) := by
  let names := invocationTypeScope scope live producer rangeDemand Frame.empty.bindings
  have same := HEContextualArithmeticSource.same_symbol_match "DemandRange" Frame.empty.bindings (by decide) (by decide)
  refine ⟨[producerSignature.functionType], reads.producerHead names Frame.empty _,
    .selected (errors := []) ?_ (by simp)⟩
  simpa [names, producer, producerSignature, rangeDemand, HEDemandedConstructorEdge.demand, checkedFrames, checkedFailures] using
    (AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := producer) (expected := rangeDemand) (selected := producerSignature)
      (before := Frame.empty) (operator := .symbol "other-demand-result") (arguments := []) rfl
      AdmissionArgumentsRel.nil (.cons (TypeCheckRel.accepted (.unchanged (Frame.empty.preserved_type_match policy same))) .nil))

theorem producer_selection_with_policy (policy : Policy) (live : List Atom) (scope : List String) :
    kindArgumentService.selection space HEDemandedConstructorEdge.inferredLookup policy live scope producer
      (.symbol "other-demand-result") rangeDemand Frame.empty (.selected producerSignature [Frame.empty]) :=
  producer_selection_with_policy_of_reads HEDemandedConstructorInferred.historicalReads policy live scope

theorem producer_selection (live : List Atom) (scope : List String) :
    kindArgumentService.selection space HEDemandedConstructorEdge.inferredLookup Policy.ready live scope producer
      (.symbol "other-demand-result") rangeDemand Frame.empty (.selected producerSignature [Frame.empty]) :=
  producer_selection_with_policy Policy.ready live scope

theorem closed_operator_with_policy_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : Frame) (head : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = [])
    (notEmpty : head ≠ "Empty") (notAtom : expected ≠ Atom.atomType) (notSymbol : expected ≠ Atom.symbolType)
    (queried : reads.lookup
      (invocationTypeScope scope live (.symbol head) expected frame.bindings) space frame.bindings (.symbol head) expected [expected]) :
    Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope (.symbol head) expected frame
      [(.symbol head, frame)] () (policy := policy) := by
  have read : frame.read policy (.symbol head) = .symbol head := by simp [Frame.read, Entry.Value.substitute]
  have matched := frame.preserved_type_match policy
    (FirstSuccessSourceApplicability.closed_type_match expected frame.bindings
      (sizeOf expected + sizeOf expected + 2) closed (Nat.le_refl _)).2
  apply Stateful.AtomRel.cast (raw := [(.symbol head, frame.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol head
    · rintro (asAtom | asSymbol | impossible)
      · exact notAtom asAtom
      · exact notSymbol asSymbol
      · exact (by decide : Atom.symbolType ≠ Atom.variableType) impossible
    · exact Or.inl ⟨head, by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, id_eq, Entry.Value.erase] using
      (TypeCastBatchRel.success (space := space) (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched)
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same frame, by simp [Entry.Value.erase]⟩ .nil

theorem closed_operator_with_policy (minimal : Minimal.Services) (policy : Policy) (live : List Atom) (scope : List String)
    (frame : Frame) (head : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = [])
    (notEmpty : head ≠ "Empty") (notAtom : expected ≠ Atom.atomType) (notSymbol : expected ≠ Atom.symbolType)
    (queried : HEDemandedConstructorEdge.inferredLookup
      (invocationTypeScope scope live (.symbol head) expected frame.bindings) space frame.bindings (.symbol head) expected [expected]) :
    Stateful.AtomRel (environment minimal) space () live scope (.symbol head) expected frame
      [(.symbol head, frame)] () (policy := policy) :=
  closed_operator_with_policy_of_reads HEDemandedConstructorInferred.historicalReads minimal policy live scope frame head expected closed notEmpty notAtom notSymbol queried

theorem closed_operator (minimal : Minimal.Services) (live : List Atom) (scope : List String)
    (frame : Frame) (head : String) (expected : Atom)
    (closed : TypeSubst.typeVars expected = [])
    (notEmpty : head ≠ "Empty") (notAtom : expected ≠ Atom.atomType) (notSymbol : expected ≠ Atom.symbolType)
    (queried : HEDemandedConstructorEdge.inferredLookup
      (invocationTypeScope scope live (.symbol head) expected frame.bindings) space frame.bindings (.symbol head) expected [expected]) :
    Stateful.AtomRel (environment minimal) space () live scope (.symbol head) expected frame
      [(.symbol head, frame)] () (policy := Policy.ready) :=
  closed_operator_with_policy minimal Policy.ready live scope frame head expected closed notEmpty notAtom notSymbol queried

/-- The complete authored nullary producer, including selection, operator
cast, empty argument delivery, equation frontier and its executed body. -/
theorem producer_source_with_marking_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope producerCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
  obtain ⟨after, called⟩ := producer_call_with_marking_of_reads reads minimal marking supported live scope
  have calls : Stateful.CallsRel (HEDemandedReadInterface.environment reads minimal) space () live scope (invocationReturnType producerSignature)
      ([(Entry.Value.argumentPacket [], Frame.empty)].map (functionAssemble (.symbol "other-demand-result")))
      [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
    have combined := Stateful.CallsRel.cons (head := (producerCall, Frame.empty)) called Stateful.CallsRel.nil
    simpa [functionAssemble, producerSignature, invocationReturnType, rangeDemand, HEDemandedConstructorEdge.demand,
      Atom.expressionType, producerCall, producer, Entry.Value.ofAtom] using combined
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(heldResult, after)].map (readResult (HEDemandedPublication.policy marking))) [(heldResult, after)] := by
    simp only [List.map_cons, List.map_nil, readResult, HEDemandedPublication.read, HEDemandedConstructorEdge.held_read]
    simpa [heldResult, Entry.Value.erase, isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => isErrorAtom result.1.erase) (raw := [(heldResult, after)])
        ⟨(heldResult, after), by simp, by simp [heldResult, Entry.Value.erase, isErrorAtom]⟩)
  have composed := HEStatefulSelectedComposition.selected_of_parts (HEDemandedReadInterface.environment reads minimal) (HEDemandedPublication.policy marking) space () () () ()
    live scope producerCall rangeDemand Frame.empty Frame.empty Frame.empty .active
    (.symbol "other-demand-result") (.symbol "other-demand-result") [] producerSignature
    [(Entry.Value.argumentPacket [], Frame.empty)] [(heldResult, after)] [(heldResult, after)]
    (by
      simp only [Frame.read_empty, producerCall, producer, Entry.Value.ofAtom, List.map_cons, List.map_nil,
        Entry.Value.status, Entry.Value.erase]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simp [rangeDemand, HEDemandedConstructorEdge.demand, Atom.atomType, Atom.expressionType, Atom.variableType]) (Or.inr rfl))
    (by rw [Frame.read_empty]; simp [producerCall, producer, Entry.Value.ofAtom])
    (by simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, id_eq,
        producerCall, Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase] using producer_selection_with_policy_of_reads reads (HEDemandedPublication.policy marking) live scope)
    rfl
    (closed_operator_with_policy_of_reads reads minimal (HEDemandedPublication.policy marking) _ _ Frame.empty "other-demand-result" producerSignature.functionType
      rfl (by decide) (by decide) (by decide) (reads.producerHead _ Frame.empty _))
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    Stateful.ArgumentsRel.nil calls priority
  have publication := HEDemandedPublication.held marking supported producer heldResult after.source
    (by simp [heldResult, Entry.Value.status]) (by simp [heldResult, Entry.Value.erase, isErrorAtom])
  refine ⟨after, ?_⟩
  simpa only [List.map_cons, List.map_nil, Frame.read_empty, producerCall, Entry.Value.erase_ofAtom,
    publishResult, HEDemandedPublication.policy, publication] using composed

theorem producer_source_with_marking (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope producerCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) :=
  producer_source_with_marking_of_reads HEDemandedConstructorInferred.historicalReads minimal marking supported live scope

theorem producer_source (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope producerCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) :=
  producer_source_with_marking minimal .successes (Or.inl rfl) live scope

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorProgram
