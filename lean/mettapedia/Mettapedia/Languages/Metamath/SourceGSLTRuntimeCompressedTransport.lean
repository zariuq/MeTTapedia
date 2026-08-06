import Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport
import Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection

/-!
# Compressed proof-DAG transport from the canonical runtime prefix

The runtime object map forgets declaration order, whereas source theorem
occurrences retain authored order.  This module transports compressed proof
DAGs from the canonical runtime prefix back to the authored prefix through
assertion-application semantics.  Node identities, heap indices, stack
indices, and save indices are unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.SourceGSLTRuntimeCompressedTransport

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.SourceGSLTCompressedReflection
open Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeProofTransport
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Metamath.Verify

/-- Transport one proof node while retaining its formula, parent identities,
and occurrence identity. -/
noncomputable def runtimeProofNodeToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (node : ProofNode (runtimePrefix state) runtimeTarget) :
    ProofNode state.toSourcePrefix sourceTarget :=
  { formula := node.formula
    tree := runtimePrefixTreeToSource runtimePresentation sourcePresentation
      node.tree
    parents := node.parents }

/-- Assertion heap entries retain the same authored assertion object; proof
heap entries retain the same node index. -/
def runtimeHeapEntryToSource
    {state : SourceState} :
    HeapEntry (runtimePrefix state) → HeapEntry state.toSourcePrefix
  | .proof nodeId => .proof nodeId
  | .assertion assertion => .assertion assertion

@[simp] theorem runtimeProofNodeToSource_active
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (hypothesis : HypothesisView)
    (member : hypothesis ∈ (runtimePrefix state).activeHypotheses)
    (sourceMember : hypothesis ∈ state.toSourcePrefix.activeHypotheses) :
    runtimeProofNodeToSource runtimePresentation sourcePresentation
        { formula := hypothesis.formula
          tree := .active hypothesis member
          parents := [] } =
      { formula := hypothesis.formula
        tree := .active hypothesis sourceMember
        parents := [] } := by
  simp [runtimeProofNodeToSource, runtimePrefixTreeToSource]

@[simp] theorem runtimePrefixTreeToSource_active
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (hypothesis : HypothesisView)
    (member : hypothesis ∈ (runtimePrefix state).activeHypotheses)
    (sourceMember : hypothesis ∈ state.toSourcePrefix.activeHypotheses) :
    runtimePrefixTreeToSource runtimePresentation sourcePresentation
        (.active hypothesis member) =
      .active hypothesis sourceMember := by
  simp [runtimePrefixTreeToSource]

/-- Transport a compressed machine state without renumbering anything. -/
noncomputable def runtimeMachineToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (machine : MachineState (runtimePrefix state) runtimeTarget) :
    MachineState state.toSourcePrefix sourceTarget :=
  { nodes := machine.nodes.map
      (runtimeProofNodeToSource runtimePresentation sourcePresentation)
    heap := machine.heap.map runtimeHeapEntryToSource
    stack := machine.stack
    saves := machine.saves }

@[simp] theorem runtimeProofNodeToSource_formula
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (node : ProofNode (runtimePrefix state) runtimeTarget) :
    (runtimeProofNodeToSource runtimePresentation sourcePresentation
      node).formula = node.formula := rfl

@[simp] theorem runtimeProofNodeToSource_parents
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (node : ProofNode (runtimePrefix state) runtimeTarget) :
    (runtimeProofNodeToSource runtimePresentation sourcePresentation
      node).parents = node.parents := rfl

@[simp] theorem runtimeMachineToSource_stack
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (machine : MachineState (runtimePrefix state) runtimeTarget) :
    (runtimeMachineToSource runtimePresentation sourcePresentation
      machine).stack = machine.stack := rfl

@[simp] theorem runtimeMachineToSource_saves
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (machine : MachineState (runtimePrefix state) runtimeTarget) :
    (runtimeMachineToSource runtimePresentation sourcePresentation
      machine).saves = machine.saves := rfl

@[simp] theorem runtimeMachineToSource_empty
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1) :
    runtimeMachineToSource runtimePresentation sourcePresentation
        (emptyMachine (runtimePrefix state) runtimeTarget) =
      emptyMachine state.toSourcePrefix sourceTarget := by
  rfl

@[simp] theorem runtimeMachineToSource_nodes
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (machine : MachineState (runtimePrefix state) runtimeTarget) :
    (runtimeMachineToSource runtimePresentation sourcePresentation
      machine).nodes =
        machine.nodes.map
          (runtimeProofNodeToSource runtimePresentation sourcePresentation) :=
  rfl

@[simp] theorem runtimeMachineToSource_heap
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (machine : MachineState (runtimePrefix state) runtimeTarget) :
    (runtimeMachineToSource runtimePresentation sourcePresentation
      machine).heap = machine.heap.map runtimeHeapEntryToSource :=
  rfl

/-- Index lookup commutes with proof-node transport. -/
theorem runtimeNodeLookupToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    (nodes : List (ProofNode (runtimePrefix state) runtimeTarget))
    (nodeId : Nat) (node : ProofNode (runtimePrefix state) runtimeTarget)
    (lookup : nodes[nodeId]? = some node) :
    (nodes.map
      (runtimeProofNodeToSource runtimePresentation sourcePresentation))[
        nodeId]? =
      some (runtimeProofNodeToSource runtimePresentation sourcePresentation
        node) := by
  simpa using congrArg
    (Option.map
      (runtimeProofNodeToSource runtimePresentation sourcePresentation))
    lookup

/-- Index lookup commutes with heap-entry transport. -/
theorem runtimeHeapLookupToSource
    {state : SourceState}
    (heap : List (HeapEntry (runtimePrefix state)))
    (index : Nat) (entry : HeapEntry (runtimePrefix state))
    (lookup : heap[index]? = some entry) :
    (heap.map runtimeHeapEntryToSource)[index]? =
      some (runtimeHeapEntryToSource entry) := by
  simpa using congrArg (Option.map runtimeHeapEntryToSource) lookup

/-- Parent resolution is representation-independent: node identities and
formulas stay fixed while the proof trees at those identities are rebuilt
over the authored prefix. -/
noncomputable def runtimeResolvesForestToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {nodes : List (ProofNode (runtimePrefix state) runtimeTarget)}
    {parents : List Nat} {formulas : List ConstantHeadedFormula}
    {forest : SourceGeneratedProvesForest
      (runtimePrefix state) runtimeTarget formulas}
    (resolved : ResolvesForest nodes parents formulas forest) :
    ResolvesForest
      (nodes.map
        (runtimeProofNodeToSource runtimePresentation sourcePresentation))
      parents formulas
      (runtimePrefixForestToSource runtimePresentation sourcePresentation
        forest) := by
  induction resolved with
  | nil => exact .nil
  | @cons parent parents formulas node forest lookup tail ih =>
      exact .cons
        (runtimeProofNodeToSource runtimePresentation sourcePresentation node)
        (runtimePrefixForestToSource runtimePresentation sourcePresentation
          forest)
        (runtimeNodeLookupToSource runtimePresentation sourcePresentation
          _ parent node lookup)
        ih

/-- Header construction commutes with runtime-prefix canonicalization. -/
noncomputable def runtimeHeaderStepToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {item : HeaderItem}
    {before after : MachineState (runtimePrefix state) runtimeTarget}
    (step : HeaderStep item before after) :
    HeaderStep item
      (runtimeMachineToSource runtimePresentation sourcePresentation before)
      (runtimeMachineToSource runtimePresentation sourcePresentation after) :=
  by
    cases step with
    | mandatory before hypothesis member =>
        let sourceMember :
            hypothesis ∈ state.toSourcePrefix.activeHypotheses := by
          simpa [runtimePrefix, SourceState.toSourcePrefix] using member
        have canonical := HeaderStep.mandatory
          (runtimeMachineToSource runtimePresentation sourcePresentation
            before)
          hypothesis sourceMember
        convert canonical using 1
        all_goals
          simp [runtimeMachineToSource, runtimeProofNodeToSource,
            runtimeHeapEntryToSource]
        exact runtimePrefixTreeToSource_active runtimePresentation
          sourcePresentation hypothesis member sourceMember
    | explicitHypothesis before label hypothesis member label_eq =>
        let sourceMember :
            hypothesis ∈ state.toSourcePrefix.activeHypotheses := by
          simpa [runtimePrefix, SourceState.toSourcePrefix] using member
        have canonical := HeaderStep.explicitHypothesis
          (runtimeMachineToSource runtimePresentation sourcePresentation
            before)
          label hypothesis sourceMember label_eq
        convert canonical using 1
        all_goals
          simp [runtimeMachineToSource, runtimeProofNodeToSource,
            runtimeHeapEntryToSource]
        exact runtimePrefixTreeToSource_active runtimePresentation
          sourcePresentation hypothesis member sourceMember
    | explicitAssertion before label assertion member label_eq =>
        simpa [runtimeMachineToSource, runtimeHeapEntryToSource] using
          (HeaderStep.explicitAssertion
            (runtimeMachineToSource runtimePresentation sourcePresentation
              before)
            label assertion
            ((runtimePrefix_assertion_mem_iff state assertion).mp member)
            label_eq)

/-- Ordered header builds transport without changing their item list. -/
noncomputable def runtimeHeaderBuildToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {items : List HeaderItem}
    {before after : MachineState (runtimePrefix state) runtimeTarget}
    (build : HeaderBuild items before after) :
    HeaderBuild items
      (runtimeMachineToSource runtimePresentation sourcePresentation before)
      (runtimeMachineToSource runtimePresentation sourcePresentation after) :=
  by
    induction build with
    | nil machine => exact .nil _
    | cons head tail ih =>
        exact .cons
          (runtimeHeaderStepToSource runtimePresentation sourcePresentation
            head)
          ih

/-- One compressed action commutes with canonical-prefix transport.  The
assertion branch reuses the same semantic node reconstruction as proof-tree
transport, so the appended DAG node is definitionally the transported tree. -/
noncomputable def runtimeActionStepToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {before after : MachineState (runtimePrefix state) runtimeTarget}
    {action : CompressedAction}
    (step : ActionStep before action after) :
    ActionStep
      (runtimeMachineToSource runtimePresentation sourcePresentation before)
      action
      (runtimeMachineToSource runtimePresentation sourcePresentation after) :=
  by
    cases step with
    | proof index nodeId node heapLookup nodeLookup =>
        let sourceNode := runtimeProofNodeToSource runtimePresentation
          sourcePresentation node
        have sourceHeapLookup :
            (runtimeMachineToSource runtimePresentation sourcePresentation
              before).heap[index]? = some (.proof nodeId) := by
          exact runtimeHeapLookupToSource before.heap index (.proof nodeId)
            heapLookup
        have sourceNodeLookup :
            (runtimeMachineToSource runtimePresentation sourcePresentation
              before).nodes[nodeId]? = some sourceNode := by
          exact runtimeNodeLookupToSource runtimePresentation
            sourcePresentation before.nodes nodeId node nodeLookup
        have canonical := ActionStep.proof
          (runtimeMachineToSource runtimePresentation sourcePresentation
            before)
          index nodeId sourceNode sourceHeapLookup sourceNodeLookup
        convert canonical using 1
        all_goals
          simp [runtimeMachineToSource]
    | @assertion index assertion actuals result substitution retained
        parents children heapLookup member stack_eq node resolved =>
        let sourceMember : assertion ∈ state.toSourcePrefix.assertions :=
          (runtimePrefix_assertion_mem_iff state assertion).mp member
        let sourceNode := runtimePrefixAssertionNodeToSource
          runtimePresentation sourcePresentation member node
        let sourceChildren := runtimePrefixForestToSource
          runtimePresentation sourcePresentation children
        have sourceHeapLookup :
            (runtimeMachineToSource runtimePresentation sourcePresentation
              before).heap[index]? = some (.assertion assertion) := by
          exact runtimeHeapLookupToSource before.heap index
            (.assertion assertion) heapLookup
        have sourceResolved : ResolvesForest
            (runtimeMachineToSource runtimePresentation sourcePresentation
              before).nodes
            parents actuals sourceChildren := by
          exact runtimeResolvesForestToSource runtimePresentation
            sourcePresentation resolved
        have canonical := ActionStep.assertion
          (runtimeMachineToSource runtimePresentation sourcePresentation
            before)
          index assertion retained parents sourceChildren sourceHeapLookup
          sourceMember stack_eq sourceNode.2 sourceResolved
        convert canonical using 1
        all_goals
          simp [runtimeMachineToSource, runtimeProofNodeToSource,
            runtimePrefixTreeToSource, sourceNode,
            sourceChildren]
    | save nodeId node stackTop nodeLookup =>
        let sourceNode := runtimeProofNodeToSource runtimePresentation
          sourcePresentation node
        have sourceNodeLookup :
            (runtimeMachineToSource runtimePresentation sourcePresentation
              before).nodes[nodeId]? = some sourceNode := by
          exact runtimeNodeLookupToSource runtimePresentation
            sourcePresentation before.nodes nodeId node nodeLookup
        have canonical := ActionStep.save
          (runtimeMachineToSource runtimePresentation sourcePresentation
            before)
          nodeId sourceNode stackTop sourceNodeLookup
        convert canonical using 1
        all_goals
          simp [runtimeMachineToSource, runtimeHeapEntryToSource]

/-- A complete compressed program transports action-for-action. -/
noncomputable def runtimeExecuteToSource
    {state : SourceState}
    {runtimeTarget sourceTarget : ValidatedPresentation}
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix state) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? state.toSourcePrefix =
        some sourceTarget.1)
    {before after : MachineState (runtimePrefix state) runtimeTarget}
    {actions : List CompressedAction}
    (execution : Execute before actions after) :
    Execute
      (runtimeMachineToSource runtimePresentation sourcePresentation before)
      actions
      (runtimeMachineToSource runtimePresentation sourcePresentation after) :=
  by
    induction execution with
    | nil machine => exact .nil _
    | cons head tail ih =>
        exact .cons
          (runtimeActionStepToSource runtimePresentation sourcePresentation
            head)
          ih

/-- For a mandatory hypothesis selected from the authored state, canonical
runtime-prefix projection is sufficient to identify the shipped preload
transition.  Declaration and assertion ordering play no role in this gate. -/
theorem mandatoryPreloadStep_eq_preload_runtimePrefix
    (db : RuntimeDB) (state : SourceState)
    (formula : ConstantHeadedFormula) (runtime : RuntimeProofState)
    (hypothesis : HypothesisView)
    (hproject : projectPrefix? db =
      some (runtimePrefix state).toProjection)
    (member : hypothesis ∈ mandatoryHypotheses state formula) :
    mandatoryPreloadStep db runtime hypothesis.label =
      db.preload runtime hypothesis.label := by
  have active : hypothesis ∈ (runtimePrefix state).activeHypotheses := by
    simpa [runtimePrefix] using (List.mem_filter.mp member).1
  obtain ⟨scope, found⟩ :=
    projectedActiveHypothesis_database_fidelity db
      (runtimePrefix state).toProjection hypothesis hproject active
  simp [mandatoryPreloadStep, Metamath.Verify.DB.preload, found, scope,
    Pure.pure, Except.pure]

/-- The implementation's bulk mandatory preload and ordinary checked
preloads coincide under canonical runtime-prefix projection. -/
theorem mandatoryPreloadFold_eq_preloadFold_runtimePrefix
    (db : RuntimeDB) (state : SourceState)
    (formula : ConstantHeadedFormula) (runtime : RuntimeProofState)
    (hproject : projectPrefix? db =
      some (runtimePrefix state).toProjection) :
    ((mandatoryHypotheses state formula).map HypothesisView.label).foldlM
        (mandatoryPreloadStep db) runtime =
      ((mandatoryHypotheses state formula).map
        HypothesisView.label).foldlM (db.preload) runtime := by
  let hypotheses := mandatoryHypotheses state formula
  have go : ∀ remaining : List HypothesisView,
      (∀ hypothesis ∈ remaining,
        hypothesis ∈ mandatoryHypotheses state formula) →
      ∀ current,
        (remaining.map HypothesisView.label).foldlM
            (mandatoryPreloadStep db) current =
          (remaining.map HypothesisView.label).foldlM
            (db.preload) current := by
    intro remaining
    induction remaining with
    | nil =>
        intro subset current
        rfl
    | cons hypothesis rest inductionHypothesis =>
        intro subset current
        have headMember :
            hypothesis ∈ mandatoryHypotheses state formula :=
          subset hypothesis (.head rest)
        have tailSubset : ∀ other ∈ rest,
            other ∈ mandatoryHypotheses state formula := by
          intro other otherMember
          exact subset other (.tail hypothesis otherMember)
        simp only [List.map_cons, List.foldlM_cons]
        rw [mandatoryPreloadStep_eq_preload_runtimePrefix db state formula
          current hypothesis hproject headMember]
        cases step : db.preload current hypothesis.label with
        | error error => rfl
        | ok middle =>
            simp only [bind, Except.bind]
            exact inductionHypothesis tailSubset middle
  exact go hypotheses (by
    intro hypothesis member
    exact member) runtime

/-- Shipped compressed acceptance over the canonical runtime prefix rebuilds
the complete theorem occurrence over the authored prefix.  The runtime
database is projected only once; all proof-relevant header and action data is
then transported through order-independent assertion semantics. -/
noncomputable def compressedTheoremStep_of_runtimePrefix
    {before next : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (runtimeTarget sourceTarget : ValidatedPresentation)
    (hvalid : sourceStateValid before = true)
    (runtimePresentation :
      presentationOfSourcePrefix? (runtimePrefix before) =
        some runtimeTarget.1)
    (sourcePresentation :
      presentationOfSourcePrefix? before.toSourcePrefix =
        some sourceTarget.1)
    (hins : insertAssertion? before label formula = some next)
    {actions : List CompressedAction}
    (hdecode : decodeProgram bodyWords = some actions)
    (hverified : actionsVerified actions)
    (db : RuntimeDB)
    (hproject : projectPrefix? db =
      some (runtimePrefix before).toProjection)
    (runtimeBase : RuntimeProofState)
    {runtimeInitial runtimeFinal : RuntimeProofState}
    (hheader :
      (((headerItems before formula explicitHeaderLabels).map
          headerRuntimeLabel).foldlM
        (fun state label => db.preload state label)
        { runtimeBase with heap := #[], stack := #[] }) =
        .ok runtimeInitial)
    (hactions :
      ParserState.applyCompressedActions db runtimeInitial
        (actions.map toMMLean4Action) = .ok runtimeFinal)
    (hstack : runtimeFinal.stack = #[formula.toRuntime]) :
    CompressedTheoremStep before next label formula explicitHeaderLabels
      bodyWords := by
  have mandatoryMember : ∀ hypothesis : HypothesisView,
      HeaderItem.mandatory hypothesis ∈
        headerItems before formula explicitHeaderLabels →
      hypothesis ∈ (runtimePrefix before).activeHypotheses := by
    intro hypothesis member
    unfold headerItems at member
    rcases List.mem_append.mp member with mandatory | explicit
    · obtain ⟨candidate, candidateMember, equality⟩ :=
        List.mem_map.mp mandatory
      cases HeaderItem.mandatory.inj equality
      exact List.mem_of_mem_filter candidateMember
    · obtain ⟨candidate, candidateMember, equality⟩ :=
        List.mem_map.mp explicit
      exact nomatch equality
  obtain ⟨runtimeInitialSource, runtimeHeader, initialAgreement⟩ :=
    headerBuild_runtimeReflected db hproject
      (emptyMachineAgrees db (runtimePrefix before) runtimeTarget runtimeBase)
      hheader mandatoryMember
  obtain ⟨runtimeFinalSource, runtimeExecution, finalAgreement⟩ :=
    execute_mmLean4Reflected actions db runtimePresentation hproject
      runtimeInitial runtimeFinal initialAgreement hverified hactions
  have runtimeStackFormulas :
      finalAgreement.stackFormulas = [formula.toRuntime] := by
    have stackEquality := finalAgreement.stack_eq
    rw [hstack] at stackEquality
    have listEquality := congrArg Array.toList stackEquality
    simpa using listEquality.symm
  obtain ⟨rootId, runtimeRoot, runtimeFinalStack, runtimeRootLookup,
      runtimeRootFormula⟩ :=
    stackSingletonWitness
      (runtimeStackFormulas ▸ finalAgreement.stackAgreement)
  let sourceInitial := runtimeMachineToSource runtimePresentation
    sourcePresentation runtimeInitialSource
  let sourceFinal := runtimeMachineToSource runtimePresentation
    sourcePresentation runtimeFinalSource
  let sourceRoot := runtimeProofNodeToSource runtimePresentation
    sourcePresentation runtimeRoot
  have sourceHeader : HeaderBuild
      (headerItems before formula explicitHeaderLabels)
      (emptyMachine before.toSourcePrefix sourceTarget) sourceInitial := by
    simpa [sourceInitial] using
      runtimeHeaderBuildToSource runtimePresentation sourcePresentation
        runtimeHeader
  have sourceExecution : Execute sourceInitial actions sourceFinal := by
    exact runtimeExecuteToSource runtimePresentation sourcePresentation
      runtimeExecution
  have sourceFinalStack : sourceFinal.stack = [rootId] := by
    simpa [sourceFinal] using runtimeFinalStack
  have sourceRootLookup : sourceFinal.nodes[rootId]? = some sourceRoot := by
    exact runtimeNodeLookupToSource runtimePresentation sourcePresentation
      runtimeFinalSource.nodes rootId runtimeRoot runtimeRootLookup
  have sourceRootFormula : sourceRoot.formula = formula := by
    change runtimeRoot.formula = formula
    exact
      SourceGSLTCompressedReflection.ConstantHeadedFormula.toRuntime_injective
        runtimeRootFormula
  exact
    { sourceValid := hvalid
      target := sourceTarget
      presentation_eq := sourcePresentation
      actions := actions
      decoded := hdecode
      initialState := sourceInitial
      finalState := sourceFinal
      header := sourceHeader
      execution := sourceExecution
      rootId := rootId
      root := sourceRoot
      finalStack := sourceFinalStack
      rootLookup := sourceRootLookup
      rootFormula := sourceRootFormula
      inserted := hins }

end Mettapedia.Languages.Metamath.SourceGSLTRuntimeCompressedTransport
