import Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
import Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement
import Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
import Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
import Mettapedia.Languages.Metamath.InferenceNormalStepReflection
import Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification

/-!
# Occurrence-preserving compressed execution agreement

The source compressed machine stores proof-node identities.  The verified
implementation stores only their runtime formulas in its stack and heap.
This file relates those two representations without erasing the source proof
DAG: every runtime formula is tied to the exact source node from which it was
projected, while assertion heap entries retain their authored source schema.

This relation is the semantic waist for proving that `mm-lean4` compressed
execution refines and reflects the source-owned checker GSLT.  Decoder
agreement is imported, but token equality is not used as semantic evidence.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceProjectionFidelity
open Mettapedia.Languages.Metamath.InferenceProjectionRuntimeClassification
open Mettapedia.Languages.Metamath.InferenceAssertionStepAgreement
open Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceNormalStepReflection
open Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTState
open Metamath.Verify

/-! ## Exact representation relations -/

/-- One source proof-node identity denotes exactly one runtime formula. -/
inductive StackEntriesAgree
    {source : SourcePrefix} {target : ValidatedPresentation}
    (nodes : List (ProofNode source target)) :
    List Nat → List RuntimeFormula → Type where
  | nil : StackEntriesAgree nodes [] []
  | cons
      {nodeId : Nat} {nodeIds : List Nat}
      {runtimeFormulas : List RuntimeFormula}
      (node : ProofNode source target)
      (lookup : nodes[nodeId]? = some node)
      (tail : StackEntriesAgree nodes nodeIds runtimeFormulas) :
      StackEntriesAgree nodes (nodeId :: nodeIds)
        (node.formula.toRuntime :: runtimeFormulas)

/-- A source compressed heap entry denotes exactly one runtime heap entry.
Proof entries retain the source node identity even though `mm-lean4` stores
only the node's formula. -/
inductive HeapEntryAgrees
    {source : SourcePrefix} {target : ValidatedPresentation}
    (nodes : List (ProofNode source target)) :
    HeapEntry source → Metamath.Verify.HeapEl → Type where
  | proof
      (nodeId : Nat) (node : ProofNode source target)
      (lookup : nodes[nodeId]? = some node) :
      HeapEntryAgrees nodes (.proof nodeId) (.fmla node.formula.toRuntime)
  | assertion (assertion : SourceAssertion)
      (member : assertion ∈ source.assertions) :
      HeapEntryAgrees nodes (.assertion assertion)
        (.assert assertion.formula.toRuntime assertion.frame.toRuntime)

/-- Ordered pointwise agreement of the complete compressed-proof heap. -/
inductive HeapEntriesAgree
    {source : SourcePrefix} {target : ValidatedPresentation}
    (nodes : List (ProofNode source target)) :
    List (HeapEntry source) → List Metamath.Verify.HeapEl → Type where
  | nil : HeapEntriesAgree nodes [] []
  | cons
      {sourceEntry : HeapEntry source}
      {runtimeEntry : Metamath.Verify.HeapEl}
      {sourceEntries : List (HeapEntry source)}
      {runtimeEntries : List Metamath.Verify.HeapEl}
      (head : HeapEntryAgrees nodes sourceEntry runtimeEntry)
      (tail : HeapEntriesAgree nodes sourceEntries runtimeEntries) :
      HeapEntriesAgree nodes
        (sourceEntry :: sourceEntries) (runtimeEntry :: runtimeEntries)

/-- Complete state relation.  Runtime arrays are exact images of ordered
source lists, and the live runtime stack satisfies the caller-frame gate used
by assertion execution.  Source `saves` remain proof-relevant ghost data;
their identities are observable through the source heap relation. -/
structure MachineAgrees
    (db : RuntimeDB) (source : SourcePrefix)
    (target : ValidatedPresentation)
    (sourceState : MachineState source target)
    (runtimeState : RuntimeProofState) : Type where
  stackFormulas : List RuntimeFormula
  heapEntries : List Metamath.Verify.HeapEl
  stackAgreement :
    StackEntriesAgree sourceState.nodes sourceState.stack stackFormulas
  heapAgreement :
    HeapEntriesAgree sourceState.nodes sourceState.heap heapEntries
  stack_eq : runtimeState.stack = stackFormulas.toArray
  heap_eq : runtimeState.heap = heapEntries.toArray
  stackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame runtimeState.stack

/-! ## Structural laws for the representation relation -/

noncomputable def StackEntriesAgree.append
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {leftIds rightIds : List Nat}
    {leftFormulas rightFormulas : List RuntimeFormula}
    (left : StackEntriesAgree nodes leftIds leftFormulas)
    (right : StackEntriesAgree nodes rightIds rightFormulas) :
    StackEntriesAgree nodes (leftIds ++ rightIds)
      (leftFormulas ++ rightFormulas) := by
  induction left with
  | nil => exact right
  | cons node lookup tail ih =>
      exact .cons node lookup ih

theorem StackEntriesAgree.length_eq
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {nodeIds : List Nat} {runtimeFormulas : List RuntimeFormula}
    (agreement : StackEntriesAgree nodes nodeIds runtimeFormulas) :
    nodeIds.length = runtimeFormulas.length := by
  induction agreement with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- Split an identity stack into the retained prefix and the exact consumed
suffix selected by an assertion's mandatory-hypothesis count.  The witness is
Type-valued because reflection returns executable proof data, rather than
merely asserting that some split exists. -/
noncomputable def splitSuffixIds
    (nodeIds : List Nat) (count : Nat)
    (hcount : count ≤ nodeIds.length) :
    Σ retained : List Nat, Σ parents : List Nat,
      (nodeIds = retained ++ parents) ×' (parents.length = count) := by
  refine ⟨nodeIds.take (nodeIds.length - count),
    nodeIds.drop (nodeIds.length - count), ?_, ?_⟩
  · exact (List.take_append_drop (nodeIds.length - count) nodeIds).symm
  · simp only [List.length_drop]
    omega

/-- Split a stack relation at an exact source-identity boundary, retaining
both ordered runtime images. -/
noncomputable def StackEntriesAgree.split
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    (leftIds rightIds : List Nat)
    {runtimeFormulas : List RuntimeFormula}
    (agreement :
      StackEntriesAgree nodes (leftIds ++ rightIds) runtimeFormulas) :
    Σ leftFormulas, Σ rightFormulas,
      (runtimeFormulas = leftFormulas ++ rightFormulas) ×'
        StackEntriesAgree nodes leftIds leftFormulas ×'
          StackEntriesAgree nodes rightIds rightFormulas := by
  induction leftIds generalizing runtimeFormulas with
  | nil =>
      exact ⟨[], runtimeFormulas, rfl, .nil, agreement⟩
  | cons leftId leftIds ih =>
      cases agreement with
      | cons node lookup tail =>
          obtain ⟨leftFormulas, rightFormulas, hformulas,
              leftAgreement, rightAgreement⟩ := ih tail
          exact
            ⟨node.formula.toRuntime :: leftFormulas, rightFormulas,
              by simp [hformulas], .cons node lookup leftAgreement,
              rightAgreement⟩

/-- Singleton stack identity fixes its runtime formula uniquely. -/
theorem StackEntriesAgree.singleton_eq
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {nodeId : Nat} {runtimeFormulas : List RuntimeFormula}
    (agreement : StackEntriesAgree nodes [nodeId] runtimeFormulas)
    (node : ProofNode source target)
    (nodeLookup : nodes[nodeId]? = some node) :
    runtimeFormulas = [node.formula.toRuntime] := by
  cases agreement with
  | cons otherNode otherLookup tail =>
      cases tail
      have hnode : otherNode = node := by
        rw [nodeLookup] at otherLookup
        exact Option.some.inj otherLookup.symm
      subst otherNode
      rfl

/-- The final source node identity and the final runtime formula agree. -/
theorem StackEntriesAgree.getLast?_eq
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {nodeIds : List Nat} {runtimeFormulas : List RuntimeFormula}
    (agreement : StackEntriesAgree nodes nodeIds runtimeFormulas)
    (nodeId : Nat) (node : ProofNode source target)
    (sourceLast : nodeIds.getLast? = some nodeId)
    (nodeLookup : nodes[nodeId]? = some node) :
    runtimeFormulas.getLast? = some node.formula.toRuntime := by
  have hmember : nodeId ∈ nodeIds.getLast? := by
    rw [sourceLast]
    simp
  have hdecompose : nodeIds.dropLast ++ [nodeId] = nodeIds :=
    List.dropLast_append_getLast? nodeId hmember
  have indexed :
      StackEntriesAgree nodes (nodeIds.dropLast ++ [nodeId])
        runtimeFormulas := by
    rw [hdecompose]
    exact agreement
  obtain ⟨leftFormulas, rightFormulas, hformulas, _leftAgreement,
      rightAgreement⟩ := indexed.split nodeIds.dropLast [nodeId]
  have hright : rightFormulas = [node.formula.toRuntime] :=
    rightAgreement.singleton_eq node nodeLookup
  rw [hformulas, hright,
    List.getLast?_append_of_ne_nil leftFormulas (by simp)]
  simp

/-- A successful runtime `back?` lookup reconstructs the exact source node
identity at the top of the related stack.  The node is recovered from the
existing occurrence relation, never guessed from formula equality. -/
noncomputable def StackEntriesAgree.runtimeLastSource
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {nodeIds : List Nat} {runtimeFormulas : List RuntimeFormula}
    (agreement : StackEntriesAgree nodes nodeIds runtimeFormulas)
    (runtimeFormula : RuntimeFormula)
    (runtimeLast : runtimeFormulas.getLast? = some runtimeFormula) :
    Σ nodeId : Nat, Σ node : ProofNode source target,
      (nodeIds.getLast? = some nodeId) ×'
      (nodes[nodeId]? = some node) ×'
      (node.formula.toRuntime = runtimeFormula) := by
  induction agreement with
  | nil =>
      simp at runtimeLast
  | @cons nodeId nodeIds runtimeFormulas node lookup tail ih =>
      cases tail with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at runtimeLast
          exact ⟨nodeId, node, rfl, lookup, runtimeLast⟩
      | @cons tailNodeId tailNodeIds tailRuntimeFormulas tailNode
          tailLookup tailAgreement =>
          have tailLast :
              (tailNode.formula.toRuntime :: tailRuntimeFormulas).getLast? =
                some runtimeFormula := by
            simpa using runtimeLast
          obtain ⟨lastId, lastNode, sourceLast, lastLookup, formulaEq⟩ :=
            ih tailLast
          exact
            ⟨lastId, lastNode, by simpa using sourceLast,
              lastLookup, formulaEq⟩

/-- Resolving the same ordered source node identities determines the runtime
formula list uniquely. -/
theorem StackEntriesAgree.eq_runtimeMap_of_resolves
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {nodeIds : List Nat} {runtimeFormulas : List RuntimeFormula}
    {formulas : List ConstantHeadedFormula}
    {forest : SourceGeneratedProvesForest source target formulas}
    (agreement : StackEntriesAgree nodes nodeIds runtimeFormulas)
    (resolved : ResolvesForest nodes nodeIds formulas forest) :
    runtimeFormulas = formulas.map ConstantHeadedFormula.toRuntime := by
  induction resolved generalizing runtimeFormulas with
  | nil =>
      cases agreement
      rfl
  | cons resolvedNode _forest resolvedLookup tail ih =>
      cases agreement with
      | cons runtimeNode runtimeLookup runtimeTail =>
          have hnode : runtimeNode = resolvedNode := by
            rw [resolvedLookup] at runtimeLookup
            exact Option.some.inj runtimeLookup.symm
          subst runtimeNode
          simp only [List.map_cons, List.cons.injEq, true_and]
          exact ih runtimeTail

/-- Every related source stack already carries an exact proof-occurrence
forest.  This is the constructive inverse used by runtime-to-source
reflection; no proof tree is reconstructed from formulas alone. -/
noncomputable def StackEntriesAgree.toResolvedForest
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {nodeIds : List Nat} {runtimeFormulas : List RuntimeFormula}
    (agreement : StackEntriesAgree nodes nodeIds runtimeFormulas) :
    Σ formulas : List ConstantHeadedFormula,
      Σ forest : SourceGeneratedProvesForest source target formulas,
        (runtimeFormulas =
          formulas.map ConstantHeadedFormula.toRuntime) ×'
        ResolvesForest nodes nodeIds formulas forest := by
  induction agreement with
  | nil =>
      exact ⟨[], .nil, rfl, .nil⟩
  | cons node lookup tail ih =>
      obtain ⟨formulas, forest, hformulas, resolved⟩ := ih
      exact
        ⟨node.formula :: formulas, .cons node.tree forest,
          by simp [hformulas], .cons node forest lookup resolved⟩

noncomputable def HeapEntriesAgree.append
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {leftSource rightSource : List (HeapEntry source)}
    {leftRuntime rightRuntime : List Metamath.Verify.HeapEl}
    (left : HeapEntriesAgree nodes leftSource leftRuntime)
    (right : HeapEntriesAgree nodes rightSource rightRuntime) :
    HeapEntriesAgree nodes (leftSource ++ rightSource)
      (leftRuntime ++ rightRuntime) := by
  induction left with
  | nil => exact right
  | cons head tail ih =>
      exact .cons head ih

/-- Existing node references remain exact when later proof occurrences are
appended to the topologically ordered source DAG. -/
theorem nodeLookup_append
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes suffix : List (ProofNode source target)}
    {nodeId : Nat} {node : ProofNode source target}
    (lookup : nodes[nodeId]? = some node) :
    (nodes ++ suffix)[nodeId]? = some node := by
  have hbound : nodeId < nodes.length := by
    exact (List.getElem?_eq_some_iff.mp lookup).1
  rw [List.getElem?_append_left hbound]
  exact lookup

noncomputable def StackEntriesAgree.weakenNodes
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes suffix : List (ProofNode source target)}
    {nodeIds : List Nat} {runtimeFormulas : List RuntimeFormula}
    (agreement : StackEntriesAgree nodes nodeIds runtimeFormulas) :
    StackEntriesAgree (nodes ++ suffix) nodeIds runtimeFormulas := by
  induction agreement with
  | nil => exact .nil
  | cons node lookup tail ih =>
      exact .cons node (nodeLookup_append lookup) ih

noncomputable def HeapEntryAgrees.weakenNodes
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes suffix : List (ProofNode source target)}
    {sourceEntry : HeapEntry source}
    {runtimeEntry : Metamath.Verify.HeapEl}
    (agreement : HeapEntryAgrees nodes sourceEntry runtimeEntry) :
    HeapEntryAgrees (nodes ++ suffix) sourceEntry runtimeEntry := by
  cases agreement with
  | proof nodeId node lookup =>
      exact .proof nodeId node (nodeLookup_append lookup)
  | assertion assertion member =>
      exact .assertion assertion member

noncomputable def HeapEntriesAgree.weakenNodes
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes suffix : List (ProofNode source target)}
    {sourceEntries : List (HeapEntry source)}
    {runtimeEntries : List Metamath.Verify.HeapEl}
    (agreement : HeapEntriesAgree nodes sourceEntries runtimeEntries) :
    HeapEntriesAgree (nodes ++ suffix) sourceEntries runtimeEntries := by
  induction agreement with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons head.weakenNodes ih

/-- Pointwise source-heap lookup carries the corresponding runtime entry at
the same index. -/
noncomputable def HeapEntriesAgree.lookup
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {sourceEntries : List (HeapEntry source)}
    {runtimeEntries : List Metamath.Verify.HeapEl}
    (agreement : HeapEntriesAgree nodes sourceEntries runtimeEntries)
    (index : Nat) (sourceEntry : HeapEntry source)
    (sourceLookup : sourceEntries[index]? = some sourceEntry) :
    Σ runtimeEntry,
      (runtimeEntries[index]? = some runtimeEntry) ×'
        HeapEntryAgrees nodes sourceEntry runtimeEntry := by
  induction agreement generalizing index sourceEntry with
  | nil =>
      simp at sourceLookup
  | @cons sourceHead runtimeHead sourceTail runtimeTail head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceLookup
          subst sourceHead
          exact ⟨runtimeHead, rfl, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at sourceLookup
          exact ih index sourceEntry sourceLookup

/-- Runtime-to-source lookup at the same heap index. -/
noncomputable def HeapEntriesAgree.runtimeLookup
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {sourceEntries : List (HeapEntry source)}
    {runtimeEntries : List Metamath.Verify.HeapEl}
    (agreement : HeapEntriesAgree nodes sourceEntries runtimeEntries)
    (index : Nat) (runtimeEntry : Metamath.Verify.HeapEl)
    (runtimeLookup : runtimeEntries[index]? = some runtimeEntry) :
    Σ sourceEntry,
      (sourceEntries[index]? = some sourceEntry) ×'
        HeapEntryAgrees nodes sourceEntry runtimeEntry := by
  induction agreement generalizing index runtimeEntry with
  | nil =>
      simp at runtimeLookup
  | @cons sourceHead runtimeHead sourceTail runtimeTail head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at runtimeLookup
          subst runtimeHead
          exact ⟨sourceHead, rfl, head⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at runtimeLookup
          exact ih index runtimeEntry runtimeLookup

/-- A source proof reference therefore indexes the exact runtime formula of
the referenced node. -/
theorem HeapEntriesAgree.proofLookup
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {sourceEntries : List (HeapEntry source)}
    {runtimeEntries : List Metamath.Verify.HeapEl}
    (agreement : HeapEntriesAgree nodes sourceEntries runtimeEntries)
    (index nodeId : Nat) (node : ProofNode source target)
    (sourceLookup : sourceEntries[index]? = some (.proof nodeId))
    (nodeLookup : nodes[nodeId]? = some node) :
    runtimeEntries[index]? =
      some (.fmla node.formula.toRuntime) := by
  obtain ⟨runtimeEntry, runtimeLookup, entryAgreement⟩ :=
    agreement.lookup index (.proof nodeId) sourceLookup
  cases entryAgreement with
  | proof _ otherNode otherLookup =>
      have hnode : otherNode = node := by
        rw [nodeLookup] at otherLookup
        exact Option.some.inj otherLookup.symm
      subst otherNode
      exact runtimeLookup

/-- A source assertion schema indexes the exact runtime assertion payload. -/
theorem HeapEntriesAgree.assertionLookup
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    {sourceEntries : List (HeapEntry source)}
    {runtimeEntries : List Metamath.Verify.HeapEl}
    (agreement : HeapEntriesAgree nodes sourceEntries runtimeEntries)
    (index : Nat) (assertion : SourceAssertion)
    (sourceLookup :
      sourceEntries[index]? = some (.assertion assertion)) :
    runtimeEntries[index]? =
      some (.assert assertion.formula.toRuntime assertion.frame.toRuntime) := by
  obtain ⟨runtimeEntry, runtimeLookup, entryAgreement⟩ :=
    agreement.lookup index (.assertion assertion) sourceLookup
  cases entryAgreement with
  | assertion _ _ =>
      exact runtimeLookup

/-- Every source proof node denotes a runtime formula accepted by the live
caller-frame gate. -/
theorem ProofNode.runtimeFormula_respects
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (node : ProofNode source target) :
    db.formulaSymsRespectFrame node.formula.toRuntime db.frame = true := by
  have hfields :=
    projectPrefix?_eq_some_fields db source.toProjection hproject
  rw [← formulaSymbolsRespectFrame_eq_runtime_of_projectHypotheses
    db db.frame source.activeHypotheses hfields.2.2.2.1 node.formula]
  exact sourceTree_result_respects hsource node.tree

/-! ## Header preload preservation -/

def headerRuntimeLabel : HeaderItem → String
  | .mandatory hypothesis => hypothesis.label
  | .explicit label => label

/-- Empty source and implementation machines agree over any fixed non-stack
runtime proof context. -/
def emptyMachineAgrees
    (db : RuntimeDB) (source : SourcePrefix)
    (target : ValidatedPresentation) (runtimeBase : RuntimeProofState) :
    MachineAgrees db source target (emptyMachine source target)
      {runtimeBase with heap := #[], stack := #[]} :=
  { stackFormulas := []
    heapEntries := []
    stackAgreement := .nil
    heapAgreement := .nil
    stack_eq := rfl
    heap_eq := rfl
    stackRespects := Metamath.Kernel.stackRespectsFrame_empty db db.frame }

/-- One source header transition is exactly one verified implementation
`preload` transition, while hypothesis entries allocate explicit source DAG
leaves and assertion entries allocate schemas only. -/
noncomputable def headerStep_runtimePreserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    {item : HeaderItem}
    {before after : MachineState source target}
    (db : RuntimeDB)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore : RuntimeProofState)
    (step : HeaderStep item before after)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    Σ runtimeAfter,
      (db.preload runtimeBefore (headerRuntimeLabel item) =
        .ok runtimeAfter) ×'
      MachineAgrees db source target after runtimeAfter ×'
      runtimeAfter.incomplete = runtimeBefore.incomplete := by
  cases step with
  | mandatory before hypothesis member =>
      have hmemberRuntime :
          hypothesis ∈ source.toProjection.activeHypotheses := member
      obtain ⟨hscope, hfind⟩ :=
        projectedActiveHypothesis_database_fidelity
          db source.toProjection hypothesis hproject hmemberRuntime
      have runtimePreload :
          db.preload runtimeBefore hypothesis.label =
            .ok (runtimeBefore.pushHeap
              (.fmla hypothesis.formula.toRuntime)) := by
        simp only [Metamath.Verify.DB.preload, hfind, hscope]
        rfl
      let newNode : ProofNode source target :=
        { formula := hypothesis.formula
          tree := .active hypothesis member
          parents := [] }
      have newNodeLookup :
          (before.nodes ++ [newNode])[before.nodes.length]? = some newNode := by
        simp [newNode]
      refine
        ⟨runtimeBefore.pushHeap (.fmla hypothesis.formula.toRuntime),
          runtimePreload, ?_, rfl⟩
      refine
        { stackFormulas := agreement.stackFormulas
          heapEntries := agreement.heapEntries ++
            [.fmla hypothesis.formula.toRuntime]
          stackAgreement :=
            agreement.stackAgreement.weakenNodes (suffix := [newNode])
          heapAgreement :=
            (agreement.heapAgreement.weakenNodes
              (suffix := [newNode])).append
                (.cons
                  (.proof before.nodes.length newNode newNodeLookup) .nil)
          stack_eq := ?_
          heap_eq := ?_
          stackRespects := ?_ }
      · simp [Metamath.Verify.ProofState.pushHeap, agreement.stack_eq]
      · simp [Metamath.Verify.ProofState.pushHeap, agreement.heap_eq]
      · simpa [Metamath.Verify.ProofState.pushHeap] using
          agreement.stackRespects
  | explicitHypothesis before label hypothesis member label_eq =>
      subst label
      have hmemberRuntime :
          hypothesis ∈ source.toProjection.activeHypotheses := member
      obtain ⟨hscope, hfind⟩ :=
        projectedActiveHypothesis_database_fidelity
          db source.toProjection hypothesis hproject hmemberRuntime
      have runtimePreload :
          db.preload runtimeBefore hypothesis.label =
            .ok (runtimeBefore.pushHeap
              (.fmla hypothesis.formula.toRuntime)) := by
        simp only [Metamath.Verify.DB.preload, hfind, hscope]
        rfl
      let newNode : ProofNode source target :=
        { formula := hypothesis.formula
          tree := .active hypothesis member
          parents := [] }
      have newNodeLookup :
          (before.nodes ++ [newNode])[before.nodes.length]? = some newNode := by
        simp [newNode]
      refine
        ⟨runtimeBefore.pushHeap (.fmla hypothesis.formula.toRuntime),
          runtimePreload, ?_, rfl⟩
      refine
        { stackFormulas := agreement.stackFormulas
          heapEntries := agreement.heapEntries ++
            [.fmla hypothesis.formula.toRuntime]
          stackAgreement :=
            agreement.stackAgreement.weakenNodes (suffix := [newNode])
          heapAgreement :=
            (agreement.heapAgreement.weakenNodes
              (suffix := [newNode])).append
                (.cons
                  (.proof before.nodes.length newNode newNodeLookup) .nil)
          stack_eq := ?_
          heap_eq := ?_
          stackRespects := ?_ }
      · simp [Metamath.Verify.ProofState.pushHeap, agreement.stack_eq]
      · simp [Metamath.Verify.ProofState.pushHeap, agreement.heap_eq]
      · simpa [Metamath.Verify.ProofState.pushHeap] using
          agreement.stackRespects
  | explicitAssertion before label assertion member label_eq =>
      subst label
      have hmemberRuntime :
          assertion.toProjectionView ∈ source.toProjection.assertions := by
        change assertion.toProjectionView ∈
          source.assertions.map SourceAssertion.toProjectionView
        exact List.mem_map.mpr ⟨assertion, member, rfl⟩
      have hfind :
          db.find? assertion.label =
            some (.assert assertion.formula.toRuntime
              assertion.frame.toRuntime assertion.label) := by
        simpa [SourceAssertion.toProjectionView] using
          (projectedAssertion_database_fidelity db source.toProjection
            assertion.toProjectionView hproject hmemberRuntime).1
      have runtimePreload :
          db.preload runtimeBefore assertion.label =
            .ok (runtimeBefore.pushHeap
              (.assert assertion.formula.toRuntime
                assertion.frame.toRuntime)) := by
        simp only [Metamath.Verify.DB.preload, hfind]
        rfl
      refine
        ⟨runtimeBefore.pushHeap
            (.assert assertion.formula.toRuntime assertion.frame.toRuntime),
          runtimePreload, ?_, rfl⟩
      refine
        { stackFormulas := agreement.stackFormulas
          heapEntries := agreement.heapEntries ++
            [.assert assertion.formula.toRuntime assertion.frame.toRuntime]
          stackAgreement := agreement.stackAgreement
          heapAgreement := agreement.heapAgreement.append
            (.cons (.assertion assertion member) .nil)
          stack_eq := ?_
          heap_eq := ?_
          stackRespects := ?_ }
      · simp [Metamath.Verify.ProofState.pushHeap, agreement.stack_eq]
      · simp [Metamath.Verify.ProofState.pushHeap, agreement.heap_eq]
      · simpa [Metamath.Verify.ProofState.pushHeap] using
          agreement.stackRespects

/-- Ordered source header construction is preserved by the corresponding
ordered fold of verified implementation preloads. -/
noncomputable def headerBuild_runtimePreserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    {items : List HeaderItem}
    {before after : MachineState source target}
    (db : RuntimeDB)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore : RuntimeProofState)
    (build : HeaderBuild items before after)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    Σ runtimeAfter,
      ((items.map headerRuntimeLabel).foldlM
          (fun state label => db.preload state label) runtimeBefore =
        .ok runtimeAfter) ×'
      MachineAgrees db source target after runtimeAfter ×'
      runtimeAfter.incomplete = runtimeBefore.incomplete := by
  induction build generalizing runtimeBefore with
  | nil state =>
      exact ⟨runtimeBefore, rfl, agreement, rfl⟩
  | @cons item items before middle after head tail ih =>
      obtain ⟨runtimeMiddle, headStep, middleAgreement,
          middleIncomplete⟩ :=
        headerStep_runtimePreserved db hproject runtimeBefore head agreement
      obtain ⟨runtimeAfter, tailSteps, afterAgreement,
          afterIncomplete⟩ :=
        ih runtimeMiddle middleAgreement
      refine ⟨runtimeAfter, ?_, afterAgreement,
        afterIncomplete.trans middleIncomplete⟩
      · simp only [List.map_cons, List.foldlM_cons]
        rw [headStep]
        exact tailSteps

/-! ## Verified implementation steps -/

/-- A source proof-reference action is exactly `mm-lean4`'s compressed heap
lookup and push.  The resulting state relation retains the original source
node identity. -/
noncomputable def proofAction_preserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (before : MachineState source target)
    (runtimeBefore : RuntimeProofState)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : before.heap[index]? = some (.proof nodeId))
    (nodeLookup : before.nodes[nodeId]? = some node)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    (db.stepProof runtimeBefore index =
        .ok (runtimeBefore.push node.formula.toRuntime)) ×'
      MachineAgrees db source target
        {before with stack := before.stack ++ [nodeId]}
        (runtimeBefore.push node.formula.toRuntime) := by
  have runtimeHeapLookup :
      runtimeBefore.heap[index]? =
        some (.fmla node.formula.toRuntime) := by
    rw [agreement.heap_eq]
    simpa using agreement.heapAgreement.proofLookup
      index nodeId node heapLookup nodeLookup
  refine ⟨?_, ?_⟩
  · simp only [Metamath.Verify.DB.stepProof, runtimeHeapLookup]
    rfl
  · refine
      { stackFormulas := agreement.stackFormulas ++
          [node.formula.toRuntime]
        heapEntries := agreement.heapEntries
        stackAgreement := agreement.stackAgreement.append
          (.cons node nodeLookup .nil)
        heapAgreement := agreement.heapAgreement
        stack_eq := ?_
        heap_eq := ?_
        stackRespects := ?_ }
    · simp [Metamath.Verify.ProofState.push, agreement.stack_eq]
    · simp [Metamath.Verify.ProofState.push, agreement.heap_eq]
    · exact Metamath.Kernel.stackRespectsFrame_push
        db db.frame runtimeBefore.stack node.formula.toRuntime
        agreement.stackRespects
        (ProofNode.runtimeFormula_respects db hsource hproject node)

/-- Reflection for a compressed proof-reference action.  The runtime heap
success is tied to the already related source heap entry, so the recovered
transition retains the original proof-node identity. -/
noncomputable def proofAction_reflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (before : MachineState source target)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : before.heap[index]? = some (.proof nodeId))
    (nodeLookup : before.nodes[nodeId]? = some node)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (runtimeStep : db.stepProof runtimeBefore index = .ok runtimeAfter) :
    Σ sourceAfter : MachineState source target,
      ActionStep before (.step index) sourceAfter ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  obtain ⟨canonicalStep, nextAgreement⟩ :=
    proofAction_preserved db hsource hproject before runtimeBefore index
      nodeId node heapLookup nodeLookup agreement
  have runtimeAfterEq :
      runtimeAfter = runtimeBefore.push node.formula.toRuntime :=
    Except.ok.inj (runtimeStep.symm.trans canonicalStep)
  subst runtimeAfter
  exact
    ⟨{before with stack := before.stack ++ [nodeId]},
      .proof before index nodeId node heapLookup nodeLookup,
      nextAgreement⟩

/-- Canonical runtime state produced by one successful assertion heap entry. -/
def assertionResultState
    (runtimeBefore : RuntimeProofState) (assertion : SourceAssertion)
    (result : ConstantHeadedFormula) : RuntimeProofState :=
  { runtimeBefore with
    stack :=
      (runtimeBefore.stack.shrink
        (runtimeBefore.stack.size - assertion.frame.toRuntime.hyps.size)).push
          result.toRuntime }

/-- A source assertion occurrence and the verified implementation consume the
same ordered parent suffix and produce the same formula.  The source result
additionally allocates a fresh proof-occurrence identity whose exact parent
identities and unfolding remain in the DAG. -/
noncomputable def assertionAction_preserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (before : MachineState source target)
    (runtimeBefore : RuntimeProofState)
    (index : Nat) (assertion : SourceAssertion)
    {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula}
    {substitution : FiniteSubstitution}
    (retained parents : List Nat)
    (children : SourceGeneratedProvesForest source target actuals)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (stack_eq : before.stack = retained ++ parents)
    (node :
      GeneratedAssertionNode source.toProjection target
        assertion.toProjectionView actuals result substitution)
    (resolved : ResolvesForest before.nodes parents actuals children)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    let newNode : ProofNode source target :=
      { formula := result
        tree := .assertion member node children
        parents }
    let sourceAfter : MachineState source target :=
      { before with
        nodes := before.nodes ++ [newNode]
        stack := retained ++ [before.nodes.length] }
    let runtimeAfter := assertionResultState runtimeBefore assertion result
    (db.stepProof runtimeBefore index = .ok runtimeAfter) ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  dsimp only
  have hprojection :
      presentationOfProjection? source.toProjection = some target.1 := by
    rw [← presentationOfSourcePrefix?_eq_runtime]
    exact hsource
  have hmemberRuntime :
      assertion.toProjectionView ∈ source.toProjection.assertions := by
    change assertion.toProjectionView ∈
      source.assertions.map SourceAssertion.toProjectionView
    exact List.mem_map.mpr ⟨assertion, member, rfl⟩
  have indexedStack :
      StackEntriesAgree before.nodes (retained ++ parents)
        agreement.stackFormulas := by
    rw [← stack_eq]
    exact agreement.stackAgreement
  obtain ⟨retainedRuntime, parentRuntime, hstackFormulas,
      retainedAgreement, parentAgreement⟩ :=
    indexedStack.split retained parents
  have hparentRuntime :
      parentRuntime = actuals.map ConstantHeadedFormula.toRuntime :=
    parentAgreement.eq_runtimeMap_of_resolves resolved
  have hstackFormulas' :
      agreement.stackFormulas =
        retainedRuntime ++ actuals.map ConstantHeadedFormula.toRuntime := by
    calc
      agreement.stackFormulas = retainedRuntime ++ parentRuntime :=
        hstackFormulas
      _ = retainedRuntime ++
          actuals.map ConstantHeadedFormula.toRuntime := by
        rw [hparentRuntime]
  have runtimeStackEq :
      runtimeBefore.stack =
        (retainedRuntime ++
          actuals.map ConstantHeadedFormula.toRuntime).toArray := by
    rw [agreement.stack_eq, hstackFormulas']
  have hactualLength :
      actuals.length = assertion.toProjectionView.frame.hyps.size :=
    generatedAssertionNode_actuals_length_eq_frameHyps
      db source.toProjection target hprojection assertion.toProjectionView
        actuals result substitution node hproject hmemberRuntime
  have hoffset :
      runtimeBefore.stack.size -
          assertion.toProjectionView.frame.hyps.size =
        retainedRuntime.length := by
    rw [runtimeStackEq]
    simp [hactualLength]
  have hwindow :
      runtimeBefore.stack.extract
          (runtimeBefore.stack.size -
            assertion.toProjectionView.frame.hyps.size)
          runtimeBefore.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray := by
    have hoffsetImage :
        (retainedRuntime ++
            actuals.map ConstantHeadedFormula.toRuntime).toArray.size -
              assertion.toProjectionView.frame.hyps.size =
          retainedRuntime.length := by
      simpa [runtimeStackEq] using hoffset
    rw [runtimeStackEq, hoffsetImage]
    simp
  have hnode :
      Nonempty
        (Σ semanticSubstitution : FiniteSubstitution,
          GeneratedAssertionNode source.toProjection target
            assertion.toProjectionView actuals result
              semanticSubstitution) :=
    ⟨⟨substitution, node⟩⟩
  have hstepNormal :=
    (generatedAssertionNode_nonempty_iff_stepNormal
      db source.toProjection target hprojection assertion.toProjectionView
        runtimeBefore actuals result hproject hmemberRuntime hwindow
          agreement.stackRespects).mp hnode
  have hfind :
      db.find? assertion.label =
        some (.assert assertion.formula.toRuntime
          assertion.frame.toRuntime assertion.label) := by
    simpa [SourceAssertion.toProjectionView] using
      (projectedAssertion_database_fidelity
        db source.toProjection assertion.toProjectionView hproject
          hmemberRuntime).1
  have hstepAssert :
      db.stepAssert runtimeBefore assertion.formula.toRuntime
          assertion.frame.toRuntime =
        .ok (assertionResultState runtimeBefore assertion result) := by
    simpa [Metamath.Verify.DB.stepNormal, hfind,
      SourceAssertion.toProjectionView, assertionResultState] using
        hstepNormal
  have runtimeHeapLookup :
      runtimeBefore.heap[index]? =
        some (.assert assertion.formula.toRuntime
          assertion.frame.toRuntime) := by
    rw [agreement.heap_eq]
    simpa using agreement.heapAgreement.assertionLookup
      index assertion heapLookup
  refine ⟨?_, ?_⟩
  · simp only [Metamath.Verify.DB.stepProof, runtimeHeapLookup]
    exact hstepAssert
  · let newNode : ProofNode source target :=
      { formula := result
        tree := .assertion member node children
        parents }
    have newNodeLookup :
        (before.nodes ++ [newNode])[before.nodes.length]? = some newNode := by
      simp [newNode]
    have hshrink :
        runtimeBefore.stack.shrink
            (runtimeBefore.stack.size -
              assertion.toProjectionView.frame.hyps.size) =
          retainedRuntime.toArray := by
      rw [hoffset, runtimeStackEq]
      simp
    refine
      { stackFormulas := retainedRuntime ++ [result.toRuntime]
        heapEntries := agreement.heapEntries
        stackAgreement :=
          (retainedAgreement.weakenNodes (suffix := [newNode])).append
            (.cons newNode newNodeLookup .nil)
        heapAgreement :=
          agreement.heapAgreement.weakenNodes (suffix := [newNode])
        stack_eq := ?_
        heap_eq := ?_
        stackRespects := ?_ }
    · change
        (runtimeBefore.stack.shrink
          (runtimeBefore.stack.size -
            assertion.toProjectionView.frame.hyps.size)).push
              result.toRuntime =
          (retainedRuntime ++ [result.toRuntime]).toArray
      rw [hshrink]
      simp
    · simp [assertionResultState, agreement.heap_eq]
    · simpa [assertionResultState, SourceAssertion.toProjectionView] using
        generatedAssertionNode_stackResult_respects_callerFrame
          db source.toProjection target hprojection assertion.toProjectionView
            runtimeBefore.stack actuals result hproject hmemberRuntime hnode
              hwindow agreement.stackRespects

/-- Reflection for a successful assertion heap action.  The exact related
source stack is split at the assertion's mandatory-hypothesis arity; its
suffix already contains the consumed proof occurrences and therefore yields
the source children and parent identities without reconstructing either from
runtime formulas. -/
noncomputable def assertionAction_reflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (before : MachineState source target)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (index : Nat) (assertion : SourceAssertion)
    (heapLookup : before.heap[index]? = some (.assertion assertion))
    (member : assertion ∈ source.assertions)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (runtimeStep : db.stepProof runtimeBefore index = .ok runtimeAfter) :
    Σ sourceAfter : MachineState source target,
      ActionStep before (.step index) sourceAfter ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  have hprojection :
      presentationOfProjection? source.toProjection = some target.1 := by
    rw [← presentationOfSourcePrefix?_eq_runtime]
    exact hsource
  have hmemberRuntime :
      assertion.toProjectionView ∈ source.toProjection.assertions := by
    change assertion.toProjectionView ∈
      source.assertions.map SourceAssertion.toProjectionView
    exact List.mem_map.mpr ⟨assertion, member, rfl⟩
  have runtimeHeapLookup :
      runtimeBefore.heap[index]? =
        some (.assert assertion.formula.toRuntime
          assertion.frame.toRuntime) := by
    rw [agreement.heap_eq]
    simpa using agreement.heapAgreement.assertionLookup
      index assertion heapLookup
  have hstepAssert :
      db.stepAssert runtimeBefore assertion.formula.toRuntime
          assertion.frame.toRuntime = .ok runtimeAfter := by
    simpa only [Metamath.Verify.DB.stepProof, runtimeHeapLookup] using
      runtimeStep
  have hfind :
      db.find? assertion.label =
        some (.assert assertion.formula.toRuntime
          assertion.frame.toRuntime assertion.label) := by
    simpa [SourceAssertion.toProjectionView] using
      (projectedAssertion_database_fidelity db source.toProjection
        assertion.toProjectionView hproject hmemberRuntime).1
  have hstepNormal :
      db.stepNormal runtimeBefore assertion.label = .ok runtimeAfter := by
    simpa only [Metamath.Verify.DB.stepNormal, hfind] using hstepAssert
  have hgraph :
      AssertionLabelStepGraph db runtimeBefore assertion.label runtimeAfter :=
    (assertionLabelStepGraph_iff_stepNormal_ok_of_lookup
      db runtimeBefore runtimeAfter assertion.label
        assertion.formula.toRuntime assertion.frame.toRuntime assertion.label
          hfind).mpr hstepNormal
  let witness := Classical.choice hgraph
  have hobjects :
      some (Metamath.Verify.Object.assert witness.assertionFormula
        witness.assertionFrame witness.embeddedLabel) =
      some (Metamath.Verify.Object.assert assertion.formula.toRuntime
        assertion.frame.toRuntime assertion.label) := by
    rw [← witness.lookup, ← hfind]
  obtain ⟨hwitnessFormula, hwitnessFrame, _hwitnessEmbedded⟩ :=
    Metamath.Verify.Object.assert.inj (Option.some.inj hobjects)
  have hconclusionView := constantHeadedFormula_of_subst_ok
    assertion.formula witness.substitution witness.conclusion
      (by simpa [hwitnessFormula] using witness.formula_subst_ok)
  let result := Classical.choose hconclusionView
  have hconclusion : witness.conclusion = result.toRuntime :=
    Classical.choose_spec hconclusionView
  have hcountRuntime :
      assertion.frame.toRuntime.hyps.size ≤ runtimeBefore.stack.size := by
    calc
      assertion.frame.toRuntime.hyps.size =
          witness.assertionFrame.hyps.size := by rw [hwitnessFrame]
      _ ≤ runtimeBefore.stack.size := witness.stackEnough
  have hstackSize :
      runtimeBefore.stack.size = before.stack.length := by
    calc
      runtimeBefore.stack.size = agreement.stackFormulas.length := by
        rw [agreement.stack_eq]
        simp
      _ = before.stack.length := agreement.stackAgreement.length_eq.symm
  have hcountSource :
      assertion.frame.toRuntime.hyps.size ≤ before.stack.length := by
    simpa [hstackSize] using hcountRuntime
  obtain ⟨retained, parents, stackEq, parentLength⟩ :=
    splitSuffixIds before.stack
      assertion.frame.toRuntime.hyps.size hcountSource
  have indexedStack :
      StackEntriesAgree before.nodes (retained ++ parents)
        agreement.stackFormulas := by
    rw [← stackEq]
    exact agreement.stackAgreement
  obtain ⟨retainedRuntime, parentRuntime, hstackFormulas,
      retainedAgreement, parentAgreement⟩ :=
    indexedStack.split retained parents
  obtain ⟨actuals, children, hparentRuntime, resolved⟩ :=
    parentAgreement.toResolvedForest
  have hparentLengths := parentAgreement.length_eq
  have hparentRuntimeLengths := congrArg List.length hparentRuntime
  simp only [List.length_map] at hparentRuntimeLengths
  have hactualLength :
      actuals.length = assertion.frame.toRuntime.hyps.size := by
    omega
  have hstackFormulas' :
      agreement.stackFormulas =
        retainedRuntime ++
          actuals.map ConstantHeadedFormula.toRuntime := by
    calc
      agreement.stackFormulas = retainedRuntime ++ parentRuntime :=
        hstackFormulas
      _ = retainedRuntime ++
          actuals.map ConstantHeadedFormula.toRuntime := by
        rw [hparentRuntime]
  have runtimeStackEq :
      runtimeBefore.stack =
        (retainedRuntime ++
          actuals.map ConstantHeadedFormula.toRuntime).toArray := by
    rw [agreement.stack_eq, hstackFormulas']
  have hoffset :
      runtimeBefore.stack.size - assertion.frame.toRuntime.hyps.size =
        retainedRuntime.length := by
    rw [runtimeStackEq]
    simp [hactualLength]
  have hwindow :
      runtimeBefore.stack.extract
          (runtimeBefore.stack.size - assertion.frame.toRuntime.hyps.size)
          runtimeBefore.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray := by
    have hoffsetImage :
        (retainedRuntime ++
            actuals.map ConstantHeadedFormula.toRuntime).toArray.size -
              assertion.frame.toRuntime.hyps.size =
          retainedRuntime.length := by
      simpa [runtimeStackEq] using hoffset
    rw [runtimeStackEq, hoffsetImage]
    simp
  have runtimeAfterEq :
      runtimeAfter = assertionResultState runtimeBefore assertion result := by
    calc
      runtimeAfter =
          {runtimeBefore with
            stack := witness.stackPrefix.push witness.conclusion} :=
        witness.result_eq
      _ = assertionResultState runtimeBefore assertion result := by
        rw [witness.stackPrefix_eq, witness.offset_canonical,
          hwitnessFrame, hconclusion]
        rfl
  have hstepCanonical :
      db.stepNormal runtimeBefore assertion.label =
        .ok (assertionResultState runtimeBefore assertion result) := by
    simpa [runtimeAfterEq] using hstepNormal
  have hnodeNonempty :
      Nonempty
        (Σ substitution : FiniteSubstitution,
          GeneratedAssertionNode source.toProjection target
            assertion.toProjectionView actuals result substitution) :=
    (generatedAssertionNode_nonempty_iff_stepNormal
      db source.toProjection target hprojection assertion.toProjectionView
        runtimeBefore actuals result hproject hmemberRuntime
          (by simpa [SourceAssertion.toProjectionView] using hwindow)
          agreement.stackRespects).mpr hstepCanonical
  let selected := Classical.choice hnodeNonempty
  let substitution : FiniteSubstitution := selected.1
  let node : GeneratedAssertionNode source.toProjection target
      assertion.toProjectionView actuals result substitution := selected.2
  let newNode : ProofNode source target :=
    { formula := result
      tree := .assertion member node children
      parents }
  let sourceAfter : MachineState source target :=
    { before with
      nodes := before.nodes ++ [newNode]
      stack := retained ++ [before.nodes.length] }
  have sourceStep : ActionStep before (.step index) sourceAfter := by
    dsimp only [sourceAfter, newNode]
    exact .assertion before index assertion retained parents children
      heapLookup member stackEq node resolved
  obtain ⟨_canonicalStep, nextAgreement⟩ :=
    assertionAction_preserved db hsource hproject before runtimeBefore index
      assertion retained parents children heapLookup member stackEq node
        resolved agreement
  have nextAgreementRuntime :
      MachineAgrees db source target sourceAfter runtimeAfter := by
    rw [runtimeAfterEq]
    exact nextAgreement
  exact ⟨sourceAfter, sourceStep, nextAgreementRuntime⟩

/-- A source `Z` action is exactly `mm-lean4`'s save operation.  The runtime
heap copies the formula, while the source heap and save ledger retain the
identity of the reused proof node. -/
noncomputable def saveAction_preserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (before : MachineState source target)
    (runtimeBefore : RuntimeProofState)
    (nodeId : Nat) (node : ProofNode source target)
    (stackTop : before.stack.getLast? = some nodeId)
    (nodeLookup : before.nodes[nodeId]? = some node)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    (runtimeBefore.save =
        .ok (runtimeBefore.pushHeap (.fmla node.formula.toRuntime))) ×'
      MachineAgrees db source target
        { before with
          heap := before.heap ++ [.proof nodeId]
          saves := before.saves ++ [nodeId] }
        (runtimeBefore.pushHeap (.fmla node.formula.toRuntime)) := by
  have runtimeLast :
      agreement.stackFormulas.getLast? =
        some node.formula.toRuntime :=
    agreement.stackAgreement.getLast?_eq
      nodeId node stackTop nodeLookup
  have runtimeBack :
      runtimeBefore.stack.back? = some node.formula.toRuntime := by
    rw [agreement.stack_eq]
    simpa using runtimeLast
  refine ⟨?_, ?_⟩
  · simp only [Metamath.Verify.ProofState.save, runtimeBack]
    rfl
  · refine
      { stackFormulas := agreement.stackFormulas
        heapEntries := agreement.heapEntries ++
          [.fmla node.formula.toRuntime]
        stackAgreement := agreement.stackAgreement
        heapAgreement := agreement.heapAgreement.append
          (.cons (.proof nodeId node nodeLookup) .nil)
        stack_eq := ?_
        heap_eq := ?_
        stackRespects := ?_ }
    · simp [Metamath.Verify.ProofState.pushHeap, agreement.stack_eq]
    · simp [Metamath.Verify.ProofState.pushHeap, agreement.heap_eq]
    · simpa [Metamath.Verify.ProofState.pushHeap] using
        agreement.stackRespects

/-- Reflection for a successful `Z`.  Runtime formulas alone do not identify
occurrences, so the source node is recovered from the existing stack relation
before the source heap and save ledger are extended. -/
noncomputable def saveAction_reflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    (db : RuntimeDB)
    (before : MachineState source target)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (runtimeSave : runtimeBefore.save = .ok runtimeAfter) :
    Σ sourceAfter : MachineState source target,
      ActionStep before .save sourceAfter ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  cases runtimeBack : runtimeBefore.stack.back? with
  | none =>
      simp [Metamath.Verify.ProofState.save, runtimeBack] at runtimeSave
  | some runtimeFormula =>
      have runtimeLast :
          agreement.stackFormulas.getLast? = some runtimeFormula := by
        rw [agreement.stack_eq] at runtimeBack
        simpa using runtimeBack
      obtain ⟨nodeId, node, sourceLast, nodeLookup, formulaEq⟩ :=
        agreement.stackAgreement.runtimeLastSource runtimeFormula runtimeLast
      obtain ⟨canonicalSave, nextAgreement⟩ :=
        saveAction_preserved db before runtimeBefore nodeId node sourceLast
          nodeLookup agreement
      have runtimeAfterEq :
          runtimeAfter =
            runtimeBefore.pushHeap (.fmla node.formula.toRuntime) :=
        Except.ok.inj (runtimeSave.symm.trans canonicalSave)
      subst runtimeAfter
      exact
        ⟨{ before with
            heap := before.heap ++ [.proof nodeId]
            saves := before.saves ++ [nodeId] },
          .save before nodeId node sourceLast nodeLookup,
          nextAgreement⟩

/-! ## Compositional action-list preservation -/

/-- The named one-action function used to expose the fold performed by
`mm-lean4`.  It is definitionally the body of `applyCompressedActions`. -/
def runtimeAction
    (db : RuntimeDB) (runtimeState : RuntimeProofState) :
    ParserState.CompressedAction → Except ProofCheckFail RuntimeProofState
  | .step index => db.stepProof runtimeState index
  | .save =>
      match runtimeState.save with
      | .ok next => .ok next
      | .error error => .error (.compressedSave error)
  | .unknown =>
      if db.config.rejectUnknownSteps then
        .error (.proofCheck .unknownStepQuestionRejected)
      else
        .ok { runtimeState.push runtimeState.fmla with incomplete := true }

/-- Every successful verified implementation action reflects to a source
occurrence transition.  Heap dispatch is recovered through the exact related
entry, while `Z` recovers the top source identity.  Unknown actions are
excluded by the same source completeness condition used by theorem steps. -/
noncomputable def actionStep_runtimeReflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before : MachineState source target}
    {action : CompressedAction}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (actionVerified : action ≠ .unknown)
    (runtimeStep :
      runtimeAction db runtimeBefore (toMMLean4Action action) =
        .ok runtimeAfter) :
    Σ sourceAfter : MachineState source target,
      ActionStep before action sourceAfter ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  cases action with
  | step index =>
      have stepProof :
          db.stepProof runtimeBefore index = .ok runtimeAfter := by
        simpa [runtimeAction, toMMLean4Action] using runtimeStep
      cases runtimeEntryLookup : runtimeBefore.heap[index]? with
      | none =>
          simp [Metamath.Verify.DB.stepProof, runtimeEntryLookup] at stepProof
      | some runtimeEntry =>
          have runtimeListLookup :
              agreement.heapEntries[index]? = some runtimeEntry := by
            rw [agreement.heap_eq] at runtimeEntryLookup
            simpa using runtimeEntryLookup
          obtain ⟨sourceEntry, sourceLookup, entryAgreement⟩ :=
            agreement.heapAgreement.runtimeLookup index runtimeEntry
              runtimeListLookup
          cases entryAgreement with
          | proof nodeId node nodeLookup =>
              exact proofAction_reflected db hsource hproject before
                runtimeBefore runtimeAfter index nodeId node sourceLookup
                  nodeLookup agreement stepProof
          | assertion assertion member =>
              exact assertionAction_reflected db hsource hproject before
                runtimeBefore runtimeAfter index assertion sourceLookup member
                  agreement stepProof
  | save =>
      cases runtimeSave : runtimeBefore.save with
      | error error =>
          simp [runtimeAction, toMMLean4Action, runtimeSave] at runtimeStep
      | ok next =>
          have nextEq : next = runtimeAfter := by
            simpa [runtimeAction, toMMLean4Action, runtimeSave] using runtimeStep
          subst next
          exact saveAction_reflected db before runtimeBefore runtimeAfter
            agreement runtimeSave
  | unknown =>
      exact (actionVerified rfl).elim

theorem applyCompressedActions_eq_runtimeFold
    (db : RuntimeDB) (runtimeState : RuntimeProofState)
    (actions : List ParserState.CompressedAction) :
    ParserState.applyCompressedActions db runtimeState actions =
      actions.foldlM (runtimeAction db) runtimeState := by
  rfl

/-- Every single verified source action has a corresponding successful live
implementation action and an occurrence-preserving successor relation. -/
noncomputable def actionStep_runtimePreserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    {action : CompressedAction}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore : RuntimeProofState)
    (step : ActionStep before action after)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    Σ runtimeAfter,
      (runtimeAction db runtimeBefore (toMMLean4Action action) =
        .ok runtimeAfter) ×'
      MachineAgrees db source target after runtimeAfter ×'
      runtimeAfter.incomplete = runtimeBefore.incomplete := by
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      obtain ⟨runtimeStep, nextAgreement⟩ :=
        proofAction_preserved db hsource hproject before runtimeBefore
          index nodeId node heapLookup nodeLookup agreement
      exact
        ⟨runtimeBefore.push node.formula.toRuntime,
          by simpa [runtimeAction, toMMLean4Action] using runtimeStep,
          nextAgreement, rfl⟩
  | @assertion index assertion actuals result substitution retained
        parents children heapLookup member stack_eq node resolved =>
      obtain ⟨runtimeStep, nextAgreement⟩ :=
        assertionAction_preserved db hsource hproject before runtimeBefore
          index assertion retained parents children heapLookup member stack_eq
            node resolved agreement
      exact
        ⟨assertionResultState runtimeBefore assertion result,
          by simpa [runtimeAction, toMMLean4Action] using runtimeStep,
          nextAgreement, rfl⟩
  | save nodeId node stackTop nodeLookup =>
      obtain ⟨runtimeSave, nextAgreement⟩ :=
        saveAction_preserved db before runtimeBefore nodeId node stackTop
          nodeLookup agreement
      refine
        ⟨runtimeBefore.pushHeap (.fmla node.formula.toRuntime), ?_,
          nextAgreement, rfl⟩
      simp only [toMMLean4Action, runtimeAction]
      rw [runtimeSave]

/-- Structural induction over the source execution relation.  Each source
action is translated independently, so neither a final-formula shortcut nor
a token-ledger premise can enter the proof. -/
noncomputable def execute_runtimeFoldPreserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore : RuntimeProofState)
    (execution : Execute before actions after)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    Σ runtimeAfter,
      ((actions.map toMMLean4Action).foldlM (runtimeAction db)
          runtimeBefore = .ok runtimeAfter) ×'
      MachineAgrees db source target after runtimeAfter ×'
      runtimeAfter.incomplete = runtimeBefore.incomplete := by
  induction execution generalizing runtimeBefore with
  | nil state =>
      exact ⟨runtimeBefore, rfl, agreement, rfl⟩
  | @cons before middle after action actions head tail ih =>
      obtain ⟨runtimeMiddle, headStep, middleAgreement,
          middleIncomplete⟩ :=
        actionStep_runtimePreserved db hsource hproject runtimeBefore head
          agreement
      obtain ⟨runtimeAfter, tailSteps, afterAgreement,
          afterIncomplete⟩ :=
        ih runtimeMiddle middleAgreement
      refine ⟨runtimeAfter, ?_, afterAgreement,
        afterIncomplete.trans middleIncomplete⟩
      · simp only [List.map_cons, List.foldlM_cons]
        rw [headStep]
        exact tailSteps

/-- Full source-execution preservation stated against the shipped
`mm-lean4` compressed-action driver. -/
noncomputable def execute_mmLean4Preserved
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore : RuntimeProofState)
    (execution : Execute before actions after)
    (agreement : MachineAgrees db source target before runtimeBefore) :
    Σ runtimeAfter,
      (ParserState.applyCompressedActions db runtimeBefore
          (actions.map toMMLean4Action) = .ok runtimeAfter) ×'
      MachineAgrees db source target after runtimeAfter ×'
      runtimeAfter.incomplete = runtimeBefore.incomplete := by
  obtain ⟨runtimeAfter, runtimeSteps, afterAgreement,
      afterIncomplete⟩ :=
    execute_runtimeFoldPreserved db hsource hproject runtimeBefore execution
      agreement
  exact ⟨runtimeAfter,
    applyCompressedActions_eq_runtimeFold db runtimeBefore
      (actions.map toMMLean4Action) |>.trans runtimeSteps,
    afterAgreement, afterIncomplete⟩

/-- Reflection of an arbitrary successful runtime compressed-action fold.
Each step reconstructs its source occurrence before the induction proceeds,
so saved-node reuse and assertion-parent identities remain stable across the
whole program. -/
noncomputable def execute_runtimeFoldReflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before : MachineState source target}
    (actions : List CompressedAction)
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (verified : actionsVerified actions)
    (runtimeSteps :
      (actions.map toMMLean4Action).foldlM (runtimeAction db)
          runtimeBefore = .ok runtimeAfter) :
    Σ sourceAfter : MachineState source target,
      Execute before actions sourceAfter ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  induction actions generalizing before runtimeBefore runtimeAfter with
  | nil =>
      have runtimeOk :
          (Except.ok runtimeBefore :
            Except ProofCheckFail RuntimeProofState) =
              Except.ok runtimeAfter := by
        simpa [pure, Except.pure] using runtimeSteps
      have runtimeEq : runtimeBefore = runtimeAfter := by
        exact Except.ok.inj runtimeOk
      subst runtimeAfter
      exact ⟨before, .nil before, agreement⟩
  | cons action actions ih =>
      have headVerified : action ≠ .unknown :=
        verified action (by simp)
      have tailVerified : actionsVerified actions := by
        intro candidate member
        exact verified candidate (by simp [member])
      simp only [List.map_cons, List.foldlM_cons] at runtimeSteps
      cases headRuntime :
          runtimeAction db runtimeBefore (toMMLean4Action action) with
      | error error =>
          rw [headRuntime] at runtimeSteps
          simp only [bind, Except.bind] at runtimeSteps
          exact nomatch runtimeSteps
      | ok runtimeMiddle =>
          rw [headRuntime] at runtimeSteps
          have tailRuntime :
              (actions.map toMMLean4Action).foldlM (runtimeAction db)
                  runtimeMiddle = .ok runtimeAfter := by
            simpa [bind, Except.bind] using runtimeSteps
          obtain ⟨sourceMiddle, headStep, middleAgreement⟩ :=
            actionStep_runtimeReflected db hsource hproject runtimeBefore
              runtimeMiddle agreement headVerified headRuntime
          obtain ⟨sourceAfter, tailSteps, afterAgreement⟩ :=
            ih runtimeMiddle runtimeAfter middleAgreement tailVerified
              tailRuntime
          exact
            ⟨sourceAfter, .cons headStep tailSteps, afterAgreement⟩

/-- Full execution reflection stated against the shipped `mm-lean4`
compressed-action driver. -/
noncomputable def execute_mmLean4Reflected
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before : MachineState source target}
    (actions : List CompressedAction)
    (db : RuntimeDB)
    (hsource : presentationOfSourcePrefix? source = some target.1)
    (hproject : projectPrefix? db = some source.toProjection)
    (runtimeBefore runtimeAfter : RuntimeProofState)
    (agreement : MachineAgrees db source target before runtimeBefore)
    (verified : actionsVerified actions)
    (runtimeSteps :
      ParserState.applyCompressedActions db runtimeBefore
          (actions.map toMMLean4Action) = .ok runtimeAfter) :
    Σ sourceAfter : MachineState source target,
      Execute before actions sourceAfter ×'
      MachineAgrees db source target sourceAfter runtimeAfter := by
  apply execute_runtimeFoldReflected actions db hsource hproject
    runtimeBefore runtimeAfter agreement verified
  rw [← applyCompressedActions_eq_runtimeFold]
  exact runtimeSteps

/-! ## Complete compressed theorem preservation -/

/-- A singleton source stack fixes the exact singleton runtime stack while
retaining the source proof-node identity. -/
theorem MachineAgrees.singletonStack_eq
    {source : SourcePrefix} {target : ValidatedPresentation}
    {sourceState : MachineState source target}
    {runtimeState : RuntimeProofState}
    {db : RuntimeDB}
    (agreement : MachineAgrees db source target sourceState runtimeState)
    (nodeId : Nat) (node : ProofNode source target)
    (sourceStack : sourceState.stack = [nodeId])
    (nodeLookup : sourceState.nodes[nodeId]? = some node) :
    runtimeState.stack = #[node.formula.toRuntime] := by
  have indexed :
      StackEntriesAgree sourceState.nodes [nodeId]
        agreement.stackFormulas := by
    rw [← sourceStack]
    exact agreement.stackAgreement
  have hformulas :
      agreement.stackFormulas = [node.formula.toRuntime] :=
    indexed.singleton_eq node nodeLookup
  rw [agreement.stack_eq, hformulas]

/-- Proof-relevant implementation witness for one complete source compressed
theorem occurrence.  Header preload and compressed actions are both the
shipped `mm-lean4` functions; the final stack is tied to the exact source DAG
root, not merely to an independently supplied conclusion formula. -/
structure CompressedExecutionPreservation
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (db : RuntimeDB) (runtimeBase : RuntimeProofState)
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) : Type where
  runtimeInitial : RuntimeProofState
  runtimeFinal : RuntimeProofState
  headerExecution :
    ((headerItems before formula explicitHeaderLabels).map
        headerRuntimeLabel).foldlM
          (fun state sourceLabel => db.preload state sourceLabel)
          {runtimeBase with heap := #[], stack := #[]} =
      .ok runtimeInitial
  actionExecution :
    ParserState.applyCompressedActions db runtimeInitial
        (step.actions.map toMMLean4Action) =
      .ok runtimeFinal
  finalAgreement :
    MachineAgrees db before.toSourcePrefix step.target
      step.finalState runtimeFinal
  finalStack : runtimeFinal.stack = #[formula.toRuntime]
  finalIncomplete : runtimeFinal.incomplete = runtimeBase.incomplete

/-- Full preservation from a source compressed theorem occurrence into the
verified implementation's header and action machines.  The only database
premise is an exact projection of the same pre-insertion source prefix. -/
noncomputable def CompressedTheoremStep.mmLean4ExecutionPreserved
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (db : RuntimeDB)
    (hproject :
      projectPrefix? db = some before.toSourcePrefix.toProjection)
    (runtimeBase : RuntimeProofState) :
    CompressedExecutionPreservation db runtimeBase step := by
  let runtimeStart : RuntimeProofState :=
    {runtimeBase with heap := #[], stack := #[]}
  have startAgreement :
      MachineAgrees db before.toSourcePrefix step.target
        (emptyMachine before.toSourcePrefix step.target) runtimeStart :=
    emptyMachineAgrees db before.toSourcePrefix step.target runtimeBase
  obtain ⟨runtimeInitial, headerExecution, initialAgreement,
      headerIncomplete⟩ :=
    headerBuild_runtimePreserved db hproject runtimeStart step.header
      startAgreement
  obtain ⟨runtimeFinal, actionExecution, finalAgreement,
      actionIncomplete⟩ :=
    execute_mmLean4Preserved db step.presentation_eq hproject runtimeInitial
      step.execution initialAgreement
  have rootStack :
      runtimeFinal.stack = #[step.root.formula.toRuntime] :=
    finalAgreement.singletonStack_eq step.rootId step.root step.finalStack
      step.rootLookup
  have finalStack : runtimeFinal.stack = #[formula.toRuntime] := by
    rw [rootStack, step.rootFormula]
  exact
    { runtimeInitial
      runtimeFinal
      headerExecution := headerExecution
      actionExecution := actionExecution
      finalAgreement := finalAgreement
      finalStack := finalStack
      finalIncomplete := by
        simpa [runtimeStart] using actionIncomplete.trans headerIncomplete }

/-! ## Positive and negative representation boundaries -/

example {source : SourcePrefix} {target : ValidatedPresentation}
    (node : ProofNode source target) :
    StackEntriesAgree [node] [0] [node.formula.toRuntime] := by
  exact .cons node (by simp) .nil

/-- A source save cannot be represented as an assertion heap entry. -/
theorem proofEntry_not_assertion
    {source : SourcePrefix} {target : ValidatedPresentation}
    {nodes : List (ProofNode source target)}
    (nodeId : Nat) (assertion : SourceAssertion) :
    IsEmpty
      (HeapEntryAgrees nodes (.proof nodeId)
        (.assert assertion.formula.toRuntime assertion.frame.toRuntime)) := by
  constructor
  intro impossible
  cases impossible

end Mettapedia.Languages.Metamath.SourceGSLTCompressedExecutionMMLean4
