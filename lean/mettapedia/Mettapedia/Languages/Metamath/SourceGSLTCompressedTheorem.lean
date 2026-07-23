import Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem

/-!
# Source-owned compressed Metamath proof occurrences

Compressed proofs are not identified with their normal-proof expansions.
Their byte actions, header layout, heap references, and `Z` saves form a
proof-relevant DAG.  Normal proof trees are retained only as the verified
unfolding of each DAG node.

The definitions in this file do not execute the `mm-lean4` compressed checker.
They give the authored source semantics against which `mm-lean4` and generated
native code can be proved to refine and reflect.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Metamath.Spec.Equivalence

/-! ## Exact Appendix-B action decoding -/

/-- One source-level compressed-proof action.  Indices are zero-based, as in
Appendix B and the verified implementation. -/
inductive CompressedAction where
  | step (index : Nat)
  | save
  | unknown
deriving DecidableEq, Repr

/-- Decode one byte while retaining the base-five accumulator between
compressed-word tokens. -/
def decodeByte (accumulator : Nat) (byte : UInt8) :
    Option (List CompressedAction × Nat) :=
  let code := byte.toNat
  if 65 ≤ code ∧ code ≤ 84 then
    some ([.step (20 * accumulator + (code - 65))], 0)
  else if 85 ≤ code ∧ code ≤ 89 then
    some ([], 5 * accumulator + (code - 84))
  else if code = 90 then
    some ([.save], 0)
  else if code = 63 then
    some ([.unknown], 0)
  else
    none

/-- Decode one lexical compressed-word token. -/
def decodeWord : List UInt8 → Nat →
    Option (List CompressedAction × Nat)
  | [], accumulator => some ([], accumulator)
  | byte :: bytes, accumulator => do
      let (headActions, nextAccumulator) ←
        decodeByte accumulator byte
      let (tailActions, finalAccumulator) ←
        decodeWord bytes nextAccumulator
      pure (headActions ++ tailActions, finalAccumulator)

/-- Decode a list of lexical compressed-word tokens.  Token boundaries are
retained in the input while the numeric accumulator crosses those boundaries,
as required by the source language. -/
def decodeWords : List (List UInt8) → Nat →
    Option (List CompressedAction × Nat)
  | [], accumulator => some ([], accumulator)
  | word :: words, accumulator => do
      let (headActions, nextAccumulator) ←
        decodeWord word accumulator
      let (tailActions, finalAccumulator) ←
        decodeWords words nextAccumulator
      pure (headActions ++ tailActions, finalAccumulator)

/-- A complete compressed program must finish outside a numeric index. -/
def decodeProgram (words : List (List UInt8)) :
    Option (List CompressedAction) := do
  let (actions, accumulator) ← decodeWords words 0
  if accumulator = 0 then
    some actions
  else
    none

def actionsVerified (actions : List CompressedAction) : Prop :=
  ∀ action ∈ actions, action ≠ .unknown

/-! Positive and negative decoder witnesses. -/

theorem decode_single_index :
    decodeProgram [[65]] = some [.step 0] := by
  decide

theorem decode_multibyte_index_across_words :
    decodeProgram [[85], [65]] = some [.step 20] := by
  decide

theorem decode_save_preserves_action_order :
    decodeProgram [[65, 90, 66]] =
      some [.step 0, .save, .step 1] := by
  decide

theorem decode_unknown_is_explicit :
    decodeProgram [[63]] = some [.unknown] := by
  decide

theorem decode_incomplete_index_rejected :
    decodeProgram [[85]] = none := by
  decide

theorem decode_noncode_byte_rejected :
    decodeProgram [[97]] = none := by
  decide

/-! ## Proof DAG carrier -/

/-- One topologically ordered proof node.  `parents` records the exact node
identities consumed by an assertion occurrence.  `tree` is its verified
normal unfolding, not its identity. -/
structure ProofNode (source : SourcePrefix)
    (target : ValidatedPresentation) where
  formula : ConstantHeadedFormula
  tree : SourceGeneratedProvesTree source target formula
  parents : List Nat

/-- Resolve an ordered list of parent identities to the exact proof forest
consumed by one assertion occurrence. -/
inductive ResolvesForest
    {source : SourcePrefix} {target : ValidatedPresentation}
    (nodes : List (ProofNode source target)) :
    (parents : List Nat) →
    (formulas : List ConstantHeadedFormula) →
    SourceGeneratedProvesForest source target formulas → Type where
  | nil : ResolvesForest nodes [] [] .nil
  | cons
      {parent : Nat} {parents : List Nat}
      {formulas : List ConstantHeadedFormula}
      (node : ProofNode source target)
      (forest : SourceGeneratedProvesForest source target formulas)
      (lookup : nodes[parent]? = some node)
      (tail : ResolvesForest nodes parents formulas forest) :
      ResolvesForest nodes
        (parent :: parents)
        (node.formula :: formulas)
        (.cons node.tree forest)

namespace ProofNode

/-- A node is valid relative to the strict prefix of nodes preceding it.
This is the acyclicity and parent-identity law for the source proof DAG. -/
inductive Valid
    {source : SourcePrefix} {target : ValidatedPresentation}
    (prior : List (ProofNode source target)) :
    ProofNode source target → Type where
  | active
      (hypothesis : HypothesisView)
      (member : hypothesis ∈ source.activeHypotheses) :
      Valid prior
        { formula := hypothesis.formula
          tree := .active hypothesis member
          parents := [] }
  | assertion
      {assertion : SourceAssertion}
      {actuals : List ConstantHeadedFormula}
      {result : ConstantHeadedFormula}
      {substitution : FiniteSubstitution}
      (member : assertion ∈ source.assertions)
      (node :
        GeneratedAssertionNode source.toProjection target
          assertion.toProjectionView actuals result substitution)
      (children : SourceGeneratedProvesForest source target actuals)
      (parents : List Nat)
      (resolved : ResolvesForest prior parents actuals children) :
      Valid prior
        { formula := result
          tree := .assertion member node children
          parents }

end ProofNode

/-- A complete topological validity witness for a proof-node list. -/
inductive DAGValid
    {source : SourcePrefix} {target : ValidatedPresentation} :
    List (ProofNode source target) → Type where
  | nil : DAGValid []
  | snoc
      {nodes : List (ProofNode source target)}
      {node : ProofNode source target}
      (prefixValid : DAGValid nodes)
      (last : node.Valid nodes) :
      DAGValid (nodes ++ [node])

/-! ## Header and machine state -/

/-- Heap entries either reuse a proof-node identity or name an authored
assertion schema. -/
inductive HeapEntry
    (source : SourcePrefix) where
  | proof (nodeId : Nat)
  | assertion (assertion : SourceAssertion)

/-- Source-owned compressed machine.  The stack and saved-receipt list contain
node identities, not copied proof trees. -/
structure MachineState
    (source : SourcePrefix) (target : ValidatedPresentation) where
  nodes : List (ProofNode source target)
  heap : List (HeapEntry source)
  stack : List Nat
  saves : List Nat

def emptyMachine
    (source : SourcePrefix) (target : ValidatedPresentation) :
    MachineState source target :=
  { nodes := []
    heap := []
    stack := []
    saves := [] }

inductive HeaderItem where
  | mandatory (hypothesis : HypothesisView)
  | explicit (label : String)

def headerItems (state : SourceState)
    (formula : ConstantHeadedFormula)
    (explicitLabels : List String) : List HeaderItem :=
  (mandatoryHypotheses state formula).map .mandatory ++
    explicitLabels.map .explicit

/-- One exact header-preload transition.  Hypotheses allocate leaf nodes;
assertions allocate schemas only. -/
inductive HeaderStep
    {source : SourcePrefix} {target : ValidatedPresentation} :
    HeaderItem →
    MachineState source target →
    MachineState source target → Type where
  | mandatory
      (before : MachineState source target)
      (hypothesis : HypothesisView)
      (member : hypothesis ∈ source.activeHypotheses) :
      HeaderStep (.mandatory hypothesis) before
        { before with
          nodes := before.nodes ++
            [{ formula := hypothesis.formula
               tree := .active hypothesis member
               parents := [] }]
          heap := before.heap ++ [.proof before.nodes.length] }
  | explicitHypothesis
      (before : MachineState source target)
      (label : String)
      (hypothesis : HypothesisView)
      (member : hypothesis ∈ source.activeHypotheses)
      (label_eq : hypothesis.label = label) :
      HeaderStep (.explicit label) before
        { before with
          nodes := before.nodes ++
            [{ formula := hypothesis.formula
               tree := .active hypothesis member
               parents := [] }]
          heap := before.heap ++ [.proof before.nodes.length] }
  | explicitAssertion
      (before : MachineState source target)
      (label : String)
      (assertion : SourceAssertion)
      (member : assertion ∈ source.assertions)
      (label_eq : assertion.label = label) :
      HeaderStep (.explicit label) before
        { before with
          heap := before.heap ++ [.assertion assertion] }

/-- Ordered header construction, beginning with mandatory hypotheses and then
the authored explicit label list. -/
inductive HeaderBuild
    {source : SourcePrefix} {target : ValidatedPresentation} :
    List HeaderItem →
    MachineState source target →
    MachineState source target → Type where
  | nil (state : MachineState source target) :
      HeaderBuild [] state state
  | cons
      {item : HeaderItem} {items : List HeaderItem}
      {before middle after : MachineState source target}
      (head : HeaderStep item before middle)
      (tail : HeaderBuild items middle after) :
      HeaderBuild (item :: items) before after

noncomputable def HeaderStep.preservesDAGValid
    {source : SourcePrefix} {target : ValidatedPresentation}
    {item : HeaderItem}
    {before after : MachineState source target}
    (step : HeaderStep item before after)
    (valid : DAGValid before.nodes) :
    DAGValid after.nodes := by
  cases step with
  | mandatory before hypothesis member =>
      exact .snoc valid (.active hypothesis member)
  | explicitHypothesis before label hypothesis member label_eq =>
      exact .snoc valid (.active hypothesis member)
  | explicitAssertion =>
      exact valid

noncomputable def HeaderBuild.preservesDAGValid
    {source : SourcePrefix} {target : ValidatedPresentation}
    {items : List HeaderItem}
    {before after : MachineState source target}
    (build : HeaderBuild items before after)
    (valid : DAGValid before.nodes) :
    DAGValid after.nodes := by
  induction build with
  | nil => exact valid
  | cons head tail ih =>
      exact ih (head.preservesDAGValid valid)

/-! ## Exact action execution -/

/-- One verified compressed action.  There is deliberately no constructor for
`unknown`: incomplete-proof admission is a distinct source judgment and cannot
manufacture a proof tree. -/
inductive ActionStep
    {source : SourcePrefix} {target : ValidatedPresentation} :
    MachineState source target →
    CompressedAction →
    MachineState source target → Type where
  | proof
      (before : MachineState source target)
      (index nodeId : Nat)
      (node : ProofNode source target)
      (heapLookup : before.heap[index]? = some (.proof nodeId))
      (nodeLookup : before.nodes[nodeId]? = some node) :
      ActionStep before (.step index)
        { before with stack := before.stack ++ [nodeId] }
  | assertion
      (before : MachineState source target)
      (index : Nat)
      (assertion : SourceAssertion)
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
      (resolved : ResolvesForest before.nodes parents actuals children) :
      ActionStep before (.step index)
        { before with
          nodes := before.nodes ++
            [{ formula := result
               tree := .assertion member node children
               parents }]
          stack := retained ++ [before.nodes.length] }
  | save
      (before : MachineState source target)
      (nodeId : Nat)
      (node : ProofNode source target)
      (stackTop : before.stack.getLast? = some nodeId)
      (nodeLookup : before.nodes[nodeId]? = some node) :
      ActionStep before .save
        { before with
          heap := before.heap ++ [.proof nodeId]
          saves := before.saves ++ [nodeId] }

inductive Execute
    {source : SourcePrefix} {target : ValidatedPresentation} :
    MachineState source target →
    List CompressedAction →
    MachineState source target → Type where
  | nil (state : MachineState source target) :
      Execute state [] state
  | cons
      {before middle after : MachineState source target}
      {action : CompressedAction} {actions : List CompressedAction}
      (head : ActionStep before action middle)
      (tail : Execute middle actions after) :
      Execute before (action :: actions) after

noncomputable def ActionStep.preservesDAGValid
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    {action : CompressedAction}
    (step : ActionStep before action after)
    (valid : DAGValid before.nodes) :
    DAGValid after.nodes := by
  cases step with
  | proof =>
      exact valid
  | assertion index assertion retained parents children heapLookup
      member stack_eq node resolved =>
      exact .snoc valid
        (.assertion member node children parents resolved)
  | save =>
      exact valid

noncomputable def Execute.preservesDAGValid
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (execution : Execute before actions after)
    (valid : DAGValid before.nodes) :
    DAGValid after.nodes := by
  induction execution with
  | nil => exact valid
  | cons head tail ih =>
      exact ih (head.preservesDAGValid valid)

theorem Execute.actions_verified
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (execution : Execute before actions after) :
    actionsVerified actions := by
  induction execution with
  | nil =>
      simp [actionsVerified]
  | cons head tail ih =>
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · cases head <;> simp
      · exact ih candidate member

/-- `Z` extends the heap with the same node identity; it neither copies nor
allocates a proof node. -/
theorem ActionStep.save_reuses_identity
    {source : SourcePrefix} {target : ValidatedPresentation}
    {before after : MachineState source target}
    (step : ActionStep before .save after) :
    ∃ nodeId node,
      before.stack.getLast? = some nodeId ∧
      before.nodes[nodeId]? = some node ∧
      after.nodes = before.nodes ∧
    after.heap = before.heap ++ [.proof nodeId] ∧
      after.saves = before.saves ++ [nodeId] := by
  cases step with
  | save nodeId node stackTop nodeLookup =>
      exact ⟨nodeId, node, stackTop, nodeLookup, rfl, rfl, rfl⟩

/-! ## Compressed theorem occurrence -/

/-- Proof-relevant semantics of one complete compressed `$p` occurrence. -/
structure CompressedTheoremStep
    (before after : SourceState)
    (label : String)
    (formula : ConstantHeadedFormula)
    (explicitHeaderLabels : List String)
    (bodyWords : List (List UInt8)) : Type where
  sourceValid : sourceStateValid before = true
  target : ValidatedPresentation
  presentation_eq :
    presentationOfSourcePrefix? before.toSourcePrefix = some target.1
  actions : List CompressedAction
  decoded : decodeProgram bodyWords = some actions
  initialState :
    MachineState before.toSourcePrefix target
  finalState :
    MachineState before.toSourcePrefix target
  header :
    HeaderBuild
      (headerItems before formula explicitHeaderLabels)
      (emptyMachine before.toSourcePrefix target)
      initialState
  execution : Execute initialState actions finalState
  rootId : Nat
  root : ProofNode before.toSourcePrefix target
  finalStack : finalState.stack = [rootId]
  rootLookup : finalState.nodes[rootId]? = some root
  rootFormula : root.formula = formula
  inserted : insertAssertion? before label formula = some after

def CompressedTheoremStep.operation
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (_ : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    SourceOperation :=
  .checkTheoremCompressed

def CompressedTheoremStep.rootTree
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    SourceGeneratedProvesTree
      before.toSourcePrefix step.target formula := by
  exact Eq.ndrec
    (motive := fun result =>
      SourceGeneratedProvesTree
        before.toSourcePrefix step.target result)
    step.root.tree step.rootFormula

theorem CompressedTheoremStep.actions_complete
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    actionsVerified step.actions :=
  step.execution.actions_verified

noncomputable def CompressedTheoremStep.finalDAGValid
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    DAGValid step.finalState.nodes := by
  exact step.execution.preservesDAGValid <|
    step.header.preservesDAGValid .nil

theorem CompressedTheoremStep.insertedAssertion
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    sourceAssertion before label formula ∈ after.assertions := by
  have shape := insertAssertion?_eq_some_shape step.inserted
  rw [shape.1]
  simp

/-- Source compressed execution unfolds to the independently defined
operational Metamath semantics. -/
theorem CompressedTheoremStep.toOperationalProvable
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (fallback : Metamath.Spec.Subst) :
    Metamath.Spec.Provable
      (sourceOperationalDatabase before.toSourcePrefix)
      (sourceOperationalCallerFrame before.toSourcePrefix)
      (operationalExpr formula) := by
  exact sourceTree_to_sourceOperationalProvable
    step.presentation_eq step.rootTree fallback

theorem CompressedTheoremStep.toSupportedDeclarative
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    SupportedProvable
      (sourceOperationalDatabase before.toSourcePrefix)
      (sourceOperationalCallerFrame before.toSourcePrefix)
      (exprToFormula
        (varMapOfFrame
          (sourceOperationalCallerFrame before.toSourcePrefix))
        (operationalExpr formula)) := by
  have respects :
      formulaSymbolsRespectFrame
          (floatingVariableNames
            before.toSourcePrefix.activeHypotheses)
          formula =
        true :=
    sourceTree_result_respects step.presentation_eq step.rootTree
  exact
    (sourceGeneratedProvesTree_nonempty_iff_supportedDeclarative
      before.toSourcePrefix step.target step.presentation_eq formula
        respects).mp
      ⟨step.rootTree⟩

theorem CompressedTheoremStep.toSemanticProvable
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords) :
    Metamath.Spec.Semantic.Provable
      (dbToAxioms
        (sourceOperationalDatabase before.toSourcePrefix))
      (frameToContext
        (sourceOperationalCallerFrame before.toSourcePrefix))
      (exprToFormula
        (varMapOfFrame
          (sourceOperationalCallerFrame before.toSourcePrefix))
        (operationalExpr formula)) := by
  exact step.toSupportedDeclarative.toSemantic

/-- Negative boundary: local declaration effects cannot witness compressed
theorem verification. -/
theorem compressedTheorem_not_local :
    SourceOperation.checkTheoremCompressed ∉ localOperations :=
  nonlocalOperations_absent.2.1

end Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
