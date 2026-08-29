import Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-!
# Derivation-generated compressed-proof occurrence ledger

The source compressed-proof machine intentionally stores proof nodes without
MM2 occurrence atoms.  This module computes the target occurrence decoration
from verified header and action execution.  The decoration is therefore not
an admitted side packet: callers can only obtain it by folding an existing
source execution witness.

The ledger is displayed over the source machine state by an exact length law.
Header hypothesis steps append their header position, assertion actions append
their action position and label, and proof lookups or saves append nothing.
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Target occurrence decoration displayed over one source machine state.
There is exactly one occurrence atom for every allocated source proof node. -/
structure NodeOccurrenceLedger
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (state : MachineState source target) where
  occurrences : List Atom
  aligned : occurrences.length = state.nodes.length

namespace NodeOccurrenceLedger

@[ext] theorem ext
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {state : MachineState source target}
    {left right : NodeOccurrenceLedger state}
    (equal : left.occurrences = right.occurrences) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Empty compressed execution has no proof-node occurrences. -/
def empty (source : SourcePrefix) (target : ValidatedCalculusLanguageDef) :
    NodeOccurrenceLedger (emptyMachine source target) :=
  ⟨[], rfl⟩

end NodeOccurrenceLedger

/-! ## Header fold -/

/-- One verified header transition computes its occurrence delta.  Mandatory
and explicit hypotheses allocate one node; explicit assertions allocate only
a heap schema and therefore leave the node ledger unchanged. -/
def HeaderStep.occurrenceLedger
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {item : HeaderItem} {before after : MachineState source target}
    (step : HeaderStep item before after) (proofOwner : Atom)
    (headerPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    NodeOccurrenceLedger after := by
  cases step with
  | mandatory before hypothesis member =>
      exact
        ⟨ledger.occurrences ++
            [compressedHeaderOccurrenceAtom proofOwner headerPosition],
          by simpa using congrArg Nat.succ ledger.aligned⟩
  | explicitHypothesis before mandatory label hypothesis member
      nonmandatory label_eq =>
      exact
        ⟨ledger.occurrences ++
            [compressedHeaderOccurrenceAtom proofOwner headerPosition],
          by simpa using congrArg Nat.succ ledger.aligned⟩
  | explicitAssertion before mandatory label assertion member
      nonmandatory label_eq =>
      exact ⟨ledger.occurrences, ledger.aligned⟩

/-- Ordered header construction computes its ledger while advancing the
header occurrence position once per authored item. -/
def HeaderBuild.occurrenceLedger
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {items : List HeaderItem} {before after : MachineState source target}
    (build : HeaderBuild items before after) (proofOwner : Atom)
    (headerPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    NodeOccurrenceLedger after :=
  match build with
  | .nil _ => ledger
  | .cons head tail =>
      HeaderBuild.occurrenceLedger tail proofOwner (headerPosition + 1)
        (HeaderStep.occurrenceLedger head proofOwner headerPosition ledger)

@[simp] theorem HeaderStep.mandatory_occurrenceLedger_occurrences
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (hypothesis : HypothesisView)
    (member : hypothesis ∈ source.activeHypotheses) (proofOwner : Atom)
    (headerPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    (HeaderStep.occurrenceLedger
      (HeaderStep.mandatory before hypothesis member)
      proofOwner headerPosition ledger).occurrences =
        ledger.occurrences ++
          [compressedHeaderOccurrenceAtom proofOwner headerPosition] := by
  rfl

@[simp] theorem HeaderStep.explicitAssertion_occurrenceLedger_occurrences
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target) (mandatory : List HypothesisView)
    (label : String) (assertion : SourceAssertion)
    (member : assertion ∈ source.assertions)
    (nonmandatory : label ∉ mandatory.map HypothesisView.label)
    (label_eq : assertion.label = label) (proofOwner : Atom)
    (headerPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    (HeaderStep.occurrenceLedger
      (HeaderStep.explicitAssertion before mandatory label assertion member
        nonmandatory label_eq)
      proofOwner headerPosition ledger).occurrences = ledger.occurrences := by
  rfl

/-! ## Action fold -/

/-- Heap information sufficient to compute occurrence allocation.  Proof
identities are irrelevant here; assertion labels are the only heap payload
that can allocate a new proof node. -/
inductive HeapOccurrenceKind where
  | proof
  | assertion (label : String)
deriving DecidableEq

def heapOccurrenceKinds {source : SourcePrefix} :
    List (HeapEntry source) → List HeapOccurrenceKind :=
  List.map fun entry =>
    match entry with
    | .proof _ => .proof
    | .assertion assertion => .assertion assertion.label

/-- Pure occurrence delta for one compressed action at one action position. -/
def actionOccurrenceAtoms (heap : List HeapOccurrenceKind)
    (action : CompressedAction) (proofPosition : Nat) : List Atom :=
  match action with
  | .save | .unknown => []
  | .step index =>
      match heap[index]? with
      | some (.assertion label) =>
          [compressedAssertionOccurrenceAtom proofPosition label]
      | _ => []

/-- Pure heap-shape transition.  Only `Z` changes the heap shape, by
appending a proof entry. -/
def advanceHeapOccurrenceKinds (heap : List HeapOccurrenceKind) :
    CompressedAction → List HeapOccurrenceKind
  | .save => heap ++ [.proof]
  | .step _ | .unknown => heap

/-- Every verified action transition has exactly the projected heap-shape
transition above. -/
theorem ActionStep.heapOccurrenceKinds_after
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {action : CompressedAction} (step : ActionStep before action after) :
    heapOccurrenceKinds after.heap =
      advanceHeapOccurrenceKinds (heapOccurrenceKinds before.heap) action := by
  cases step <;> simp [heapOccurrenceKinds, advanceHeapOccurrenceKinds]

/-- A verified source action computes the next displayed ledger. -/
def ActionStep.occurrenceLedger
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {action : CompressedAction} (step : ActionStep before action after)
    (proofPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    NodeOccurrenceLedger after := by
  refine
    ⟨ledger.occurrences ++
        actionOccurrenceAtoms (heapOccurrenceKinds before.heap) action
          proofPosition,
      ?_⟩
  cases step with
  | proof index nodeId node heapLookup nodeLookup =>
      simp [actionOccurrenceAtoms, heapOccurrenceKinds, heapLookup,
        ledger.aligned]
  | assertion index assertion retained parents children heapLookup
      member stack_eq node resolved =>
      simp [actionOccurrenceAtoms, heapOccurrenceKinds, heapLookup,
        ledger.aligned]
  | save nodeId node stackTop nodeLookup =>
      simp [actionOccurrenceAtoms, ledger.aligned]

/-- Complete verified action execution folds the displayed ledger. -/
def Execute.occurrenceLedger
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {actions : List CompressedAction} (execution : Execute before actions after)
    (proofPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    NodeOccurrenceLedger after :=
  match execution with
  | .nil _ => ledger
  | .cons head tail =>
      Execute.occurrenceLedger tail (proofPosition + 1)
        (ActionStep.occurrenceLedger head proofPosition ledger)

/-- Pure action-list fold used to expose that the occurrence ledger depends
on the initial heap shape and authored actions, not on proof-witness identity. -/
def executeOccurrenceAtoms (heap : List HeapOccurrenceKind) :
    List CompressedAction → Nat → List Atom → List Atom
  | [], _, occurrences => occurrences
  | action :: actions, proofPosition, occurrences =>
      executeOccurrenceAtoms (advanceHeapOccurrenceKinds heap action) actions
        (proofPosition + 1)
        (occurrences ++ actionOccurrenceAtoms heap action proofPosition)

/-- The derivation fold is exactly the pure action-list fold. -/
theorem Execute.occurrenceLedger_occurrences_eq_fold
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {actions : List CompressedAction} (execution : Execute before actions after)
    (proofPosition : Nat) (ledger : NodeOccurrenceLedger before) :
    (Execute.occurrenceLedger execution proofPosition ledger).occurrences =
      executeOccurrenceAtoms (heapOccurrenceKinds before.heap) actions
        proofPosition ledger.occurrences := by
  induction execution generalizing proofPosition with
  | nil => rfl
  | @cons before middle after action actions head tail induction =>
      rw [Execute.occurrenceLedger, induction]
      rw [ActionStep.heapOccurrenceKinds_after head]
      rfl

/-- Action-list determinacy: proof-relevant derivation witnesses cannot
smuggle a different occurrence decoration for the same execution problem. -/
theorem Execute.occurrenceLedger_deterministic
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (left right : Execute before actions after) (proofPosition : Nat)
    (ledger : NodeOccurrenceLedger before) :
    Execute.occurrenceLedger left proofPosition ledger =
      Execute.occurrenceLedger right proofPosition ledger := by
  apply NodeOccurrenceLedger.ext
  rw [Execute.occurrenceLedger_occurrences_eq_fold left,
    Execute.occurrenceLedger_occurrences_eq_fold right]

/-- Concatenation of verified executions. -/
def Execute.append
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before middle after : MachineState source target}
    {leftActions rightActions : List CompressedAction}
    (left : Execute before leftActions middle)
    (right : Execute middle rightActions after) :
    Execute before (leftActions ++ rightActions) after :=
  match left with
  | .nil _ => right
  | .cons head tail => .cons head (Execute.append tail right)

/-- Functoriality of the displayed ledger under execution composition. -/
theorem Execute.occurrenceLedger_append
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before middle after : MachineState source target}
    {leftActions rightActions : List CompressedAction}
    (left : Execute before leftActions middle)
    (right : Execute middle rightActions after) (proofPosition : Nat)
    (ledger : NodeOccurrenceLedger before) :
    Execute.occurrenceLedger (Execute.append left right) proofPosition ledger =
      Execute.occurrenceLedger right (proofPosition + leftActions.length)
        (Execute.occurrenceLedger left proofPosition ledger) := by
  induction left generalizing proofPosition with
  | nil => simp [Execute.append, Execute.occurrenceLedger]
  | @cons before middle after action actions head tail induction =>
      simp only [Execute.append, Execute.occurrenceLedger, List.length_cons]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        induction right (proofPosition + 1)
          (ActionStep.occurrenceLedger head proofPosition ledger)

/-- Canonical occurrence ledger of one complete admitted compressed theorem.
It starts from the empty source machine, folds the source-validated header,
then folds the decoded verified action execution. -/
def CompressedTheoremStep.occurrenceLedger
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (proofOwner : Atom) : NodeOccurrenceLedger step.finalState :=
  Execute.occurrenceLedger step.execution 0
    (HeaderBuild.occurrenceLedger step.header proofOwner 0
      (NodeOccurrenceLedger.empty before.toSourcePrefix step.target))

/-! ## Negative controls -/

/-- The same assertion label at adjacent action positions receives distinct
occurrence atoms.  Action position is therefore load-bearing. -/
theorem assertion_occurrence_changes_with_position
    (position : Nat) (label : String) :
    compressedAssertionOccurrenceAtom position label ≠
      compressedAssertionOccurrenceAtom (position + 1) label := by
  intro equal
  have atomsEqual := Atom.expression.inj equal
  have afterTag := (List.cons.inj atomsEqual).2
  have positionEqual := (List.cons.inj afterTag).1
  have codeEqual :=
    MM2CompressedIndexSpine.CanonicalIndexCode.atom_injective positionEqual
  have natEqual :=
    MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_injective codeEqual
  omega

/-- Saving a proof node changes heap identity but cannot invent a fresh node
occurrence. -/
theorem ActionStep.save_occurrenceLedger_unchanged
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    (step : ActionStep before .save after) (proofPosition : Nat)
    (ledger : NodeOccurrenceLedger before) :
    (ActionStep.occurrenceLedger step proofPosition ledger).occurrences =
      ledger.occurrences := by
  cases step
  simp [ActionStep.occurrenceLedger, actionOccurrenceAtoms]

#print axioms HeaderStep.mandatory_occurrenceLedger_occurrences
#print axioms HeaderStep.explicitAssertion_occurrenceLedger_occurrences
#print axioms ActionStep.heapOccurrenceKinds_after
#print axioms Execute.occurrenceLedger_occurrences_eq_fold
#print axioms Execute.occurrenceLedger_deterministic
#print axioms Execute.occurrenceLedger_append
#print axioms assertion_occurrence_changes_with_position
#print axioms ActionStep.save_occurrenceLedger_unchanged

end Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
