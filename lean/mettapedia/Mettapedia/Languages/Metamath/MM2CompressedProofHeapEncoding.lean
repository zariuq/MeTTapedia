import Mettapedia.GSLT.Core.OccurrenceHeapProtocol
import Mettapedia.Languages.Metamath.MM2CompressedIndexSpine

/-!
# Occurrence-heap representation for compressed Metamath proofs

This module instantiates the reusable occurrence-heap protocol at the MM2
compressed-proof representation boundary.  It specifies rows only: the
abstract heap operation, MM2 rule execution, and source-proof adequacy remain
separate obligations.

Saving retains three independent coordinates: the fresh heap position, the
proof-node identity, and the source occurrence that produced the node.  Equal
formulas therefore do not collapse proof occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding

open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-- Payload retained behind an opaque compressed proof-node identity. -/
structure ProofNodeValue where
  formula : Atom
  sourceOccurrence : Atom
deriving DecidableEq

/-- The generic occurrence identity is the compact proof-node identifier. -/
abbrev ProofOccurrence := Occurrence Atom ProofNodeValue

/-- One position in the heterogeneous compressed-proof heap.  Non-proof
entries remain opaque here but still occupy their exact source index. -/
abbrev HeapEntry (Other : Type) := Entry Atom ProofNodeValue Other

/-- MM2 node row retaining formula and source occurrence. -/
def nodeRow (proofOwner : Atom) (occurrence : ProofOccurrence) : Atom :=
  .expression
    [.symbol "mm-compressed-node", proofOwner, occurrence.identity,
      occurrence.value.formula, occurrence.value.sourceOccurrence]

/-- MM2 heap row whose indexed entry points to the same proof-node identity. -/
def heapProofRow (proofOwner : Atom) (position : Nat)
    (occurrence : ProofOccurrence) : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", proofOwner,
      (CompressedIndexCode.ofNat position).atom, occurrence.identity]

/-- Verifier observation emitted by a successful `Z` save. -/
def saveReceiptRow (proofOwner : Atom) (position : Nat)
    (occurrence : ProofOccurrence) : Atom :=
  .expression
    [.symbol "mm-compressed-save-receipt", proofOwner,
      (CompressedIndexCode.ofNat position).atom, occurrence.identity,
      occurrence.value.sourceOccurrence]

/-! ## Encoder separation and inversion -/

/-- At a fixed owner, equality of compact heap-pointer rows recovers exactly
the source position and proof-node identity carried by those rows.  Formula
and source occurrence deliberately live in the separate node row. -/
theorem heapProofRow_eq_iff (proofOwner : Atom)
    (leftPosition rightPosition : Nat)
    (left right : ProofOccurrence) :
    heapProofRow proofOwner leftPosition left =
        heapProofRow proofOwner rightPosition right ↔
      leftPosition = rightPosition ∧ left.identity = right.identity := by
  constructor
  · intro equal
    have atomsEqual := Atom.expression.inj equal
    have afterTag := (List.cons.inj atomsEqual).2
    have afterOwner := (List.cons.inj afterTag).2
    have codeEqual := (List.cons.inj afterOwner).1
    have identityEqual := (List.cons.inj (List.cons.inj afterOwner).2).1
    exact
      ⟨CanonicalIndexCode.ofNat_injective
          (CanonicalIndexCode.atom_injective codeEqual),
        identityEqual⟩
  · rintro ⟨rfl, identityEqual⟩
    simp only [heapProofRow]
    rw [identityEqual]

/-- The node-payload row is injective in the complete proof occurrence:
identity, formula, and source occurrence all remain independently visible. -/
theorem nodeRow_injective (proofOwner : Atom) :
    Function.Injective (nodeRow proofOwner) := by
  rintro ⟨leftIdentity, leftValue⟩ ⟨rightIdentity, rightValue⟩ equal
  rcases leftValue with ⟨leftFormula, leftSourceOccurrence⟩
  rcases rightValue with ⟨rightFormula, rightSourceOccurrence⟩
  have atomsEqual := Atom.expression.inj equal
  have afterTag := (List.cons.inj atomsEqual).2
  have afterOwner := (List.cons.inj afterTag).2
  have identityEqual := (List.cons.inj afterOwner).1
  have afterIdentity := (List.cons.inj afterOwner).2
  have formulaEqual := (List.cons.inj afterIdentity).1
  have sourceOccurrenceEqual :=
    (List.cons.inj (List.cons.inj afterIdentity).2).1
  cases identityEqual
  cases formulaEqual
  cases sourceOccurrenceEqual
  rfl

/-- The paired heap-pointer and node-payload encoding is injective in both
the heap position and the complete proof occurrence.  This is the row-level
no-collapse fact needed by later representation reflection. -/
theorem heapProofAndNodeRows_injective (proofOwner : Atom) :
    Function.Injective fun value : Nat × ProofOccurrence =>
      (heapProofRow proofOwner value.1 value.2,
        nodeRow proofOwner value.2) := by
  intro left right equal
  have heapEqual := congrArg Prod.fst equal
  have nodeEqual := congrArg Prod.snd equal
  have occurrenceEqual := nodeRow_injective proofOwner nodeEqual
  have positionEqual :=
    (heapProofRow_eq_iff proofOwner left.1 right.1 left.2 right.2).mp
      heapEqual |>.1
  exact Prod.ext positionEqual occurrenceEqual

/-- Negative control: even the same proof occurrence cannot occupy two
different semantic heap positions while producing the same pointer row. -/
theorem heapProofRow_different_position
    (proofOwner : Atom) (leftPosition rightPosition : Nat)
    (occurrence : ProofOccurrence) (different : leftPosition ≠ rightPosition) :
    heapProofRow proofOwner leftPosition occurrence ≠
      heapProofRow proofOwner rightPosition occurrence := by
  intro equal
  exact different
    ((heapProofRow_eq_iff proofOwner leftPosition rightPosition occurrence
      occurrence).mp equal).1

/-- Occurrence-indexed heap rows starting at an explicit position. -/
def heapProofRowsFrom {Other : Type} (proofOwner : Atom) :
    Nat → List (HeapEntry Other) → List Atom
  | _, [] => []
  | position, .occurrence item :: remaining =>
      heapProofRow proofOwner position item ::
        heapProofRowsFrom proofOwner (position + 1) remaining
  | position, .opaque _ :: remaining =>
      heapProofRowsFrom proofOwner (position + 1) remaining

def heapProofRows {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) : List Atom :=
  heapProofRowsFrom proofOwner 0 heap

def nodeRows {Other : Type} (proofOwner : Atom) :
    List (HeapEntry Other) → List Atom
  | [] => []
  | .occurrence item :: remaining =>
      nodeRow proofOwner item :: nodeRows proofOwner remaining
  | .opaque _ :: remaining => nodeRows proofOwner remaining

/-- An occurrence found at an arbitrary heap index contributes its exact
position-shifted proof row to the encoded suffix. -/
theorem heapProofRow_mem_heapProofRowsFrom_of_getElem_occurrence
    {Other : Type} (proofOwner : Atom) (position index : Nat)
    (heap : List (HeapEntry Other)) (item : ProofOccurrence)
    (found : heap[index]? = some (.occurrence item)) :
    heapProofRow proofOwner (position + index) item ∈
      heapProofRowsFrom proofOwner position heap := by
  induction heap generalizing position index with
  | nil => simp at found
  | cons entry remaining induction =>
      cases index with
      | zero =>
          cases entry with
          | occurrence actual =>
              simp at found
              subst actual
              simp [heapProofRowsFrom]
          | «opaque» value => simp at found
      | succ index =>
          cases entry with
          | occurrence actual =>
              simp only [List.getElem?_cons_succ] at found
              simp only [heapProofRowsFrom, List.mem_cons]
              exact Or.inr (by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  induction (position + 1) index found)
          | «opaque» value =>
              simp only [List.getElem?_cons_succ] at found
              simp only [heapProofRowsFrom]
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                induction (position + 1) index found

/-- The same occurrence contributes its exact node payload row, independently
of preceding opaque heap occupants. -/
theorem nodeRow_mem_nodeRows_of_getElem_occurrence
    {Other : Type} (proofOwner : Atom) (index : Nat)
    (heap : List (HeapEntry Other)) (item : ProofOccurrence)
    (found : heap[index]? = some (.occurrence item)) :
    nodeRow proofOwner item ∈ nodeRows proofOwner heap := by
  induction heap generalizing index with
  | nil => simp at found
  | cons entry remaining induction =>
      cases index with
      | zero =>
          cases entry with
          | occurrence actual =>
              simp at found
              subst actual
              simp [nodeRows]
          | «opaque» value => simp at found
      | succ index =>
          cases entry with
          | occurrence actual =>
              simp only [List.getElem?_cons_succ] at found
              simp only [nodeRows, List.mem_cons]
              exact Or.inr (induction index found)
          | «opaque» value =>
              simp only [List.getElem?_cons_succ] at found
              exact induction index found

theorem heapProofRowsFrom_length_le {Other : Type} (proofOwner : Atom)
    (position : Nat) (heap : List (HeapEntry Other)) :
    (heapProofRowsFrom proofOwner position heap).length ≤ heap.length := by
  induction heap generalizing position with
  | nil => simp [heapProofRowsFrom]
  | cons entry remaining induction =>
      cases entry with
      | occurrence item => simp [heapProofRowsFrom, induction]
      | «opaque» value =>
          exact Nat.le.step (induction (position + 1))

theorem heapProofRows_length_le {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) :
    (heapProofRows proofOwner heap).length ≤ heap.length := by
  exact heapProofRowsFrom_length_le proofOwner 0 heap

/-- Appending one semantic occurrence appends exactly one fresh indexed MM2
heap row. -/
theorem heapProofRowsFrom_append_singleton {Other : Type} (proofOwner : Atom)
    (position : Nat) (heap : List (HeapEntry Other))
    (occurrence : ProofOccurrence) :
    heapProofRowsFrom proofOwner position
        (heap ++ [.occurrence occurrence]) =
      heapProofRowsFrom proofOwner position heap ++
        [heapProofRow proofOwner (position + heap.length) occurrence] := by
  induction heap generalizing position with
  | nil => simp [heapProofRowsFrom]
  | cons entry tail induction =>
      cases entry with
      | occurrence item =>
          simp only [List.cons_append, heapProofRowsFrom, List.length_cons,
            List.cons.injEq, true_and]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            induction (position + 1)
      | «opaque» value =>
          simp only [List.cons_append, heapProofRowsFrom, List.length_cons]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            induction (position + 1)

theorem heapProofRows_append_singleton {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) (occurrence : ProofOccurrence) :
    heapProofRows proofOwner (heap ++ [.occurrence occurrence]) =
      heapProofRows proofOwner heap ++
        [heapProofRow proofOwner heap.length occurrence] := by
  simpa [heapProofRows] using
    heapProofRowsFrom_append_singleton proofOwner 0 heap occurrence

@[simp] theorem nodeRows_append_singleton {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) (occurrence : ProofOccurrence) :
    nodeRows proofOwner (heap ++ [.occurrence occurrence]) =
      nodeRows proofOwner heap ++ [nodeRow proofOwner occurrence] := by
  induction heap with
  | nil => simp [nodeRows]
  | cons entry remaining induction =>
      cases entry <;> simp [nodeRows, induction]

/-- Exact MM2 representation delta of the abstract save transition.  No
normal-label expansion or proof checking occurs here. -/
structure SaveDelta where
  heapPosition : Nat
  heapRow : Atom
  nodeRow : Atom
  receiptRow : Atom
deriving DecidableEq

def encodeSaveDelta {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other))
    (occurrence : ProofOccurrence) : SaveDelta :=
  { heapPosition := heap.length
    heapRow := heapProofRow proofOwner heap.length occurrence
    nodeRow := nodeRow proofOwner occurrence
    receiptRow := saveReceiptRow proofOwner heap.length occurrence }

/-- Representation correctness for save: the row delta uses exactly the
position and occurrence appended by the semantic GSLT step. -/
theorem encodeSaveDelta_exact {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) (occurrence : ProofOccurrence) :
    (encodeSaveDelta proofOwner heap occurrence).heapPosition = heap.length ∧
    heapProofRows proofOwner (heap ++ [.occurrence occurrence]) =
      heapProofRows proofOwner heap ++
        [(encodeSaveDelta proofOwner heap occurrence).heapRow] ∧
    nodeRows proofOwner (heap ++ [.occurrence occurrence]) =
      nodeRows proofOwner heap ++
        [(encodeSaveDelta proofOwner heap occurrence).nodeRow] := by
  simp [encodeSaveDelta, heapProofRows_append_singleton]

/-- The saved heap pointer and receipt share the exact same node identity and
fresh position. -/
theorem encoded_save_reuses_identity {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) (occurrence : ProofOccurrence) :
    (encodeSaveDelta proofOwner heap occurrence).heapRow =
        heapProofRow proofOwner heap.length occurrence ∧
      (encodeSaveDelta proofOwner heap occurrence).receiptRow =
        saveReceiptRow proofOwner heap.length occurrence := by
  constructor <;> rfl

/-- Negative control: equal formulas from different source occurrences yield
different receipts. -/
theorem equal_formula_different_occurrence_receipts_differ :
    let owner : Atom := .symbol "proof-owner"
    let formula : Atom := .symbol "same-formula"
    let first : ProofOccurrence :=
      ⟨.symbol "node-0", ⟨formula, .symbol "occurrence-0"⟩⟩
    let second : ProofOccurrence :=
      ⟨.symbol "node-1", ⟨formula, .symbol "occurrence-1"⟩⟩
    saveReceiptRow owner 0 first ≠ saveReceiptRow owner 0 second := by
  decide

/-- The protocol's successful lookup-and-save path instantiates directly with
MM2 proof occurrences while remaining independent of byte scanning. -/
def lookupThenSaveProofPath {Other : Type} (proofOwner : Atom)
    (heap : List (HeapEntry Other)) (index : Nat)
    (occurrence : ProofOccurrence)
    (found : heap[index]? = some (.occurrence occurrence)) :
    (Mettapedia.GSLT.OccurrenceHeapProtocol.gslt
      Atom Atom ProofNodeValue Other).RewritePath
      ⟨proofOwner, heap, .lookup proofOwner index⟩
      ⟨proofOwner, heap ++ [.occurrence occurrence],
        .saved proofOwner heap.length occurrence⟩ :=
  lookupThenSavePath proofOwner heap index occurrence found

#print axioms heapProofRowsFrom_append_singleton
#print axioms heapProofRows_append_singleton
#print axioms heapProofRow_eq_iff
#print axioms nodeRow_injective
#print axioms heapProofAndNodeRows_injective
#print axioms heapProofRow_different_position
#print axioms heapProofRow_mem_heapProofRowsFrom_of_getElem_occurrence
#print axioms nodeRow_mem_nodeRows_of_getElem_occurrence
#print axioms encodeSaveDelta_exact
#print axioms encoded_save_reuses_identity
#print axioms equal_formula_different_occurrence_receipts_differ
#print axioms lookupThenSaveProofPath

end Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
