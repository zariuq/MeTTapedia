import Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
import Mettapedia.Languages.Metamath.MM2CompressedProofData

/-!
# Compressed proof data and finite cursor spine agreement

The compressed source-data transform reserves a finite heap cursor spine.
This module characterizes that emitted inventory exactly.  It does not claim
that rendering, parsing, or execution preserves the inventory; those are
separate target-boundary obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDataSpineAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
open Mettapedia.Languages.Metamath.MM2CompressedProofData
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- A natural-number-indexed compact successor row retains its source
position. -/
theorem compactSuccessorRowOfNat_injective (owner : Atom) :
    Function.Injective fun position =>
      compressedIndexSuccessorRow owner
        (CompressedIndexCode.ofNat position).atom
        (CompressedIndexCode.ofNat (position + 1)).atom := by
  intro left right equal
  have atomsEqual := Atom.expression.inj equal
  have currentEqual :
      (CompressedIndexCode.ofNat left).atom =
        (CompressedIndexCode.ofNat right).atom := by
    exact
      (List.cons.inj
        (List.cons.inj (List.cons.inj atomsEqual).2).2).1
  exact CanonicalIndexCode.ofNat_injective
    (CanonicalIndexCode.atom_injective currentEqual)

/-- Exact row-level characterization of the heap successor inventory emitted
by the source-data transform. -/
theorem mem_transformedHeapSuccessors_iff
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8))
    (row : Atom) :
    row ∈
        (transformCompressedProofData scopeOwner proofOwner state theoremLabel
          formula explicitLabels bodyWords).heapSuccessors ↔
      ∃ position < compressedHeapCapacity state formula explicitLabels bodyWords,
        row = compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat position).atom
          (CompressedIndexCode.ofNat (position + 1)).atom := by
  simpa only [transformCompressedProofData] using
    (mem_compressedIndexSuccessorRows_iff
      (compressedHeapOwner proofOwner) row
      (compressedHeapCapacity state formula explicitLabels bodyWords))

/-- A particular compact cursor edge is emitted exactly below the reserved
heap capacity. -/
theorem transformedHeapSuccessor_mem_iff
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8))
    (position : Nat) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat position).atom
          (CompressedIndexCode.ofNat (position + 1)).atom ∈
        (transformCompressedProofData scopeOwner proofOwner state theoremLabel
          formula explicitLabels bodyWords).heapSuccessors ↔
      position < compressedHeapCapacity state formula explicitLabels bodyWords := by
  constructor
  · intro member
    obtain ⟨other, bound, equal⟩ :=
      (mem_transformedHeapSuccessors_iff scopeOwner proofOwner state theoremLabel
        formula explicitLabels bodyWords _).1 member
    have positionEqual : position = other :=
      compactSuccessorRowOfNat_injective (compressedHeapOwner proofOwner) equal
    simpa only [positionEqual] using bound
  · intro bound
    apply
      (mem_transformedHeapSuccessors_iff scopeOwner proofOwner state theoremLabel
        formula explicitLabels bodyWords _).2
    exact ⟨position, bound, rfl⟩

/-- Every edge strictly below a live source heap frontier occurs in the
emitted reservation whenever that heap fits in the reservation. -/
theorem liveHeapCursor_mem_transformedHeapSuccessors
    {source : SourcePrefix}
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8))
    (heap : List (HeapEntry source))
    (heapFits :
      heap.length ≤ compressedHeapCapacity state formula explicitLabels bodyWords)
    (position : Nat) (live : position < heap.length) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat position).atom
          (CompressedIndexCode.ofNat (position + 1)).atom ∈
        (transformCompressedProofData scopeOwner proofOwner state theoremLabel
          formula explicitLabels bodyWords).heapSuccessors := by
  exact
    (transformedHeapSuccessor_mem_iff scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords position).2
      (lt_of_lt_of_le live heapFits)

/-- The live heap frontier has an emitted successor precisely when unused
reserved capacity remains.  Therefore absence of a successor row cannot be
the verifier's missing-reference test when reserve is nonzero. -/
theorem liveHeapFrontier_mem_transformedHeapSuccessors_iff
    {source : SourcePrefix}
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8))
    (heap : List (HeapEntry source)) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat heap.length).atom
          (CompressedIndexCode.ofNat (heap.length + 1)).atom ∈
        (transformCompressedProofData scopeOwner proofOwner state theoremLabel
          formula explicitLabels bodyWords).heapSuccessors ↔
      heap.length <
        compressedHeapCapacity state formula explicitLabels bodyWords := by
  exact transformedHeapSuccessor_mem_iff scopeOwner proofOwner state theoremLabel
    formula explicitLabels bodyWords heap.length

/-- The canonical code at position twenty has a nonempty reverse prefix, so
this control crosses the single-byte boundary. -/
theorem compactIndexTwenty_is_multibyte :
    (CompressedIndexCode.ofNat 20).reversePrefixDigits = [1] ∧
      (CompressedIndexCode.ofNat 20).terminalDigit = 0 := by
  decide

/-- Positive multi-byte control for the emitted artifact. -/
theorem transformedHeapSuccessors_contain_twenty
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8))
    (reserved :
      20 < compressedHeapCapacity state formula explicitLabels bodyWords) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat 20).atom
          (CompressedIndexCode.ofNat 21).atom ∈
        (transformCompressedProofData scopeOwner proofOwner state theoremLabel
          formula explicitLabels bodyWords).heapSuccessors := by
  exact
    (transformedHeapSuccessor_mem_iff scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords 20).2 reserved

/-- Negative control: no cursor edge begins at the reserved capacity. -/
theorem transformedHeapSuccessors_exclude_capacity
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    compressedIndexSuccessorRow (compressedHeapOwner proofOwner)
          (CompressedIndexCode.ofNat
            (compressedHeapCapacity state formula explicitLabels bodyWords)).atom
          (CompressedIndexCode.ofNat
            (compressedHeapCapacity state formula explicitLabels bodyWords + 1)).atom ∉
        (transformCompressedProofData scopeOwner proofOwner state theoremLabel
          formula explicitLabels bodyWords).heapSuccessors := by
  intro member
  have bound :=
    (transformedHeapSuccessor_mem_iff scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords
      (compressedHeapCapacity state formula explicitLabels bodyWords)).1 member
  omega

#print axioms compactSuccessorRowOfNat_injective
#print axioms mem_transformedHeapSuccessors_iff
#print axioms transformedHeapSuccessor_mem_iff
#print axioms liveHeapCursor_mem_transformedHeapSuccessors
#print axioms liveHeapFrontier_mem_transformedHeapSuccessors_iff
#print axioms compactIndexTwenty_is_multibyte
#print axioms transformedHeapSuccessors_contain_twenty
#print axioms transformedHeapSuccessors_exclude_capacity

end Mettapedia.Languages.Metamath.MM2CompressedProofDataSpineAgreement
