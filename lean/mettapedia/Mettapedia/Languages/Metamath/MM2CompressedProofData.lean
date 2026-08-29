import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

/-!
# Compact source data for the MM2 compressed-proof verifier

This is a representation transform, not a decompressor and not a proof
checker.  It retains lexical proof words, derives the source-owned mandatory
header, and emits only linear-size cursor/allocation infrastructure.  The MM2
verifier remains responsible for decoding actions and checking proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState

inductive CompressedHeaderInput where
  | mandatory (hypothesis : HypothesisView)
  | explicit (label : String)
deriving DecidableEq

def compressedHeaderInputAtom : CompressedHeaderInput → Atom
  | .mandatory hypothesis =>
      .expression [.symbol "mm-compressed-header-mandatory",
        stringAtom hypothesis.label, formulaAtom hypothesis.formula]
  | .explicit label =>
      .expression [.symbol "mm-compressed-header-explicit",
        stringAtom label]

def compressedHeaderInputs (state : SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String) :
    List CompressedHeaderInput :=
  (mandatoryHypotheses state formula).map .mandatory ++
    explicitLabels.map .explicit

def compressedHeaderRows (proofOwner : Atom) (state : SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String) :
    List Atom :=
  linkedRows "compressed-header-item" proofOwner compressedHeaderInputAtom
    (compressedHeaderInputs state formula explicitLabels)

def compressedBodyRows (proofOwner : Atom)
    (bodyWords : List (List UInt8)) : List Atom :=
  indexedRows "compressed-body-word" proofOwner compressedWordAtom bodyWords

def compressedBodyByteCount (bodyWords : List (List UInt8)) : Nat :=
  (bodyWords.map List.length).sum

def compressedMandatoryCount (state : SourceState)
    (formula : ConstantHeadedFormula) : Nat :=
  (mandatoryHypotheses state formula).length

def compressedHeaderCount (state : SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String) : Nat :=
  compressedMandatoryCount state formula + explicitLabels.length

/-- Every byte can create at most one proof node; mandatory hypotheses create
one initial node each. -/
def compressedNodeCapacity (state : SourceState)
    (formula : ConstantHeadedFormula) (bodyWords : List (List UInt8)) : Nat :=
  compressedMandatoryCount state formula + compressedBodyByteCount bodyWords

/-- Header entries and `Z` saves occupy heap cells; the byte count is a safe
linear bound on the number of saves. -/
def compressedHeapCapacity (state : SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String)
    (bodyWords : List (List UInt8)) : Nat :=
  compressedHeaderCount state formula explicitLabels +
    compressedBodyByteCount bodyWords

/-- A proof byte can increase stack depth by at most one. -/
def compressedStackCapacity (bodyWords : List (List UInt8)) : Nat :=
  compressedBodyByteCount bodyWords + 1

/-- The normal assertion microkernel is index-polymorphic.  This view exposes
the compact stack successor spine under its ordinary stack-owner vocabulary,
without expanding any proof action. -/
def compressedNormalStackSuccessorRows (proofOwner : Atom)
    (count : Nat) : List Atom :=
  (List.range count).map fun position =>
    .expression
      [.symbol "mm-index-successor", proofOwner,
        (CompressedIndexCode.ofNat position).atom,
        (CompressedIndexCode.ofNat (position + 1)).atom]

structure CompressedProofDataArtifact where
  descriptor : Atom
  headerRows : List Atom
  headerEnd : Atom
  bodyRows : List Atom
  wordSuccessors : List Atom
  proofEnd : Atom
  heapSuccessors : List Atom
  nodeSuccessors : List Atom
  stackSuccessors : List Atom
  normalStackSuccessors : List Atom
  initialMachine : Atom
  initialHeaderControl : Atom
deriving DecidableEq

def CompressedProofDataArtifact.rows
    (artifact : CompressedProofDataArtifact) : List Atom :=
  artifact.descriptor ::
    (artifact.headerRows ++ [artifact.headerEnd] ++ artifact.bodyRows ++
      artifact.wordSuccessors ++ [artifact.proofEnd] ++
      artifact.heapSuccessors ++ artifact.nodeSuccessors ++
      artifact.stackSuccessors ++ artifact.normalStackSuccessors ++
      [artifact.initialMachine, artifact.initialHeaderControl])

def transformCompressedProofData
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    CompressedProofDataArtifact :=
  let headerCount := compressedHeaderCount state formula explicitLabels
  let zero := CompressedIndexCode.zero.atom
  { descriptor :=
      .expression
        [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "compressed",
          stringAtom theoremLabel, formulaAtom formula]
    headerRows := compressedHeaderRows proofOwner state formula explicitLabels
    headerEnd :=
      .expression
        [.symbol "mm-compressed-header-end", proofOwner, natAtom headerCount]
    bodyRows := compressedBodyRows proofOwner bodyWords
    wordSuccessors := indexSuccessorRows proofOwner bodyWords.length
    proofEnd :=
      .expression
        [.symbol "mm-proof-end", proofOwner, natAtom bodyWords.length]
    heapSuccessors :=
      compressedIndexSuccessorRows (compressedHeapOwner proofOwner)
        (compressedHeapCapacity state formula explicitLabels bodyWords)
    nodeSuccessors :=
      compressedIndexSuccessorRows (compressedNodeOwner proofOwner)
        (compressedNodeCapacity state formula bodyWords)
    stackSuccessors :=
      compressedIndexSuccessorRows (compressedStackOwner proofOwner)
        (compressedStackCapacity bodyWords)
    normalStackSuccessors :=
      compressedNormalStackSuccessorRows proofOwner
        (compressedStackCapacity bodyWords)
    initialMachine :=
      .expression
        [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
          zero, zero, zero]
    initialHeaderControl :=
      .expression
        [.symbol "mm-compressed-header-control", scopeOwner, proofOwner,
          natAtom 0] }

@[simp] theorem compressedHeaderInputs_length
    (state : SourceState) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) :
    (compressedHeaderInputs state formula explicitLabels).length =
      compressedHeaderCount state formula explicitLabels := by
  simp [compressedHeaderInputs, compressedHeaderCount,
    compressedMandatoryCount]

@[simp] theorem compressedHeaderRows_length
    (proofOwner : Atom) (state : SourceState)
    (formula : ConstantHeadedFormula) (explicitLabels : List String) :
    (compressedHeaderRows proofOwner state formula explicitLabels).length =
      compressedHeaderCount state formula explicitLabels := by
  simp [compressedHeaderRows]

@[simp] theorem compressedBodyRows_length
    (proofOwner : Atom) (bodyWords : List (List UInt8)) :
    (compressedBodyRows proofOwner bodyWords).length = bodyWords.length := by
  simp [compressedBodyRows, indexedRows]

/-- Even a very long compressed word remains one target data row. -/
theorem one_compressed_word_is_one_row
    (proofOwner : Atom) (word : List UInt8) :
    (compressedBodyRows proofOwner [word]).length = 1 := by
  simp

@[simp] theorem transformed_body_rows_exact
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).bodyRows =
        compressedBodyRows proofOwner bodyWords := by
  rfl

@[simp] theorem transformed_heap_successor_count
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).heapSuccessors.length =
        compressedHeapCapacity state formula explicitLabels bodyWords := by
  simp [transformCompressedProofData]

@[simp] theorem transformed_node_successor_count
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).nodeSuccessors.length =
        compressedNodeCapacity state formula bodyWords := by
  simp [transformCompressedProofData]

@[simp] theorem transformed_stack_successor_count
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).stackSuccessors.length =
        compressedStackCapacity bodyWords := by
  simp [transformCompressedProofData]

@[simp] theorem compressedNormalStackSuccessorRows_length
    (proofOwner : Atom) (count : Nat) :
    (compressedNormalStackSuccessorRows proofOwner count).length = count := by
  simp [compressedNormalStackSuccessorRows]

@[simp] theorem transformed_normal_stack_successor_count
    (scopeOwner proofOwner : Atom) (state : SourceState)
    (theoremLabel : String) (formula : ConstantHeadedFormula)
    (explicitLabels : List String) (bodyWords : List (List UInt8)) :
    (transformCompressedProofData scopeOwner proofOwner state theoremLabel
      formula explicitLabels bodyWords).normalStackSuccessors.length =
        compressedStackCapacity bodyWords := by
  simp [transformCompressedProofData]

#print axioms CompressedIndexCode.ofNat_value
#print axioms compressedIndexSuccessorRows_length
#print axioms compressedHeaderRows_length
#print axioms compressedBodyRows_length
#print axioms one_compressed_word_is_one_row
#print axioms transformed_body_rows_exact
#print axioms transformed_heap_successor_count
#print axioms transformed_node_successor_count
#print axioms transformed_stack_successor_count
#print axioms compressedNormalStackSuccessorRows_length
#print axioms transformed_normal_stack_successor_count

end Mettapedia.Languages.Metamath.MM2CompressedProofData
