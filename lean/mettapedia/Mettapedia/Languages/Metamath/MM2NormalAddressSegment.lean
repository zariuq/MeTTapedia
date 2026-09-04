import Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin

/-!
# Address-parametric normal assertion segments

The ordinary and compressed proof machines execute the same authored normal
assertion rules with different address representations.  This module records
the exact per-assertion address interface without changing the local
hypothesis, substitution, body, or disjoint-variable counters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalAddressSegment

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedIndexSpine
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2Transformation

/-- Addresses used by one normal assertion application.  Proof control has a
current and successor address; persistent stack and node identities are
injective encodings of their semantic natural-number positions. -/
structure NormalAddressSegment where
  currentProof : Atom
  nextProof : Atom
  stackAddress : Nat → Atom
  nodeAddress : Nat → Atom
  currentProof_ne_nextProof : currentProof ≠ nextProof
  stackAddress_injective : Function.Injective stackAddress
  nodeAddress_injective : Function.Injective nodeAddress

namespace NormalAddressSegment

def resultContext (segment : NormalAddressSegment) (scopeOwner : Atom)
    (assertionLabel resultTypecode : String) (stackBase : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-result-context", scopeOwner, segment.nextProof,
      stringAtom assertionLabel, stringAtom resultTypecode,
      segment.stackAddress stackBase, segment.stackAddress (stackBase + 1)]

def bodyBuiltRow (segment : NormalAddressSegment) (proofOwner scopeOwner : Atom)
    (assertionLabel resultTypecode : String) (stackBase : Nat)
    (resultBody : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-body-built", proofOwner, segment.currentProof,
      segment.resultContext scopeOwner assertionLabel resultTypecode stackBase,
      listAtom runtimeSymAtom resultBody]

def controlRow (segment : NormalAddressSegment) (scopeOwner proofOwner : Atom)
    (stackTop : Nat) : Atom :=
  .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner, segment.nextProof,
      segment.stackAddress stackTop]

def assertionOccurrence (segment : NormalAddressSegment)
    (assertionLabel : String) : Atom :=
  .expression
    [.symbol "mm-assertion-occurrence", segment.currentProof,
      stringAtom assertionLabel]

def assertionStackRow (segment : NormalAddressSegment) (proofOwner : Atom)
    (stackPosition : Nat) (resultTypecode : String)
    (resultBody : List Metamath.Verify.Sym) (assertionLabel : String) : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner,
      segment.stackAddress stackPosition,
      .expression
        [.symbol "mm-formula", stringAtom resultTypecode,
          listAtom runtimeSymAtom resultBody],
      segment.assertionOccurrence assertionLabel]

def linkedLabelRow (segment : NormalAddressSegment) (proofOwner : Atom)
    (assertionLabel : String) : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label", proofOwner,
      segment.currentProof, segment.nextProof, stringAtom assertionLabel]

def stackSuccessorRow (segment : NormalAddressSegment) (proofOwner : Atom)
    (stackPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-index-successor", proofOwner,
      segment.stackAddress stackPosition,
      segment.stackAddress (stackPosition + 1)]

def nodeSuccessorRow (segment : NormalAddressSegment) (proofOwner : Atom)
    (nodePosition : Nat) : Atom :=
  compressedIndexSuccessorRow (compressedNodeOwner proofOwner)
    (segment.nodeAddress nodePosition)
    (segment.nodeAddress (nodePosition + 1))

theorem assertionOccurrence_injective (segment : NormalAddressSegment) :
    Function.Injective segment.assertionOccurrence := by
  intro left right equal
  have fields := (List.cons.inj (Atom.expression.inj equal)).2
  exact stringAtom_injective (List.cons.inj (List.cons.inj fields).2).1

theorem assertionStackRow_occurrence_exact
    (segment : NormalAddressSegment) (proofOwner : Atom)
    (stackPosition : Nat) (resultTypecode : String)
    (resultBody : List Metamath.Verify.Sym) (assertionLabel : String) :
    segment.assertionStackRow proofOwner stackPosition resultTypecode resultBody
        assertionLabel =
      .expression
        [.symbol "mm-stack-cell", proofOwner,
          segment.stackAddress stackPosition,
          .expression
            [.symbol "mm-formula", stringAtom resultTypecode,
              listAtom runtimeSymAtom resultBody],
          segment.assertionOccurrence assertionLabel] := by
  rfl

end NormalAddressSegment

/-- Ordinary normal proof execution uses unary natural-number atoms for all
three address classes. -/
def ordinarySuccessorSegment (proofPosition : Nat) : NormalAddressSegment :=
  { currentProof := natAtom proofPosition
    nextProof := natAtom (proofPosition + 1)
    stackAddress := natAtom
    nodeAddress := natAtom
    currentProof_ne_nextProof := by
      intro equal
      have := natAtom_injective equal
      omega
    stackAddress_injective := natAtom_injective
    nodeAddress_injective := natAtom_injective }

/-- Compressed assertion execution keeps the scanner program counter as its
proof address and uses canonical compact codes for persistent positions. -/
def compressedResultSegment
    (context : NormalResultContext) : NormalAddressSegment :=
  { currentProof := context.pc
    nextProof := context.nextPC
    stackAddress := context.code
    nodeAddress := context.code
    currentProof_ne_nextProof := by
      intro equal
      have fields := Atom.expression.inj equal
      simp [NormalResultContext.pc] at fields
    stackAddress_injective := by
      intro left right equal
      exact CanonicalIndexCode.ofNat_injective
        (CanonicalIndexCode.atom_injective equal)
    nodeAddress_injective := by
      intro left right equal
      exact CanonicalIndexCode.ofNat_injective
        (CanonicalIndexCode.atom_injective equal) }

/-! ## Ordinary exactness -/

@[simp] theorem ordinary_resultContext_exact
    (scopeOwner : Atom) (proofPosition stackBase : Nat)
    (assertionLabel resultTypecode : String) :
    (ordinarySuccessorSegment proofPosition).resultContext scopeOwner
        assertionLabel resultTypecode stackBase =
      normalAssertionResultContextAtom scopeOwner (proofPosition + 1)
        assertionLabel resultTypecode stackBase (stackBase + 1) := by
  rfl

@[simp] theorem ordinary_bodyBuiltRow_exact
    (scopeOwner proofOwner : Atom) (proofPosition stackBase : Nat)
    (assertionLabel resultTypecode : String)
    (resultBody : List Metamath.Verify.Sym) :
    (ordinarySuccessorSegment proofPosition).bodyBuiltRow proofOwner scopeOwner
        assertionLabel resultTypecode stackBase resultBody =
      normalBodyBuiltAtom proofOwner proofPosition
        (normalAssertionResultContextAtom scopeOwner (proofPosition + 1)
          assertionLabel resultTypecode stackBase (stackBase + 1))
        resultBody := by
  rfl

@[simp] theorem ordinary_controlRow_exact
    (scopeOwner proofOwner : Atom) (proofPosition stackTop : Nat) :
    (ordinarySuccessorSegment proofPosition).controlRow scopeOwner proofOwner
        stackTop =
      normalControlAtom scopeOwner proofOwner (proofPosition + 1) stackTop := by
  rfl

@[simp] theorem ordinary_assertionStackRow_exact
    (proofOwner : Atom) (proofPosition stackPosition : Nat)
    (resultTypecode : String) (resultBody : List Metamath.Verify.Sym)
    (assertionLabel : String) :
    (ordinarySuccessorSegment proofPosition).assertionStackRow proofOwner
        stackPosition resultTypecode resultBody assertionLabel =
      normalAssertionStackAtom proofOwner stackPosition resultTypecode
        resultBody proofPosition assertionLabel := by
  rfl

/-! ## Compressed exactness -/

@[simp] theorem compressed_bodyBuiltRow_exact (context : NormalResultContext) :
    (compressedResultSegment context).bodyBuiltRow context.proofOwner
        context.scopeOwner context.assertionLabel context.resultTypecode
        context.stackBase context.resultBody = context.bodyBuiltRow := by
  rfl

@[simp] theorem compressed_controlRow_exact (context : NormalResultContext) :
    (compressedResultSegment context).controlRow context.scopeOwner
        context.proofOwner (context.stackBase + 1) =
      context.rejoinContext.returnedControlRow := by
  rfl

@[simp] theorem compressed_assertionOccurrence_exact
    (context : NormalResultContext) :
    (compressedResultSegment context).assertionOccurrence
        context.assertionLabel = context.rejoinContext.occurrence := by
  rfl

@[simp] theorem compressed_assertionStackRow_exact
    (context : NormalResultContext) :
    (compressedResultSegment context).assertionStackRow context.proofOwner
        context.stackBase context.resultTypecode context.resultBody
        context.assertionLabel = context.rejoinContext.returnedStackRow := by
  rfl

@[simp] theorem compressed_linkedLabelRow_exact
    (context : NormalResultContext) :
    (compressedResultSegment context).linkedLabelRow context.proofOwner
        context.assertionLabel = context.rejoinContext.normalLabelRow := by
  rfl

@[simp] theorem compressed_stackSuccessorRow_exact
    (context : NormalResultContext) :
    (compressedResultSegment context).stackSuccessorRow context.proofOwner
        context.stackBase = context.rejoinContext.normalStackSuccessorRow := by
  rfl

@[simp] theorem compressed_nodeSuccessorRow_exact
    (context : NormalResultContext) :
    (compressedResultSegment context).nodeSuccessorRow context.proofOwner
        context.nodeNext = context.rejoinContext.nodeSuccessorRow := by
  rfl

/-- Negative control: the compressed proof address cannot be confused with
the compact stack address at the same semantic number. -/
theorem compressed_currentProof_ne_stackAddress
    (context : NormalResultContext) :
    (compressedResultSegment context).currentProof ≠
      (compressedResultSegment context).stackAddress context.index := by
  simp [compressedResultSegment, NormalResultContext.pc,
    NormalResultContext.code]
  intro equal
  have decoded := congrArg CompressedIndexCode.decodeCompressedIndexCodeAtom equal
  rw [CompressedIndexCode.decodeCompressedIndexCodeAtom_atom] at decoded
  simp [CompressedIndexCode.decodeCompressedIndexCodeAtom] at decoded

section AxiomAudit

#print axioms NormalAddressSegment.assertionOccurrence_injective
#print axioms ordinary_resultContext_exact
#print axioms ordinary_bodyBuiltRow_exact
#print axioms ordinary_assertionStackRow_exact
#print axioms compressed_bodyBuiltRow_exact
#print axioms compressed_controlRow_exact
#print axioms compressed_assertionStackRow_exact
#print axioms compressed_currentProof_ne_stackAddress

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalAddressSegment
