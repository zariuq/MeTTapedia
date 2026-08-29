import Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution

/-!
# Small semantic controls for compressed-proof header loading

These controls exercise one scheduled MM2 transition at a time.  They check
that hypothesis entries allocate both node and heap identities, assertion
entries allocate only a heap identity, duplicate mandatory labels fault before
an explicit entry can load, and body scanning begins only at the exact header
end.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def scopeOwner : Atom := .symbol "compressed-header-scope"
def proofOwner : Atom := .symbol "compressed-header-proof"
def hypothesisLabel : Atom := stringAtom "h"
def assertionLabel : Atom := stringAtom "ax"
def formula : Atom := .symbol "compressed-header-formula"

def code (value : Nat) : Atom :=
  (CompressedIndexCode.ofNat value).atom

def machine (heapNext nodeNext stackPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
      code heapNext, code nodeNext, code stackPosition]

def headerControl (position : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", scopeOwner, proofOwner,
      natAtom position]

def headerRow (position nextPosition : Nat) (payload : Atom) : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "compressed-header-item",
      proofOwner, natAtom position, natAtom nextPosition, payload]

def indexSuccessor (owner : Atom) (source target : Nat) : Atom :=
  compressedIndexSuccessorRow owner (code source) (code target)

def hypothesisLookup : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", scopeOwner, hypothesisLabel, formula]

def mandatoryPayload : Atom :=
  .expression
    [.symbol "mm-compressed-header-mandatory", hypothesisLabel, formula]

def explicitHypothesisPayload : Atom :=
  .expression
    [.symbol "mm-compressed-header-explicit", hypothesisLabel]

def explicitAssertionPayload : Atom :=
  .expression
    [.symbol "mm-compressed-header-explicit", assertionLabel]

def mandatoryProgram : List Atom :=
  compressedHeaderRules ++
    [headerControl 0, headerRow 0 1 mandatoryPayload, hypothesisLookup,
      machine 0 0 0,
      indexSuccessor (compressedHeapOwner proofOwner) 0 1,
      indexSuccessor (compressedNodeOwner proofOwner) 0 1]

def mandatoryFinal : List Atom :=
  cFireReflectiveSourceExecFact mandatoryProgram
    compressedHeaderMandatoryDirective

def mandatoryNode : Atom :=
  .expression
    [.symbol "mm-compressed-node", proofOwner, code 0, formula,
      .expression
        [.symbol "mm-compressed-header-occurrence", proofOwner, natAtom 0]]

def mandatoryHeap : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", proofOwner, code 0, code 0]

def mandatoryMarker : Atom :=
  .expression
    [.symbol "mm-compressed-mandatory-label", proofOwner, hypothesisLabel]

def assertionHeader : Atom :=
  .expression
    [.symbol "mm-assertion-header", scopeOwner, natAtom 7, assertionLabel,
      natAtom 2]

def assertionProgram : List Atom :=
  compressedHeaderRules ++
    [headerControl 0, headerRow 0 1 explicitAssertionPayload,
      assertionHeader, machine 0 0 0,
      indexSuccessor (compressedHeapOwner proofOwner) 0 1]

def assertionFinal : List Atom :=
  cFireReflectiveSourceExecFact assertionProgram
    compressedHeaderExplicitAssertionDirective

def assertionHeap : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", proofOwner, code 0, natAtom 7,
      assertionLabel]

def duplicateProgram : List Atom :=
  compressedHeaderRules ++
    [headerControl 0, headerRow 0 1 explicitHypothesisPayload,
      hypothesisLookup, mandatoryMarker, machine 0 0 0,
      indexSuccessor (compressedHeapOwner proofOwner) 0 1,
      indexSuccessor (compressedNodeOwner proofOwner) 0 1]

def duplicateFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", scopeOwner, proofOwner, natAtom 0,
      .symbol "compressed-duplicate-mandatory-label", hypothesisLabel,
      hypothesisLabel, hypothesisLabel]

def headerEnd (position : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-header-end", proofOwner, natAtom position]

def bodyControl : Atom :=
  .expression
    [.symbol "mm-compressed-control", scopeOwner, proofOwner, natAtom 0,
      code 0]

def finishProgram (endPosition : Nat) : List Atom :=
  compressedHeaderRules ++
    [headerControl 0, headerEnd endPosition, machine 0 0 0]

end Mettapedia.Languages.Metamath.MM2CompressedProofHeaderCanary
