import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSaveFaultCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def scopeOwner : Atom := .symbol "compressed-save-fault-scope"
def proofOwner : Atom := .symbol "compressed-save-fault-proof"

def disallowedSaveScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner, proofOwner, natAtom 0,
      compressedWordAtom [90], .symbol "mm-compressed-between-steps",
      listAtom natAtom []]

def savePlacementFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", scopeOwner, proofOwner, natAtom 0,
      .symbol "compressed-save-placement", natAtom 90,
      .symbol "mm-compressed-between-steps", listAtom natAtom []]

/-- `Z` is a postfix save, so it faults when no proof step immediately
precedes it. -/
theorem save_between_steps_faults :
    savePlacementFault ∈
      cFireReflectiveSourceExecFact
        [compressedSaveFaultRule, disallowedSaveScan,
          compressedSaveDisallowedPhaseRow
            (.symbol "mm-compressed-between-steps")]
        compressedSaveFaultDirective := by
  decide +kernel

#print axioms save_between_steps_faults

end Mettapedia.Languages.Metamath.MM2CompressedProofSaveFaultCanary
