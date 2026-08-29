import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofInvalidByteCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def scopeOwner : Atom := .symbol "compressed-invalid-scope"
def proofOwner : Atom := .symbol "compressed-invalid-proof"

def invalidScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner, proofOwner, natAtom 0,
      compressedWordAtom [33], .symbol "mm-compressed-between-steps",
      listAtom natAtom []]

def invalidFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", scopeOwner, proofOwner, natAtom 0,
      .symbol "compressed-invalid-byte", natAtom 33,
      .symbol "mm-compressed-between-steps", listAtom natAtom []]

def invalidProgram : List Atom :=
  [compressedInvalidByteRule, invalidScan, compressedInvalidByteRow 33]

/-- In the strict Appendix-B profile, a non-code byte becomes an explicit
proof-parse fault inside MM2. -/
theorem strict_invalid_byte_faults :
    invalidFault ∈
      cFireReflectiveSourceExecFact invalidProgram
        compressedInvalidByteDirective := by
  decide +kernel

/-- A valid terminal byte is absent from the invalid-byte classifier. -/
theorem terminal_A_is_not_invalid :
    compressedInvalidByteRow 65 ∉ compressedInvalidByteRows := by
  decide +kernel

#print axioms strict_invalid_byte_faults
#print axioms terminal_A_is_not_invalid

end Mettapedia.Languages.Metamath.MM2CompressedProofInvalidByteCanary
