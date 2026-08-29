import Mettapedia.Languages.Metamath.MM2CompressedProofQuestionCanary

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofQuestionOpenFaultCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofQuestionCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def openQuestionScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner,
      MM2CompressedProofQuestionCanary.proofOwner, natAtom 0,
      compressedWordAtom [63], .symbol "mm-compressed-open-index",
      listAtom natAtom [1]]

def openQuestionFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", scopeOwner,
      MM2CompressedProofQuestionCanary.proofOwner, natAtom 0,
      .symbol "compressed-question-in-open-index", natAtom 63,
      .symbol "mm-compressed-open-index", listAtom natAtom [1]]

/-- A question mark cannot interrupt a partially accumulated compact index. -/
theorem question_inside_open_index_faults :
    openQuestionFault ∈
      cFireReflectiveSourceExecFact
        [compressedQuestionOpenFaultRule, openQuestionScan]
        compressedQuestionOpenFaultDirective := by
  decide +kernel

#print axioms question_inside_open_index_faults

end Mettapedia.Languages.Metamath.MM2CompressedProofQuestionOpenFaultCanary
