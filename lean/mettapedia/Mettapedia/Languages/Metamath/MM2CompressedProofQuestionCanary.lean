import Mettapedia.Languages.Metamath.MM2CompressedProofExecution

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofQuestionCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def scopeOwner : Atom := .symbol "compressed-question-scope"
def proofOwner : Atom := .symbol "compressed-question-proof"
def expectedFormula : Atom := .symbol "compressed-question-expected"
def theoremLabel : Atom := stringAtom "question-theorem"

def code (value : Nat) : Atom := (CompressedIndexCode.ofNat value).atom

def questionScan : Atom :=
  .expression
    [.symbol "mm-compressed-scan", scopeOwner, proofOwner, natAtom 0,
      compressedWordAtom [63], .symbol "mm-compressed-between-steps",
      listAtom natAtom []]

def machine : Atom :=
  .expression
    [.symbol "mm-compressed-machine", scopeOwner, proofOwner,
      code 0, code 0, code 0]

def descriptor : Atom :=
  .expression
    [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "compressed",
      theoremLabel, expectedFormula]

def questionOccurrence : Atom :=
  .expression
    [.symbol "mm-compressed-question-occurrence", proofOwner, natAtom 0,
      listAtom natAtom []]

def questionNode : Atom :=
  .expression
    [.symbol "mm-compressed-node", proofOwner, code 0, expectedFormula,
      questionOccurrence]

def incompleteMarker : Atom :=
  .expression
    [.symbol "mm-compressed-proof-incomplete", scopeOwner, proofOwner,
      natAtom 0, questionOccurrence]

def questionProgram : List Atom :=
  [compressedQuestionRule, questionScan, machine, descriptor,
    compressedQuestionAllowedPhaseRow
      (.symbol "mm-compressed-between-steps"),
    compressedIndexSuccessorRow (compressedNodeOwner proofOwner)
      (code 0) (code 1),
    compressedIndexSuccessorRow (compressedStackOwner proofOwner)
      (code 0) (code 1)] ++
    compressedScannerRuleCaptureRows

def questionFinal : List Atom :=
  cFireReflectiveSourceExecFact questionProgram compressedQuestionDirective

/-- The Metamath `?` action is not an invalid byte: it pushes the expected
formula as an explicitly incomplete proof occurrence inside MM2. -/
theorem question_pushes_expected_formula_and_marks_incomplete :
    questionNode ∈ questionFinal ∧ incompleteMarker ∈ questionFinal := by
  decide +kernel

#print axioms question_pushes_expected_formula_and_marks_incomplete

end Mettapedia.Languages.Metamath.MM2CompressedProofQuestionCanary
