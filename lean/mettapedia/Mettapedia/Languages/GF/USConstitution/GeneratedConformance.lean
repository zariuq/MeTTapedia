import GFCore.Check
import Algorithms.GF.Generated.USConstitutionMainSig
import Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions
import Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

/-!
# US Constitution GF Witness Conformance

Checks the real ParseEng witnesses exported for selected original-main-text
Constitution fragments. The boundary is intentionally syntactic:
`ExportedTree → RawTerm → GFCore.check → CheckedExpr`.

Legal meaning is handled in `MainText.lean`, not smuggled into the grammar.
-/

namespace Mettapedia.Languages.GF.USConstitution.GeneratedConformance

open GFCore
open Mettapedia.Languages.GF.PGFWitnessIR
open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

def contextCorrectionIds :
    List Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionId :=
  Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.allCorrectionIds

def contextCorrectionParses
    (cid : Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionId) :
    List ExportedTree :=
  Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionParses cid

def contextCorrectionsForClause (cid : ClauseId) :
    List Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionId :=
  Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.correctionsForClause cid

def constitutionSig : GrammarSig :=
  Algorithms.GF.Generated.USConstitutionMainSig.sig

def checkTree (t : ExportedTree) : Except CheckError CheckedExpr :=
  checkFromFunsList Algorithms.GF.Generated.USConstitutionMainSig.funsList t.toRawTerm

def treeChecks (t : ExportedTree) : Bool :=
  match checkTree t with
  | .ok _ => true
  | .error _ => false

private def collectAcceptedTrees : List ClauseId → List ExportedTree
  | [] => []
  | cid :: rest => clauseParses cid ++ collectAcceptedTrees rest

def allAcceptedTrees : List ExportedTree :=
  collectAcceptedTrees allClauseIds

def allAcceptedTreesCheck : Bool :=
  allAcceptedTrees.all treeChecks

private def collectContextCorrectionTrees
    : List Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions.CorrectionId →
      List ExportedTree
  | [] => []
  | cid :: rest => contextCorrectionParses cid ++ collectContextCorrectionTrees rest

def allContextCorrectionTrees : List ExportedTree :=
  collectContextCorrectionTrees contextCorrectionIds

def allContextCorrectionTreesCheck : Bool :=
  allContextCorrectionTrees.all treeChecks

def acceptedClauseIds : List ClauseId :=
  allClauseIds.filter fun cid => 0 < acceptedParseCount cid

def failedClauseIds : List ClauseId :=
  allClauseIds.filter fun cid => acceptedParseCount cid = 0

def contextCorrectedFailedClauseIds : List ClauseId :=
  failedClauseIds.filter fun cid => 0 < (contextCorrectionsForClause cid).length

def contextUncorrectedFailedClauseIds : List ClauseId :=
  failedClauseIds.filter fun cid => (contextCorrectionsForClause cid).length = 0

def badUnknownRaw : RawTerm :=
  .leaf "__not_a_parseeng_function__"

def badWrongArityRaw : RawTerm :=
  .leaf "PhrUtt"

def badCategoryRaw : RawTerm :=
  .mk "UseN" #[.leaf "shall_VV"]

def badMetaHoleRaw : RawTerm :=
  .leaf "?"

def checkRaw (t : RawTerm) : Except CheckError CheckedExpr :=
  checkFromFunsList Algorithms.GF.Generated.USConstitutionMainSig.funsList t

def rawRejected (t : RawTerm) : Bool :=
  match checkRaw t with
  | .ok _ => false
  | .error _ => true

example : constitutionSig.sourceHash = sourceHash := rfl
example : allClauseIds.length = 21 := by native_decide
example : acceptedClauseIds.length = 18 := by native_decide
example : failedClauseIds.length = 3 := by native_decide
example : contextCorrectionIds.length = 4 := by native_decide
example : contextCorrectedFailedClauseIds.length = 3 := by native_decide
example : contextUncorrectedFailedClauseIds.length = 0 := by native_decide
example : rawRejected badUnknownRaw = true := by native_decide
example : rawRejected badWrongArityRaw = true := by native_decide
example : rawRejected badCategoryRaw = true := by native_decide
example : rawRejected badMetaHoleRaw = true := by native_decide

private def ensureBool (label : String) (b : Bool) : IO Unit :=
  if b then
    IO.println s!"PASS: {label}"
  else
    throw <| IO.userError s!"FAIL: {label}"

#eval do
  ensureBool "all accepted Constitution ParseEng witnesses pass GFCore.check" allAcceptedTreesCheck
  ensureBool "all context-completion witnesses pass GFCore.check" allContextCorrectionTreesCheck
  ensureBool "all exact ParseEng failures have context-completion coverage"
    (contextUncorrectedFailedClauseIds.isEmpty)
  ensureBool "unknown function is rejected" (rawRejected badUnknownRaw)
  ensureBool "wrong arity is rejected" (rawRejected badWrongArityRaw)
  ensureBool "category mismatch is rejected" (rawRejected badCategoryRaw)
  ensureBool "PGF meta hole is rejected" (rawRejected badMetaHoleRaw)

end Mettapedia.Languages.GF.USConstitution.GeneratedConformance
