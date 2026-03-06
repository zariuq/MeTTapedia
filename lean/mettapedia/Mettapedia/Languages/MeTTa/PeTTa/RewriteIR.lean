import MeTTailCore
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec

/-!
# PeTTa Rewrite IR Artifact Derivation

Program-parametric rewrite IR for PeTTa spaces. The source of truth is
`pettaSpaceToLangDef s`, matching the formal PeTTa rule compilation used in the
OSLF/GSLT bridge.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.RewriteIR

open MeTTailCore.MeTTaIL.RewriteIR
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
open Mettapedia.Languages.MeTTa.PeTTa

private structure DerivedRule where
  ruleId : String
  ruleName : String
  sourceInstr : String
  sourceLabel : String
  priority : Nat
  leftRepr : String
  rightRepr : String
  premiseRelations : List String
deriving Repr

private def premiseRelations (rw : RewriteRule) : List String :=
  rw.premises.filterMap fun
    | .relationQuery rel _ => some rel
    | _ => none

private def foldRewriteRules
    (rules : List RewriteRule)
    (idx : Nat)
    (acc : List DerivedRule) : List DerivedRule :=
  match rules with
  | [] => acc
  | rw :: rest =>
      let key := sourceKeyOfPattern rw.left
      let next := acc ++ [{ ruleId := s!"R{idx}"
                            ruleName := rw.name
                            sourceInstr := sourceInstrOfKey key
                            sourceLabel := sourceLabelOfKey key
                            priority := idx
                            leftRepr := reprStr rw.left
                            rightRepr := reprStr rw.right
                            premiseRelations := premiseRelations rw }]
      foldRewriteRules rest (idx + 1) next

private theorem foldRewriteRules_length
    (rules : List RewriteRule) (idx : Nat) (acc : List DerivedRule) :
    (foldRewriteRules rules idx acc).length = acc.length + rules.length := by
  induction rules generalizing idx acc with
  | nil =>
      simp [foldRewriteRules]
  | cons rw rest ih =>
      simp [foldRewriteRules]
      let next :=
        acc ++ [{
          ruleId := s!"R{idx}"
          ruleName := rw.name
          sourceInstr := sourceInstrOfKey (sourceKeyOfPattern rw.left)
          sourceLabel := sourceLabelOfKey (sourceKeyOfPattern rw.left)
          priority := idx
          leftRepr := reprStr rw.left
          rightRepr := reprStr rw.right
          premiseRelations := premiseRelations rw
        }]
      calc
        (foldRewriteRules rest (idx + 1) next).length
            = next.length + rest.length := ih (idx + 1) next
        _ = acc.length + 1 + rest.length := by
              simp [next, List.length_append, Nat.add_assoc]
        _ = acc.length + (rest.length + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 rest.length]

private def toArtifactRule (r : DerivedRule) : RewriteIRRule :=
  { ruleId := r.ruleId
    ruleName := r.ruleName
    sourceInstr := r.sourceInstr
    sourceLabel := r.sourceLabel
    priority := r.priority
    leftRepr := r.leftRepr
    rightRepr := r.rightRepr
    premiseRelations := r.premiseRelations }

def derivePeTTaRewriteIR? (s : PeTTaSpace) : Except String RewriteIRArtifact := do
  let lang := pettaSpaceToLangDef s
  let derived := foldRewriteRules lang.rewrites 0 []
  if derived.isEmpty then
    throw "PeTTa rewrite-ir derivation failed: space has no rewrite rules"
  let artifact : RewriteIRArtifact :=
    { schemaVersion := 1
      dialect := "petta"
      rules := derived.map toArtifactRule }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"PeTTa rewrite-ir lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def exportPeTTaRewriteIR (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaRewriteIR? s with
  | .error err =>
      IO.println s!"petta rewrite-ir derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.rewrite_ir.json"
      let checksumPath := outDir / "petta.rewrite_ir.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported petta rewrite-ir artifact to {outDir}"
      pure 0

def checkPeTTaRewriteIR (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaRewriteIR? s with
  | .error err =>
      IO.println s!"petta rewrite-ir derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.rewrite_ir.json"
      let checksumPath := outDir / "petta.rewrite_ir.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] petta rewrite-ir artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] petta rewrite-ir artifacts mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"petta rewrite-ir artifact check failed: {e}"
        pure 2

theorem derivePeTTaRewriteIR_rule_count
    (s : PeTTaSpace) :
    (foldRewriteRules (pettaSpaceToLangDef s).rewrites 0 []).length = s.rules.length := by
  simpa [pettaSpaceToLangDef] using foldRewriteRules_length s.rules 0 []

private def sampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [{ name := "sample_rule"
         typeContext := []
         premises := []
         left := .apply "foo" [.fvar "X"]
         right := .apply "bar" [.fvar "X"] }] }

def sampleDerivationIsOk : Bool :=
  match derivePeTTaRewriteIR? sampleSpace with
  | .ok _ => true
  | .error _ => false

#guard sampleDerivationIsOk = true

end Mettapedia.Languages.MeTTa.PeTTa.RewriteIR
