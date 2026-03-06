import MeTTailCore
import Mettapedia.Languages.IMP.LanguageDef

namespace Mettapedia.Languages.IMP.RewriteIR

open MeTTailCore.MeTTaIL.RewriteIR
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.IMP.LanguageDef

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

private def rewriteSourceLabel? (rw : RewriteRule) : Option String :=
  match rw.left with
  | .apply "Start" _ => some "Start"
  | .apply "ImpState" (.apply instrLabel _ :: _) => some instrLabel
  | _ => none

private def premiseRelations (rw : RewriteRule) : List String :=
  rw.premises.filterMap (fun
    | .relationQuery rel _ => some rel
    | _ => none)

private def foldRewriteRules
    (rules : List RewriteRule)
    (idx : Nat)
    (acc : List DerivedRule) : Except String (List DerivedRule) := do
  match rules with
  | [] => pure acc
  | rw :: rest =>
      let sourceLabel ←
        match rewriteSourceLabel? rw with
        | some lbl => pure lbl
        | none => throw s!"rewrite '{rw.name}' does not match Start(...) or ImpState(control, store, kont, status)"
      let next := acc ++ [{ ruleId := s!"R{idx}"
                            ruleName := rw.name
                            sourceInstr := s!"C_{sourceLabel}"
                            sourceLabel := sourceLabel
                            priority := idx
                            leftRepr := reprStr rw.left
                            rightRepr := reprStr rw.right
                            premiseRelations := premiseRelations rw }]
      foldRewriteRules rest (idx + 1) next

private def toArtifactRule (r : DerivedRule) : RewriteIRRule :=
  { ruleId := r.ruleId
    ruleName := r.ruleName
    sourceInstr := r.sourceInstr
    sourceLabel := r.sourceLabel
    priority := r.priority
    leftRepr := r.leftRepr
    rightRepr := r.rightRepr
    premiseRelations := r.premiseRelations }

def deriveIMPRewriteIR? : Except String RewriteIRArtifact := do
  let derived ← foldRewriteRules imp.rewrites 0 []
  let artifact : RewriteIRArtifact :=
    { schemaVersion := 1
      dialect := "imp"
      rules := derived.map toArtifactRule }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"IMP rewrite-ir lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveIMPRewriteIR? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportIMPRewriteIR (outDir : System.FilePath) : IO UInt32 := do
  match deriveIMPRewriteIR? with
  | .error err =>
      IO.println s!"imp rewrite-ir derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "imp.rewrite_ir.json"
      let checksumPath := outDir / "imp.rewrite_ir.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported imp rewrite-ir artifact to {outDir}"
      pure 0

def checkIMPRewriteIR (outDir : System.FilePath) : IO UInt32 := do
  match deriveIMPRewriteIR? with
  | .error err =>
      IO.println s!"imp rewrite-ir derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "imp.rewrite_ir.json"
      let checksumPath := outDir / "imp.rewrite_ir.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] imp rewrite-ir artifact matches at {outDir}"
          pure 0
        else
          IO.println s!"[drift] imp rewrite-ir artifact mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"imp rewrite-ir artifact check failed: {e}"
        pure 2

end Mettapedia.Languages.IMP.RewriteIR
