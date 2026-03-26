import MeTTailCore
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.OSLF.MeTTaIL.Substitution

namespace Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2

open MeTTailCore.MeTTaIL.RewriteIRV2
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec

private def orderedUniq (xs : List String) : List String :=
  xs.eraseDups

private def orderedUniqNat (xs : List Nat) : List Nat :=
  xs.eraseDups

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private def premiseVars : Premise → List String
  | .freshness fc =>
      orderedUniq (fc.varName :: freeVars fc.term)
  | .congruence lhs rhs =>
      orderedUniq (freeVars lhs ++ freeVars rhs)
  | .relationQuery _ args =>
      orderedUniq (args.flatMap freeVars)
  | .forAll collection param body =>
      orderedUniq (collection :: param :: premiseVars body)

private def premiseVarFlowAux
    (seen : List String) (idx : Nat) : List Premise → List PremiseVarFlow
  | [] => []
  | prem :: rest =>
      let vars := premiseVars prem
      let introduced := vars.filter (fun x => !(seen.contains x))
      { premiseIndex := idx
        premiseVars := vars
        introducedVars := introduced } ::
        premiseVarFlowAux (seen ++ introduced) (idx + 1) rest

private def derivePremiseVarFlow (lhsVars : List String) (premises : List Premise) :
    List PremiseVarFlow :=
  premiseVarFlowAux lhsVars 0 premises

private def rootUpdateHint? : Pattern → Pattern → Option RootUpdateHint
  | .apply lhsCtor lhsArgs, .apply rhsCtor rhsArgs =>
      let shared := Nat.min lhsArgs.length rhsArgs.length
      let positions := List.range shared
      let preserved := positions.filter (fun i => listGet? lhsArgs i = listGet? rhsArgs i)
      let changed := positions.filter (fun i => listGet? lhsArgs i ≠ listGet? rhsArgs i)
      some
        { lhsRootCtor := lhsCtor
          rhsRootCtor := rhsCtor
          lhsArity := lhsArgs.length
          rhsArity := rhsArgs.length
          preservedArgPositions := orderedUniqNat preserved
          changedArgPositions := orderedUniqNat changed }
  | _, _ => none

private def foldRewriteRules
    (rules : List RewriteRule)
    (idx : Nat)
    (acc : List RewriteIRV2Rule) : List RewriteIRV2Rule :=
  match rules with
  | [] => acc
  | rw :: rest =>
      let key := sourceKeyOfPattern rw.left
      let lhsVars := orderedUniq (freeVars rw.left)
      let flows := derivePremiseVarFlow lhsVars rw.premises
      let available := orderedUniq (lhsVars ++ flows.flatMap (·.introducedVars))
      let rhsVars := orderedUniq (freeVars rw.right)
      let rhsRequires := orderedUniq (rhsVars.filter (fun x => !(available.contains x)))
      let next := acc ++
        [{ ruleId := s!"R{idx}"
           ruleName := rw.name
           sourceInstr := sourceInstrOfKey key
           sourceLabel := sourceLabelOfKey key
           priority := idx
           lhsVars := lhsVars
           premiseVarFlow := flows
           rhsVars := rhsVars
           rhsRequires := rhsRequires
           rootUpdate := rootUpdateHint? rw.left rw.right }]
      foldRewriteRules rest (idx + 1) next

def derivePeTTaRewriteIRV2? (s : PeTTaSpace) : Except String RewriteIRV2Artifact := do
  let lang := pettaSpaceToLangDef s
  let derived := foldRewriteRules lang.rewrites 0 []
  if derived.isEmpty then
    throw "PeTTa rewrite-ir-v2 derivation failed: space has no rewrite rules"
  let artifact : RewriteIRV2Artifact :=
    { dialect := "petta"
      rules := derived }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"PeTTa rewrite-ir-v2 lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def exportPeTTaRewriteIRV2 (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaRewriteIRV2? s with
  | .error err =>
      IO.println s!"petta rewrite-ir-v2 derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.rewrite_ir_v2_draft.json"
      let checksumPath := outDir / "petta.rewrite_ir_v2_draft.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported petta rewrite-ir-v2 draft artifact to {outDir}"
      pure 0

def checkPeTTaRewriteIRV2 (outDir : System.FilePath) (s : PeTTaSpace) : IO UInt32 := do
  match derivePeTTaRewriteIRV2? s with
  | .error err =>
      IO.println s!"petta rewrite-ir-v2 derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "petta.rewrite_ir_v2_draft.json"
      let checksumPath := outDir / "petta.rewrite_ir_v2_draft.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] petta rewrite-ir-v2 draft artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] petta rewrite-ir-v2 draft artifacts mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"petta rewrite-ir-v2 draft artifact check failed: {e}"
        pure 2

private def sampleSpace : PeTTaSpace :=
  { facts := []
    rules :=
      [{ name := "sample_rule"
         typeContext := []
         premises := []
         left := .apply "foo" [.fvar "X"]
         right := .apply "bar" [.fvar "X"] }] }

def sampleDerivationIsOk : Bool :=
  match derivePeTTaRewriteIRV2? sampleSpace with
  | .ok _ => true
  | .error _ => false

#guard sampleDerivationIsOk = true

end Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2
