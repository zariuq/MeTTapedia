import MeTTailCore
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
import Mettapedia.Languages.MeTTa.PeTTa.RewriteIRV2
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# PeTTa Rewrite IR Artifact Derivation

Program-parametric rewrite IR for PeTTa spaces. The source of truth is
`pettaSpaceToLangDef s`, matching the formal PeTTa rule compilation used in the
OSLF/GSLT bridge.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.RewriteIR

open MeTTailCore.MeTTaIL.RewriteIR
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.TransitionSpec
open Mettapedia.Languages.MeTTa.PeTTa

private def orderedUniq (xs : List String) : List String :=
  xs.eraseDups

private def orderedUniqNat (xs : List Nat) : List Nat :=
  xs.eraseDups

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private structure DerivedRule where
  ruleId : String
  ruleName : String
  sourceInstr : String
  sourceLabel : String
  priority : Nat
  leftRepr : String
  rightRepr : String
  premiseRelations : List String
  lhsJson : String
  rhsJson : String
  premisesJson : String
  lhsVars : List String
  premiseVarFlow : List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow
  rhsVars : List String
  rhsFreshVars : List String
  rhsEvalRequires : List String
  rootUpdate : Option MeTTailCore.MeTTaIL.RewriteIRV2.RootUpdateHint
deriving Repr

private def premiseRelations (rw : RewriteRule) : List String :=
  rw.premises.filterMap fun
    | .relationQuery rel _ => some rel
    | _ => none

private def premiseVars : Premise → List String
  | .freshness fc =>
      orderedUniq (fc.varName :: freeVars fc.term)
  | .congruence lhs rhs =>
      orderedUniq (freeVars lhs ++ freeVars rhs)
  | .relationQuery _ args =>
      orderedUniq (args.flatMap freeVars)

private def premiseVarFlowAux
    (seen : List String) (idx : Nat) :
    List Premise → List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow
  | [] => []
  | prem :: rest =>
      let vars := premiseVars prem
      let introduced := vars.filter (fun x => !(seen.contains x))
      { premiseIndex := idx
        premiseVars := vars
        introducedVars := introduced } ::
        premiseVarFlowAux (seen ++ introduced) (idx + 1) rest

private def derivePremiseVarFlow
    (lhsVars : List String) (premises : List Premise) :
    List MeTTailCore.MeTTaIL.RewriteIRV2.PremiseVarFlow :=
  premiseVarFlowAux lhsVars 0 premises

private def rootUpdateHint? :
    Pattern → Pattern → Option MeTTailCore.MeTTaIL.RewriteIRV2.RootUpdateHint
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
    (acc : List DerivedRule) : List DerivedRule :=
  match rules with
  | [] => acc
  | rw :: rest =>
      let key := sourceKeyOfPattern rw.left
      let premJsonList := rw.premises.map Premise.renderJson
      let lhsVars := orderedUniq (freeVars rw.left)
      let premiseVarFlow := derivePremiseVarFlow lhsVars rw.premises
      let available := orderedUniq (lhsVars ++ premiseVarFlow.flatMap (·.introducedVars))
      let rhsVars := orderedUniq (freeVars rw.right)
      let rhsEvalRequires := orderedUniq (rhsVars.filter (fun x => !(available.contains x)))
      let next := acc ++ [{ ruleId := s!"R{idx}"
                            ruleName := rw.name
                            sourceInstr := sourceInstrOfKey key
                            sourceLabel := sourceLabelOfKey key
                            priority := idx
                            leftRepr := reprStr rw.left
                            rightRepr := reprStr rw.right
                            premiseRelations := premiseRelations rw
                            lhsJson := rw.left.renderJson
                            rhsJson := rw.right.renderJson
                            premisesJson := "[" ++ String.intercalate "," premJsonList ++ "]"
                            lhsVars := lhsVars
                            premiseVarFlow := premiseVarFlow
                            rhsVars := rhsVars
                            rhsFreshVars := []
                            rhsEvalRequires := rhsEvalRequires
                            rootUpdate := rootUpdateHint? rw.left rw.right }]
      foldRewriteRules rest (idx + 1) next

private theorem foldRewriteRules_length
    (rules : List RewriteRule) (idx : Nat) (acc : List DerivedRule) :
    (foldRewriteRules rules idx acc).length = acc.length + rules.length := by
  induction rules generalizing idx acc with
  | nil =>
      simp [foldRewriteRules]
  | cons rw rest ih =>
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
          lhsJson := rw.left.renderJson
          rhsJson := rw.right.renderJson
          premisesJson := "[" ++ String.intercalate "," (rw.premises.map Premise.renderJson) ++ "]"
          lhsVars := orderedUniq (freeVars rw.left)
          premiseVarFlow := derivePremiseVarFlow (orderedUniq (freeVars rw.left)) rw.premises
          rhsVars := orderedUniq (freeVars rw.right)
          rhsFreshVars := []
          rhsEvalRequires :=
            let lhsVars := orderedUniq (freeVars rw.left)
            let premiseVarFlow := derivePremiseVarFlow lhsVars rw.premises
            let available := orderedUniq (lhsVars ++ premiseVarFlow.flatMap (·.introducedVars))
            orderedUniq ((orderedUniq (freeVars rw.right)).filter (fun x => !(available.contains x)))
          rootUpdate := rootUpdateHint? rw.left rw.right
        }]
      have hnext : (foldRewriteRules rest (idx + 1) next).length = next.length + rest.length :=
        ih (idx + 1) next
      calc
        (foldRewriteRules (rw :: rest) idx acc).length
            = (foldRewriteRules rest (idx + 1) next).length := by
                simp [foldRewriteRules, next]
        _ = next.length + rest.length := hnext
        _ = acc.length + (rest.length + 1) := by
              simp [next, List.length_append, Nat.add_left_comm, Nat.add_comm]

private def toArtifactRule (r : DerivedRule) : RewriteIRRule :=
  { ruleId := r.ruleId
    ruleName := r.ruleName
    sourceInstr := r.sourceInstr
    sourceLabel := r.sourceLabel
    priority := r.priority
    leftRepr := r.leftRepr
    rightRepr := r.rightRepr
    premiseRelations := r.premiseRelations
    lhsJson := some r.lhsJson
    rhsJson := some r.rhsJson
    premisesJson := some r.premisesJson
    lhsVars := r.lhsVars
    premiseVarFlow := r.premiseVarFlow
    rhsVars := r.rhsVars
    rhsFreshVars := r.rhsFreshVars
    rhsEvalRequires := r.rhsEvalRequires
    rootUpdate := r.rootUpdate }

def derivePeTTaRewriteIR? (s : PeTTaSpace) : Except String RewriteIRArtifact := do
  let lang := pettaSpaceToLangDef s
  let derived := foldRewriteRules lang.rewrites 0 []
  if derived.isEmpty then
    throw "PeTTa rewrite-ir derivation failed: space has no rewrite rules"
  let artifact : RewriteIRArtifact :=
    { schemaVersion := 2
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
