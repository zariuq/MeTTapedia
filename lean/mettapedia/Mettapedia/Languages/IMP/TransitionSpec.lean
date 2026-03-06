import MeTTailCore
import Mettapedia.Languages.IMP.LanguageDef

namespace Mettapedia.Languages.IMP.TransitionSpec

open MeTTailCore.MeTTaIL.TransitionSpec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.IMP.LanguageDef

private structure DerivedTransition where
  sourceInstr : String
  sourceLabel : String
  ruleName : String
  ruleId : String
  priority : Nat
  hasLookupPremise : Bool
deriving Repr

private def rewriteSourceLabel? (rw : RewriteRule) : Option String :=
  match rw.left with
  | .apply "Start" _ => some "Start"
  | .apply "ImpState" (.apply ctrlLabel _ :: _) => some ctrlLabel
  | _ => none

private def ruleHasLookupPremise (rw : RewriteRule) : Bool :=
  rw.premises.any (fun
    | .relationQuery _ _ => true
    | _ => false)

private def addRuleToSource
    (sources : List TransitionSource)
    (sourceLabel ruleId : String) : List TransitionSource :=
  let sourceInstr := s!"C_{sourceLabel}"
  match sources with
  | [] =>
      [{ sourceInstr := sourceInstr
         sourceLabel := sourceLabel
         orderedRules := [ruleId] }]
  | s :: rest =>
      if s.sourceInstr == sourceInstr then
        { s with orderedRules := s.orderedRules ++ [ruleId] } :: rest
      else
        s :: addRuleToSource rest sourceLabel ruleId

private def foldRewriteTransitions
    (rules : List RewriteRule)
    (idx : Nat)
    (acc : List DerivedTransition) : Except String (List DerivedTransition) := do
  match rules with
  | [] => pure acc
  | rw :: rest =>
      let sourceLabel ←
        match rewriteSourceLabel? rw with
        | some lbl => pure lbl
        | none => throw s!"rewrite '{rw.name}' does not match Start(...) or ImpState(control, store, kont, status)"
      let next := acc ++ [{ sourceInstr := s!"C_{sourceLabel}"
                            sourceLabel := sourceLabel
                            ruleName := rw.name
                            ruleId := s!"R{idx}"
                            priority := idx
                            hasLookupPremise := ruleHasLookupPremise rw }]
      foldRewriteTransitions rest (idx + 1) next

private def requiredSourceInstrs : List String :=
  ["C_Start", "C_RunStmt", "C_RunA", "C_RunB", "C_RetNat", "C_RetBool", "C_RetUnit"]

private def missingRequiredSources (sources : List TransitionSource) : List String :=
  let present := sources.map (·.sourceInstr)
  requiredSourceInstrs.filter (fun src => !present.contains src)

private def sourceInstrClassFor (sourceLabel : String) : String :=
  if sourceLabel == "Start" then "entry"
  else if sourceLabel == "RunStmt" then "stmt"
  else if sourceLabel == "RunA" then "arith"
  else if sourceLabel == "RunB" then "bool"
  else if sourceLabel == "RetNat" then "ret_nat"
  else if sourceLabel == "RetBool" then "ret_bool"
  else "ret_unit"

private def transitionKindFor (ruleName : String) : String :=
  if ruleName.contains "Start" then "enter"
  else if ruleName.contains "Final" then "finalize"
  else if ruleName.contains "Assign" then "assign"
  else if ruleName.contains "While" then "while"
  else if ruleName.contains "If" then "branch"
  else if ruleName.contains "Seq" then "sequence"
  else if ruleName.contains "Plus" then "arith_plus"
  else if ruleName.contains "Times" then "arith_times"
  else if ruleName.contains "Le" then "bool_le"
  else if ruleName.contains "Eq" then "bool_eq"
  else if ruleName.contains "Not" then "bool_not"
  else if ruleName.contains "And" then "bool_and"
  else if ruleName.contains "A" then "arith"
  else if ruleName.contains "B" then "bool"
  else "transition"

private def guardFamilyFor (t : DerivedTransition) : String :=
  if t.ruleName.contains "True" then "bool_true"
  else if t.ruleName.contains "False" then "bool_false"
  else if t.hasLookupPremise then "lookup"
  else "shape"

private def effectKindFor (ruleName : String) : String :=
  if ruleName.contains "Final" then "set_done"
  else if ruleName.contains "Assign" then "store_update"
  else if ruleName.contains "Plus" || ruleName.contains "Times" then "arith_update"
  else if ruleName.contains "Le" || ruleName.contains "Eq" || ruleName.contains "Not" || ruleName.contains "And" then "bool_update"
  else if ruleName.contains "Seq" || ruleName.contains "If" || ruleName.contains "While" then "kont_update"
  else "advance_state"

private def contractsFor (_t : DerivedTransition) : List TransitionContract :=
  [ TransitionContract.deterministicReduction
  , TransitionContract.memoizationSafe
  , TransitionContract.specializationSafe ]

private def toSpecRule (t : DerivedTransition) : TransitionRule :=
  { logicalTransitionId := s!"{t.sourceInstr}:{t.ruleName}"
    sourceInstr := t.sourceInstr
    sourceLabel := t.sourceLabel
    ruleId := t.ruleId
    semKey :=
      { sourceInstrClass := sourceInstrClassFor t.sourceLabel
        transitionKind := transitionKindFor t.ruleName
        guardFamily := guardFamilyFor t
        effectKind := effectKindFor t.ruleName
        dialectExt := none
        contracts := contractsFor t }
    priority := t.priority }

def deriveIMPTransitionSpec? : Except String TransitionSpecArtifact := do
  let derived ← foldRewriteTransitions imp.rewrites 0 []
  let sources :=
    derived.foldl
      (fun acc t => addRuleToSource acc t.sourceLabel t.ruleId)
      []
  let missing := missingRequiredSources sources
  unless missing.isEmpty do
    throw s!"missing required source instructions: {String.intercalate ", " missing}"
  let artifact : TransitionSpecArtifact :=
    { schemaVersion := 2
      dialect := "imp"
      sources := sources
      rules := derived.map toSpecRule }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"IMP transition-spec lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveIMPTransitionSpec? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportIMPTransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveIMPTransitionSpec? with
  | .error err =>
      IO.println s!"imp transition-spec derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "imp.transition_spec.json"
      let checksumPath := outDir / "imp.transition_spec.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported imp transition-spec artifact to {outDir}"
      pure 0

def checkIMPTransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveIMPTransitionSpec? with
  | .error err =>
      IO.println s!"imp transition-spec derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "imp.transition_spec.json"
      let checksumPath := outDir / "imp.transition_spec.checksum"
      try
        let jsonText ← IO.FS.readFile jsonPath
        let checksumText ← IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] imp transition artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] imp transition artifacts mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"imp transition artifact check failed: {e}"
        pure 2

end Mettapedia.Languages.IMP.TransitionSpec
