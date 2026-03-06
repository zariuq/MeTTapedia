import MeTTailCore
import Mettapedia.Languages.MinskyLite.LanguageDef

namespace Mettapedia.Languages.MinskyLite.TransitionSpec

open MeTTailCore.MeTTaIL.TransitionSpec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MinskyLite.LanguageDef

private structure DerivedTransition where
  sourceInstr : String
  sourceLabel : String
  ruleName : String
  ruleId : String
  priority : Nat
deriving Repr

private def rewriteSourceLabel? (rw : RewriteRule) : Option String :=
  match rw.left with
  | .apply "Machine" (.apply instrLabel _ :: _) => some instrLabel
  | _ => none

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
      let sourceLabel <-
        match rewriteSourceLabel? rw with
        | some lbl => pure lbl
        | none => throw s!"rewrite '{rw.name}' does not match Machine(<Control>, regA, regB, status)"
      let next := acc ++ [{ sourceInstr := s!"C_{sourceLabel}"
                            sourceLabel := sourceLabel
                            ruleName := rw.name
                            ruleId := s!"R{idx}"
                            priority := idx }]
      foldRewriteTransitions rest (idx + 1) next

private def requiredSourceInstrs : List String :=
  ["C_IncA", "C_IncB", "C_DecA", "C_DecB", "C_Halt"]

private def missingRequiredSources (sources : List TransitionSource) : List String :=
  let present := sources.map (·.sourceInstr)
  requiredSourceInstrs.filter (fun src => !present.contains src)

private def sourceInstrClassFor (sourceLabel : String) : String :=
  if sourceLabel.startsWith "Inc" then "increment"
  else if sourceLabel.startsWith "Dec" then "decrement"
  else "halt"

private def transitionKindFor (ruleName : String) : String :=
  if ruleName.contains "Inc" then "increment"
  else if ruleName.contains "Zero" then "branch_zero"
  else if ruleName.contains "Succ" then "branch_positive"
  else if ruleName.contains "Halt" then "halt"
  else "transition"

private def guardFamilyFor (ruleName : String) : String :=
  if ruleName.contains "Zero" then "zero"
  else if ruleName.contains "Succ" then "positive"
  else "none"

private def effectKindFor (ruleName : String) : String :=
  if ruleName.contains "Halt" then "set_done"
  else "advance_machine"

private def contracts : List TransitionContract :=
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
        guardFamily := guardFamilyFor t.ruleName
        effectKind := effectKindFor t.ruleName
        dialectExt := none
        contracts := contracts }
    priority := t.priority }

def deriveMinskyLiteTransitionSpec? : Except String TransitionSpecArtifact := do
  let derived <- foldRewriteTransitions minskyLite.rewrites 0 []
  let sources :=
    derived.foldl
      (fun acc t => addRuleToSource acc t.sourceLabel t.ruleId)
      []
  let missing := missingRequiredSources sources
  unless missing.isEmpty do
    throw s!"missing required source instructions: {String.intercalate ", " missing}"
  let artifact : TransitionSpecArtifact :=
    { schemaVersion := 2
      dialect := "minskylite"
      sources := sources
      rules := derived.map toSpecRule }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"minskylite transition-spec lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveMinskyLiteTransitionSpec? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportMinskyLiteTransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveMinskyLiteTransitionSpec? with
  | .error err =>
      IO.println s!"minskylite transition-spec derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "minskylite.transition_spec.json"
      let checksumPath := outDir / "minskylite.transition_spec.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
      IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
      IO.println s!"exported minskylite transition-spec artifact to {outDir}"
      pure 0

def checkMinskyLiteTransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveMinskyLiteTransitionSpec? with
  | .error err =>
      IO.println s!"minskylite transition-spec derivation failed: {err}"
      pure 2
  | .ok artifact =>
      let jsonPath := outDir / "minskylite.transition_spec.json"
      let checksumPath := outDir / "minskylite.transition_spec.checksum"
      try
        let jsonText <- IO.FS.readFile jsonPath
        let checksumText <- IO.FS.readFile checksumPath
        let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
        if jsonOk && checksumOk then
          IO.println s!"[ok] minskylite transition artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] minskylite transition artifacts mismatch at {outDir}"
          if !jsonOk then
            IO.println s!"  json mismatch at {jsonPath}"
          if !checksumOk then
            IO.println s!"  checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"minskylite transition artifact check failed: {e}"
        pure 2

end Mettapedia.Languages.MinskyLite.TransitionSpec

private def defaultOutDir : System.FilePath :=
  "artifacts/transition"

def runCli (args : List String) : IO UInt32 := do
  match args with
  | ["export", outDir] =>
      Mettapedia.Languages.MinskyLite.TransitionSpec.exportMinskyLiteTransitionSpec outDir
  | ["export"] =>
      Mettapedia.Languages.MinskyLite.TransitionSpec.exportMinskyLiteTransitionSpec defaultOutDir
  | ["check", outDir] =>
      Mettapedia.Languages.MinskyLite.TransitionSpec.checkMinskyLiteTransitionSpec outDir
  | ["check"] =>
      Mettapedia.Languages.MinskyLite.TransitionSpec.checkMinskyLiteTransitionSpec defaultOutDir
  | _ =>
      IO.println "minskylite transition-spec commands: export [out-dir] | check [out-dir]"
      pure 1
