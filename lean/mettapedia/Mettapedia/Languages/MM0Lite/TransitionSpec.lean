import MeTTailCore
import Mettapedia.Languages.MM0Lite.LanguageDef

namespace Mettapedia.Languages.MM0Lite.TransitionSpec

open MeTTailCore.MeTTaIL.TransitionSpec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MM0Lite.LanguageDef

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
  | .apply "MMState" (.apply "ICons" (.apply instrLabel _ :: _) :: _)
  => some instrLabel
  | .apply "MMState" (.apply "INil" [] :: _)
  => some "INil"
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
        | none => throw s!"rewrite '{rw.name}' does not match MMState instruction shape"
      let next := acc ++ [{ sourceInstr := s!"C_{sourceLabel}"
                            sourceLabel := sourceLabel
                            ruleName := rw.name
                            ruleId := s!"R{idx}"
                            priority := idx
                            hasLookupPremise := ruleHasLookupPremise rw }]
      foldRewriteTransitions rest (idx + 1) next

private def requiredSourceInstrs : List String :=
  ["C_IPush", "C_IUse", "C_IMP", "C_INil"]

private def missingRequiredSources (sources : List TransitionSource) : List String :=
  let present := sources.map (·.sourceInstr)
  requiredSourceInstrs.filter (fun src => !present.contains src)

private def transitionKindFor (ruleName : String) : String :=
  if ruleName.contains "Push" then "push"
  else if ruleName.contains "Use" then "lookup_push"
  else if ruleName.contains "MP" then "modus_ponens"
  else if ruleName.contains "Accept" then "accept"
  else "transition"

private def guardFamilyFor (t : DerivedTransition) : String :=
  if t.hasLookupPremise then "lookup"
  else if t.ruleName.contains "MP" then "shape"
  else "none"

private def effectKindFor (ruleName : String) : String :=
  if ruleName.contains "Accept" then "emit_verified"
  else "stack_update"

private def contractsFor (t : DerivedTransition) : List TransitionContract :=
  let base := [TransitionContract.memoizationSafe, TransitionContract.specializationSafe]
  if t.hasLookupPremise then
    TransitionContract.deterministicReduction :: base
  else
    TransitionContract.deterministicReduction :: base

private def toSpecRule (t : DerivedTransition) : TransitionRule :=
  { logicalTransitionId := s!"{t.sourceInstr}:{t.ruleName}"
    sourceInstr := t.sourceInstr
    sourceLabel := t.sourceLabel
    ruleId := t.ruleId
    semKey :=
      { sourceInstrClass := "mm0_instr"
        transitionKind := transitionKindFor t.ruleName
        guardFamily := guardFamilyFor t
        effectKind := effectKindFor t.ruleName
        dialectExt := none
        contracts := contractsFor t }
    priority := t.priority }

def deriveMM0TransitionSpec? : Except String TransitionSpecArtifact := do
  let derived ← foldRewriteTransitions mm0Lite.rewrites 0 []
  let sources :=
    derived.foldl
      (fun acc t => addRuleToSource acc t.sourceLabel t.ruleId)
      []
  let missing := missingRequiredSources sources
  unless missing.isEmpty do
    throw s!"missing required source instructions: {String.intercalate ", " missing}"
  let rules := derived.map toSpecRule
  let artifact : TransitionSpecArtifact :=
    { schemaVersion := 2
      dialect := "mm0lite"
      sources := sources
      rules := rules }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"MM0Lite transition-spec lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveMM0TransitionSpec? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportMM0TransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveMM0TransitionSpec? with
  | .error err =>
      IO.println s!"mm0lite transition-spec derivation failed: {err}"
      pure 2
  | .ok specArtifact =>
      let specJsonPath := outDir / "mm0lite.transition_spec.json"
      let specChecksumPath := outDir / "mm0lite.transition_spec.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile specJsonPath (specArtifact.renderJson ++ "\n")
      IO.FS.writeFile specChecksumPath (specArtifact.checksumString ++ "\n")
      IO.println s!"exported mm0lite transition-spec artifact to {outDir}"
      pure 0

def checkMM0TransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveMM0TransitionSpec? with
  | .error err =>
      IO.println s!"mm0lite transition-spec derivation failed: {err}"
      pure 2
  | .ok specArtifact =>
      let specJsonPath := outDir / "mm0lite.transition_spec.json"
      let specChecksumPath := outDir / "mm0lite.transition_spec.checksum"
      try
        let specJsonText ← IO.FS.readFile specJsonPath
        let specChecksumText ← IO.FS.readFile specChecksumPath
        let specJsonOk := specJsonText.trimAscii.toString == specArtifact.renderJson.trimAscii.toString
        let specChecksumOk := specChecksumText.trimAscii.toString == specArtifact.checksumString.trimAscii.toString
        if specJsonOk && specChecksumOk then
          IO.println s!"[ok] mm0lite transition artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] mm0lite transition artifacts mismatch at {outDir}"
          if !specJsonOk then
            IO.println s!"  json mismatch at {specJsonPath}"
          if !specChecksumOk then
            IO.println s!"  checksum mismatch at {specChecksumPath}"
          pure 3
      catch e =>
        IO.println s!"mm0lite transition artifact check failed: {e}"
        pure 2

end Mettapedia.Languages.MM0Lite.TransitionSpec

def runCli (args : List String) : IO UInt32 := do
  let defaultOutDir : System.FilePath := "artifacts/transition"
  match args with
  | ["export", outDir] =>
      Mettapedia.Languages.MM0Lite.TransitionSpec.exportMM0TransitionSpec outDir
  | ["export"] =>
      Mettapedia.Languages.MM0Lite.TransitionSpec.exportMM0TransitionSpec defaultOutDir
  | ["check", outDir] =>
      Mettapedia.Languages.MM0Lite.TransitionSpec.checkMM0TransitionSpec outDir
  | ["check"] =>
      Mettapedia.Languages.MM0Lite.TransitionSpec.checkMM0TransitionSpec defaultOutDir
  | _ =>
      IO.println "mm0lite transition-spec commands: export [out-dir] | check [out-dir]"
      pure 1
