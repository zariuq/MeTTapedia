import MeTTailCore
import Mettapedia.Languages.MeTTa.HE.HELanguageDef

namespace Mettapedia.Languages.MeTTa.HE.TransitionSpec

open MeTTailCore.MeTTaIL.TransitionSpec
open Mettapedia.OSLF.MeTTaIL.Syntax

private structure DerivedTransition where
  sourceInstr : String
  sourceLabel : String
  ruleName : String
  ruleId : String
  priority : Nat
deriving Repr

private def rewriteSourceLabel? (rw : RewriteRule) : Option String :=
  match rw.left with
  | .apply "State" (.apply instrLabel _ :: _) => some instrLabel
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
      let sourceLabel ←
        match rewriteSourceLabel? rw with
        | some lbl => pure lbl
        | none => throw s!"rewrite '{rw.name}' does not match State(<Instr>, space, out)"
      let sourceInstr := s!"C_{sourceLabel}"
      let next := acc ++ [{ sourceInstr := sourceInstr
                            sourceLabel := sourceLabel
                            ruleName := rw.name
                            ruleId := s!"R{idx}"
                            priority := idx }]
      foldRewriteTransitions rest (idx + 1) next

private def requiredSourceInstrs : List String :=
  ["C_Metta", "C_InterpExpr", "C_InterpFunc", "C_InterpArgs",
   "C_InterpTuple", "C_MettaCall", "C_TypeCast", "C_Return"]

private def missingRequiredSources (sources : List TransitionSource) : List String :=
  let present := sources.map (·.sourceInstr)
  requiredSourceInstrs.filter (fun src => !present.contains src)

private def sourceInstrClassFor (sourceLabel : String) : String :=
  match sourceLabel with
  | "Metta" => "metta"
  | "InterpExpr" => "interp_expr"
  | "InterpFunc" => "interp_func"
  | "InterpArgs" => "interp_args"
  | "InterpTuple" => "interp_tuple"
  | "MettaCall" => "metta_call"
  | "TypeCast" => "type_cast"
  | "Return" => "return"
  | _ => "other"

private def transitionKindFor (ruleName sourceLabel : String) : String :=
  if ruleName.startsWith "M_" then "metta_dispatch"
  else if ruleName.startsWith "IE_" then "interp_expr"
  else if ruleName.startsWith "IF_" then "interp_func"
  else if ruleName.startsWith "IA_" then "interp_args"
  else if ruleName.startsWith "IT_" then "interp_tuple"
  else if ruleName.startsWith "MC_" then "metta_call"
  else if ruleName.startsWith "TC_" then "type_cast"
  else if ruleName.startsWith "R_" || sourceLabel == "Return" then "return_finalize"
  else "transition"

private def guardFamilyFor (ruleName : String) : String :=
  if ruleName.contains "Error" then "error"
  else if ruleName.contains "Empty" || ruleName.contains "Nil" then "empty_or_nil"
  else if ruleName.contains "Mismatch" || ruleName.contains "Match" then "match"
  else if ruleName.contains "Type" then "type"
  else if ruleName.contains "Grounded" then "grounded"
  else if ruleName.contains "Equation" || ruleName.contains "NoMatch" then "lookup"
  else if ruleName.contains "Call" then "callable"
  else "shape"

private def effectKindFor (ruleName sourceLabel : String) : String :=
  if sourceLabel == "Return" || ruleName.startsWith "R_" then "emit_done"
  else if ruleName.contains "Error" then "propagate_error"
  else if ruleName.contains "Recurse" then "recurse_state"
  else if ruleName.contains "EvalArgs" then "spawn_eval_args"
  else if ruleName.contains "Call" then "emit_call"
  else if sourceLabel == "MettaCall" then "resolve_call"
  else if sourceLabel == "TypeCast" then "emit_return"
  else "advance_state"

private def contractsFor (ruleName : String) : List TransitionContract :=
  let base : List TransitionContract :=
    [TransitionContract.memoizationSafe, TransitionContract.specializationSafe]
  let withGround :=
    if ruleName.contains "Grounded" then
      TransitionContract.coreGroundEvalSafe :: base
    else
      base
  if ruleName.contains "Equation" then
    [TransitionContract.nondeterministic, TransitionContract.orderSensitive] ++ withGround
  else
    TransitionContract.deterministicReduction :: withGround

private def dialectExtFor (ruleName sourceLabel : String) : Option String :=
  if ruleName == "M_Expression" then
    some "he_internal_instructions=context-space,call-native"
  else if ruleName == "MC_Grounded" || sourceLabel == "MettaCall" then
    some "he_internal_instructions=call-native"
  else
    none

private def toSpecRule (t : DerivedTransition) : TransitionRule :=
  { logicalTransitionId := s!"{t.sourceInstr}:{t.ruleName}"
    sourceInstr := t.sourceInstr
    sourceLabel := t.sourceLabel
    ruleId := t.ruleId
    semKey :=
      { sourceInstrClass := sourceInstrClassFor t.sourceLabel
        transitionKind := transitionKindFor t.ruleName t.sourceLabel
        guardFamily := guardFamilyFor t.ruleName
        effectKind := effectKindFor t.ruleName t.sourceLabel
        dialectExt := dialectExtFor t.ruleName t.sourceLabel
        contracts := contractsFor t.ruleName }
    priority := t.priority }

def deriveFromHELanguage? : Except String TransitionSpecArtifact := do
  let derived ← foldRewriteTransitions
    Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE.rewrites
    0
    []
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
      dialect := "he"
      sources := sources
      rules := rules }
  let lintErrs := artifact.lintErrors
  unless lintErrs.isEmpty do
    throw s!"transition-spec lint failed:\n{String.intercalate "\n" lintErrs}"
  pure artifact

def derivationIsOk : Bool :=
  match deriveFromHELanguage? with
  | .ok _ => true
  | .error _ => false

#guard derivationIsOk = true

def exportHeTransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveFromHELanguage? with
  | .error err =>
      IO.println s!"he transition-spec derivation failed: {err}"
      pure 2
  | .ok specArtifact =>
      let specJsonPath := outDir / "he.transition_spec.json"
      let specChecksumPath := outDir / "he.transition_spec.checksum"
      IO.FS.createDirAll outDir
      IO.FS.writeFile specJsonPath (specArtifact.renderJson ++ "\n")
      IO.FS.writeFile specChecksumPath (specArtifact.checksumString ++ "\n")
      IO.println s!"exported he transition-spec artifact to {outDir}"
      pure 0

def checkHeTransitionSpec (outDir : System.FilePath) : IO UInt32 := do
  match deriveFromHELanguage? with
  | .error err =>
      IO.println s!"he transition-spec derivation failed: {err}"
      pure 2
  | .ok specArtifact =>
      let specJsonPath := outDir / "he.transition_spec.json"
      let specChecksumPath := outDir / "he.transition_spec.checksum"
      try
        let specJsonText ← IO.FS.readFile specJsonPath
        let specChecksumText ← IO.FS.readFile specChecksumPath
        let specJsonOk := specJsonText.trimAscii.toString == specArtifact.renderJson.trimAscii.toString
        let specChecksumOk := specChecksumText.trimAscii.toString == specArtifact.checksumString.trimAscii.toString
        if specJsonOk && specChecksumOk then
          IO.println s!"[ok] he transition artifacts match at {outDir}"
          pure 0
        else
          IO.println s!"[drift] he transition artifacts mismatch at {outDir}"
          if !specJsonOk then
            IO.println s!"  json mismatch at {specJsonPath}"
          if !specChecksumOk then
            IO.println s!"  checksum mismatch at {specChecksumPath}"
          pure 3
      catch e =>
        IO.println s!"he transition artifact check failed: {e}"
        pure 2

private def usage : String :=
  String.intercalate "\n"
    [ "he transition-spec commands:"
    , "  export <out-dir>"
    , "  export            (default out-dir: artifacts/transition)"
    , "  check <out-dir>"
    , "  check             (default out-dir: artifacts/transition)"
    , "  (exports he.transition_spec.*)"
    ]

private def defaultOutDir : System.FilePath :=
  "artifacts/transition"

def runCli (args : List String) : IO UInt32 := do
  match args with
  | ["export", outDir] => exportHeTransitionSpec outDir
  | ["export"] => exportHeTransitionSpec defaultOutDir
  | ["check", outDir] => checkHeTransitionSpec outDir
  | ["check"] => checkHeTransitionSpec defaultOutDir
  | _ =>
      IO.println usage
      pure 1

end Mettapedia.Languages.MeTTa.HE.TransitionSpec
