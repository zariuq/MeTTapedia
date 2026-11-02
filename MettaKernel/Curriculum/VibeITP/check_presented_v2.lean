import Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData
import MeTTailCore.Crypto.SHA256

/-! Lean orchestration of the existing CeTTa consumers. Exact output, process
status, diagnostics and input identities are observed separately. This finite
comparison gate does not prove native implementation refinement. -/

open Lean (Json toJson)
open Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData

private def digest (path : System.FilePath) : IO String := do
  return MeTTailCore.Crypto.SHA256.toHexString
    (MeTTailCore.Crypto.SHA256.sha256Bytes (← IO.FS.readBinFile path))

private structure Bundle where
  visited : List String := []
  active : List String := []
  pins : Array (String × String) := #[]

private def importName (line : String) : Except String (Option String) := do
  let start := "!(import! &self "
  unless line.startsWith start do return none
  unless line.endsWith ")" do throw "unsupported multiline authored import"
  let name := ((line.drop start.length).toString.dropEnd 1).toString
  unless !name.isEmpty ∧ name.toList.all (fun char => char.isAlphanum || char = '_') do
    throw "unsupported authored import name"
  return some name

private partial def bundle (directory : System.FilePath) (name : String) : StateT Bundle IO String := do
  let state ← get
  if name ∈ state.active then throw (IO.userError "cyclic authored imports")
  if name ∈ state.visited then return ""
  let path := directory / (name ++ ".metta")
  let text ← IO.FS.readFile path
  let hash ← digest path
  modify fun state => { state with active := name :: state.active, pins := state.pins.push (name, hash) }
  let lines ← (text.splitOn "\n").mapM fun line => do
    match ← unwrap (importName line) with
    | none => pure line
    | some dependency => bundle directory dependency
  modify fun state => { state with active := state.active.filter (· != name), visited := name :: state.visited }
  return String.intercalate "\n" lines

private structure Observation where
  exitCode : UInt32
  stdout : String
  stderr : String
  timedOut : Bool
  milliseconds : Nat

private partial def await (child : IO.Process.Child { stdout := .piped, stderr := .piped, stdin := .null })
    (deadline : Nat) : IO (UInt32 × Bool) := do
  if let some code ← child.tryWait then return (code, false)
  if (← IO.monoMsNow) ≥ deadline then
    let killed ← IO.Process.output { cmd := "kill", args := #["-KILL", "--", "-" ++ toString child.pid] }
    if killed.exitCode != 0 then
      if let some code ← child.tryWait then return (code, true)
      throw (IO.userError "failed to terminate the timed-out process group")
    return (← child.wait, true)
  IO.sleep 20
  await child deadline

private def execute (binary source : System.FilePath) (timeout : Nat) : IO Observation := do
  let start ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := binary.toString
    args := #["--lang", "he", "--fuel", "-1", "--quiet", source.toString]
    stdout := .piped
    stderr := .piped
    stdin := .null
    setsid := true }
  let output ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let errors ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let (code, timedOut) ← await child (start + timeout)
  return ⟨code, ← IO.ofExcept output.get, ← IO.ofExcept errors.get, timedOut, (← IO.monoMsNow) - start⟩

private structure Config where
  binary : Option System.FilePath := none
  kernel : Option System.FilePath := none
  artifacts : List System.FilePath := []
  generated : Option System.FilePath := none
  group : String := ""
  output : Option System.FilePath := none
  timeout : Nat := 90000

private def options : Config → List String → Except String Config
  | config, [] => .ok config
  | config, "--binary" :: value :: rest => options { config with binary := some value } rest
  | config, "--kernel-directory" :: value :: rest => options { config with kernel := some value } rest
  | config, "--artifacts" :: value :: rest =>
      options { config with artifacts := config.artifacts ++ [System.FilePath.mk value] } rest
  | config, "--generated" :: value :: rest => options { config with generated := some value } rest
  | config, "--group" :: value :: rest => options { config with group := value } rest
  | config, "--output" :: value :: rest => options { config with output := some value } rest
  | config, "--timeout" :: value :: rest => do
      let some seconds := value.toNat? | throw "timeout must be a positive integer number of seconds"
      unless seconds > 0 do throw "timeout must be positive"
      options { config with timeout := seconds * 1000 } rest
  | _, _ => .error "unknown or incomplete runner option"

private def pin (directory : System.FilePath) (names : List String) : IO (Array (String × String)) :=
  names.toArray.mapM fun (name : String) => do
    let hash ← digest (directory / System.FilePath.mk name)
    pure (name, hash)

private def unchanged (directory : System.FilePath) (pins : Array (String × String)) : IO Bool := do
  for (name, hash) in pins do
    unless (← digest (directory / name)) = hash do return false
  return true

private def observationJson (index : Nat) (cases : Array Json) (pins : Array (String × String))
    (source : System.FilePath) (expected : String) (inputsUnchanged : Bool) (observed : Observation) : IO (Json × Bool) := do
  let passed := !observed.timedOut && observed.exitCode == 0 && observed.stdout == expected &&
    observed.stderr.isEmpty && inputsUnchanged
  return (Json.mkObj [("program", toJson index), ("cases", .arr cases),
    ("input_sha256", Json.mkObj (pins.toList.map fun (name, hash) => (name, .str hash))),
    ("source_sha256", .str (← digest source)), ("passed", .bool passed),
    ("exit_code", toJson observed.exitCode.toNat), ("timed_out", .bool observed.timedOut),
    ("milliseconds", toJson observed.milliseconds), ("inputs_unchanged", .bool inputsUnchanged)], passed)

private def nameValid (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun char => "abcdefghijklmnopqrstuvwxyz0123456789-".contains char)

private def run (config : Config) : IO UInt32 := do
  let some binary := config.binary | throw (IO.userError "--binary is required")
  let some output := config.output | throw (IO.userError "--output is required")
  IO.FS.createDirAll output
  let binaryHash ← digest binary
  let mut reports := #[]
  let mut allPassed := true
  let mut authoredPins := #[]
  if let some generated := config.generated then
    unless nameValid config.group do throw (IO.userError "a valid --group is required")
    let base := config.group
    let pins ← pin generated [base ++ ".probe.metta", base ++ ".expected", base ++ ".json"]
    let source := output / (base ++ ".metta")
    IO.FS.writeFile source (← IO.FS.readFile (generated / (base ++ ".probe.metta")))
    let expected ← IO.FS.readFile (generated / (base ++ ".expected"))
    let metadata ← unwrap (Json.parse (← IO.FS.readFile (generated / (base ++ ".json"))))
    let cases ← unwrap (arrayField metadata "probes")
    unless !cases.isEmpty ∧ (expected.splitOn "\n").length = cases.size + 1 do
      throw (IO.userError "reference rows do not match requests")
    let observed ← execute binary source config.timeout
    IO.FS.writeFile (output / (base ++ ".stdout")) observed.stdout
    IO.FS.writeFile (output / (base ++ ".stderr")) observed.stderr
    let (record, passed) ← observationJson 0 cases pins source expected (← unchanged generated pins) observed
    reports := reports.push record
    allPassed := passed
    IO.println s!"{base}: {cases.size} observations, {if passed then "PASS" else "FAIL"}"
  else
    let some kernel := config.kernel | throw (IO.userError "--kernel-directory is required for articles")
    unless !config.artifacts.isEmpty do throw (IO.userError "at least one --artifacts directory is required")
    let (code, bundled) ← (bundle kernel "generic_inference_checker_v0").run {}
    authoredPins := bundled.pins
    for (directory, index) in config.artifacts.zipIdx do
      let data ← unwrap (Json.parse (← IO.FS.readFile (directory / "checked.json")))
      let cases ← unwrap (arrayField data "cases")
      unless !cases.isEmpty do throw (IO.userError "no article cases")
      let language ← IO.FS.readFile (directory / "language.sexp")
      let mut inputs := ["language.sexp", "checked.json"]
      let mut calls := []
      let mut expectedRows := []
      let mut names := []
      for entry in cases do
        let name ← unwrap (stringField entry "name")
        unless nameValid name ∧ name ∉ names do throw (IO.userError "invalid or duplicate case identity")
        names := name :: names
        let accepted ← unwrap do (← field entry "accepted").getBool?
        let goalName := name ++ ".goal.sexp"
        let proofName := name ++ ".proof.sexp"
        inputs := inputs ++ [goalName, proofName]
        let goal ← IO.FS.readFile (directory / goalName)
        let proof ← IO.FS.readFile (directory / proofName)
        calls := calls ++ ["!(gic-check " ++ language.trimAscii.toString ++ " " ++ goal.trimAscii.toString ++
          " " ++ proof.trimAscii.toString ++ ")"]
        expectedRows := expectedRows ++ [if accepted then "[True]" else "[False]"]
      let pins ← pin directory inputs
      let source := output / s!"presentation-{index}.metta"
      let expected := String.intercalate "\n" expectedRows ++ "\n"
      IO.FS.writeFile source (code ++ "\n" ++ String.intercalate "\n" calls ++ "\n")
      IO.FS.writeFile (output / s!"presentation-{index}.expected") expected
      let observed ← execute binary source config.timeout
      IO.FS.writeFile (output / s!"presentation-{index}.stdout") observed.stdout
      IO.FS.writeFile (output / s!"presentation-{index}.stderr") observed.stderr
      let (record, passed) ← observationJson index cases pins source expected (← unchanged directory pins) observed
      reports := reports.push record
      allPassed := allPassed && passed
      IO.println s!"{index}: {cases.size} observations, {if passed then "PASS" else "FAIL"}"
    for (name, hash) in authoredPins do
      unless (← digest (kernel / (name ++ ".metta"))) = hash do allPassed := false
  unless (← digest binary) = binaryHash do allPassed := false
  IO.FS.writeFile (output / "report.json") ((Json.mkObj [
    ("passed", .bool allPassed), ("binary_sha256", .str binaryHash), ("dialect", .str "he"),
    ("authored_source_sha256", Json.mkObj (authoredPins.toList.map fun (name, hash) => (name, .str hash))),
    ("programs", .arr reports)]).pretty ++ "\n")
  return if allPassed then 0 else 1

private def selfTest (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let make (name body : String) : IO System.FilePath := do
    let path := directory / name
    IO.FS.writeFile path ("#!/bin/sh\n" ++ body ++ "\n")
    let permission ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
    unless permission.exitCode = 0 do throw (IO.userError "failed to prepare runner control")
    return path
  let source := directory / "input.metta"
  IO.FS.writeFile source "runner-control\n"
  let success ← make "success.sh" "printf 'expected\\n'"
  let observed ← execute success source 3000
  let (_, passed) ← observationJson 0 #[] #[] source "expected\n" true observed
  unless passed do throw (IO.userError "successful process control failed")
  let (_, wrongOutput) ← observationJson 0 #[] #[] source "different\n" true observed
  unless !wrongOutput do throw (IO.userError "wrong output received success")
  let diagnostic ← make "diagnostic.sh" "printf 'expected\\n'\nprintf 'diagnostic\\n' >&2"
  let observed ← execute diagnostic source 3000
  let (_, passed) ← observationJson 0 #[] #[] source "expected\n" true observed
  unless !passed ∧ !observed.stderr.isEmpty do throw (IO.userError "diagnostics received success")
  let nonzero ← make "nonzero.sh" "printf 'expected\\n'\nexit 7"
  let observed ← execute nonzero source 3000
  let (_, passed) ← observationJson 0 #[] #[] source "expected\n" true observed
  unless !passed ∧ observed.exitCode = 7 do throw (IO.userError "nonzero process received success")
  let blocked ← make "timeout.sh" "trap '' TERM\nsleep 30"
  let observed ← execute blocked source 1000
  unless observed.timedOut ∧ observed.milliseconds < 5000 do throw (IO.userError "timeout did not terminate")
  let loud ← make "large-pipes.sh"
    "head -c 131072 /dev/zero | tr '\\000' o\nhead -c 131072 /dev/zero | tr '\\000' e >&2"
  let observed ← execute loud source 5000
  unless !observed.timedOut ∧ observed.exitCode = 0 ∧ observed.stdout.utf8ByteSize = 131072 ∧
      observed.stderr.utf8ByteSize = 131072 do throw (IO.userError "large process pipes failed")
  let before ← pin directory ["input.metta"]
  IO.FS.writeFile source "changed\n"
  unless !(← unchanged directory before) do throw (IO.userError "source change was not detected")
  IO.println "7 runner controls passed."
  IO.FS.writeFile (directory / "self-test.json") "{\"passed\":true,\"controls\":7}\n"
  return 0

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["--self-test", directory] => selfTest directory
  | _ => run (← unwrap (options {} arguments))
