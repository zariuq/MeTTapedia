import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Semantics.ImportOps
import Algorithms.MeTTa.LookupPlans

namespace Algorithms.MeTTa.Simple.Main

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile
open Algorithms.MeTTa.Simple

private def emptyLanguage : LanguageDef := {
  name := "SimpleSession"
  types := []
  terms := []
  equations := []
  rewrites := []
  congruenceCollections := []
}

private def emptyBundle : SpecBundle := {
  language := emptyLanguage
  relationEnv := RelationEnv.empty
  builtins := coreIntrinsicBuiltins
  policy := {
    maxFuel := 128
    normalizeToFixedPoint := false
  }
}

private def emptySession : Session :=
  Session.new emptyBundle

private def renderPattern (p : Pattern) : String :=
  reprStr p

private def renderPatternList (xs : List Pattern) : String :=
  "[" ++ String.intercalate ", " (xs.map renderPattern) ++ "]"

private def lookupSyntaxSpec? (dialect : String) : Option (String × MeTTailCore.MeTTaSyntax.SyntaxSpec) :=
  if dialect = "he" then
    some ("he", MeTTailCore.MeTTaSyntax.he)
  else if dialect = "petta" then
    some ("petta", MeTTailCore.MeTTaSyntax.petta)
  else
    none

private def lookupGrammarSpec? (dialect : String) : Option (String × MeTTailCore.MeTTaSyntax.GrammarSpec) :=
  if dialect = "he" then
    some ("he", MeTTailCore.MeTTaSyntax.heGrammar)
  else if dialect = "petta" then
    some ("petta", MeTTailCore.MeTTaSyntax.pettaGrammar)
  else
    none

private def syntaxSpecFileBase (name : String) : String :=
  s!"{name}.syntax_spec"

private def syntaxSpecJsonPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{syntaxSpecFileBase name}.json"

private def syntaxSpecChecksumPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{syntaxSpecFileBase name}.checksum"

private def grammarSpecFileBase (name : String) : String :=
  s!"{name}.grammar_spec"

private def grammarSpecJsonPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{grammarSpecFileBase name}.json"

private def grammarSpecChecksumPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{grammarSpecFileBase name}.checksum"

private def treeSitterGrammarPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{name}.tree_sitter_grammar.js"

private def parserProbeSnapshotPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{name}.parser_probe.snapshot"

private def parserProbeChecksumPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{name}.parser_probe.checksum"

private def lookupPlanFileBase (name : String) : String :=
  s!"{name}.lookup_plan"

private def lookupPlanJsonPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{lookupPlanFileBase name}.json"

private def lookupPlanChecksumPath (outDir : System.FilePath) (name : String) : System.FilePath :=
  outDir / s!"{lookupPlanFileBase name}.checksum"

private def exportOneLookupPlan (outDir : System.FilePath)
    (entry : String × MeTTailCore.MeTTaIL.LookupPlan.LookupPlanArtifact) : IO Unit := do
  let (name, artifact) := entry
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    throw <| IO.userError s!"lookup-plan lint failed for {name}:\n{String.intercalate "\n" lintErrs}"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (lookupPlanJsonPath outDir name) (artifact.renderJson ++ "\n")
  IO.FS.writeFile (lookupPlanChecksumPath outDir name) (artifact.checksumString ++ "\n")

private def heLookupSourceDir : IO System.FilePath := do
  match (← IO.getEnv "METTAPEDIA_LOOKUP_PLAN_DIR") with
  | some p => pure p
  | none => pure "../mettapedia/artifacts/lookup"

private def heLookupSourceJsonPath : IO System.FilePath := do
  pure <| (← heLookupSourceDir) / "he.lookup_plan.json"

private def heLookupSourceChecksumPath : IO System.FilePath := do
  pure <| (← heLookupSourceDir) / "he.lookup_plan.checksum"

private def exportHeLookupPlanFromSource (outDir : System.FilePath) : IO Unit := do
  let srcJson ← heLookupSourceJsonPath
  let srcChecksum ← heLookupSourceChecksumPath
  let jsonText ← IO.FS.readFile srcJson
  let checksumText ← IO.FS.readFile srcChecksum
  IO.FS.createDirAll outDir
  IO.FS.writeFile (lookupPlanJsonPath outDir "he") jsonText
  IO.FS.writeFile (lookupPlanChecksumPath outDir "he") checksumText

private def checkHeLookupPlanAgainstSource (outDir : System.FilePath) : IO Bool := do
  let srcJson ← heLookupSourceJsonPath
  let srcChecksum ← heLookupSourceChecksumPath
  let dstJson := lookupPlanJsonPath outDir "he"
  let dstChecksum := lookupPlanChecksumPath outDir "he"
  let srcJsonText ← IO.FS.readFile srcJson
  let srcChecksumText ← IO.FS.readFile srcChecksum
  let dstJsonText ← IO.FS.readFile dstJson
  let dstChecksumText ← IO.FS.readFile dstChecksum
  let jsonOk := srcJsonText.trimAscii.toString == dstJsonText.trimAscii.toString
  let checksumOk := srcChecksumText.trimAscii.toString == dstChecksumText.trimAscii.toString
  if jsonOk && checksumOk then
    IO.println "[ok] he lookup-plan artifact matches mettapedia source artifact"
    pure true
  else
    IO.println "[drift] he lookup-plan artifact mismatch vs mettapedia source artifact"
    if !jsonOk then
      IO.println s!"  json mismatch at {dstJson}"
    if !checksumOk then
      IO.println s!"  checksum mismatch at {dstChecksum}"
    pure false

private def exportLookupPlanCommand (dialect outDir : String) : IO UInt32 := do
  if dialect = "he" then
    try
      exportHeLookupPlanFromSource outDir
      IO.println s!"exported he lookup-plan artifact to {outDir} (source: mettapedia)"
      pure 0
    catch e =>
      IO.println s!"he lookup-plan export failed: {e}"
      IO.println "hint: regenerate source artifact via mettapedia HE lookup-plan export command"
      pure 2
  else
    match Algorithms.MeTTa.LookupPlans.lookupPlanByDialect? dialect with
    | none =>
        IO.println s!"unknown lookup-plan dialect: {dialect} (expected: he | petta)"
        pure 1
    | some entry =>
        try
          exportOneLookupPlan outDir entry
          IO.println s!"exported {entry.1} lookup-plan artifact to {outDir}"
          pure 0
        catch e =>
          IO.println s!"lookup-plan export failed: {e}"
          pure 2

private def exportAllLookupPlansCommand (outDir : String) : IO UInt32 := do
  try
    exportHeLookupPlanFromSource outDir
    exportOneLookupPlan outDir ("petta", Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact)
    IO.println s!"exported lookup-plan artifacts (he, petta) to {outDir}"
    pure 0
  catch e =>
    IO.println s!"lookup-plan export-all failed: {e}"
    IO.println "hint: regenerate mettapedia he.lookup_plan artifacts first"
    pure 2

private def checkOneLookupPlan (outDir : System.FilePath)
    (entry : String × MeTTailCore.MeTTaIL.LookupPlan.LookupPlanArtifact) : IO Bool := do
  let (name, artifact) := entry
  let jsonPath := lookupPlanJsonPath outDir name
  let checksumPath := lookupPlanChecksumPath outDir name
  let expectedJson := artifact.renderJson.trimAscii.toString
  let expectedChecksum := artifact.checksumString.trimAscii.toString
  let jsonText ← IO.FS.readFile jsonPath
  let checksumText ← IO.FS.readFile checksumPath
  let jsonOk := jsonText.trimAscii.toString == expectedJson
  let checksumOk := checksumText.trimAscii.toString == expectedChecksum
  if jsonOk && checksumOk then
    IO.println s!"[ok] {name} lookup-plan artifact matches"
    pure true
  else
    IO.println s!"[drift] {name} lookup-plan artifact mismatch"
    if !jsonOk then
      IO.println s!"  json mismatch at {jsonPath}"
    if !checksumOk then
      IO.println s!"  checksum mismatch at {checksumPath}"
    pure false

private def checkLookupPlanCommand (dialect outDir : String) : IO UInt32 := do
  if dialect = "he" then
    try
      let ok ← checkHeLookupPlanAgainstSource outDir
      pure (if ok then 0 else 3)
    catch e =>
      IO.println s!"he lookup-plan check failed: {e}"
      IO.println "hint: ensure METTAPEDIA_LOOKUP_PLAN_DIR points to generated he artifacts"
      pure 2
  else
    match Algorithms.MeTTa.LookupPlans.lookupPlanByDialect? dialect with
    | none =>
        IO.println s!"unknown lookup-plan dialect: {dialect} (expected: he | petta)"
        pure 1
    | some entry =>
        try
          let ok ← checkOneLookupPlan outDir entry
          pure (if ok then 0 else 3)
        catch e =>
          IO.println s!"lookup-plan check failed: {e}"
          pure 2

private def checkAllLookupPlansCommand (outDir : String) : IO UInt32 := do
  try
    let okHe ← checkHeLookupPlanAgainstSource outDir
    let okPeTTa ← checkOneLookupPlan outDir ("petta", Algorithms.MeTTa.LookupPlans.pettaLookupPlanArtifact)
    pure (if okHe && okPeTTa then 0 else 3)
  catch e =>
    IO.println s!"lookup-plan check-all failed: {e}"
    pure 2

private def exportOneSyntaxSpec (outDir : System.FilePath)
    (entry : String × MeTTailCore.MeTTaSyntax.SyntaxSpec) : IO Unit := do
  let (name, spec) := entry
  IO.FS.createDirAll outDir
  IO.FS.writeFile (syntaxSpecJsonPath outDir name) (spec.renderJson ++ "\n")
  IO.FS.writeFile (syntaxSpecChecksumPath outDir name) (spec.checksumString ++ "\n")

private def exportSyntaxSpecCommand (dialect outDir : String) : IO UInt32 := do
  match lookupSyntaxSpec? dialect with
  | none =>
      IO.println s!"unknown syntax spec dialect: {dialect} (expected: he | petta)"
      pure 1
  | some entry =>
      exportOneSyntaxSpec outDir entry
      IO.println s!"exported {entry.1} syntax spec to {outDir}"
      pure 0

private def exportAllSyntaxSpecsCommand (outDir : String) : IO UInt32 := do
  exportOneSyntaxSpec outDir ("he", MeTTailCore.MeTTaSyntax.he)
  exportOneSyntaxSpec outDir ("petta", MeTTailCore.MeTTaSyntax.petta)
  IO.println s!"exported syntax specs (he, petta) to {outDir}"
  pure 0

private def checkOneSyntaxSpec (outDir : System.FilePath)
    (entry : String × MeTTailCore.MeTTaSyntax.SyntaxSpec) : IO Bool := do
  let (name, spec) := entry
  let jsonPath := syntaxSpecJsonPath outDir name
  let checksumPath := syntaxSpecChecksumPath outDir name
  let expectedJson := spec.renderJson.trimAscii.toString
  let expectedChecksum := spec.checksumString.trimAscii.toString
  let jsonText ← IO.FS.readFile jsonPath
  let checksumText ← IO.FS.readFile checksumPath
  let jsonOk := jsonText.trimAscii.toString == expectedJson
  let checksumOk := checksumText.trimAscii.toString == expectedChecksum
  if jsonOk && checksumOk then
    IO.println s!"[ok] {name} syntax spec matches exported artifacts"
    pure true
  else
    IO.println s!"[drift] {name} syntax spec artifact mismatch"
    if !jsonOk then
      IO.println s!"  json mismatch at {jsonPath}"
    if !checksumOk then
      IO.println s!"  checksum mismatch at {checksumPath}"
    pure false

private def checkSyntaxSpecCommand (dialect outDir : String) : IO UInt32 := do
  match lookupSyntaxSpec? dialect with
  | none =>
      IO.println s!"unknown syntax spec dialect: {dialect} (expected: he | petta)"
      pure 1
  | some entry =>
      try
        let ok ← checkOneSyntaxSpec outDir entry
        pure (if ok then 0 else 3)
      catch e =>
        IO.println s!"syntax spec check failed: {e}"
        pure 2

private def checkAllSyntaxSpecsCommand (outDir : String) : IO UInt32 := do
  try
    let okHe ← checkOneSyntaxSpec outDir ("he", MeTTailCore.MeTTaSyntax.he)
    let okPeTTa ← checkOneSyntaxSpec outDir ("petta", MeTTailCore.MeTTaSyntax.petta)
    pure (if okHe && okPeTTa then 0 else 3)
  catch e =>
    IO.println s!"syntax spec check-all failed: {e}"
    pure 2

private def renderProbeResult (line : String) (res : Except String Algorithms.MeTTa.Simple.Parser.Stmt) : String :=
  match res with
  | .ok stmt => s!"line:{line} => ok:{reprStr stmt}"
  | .error err => s!"line:{line} => error:{err}"

private def renderProbeProgramResult (text : String)
    (res : Except String (List (Nat × Algorithms.MeTTa.Simple.Parser.Stmt))) : String :=
  match res with
  | .ok forms => s!"program:{reprStr text} => ok:{reprStr forms}"
  | .error err => s!"program:{reprStr text} => error:{err}"

private def parserProbeLines (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec) : List String :=
  let grammar := spec.toGrammarSpec
  let evalTok := grammar.evalPrefixToken
  let openTok := grammar.sexprOpen
  let closeTok := grammar.sexprClose
  let atomExpr := openTok ++ "foo" ++ closeTok
  let commentLine := (grammar.lineCommentStart.getD ";") ++ " parser drift probe"
  let evalLine := evalTok ++ atomExpr
  let evalProgram := evalTok ++ "\n" ++ atomExpr ++ "\n"
  let malformedLine := closeTok
  let defineEqLine := "(= (f a) b)"
  let defineEqFallbackLine := "(= (f a))"
  let relationLine := "(" ++ spec.loweringHeads.relationFactHead ++ " edge tim tom)"
  let builtinLine := "(" ++ spec.loweringHeads.builtinFactHead ++ " eq tim tom)"
  let inSpaceLine := "(in-space &tmp (match foo foo))"
  let memoizedLine := "(declare-memoized! fib)"
  let bangWord := "!name"
  let aliasLines :=
    spec.headAliases.map fun a =>
      let aliasProbe := s!"({a.alias} (f a) b)"
      renderProbeResult aliasProbe (Algorithms.MeTTa.Simple.Parser.parseLineWith spec aliasProbe)
  let evalSpaceAliasLines :=
    spec.evalSpaceAliases.map fun a =>
      let args := List.replicate a.arity "foo"
      let exprBody := String.intercalate " " (a.head :: "&tmp" :: args)
      let probe := s!"({exprBody})"
      renderProbeResult probe (Algorithms.MeTTa.Simple.Parser.parseLineWith spec probe)
  [ renderProbeResult commentLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec commentLine)
  , renderProbeResult evalLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec evalLine)
  , renderProbeProgramResult evalProgram (Algorithms.MeTTa.Simple.Parser.parseProgramWith spec evalProgram)
  , renderProbeResult defineEqLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec defineEqLine)
  , renderProbeResult defineEqFallbackLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec defineEqFallbackLine)
  , renderProbeResult relationLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec relationLine)
  , renderProbeResult builtinLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec builtinLine)
  , renderProbeResult inSpaceLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec inSpaceLine)
  , renderProbeResult memoizedLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec memoizedLine)
  , renderProbeResult bangWord (Algorithms.MeTTa.Simple.Parser.parseLineWith spec bangWord)
  , renderProbeResult malformedLine (Algorithms.MeTTa.Simple.Parser.parseLineWith spec malformedLine)
  ] ++ aliasLines ++ evalSpaceAliasLines

private def parserProbeSnapshotText (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec) : String :=
  String.intercalate "\n" (parserProbeLines spec)

private def parserProbeChecksumString (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec) : String :=
  toString (MeTTailCore.MeTTaSyntax.checksumText (parserProbeSnapshotText spec))

private def exportOneGrammarSpec (outDir : System.FilePath)
    (entry : String × MeTTailCore.MeTTaSyntax.GrammarSpec) : IO Unit := do
  let (name, spec) := entry
  IO.FS.createDirAll outDir
  IO.FS.writeFile (grammarSpecJsonPath outDir name) (spec.renderJson ++ "\n")
  IO.FS.writeFile (treeSitterGrammarPath outDir name) spec.renderTreeSitterJs
  IO.FS.writeFile (grammarSpecChecksumPath outDir name) (spec.checksumString ++ "\n")
  match lookupSyntaxSpec? name with
  | none => pure ()
  | some (_, syntaxSpec) =>
      let snapshot := parserProbeSnapshotText syntaxSpec
      let chk := parserProbeChecksumString syntaxSpec
      IO.FS.writeFile (parserProbeSnapshotPath outDir name) (snapshot ++ "\n")
      IO.FS.writeFile (parserProbeChecksumPath outDir name) (chk ++ "\n")

private def exportGrammarSpecCommand (dialect outDir : String) : IO UInt32 := do
  match lookupGrammarSpec? dialect with
  | none =>
      IO.println s!"unknown grammar spec dialect: {dialect} (expected: he | petta)"
      pure 1
  | some entry =>
      exportOneGrammarSpec outDir entry
      IO.println s!"exported {entry.1} grammar spec to {outDir}"
      pure 0

private def exportAllGrammarSpecsCommand (outDir : String) : IO UInt32 := do
  exportOneGrammarSpec outDir ("he", MeTTailCore.MeTTaSyntax.heGrammar)
  exportOneGrammarSpec outDir ("petta", MeTTailCore.MeTTaSyntax.pettaGrammar)
  IO.println s!"exported grammar specs (he, petta) to {outDir}"
  pure 0

private def checkOneGrammarSpec (outDir : System.FilePath)
    (entry : String × MeTTailCore.MeTTaSyntax.GrammarSpec) : IO Bool := do
  let (name, spec) := entry
  let jsonPath := grammarSpecJsonPath outDir name
  let grammarPath := treeSitterGrammarPath outDir name
  let checksumPath := grammarSpecChecksumPath outDir name
  let parserSnapshotPath := parserProbeSnapshotPath outDir name
  let parserChecksumPath := parserProbeChecksumPath outDir name
  let expectedJson := spec.renderJson.trimAscii.toString
  let expectedGrammar := spec.renderTreeSitterJs.trimAscii.toString
  let expectedChecksum := spec.checksumString.trimAscii.toString
  let jsonText ← IO.FS.readFile jsonPath
  let grammarText ← IO.FS.readFile grammarPath
  let checksumText ← IO.FS.readFile checksumPath
  let parserSnapshotText ← IO.FS.readFile parserSnapshotPath
  let parserChecksumText ← IO.FS.readFile parserChecksumPath
  let (parserSnapshotOk, parserChecksumOk) ←
    match lookupSyntaxSpec? name with
    | none => pure (true, true)
    | some (_, syntaxSpec) =>
        let expectedParserSnapshot := parserProbeSnapshotText syntaxSpec
        let expectedParserChecksum := parserProbeChecksumString syntaxSpec
        pure ( parserSnapshotText.trimAscii.toString == expectedParserSnapshot.trimAscii.toString
             , parserChecksumText.trimAscii.toString == expectedParserChecksum.trimAscii.toString)
  let jsonOk := jsonText.trimAscii.toString == expectedJson
  let grammarOk := grammarText.trimAscii.toString == expectedGrammar
  let checksumOk := checksumText.trimAscii.toString == expectedChecksum
  if jsonOk && grammarOk && checksumOk && parserSnapshotOk && parserChecksumOk then
    IO.println s!"[ok] {name} grammar spec matches exported artifacts"
    pure true
  else
    IO.println s!"[drift] {name} grammar spec artifact mismatch"
    if !jsonOk then
      IO.println s!"  json mismatch at {jsonPath}"
    if !grammarOk then
      IO.println s!"  tree-sitter grammar mismatch at {grammarPath}"
    if !checksumOk then
      IO.println s!"  checksum mismatch at {checksumPath}"
    if !parserSnapshotOk then
      IO.println s!"  parser probe snapshot mismatch at {parserSnapshotPath}"
    if !parserChecksumOk then
      IO.println s!"  parser probe checksum mismatch at {parserChecksumPath}"
    pure false

private def checkParserDriftCommand (dialect outDir : String) : IO UInt32 := do
  match lookupSyntaxSpec? dialect with
  | none =>
      IO.println s!"unknown parser drift dialect: {dialect} (expected: he | petta)"
      pure 1
  | some (name, spec) =>
      try
        let snapshotPath := parserProbeSnapshotPath outDir name
        let checksumPath := parserProbeChecksumPath outDir name
        let snapshotText ← IO.FS.readFile snapshotPath
        let checksumText ← IO.FS.readFile checksumPath
        let expectedSnapshot := parserProbeSnapshotText spec
        let expectedChecksum := parserProbeChecksumString spec
        let snapshotOk := snapshotText.trimAscii.toString == expectedSnapshot.trimAscii.toString
        let checksumOk := checksumText.trimAscii.toString == expectedChecksum.trimAscii.toString
        if snapshotOk && checksumOk then
          IO.println s!"[ok] {name} parser drift checks match exported probe artifacts"
          pure 0
        else
          IO.println s!"[drift] {name} parser drift mismatch"
          if !snapshotOk then
            IO.println s!"  probe snapshot mismatch at {snapshotPath}"
          if !checksumOk then
            IO.println s!"  probe checksum mismatch at {checksumPath}"
          pure 3
      catch e =>
        IO.println s!"parser drift check failed: {e}"
        pure 2

private def checkAllParserDriftCommand (outDir : String) : IO UInt32 := do
  let rcHe ← checkParserDriftCommand "he" outDir
  let rcPeTTa ← checkParserDriftCommand "petta" outDir
  pure (if rcHe == 0 && rcPeTTa == 0 then 0 else 3)

private def checkGrammarSpecCommand (dialect outDir : String) : IO UInt32 := do
  match lookupGrammarSpec? dialect with
  | none =>
      IO.println s!"unknown grammar spec dialect: {dialect} (expected: he | petta)"
      pure 1
  | some entry =>
      try
        let ok ← checkOneGrammarSpec outDir entry
        pure (if ok then 0 else 3)
      catch e =>
        IO.println s!"grammar spec check failed: {e}"
        pure 2

private def checkAllGrammarSpecsCommand (outDir : String) : IO UInt32 := do
  try
    let okHe ← checkOneGrammarSpec outDir ("he", MeTTailCore.MeTTaSyntax.heGrammar)
    let okPeTTa ← checkOneGrammarSpec outDir ("petta", MeTTailCore.MeTTaSyntax.pettaGrammar)
    pure (if okHe && okPeTTa then 0 else 3)
  catch e =>
    IO.println s!"grammar spec check-all failed: {e}"
    pure 2

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.ofList [c])
    ""

private def renderDiagnosticsJson (d : Diagnostics) : String :=
  let msgs :=
    d.messages.map (fun m => "\"" ++ jsonEscape m ++ "\"")
  "{"
    ++ "\"parsed_lines\":" ++ toString d.parsedLines ++ ","
    ++ "\"applied_statements\":" ++ toString d.appliedStmts ++ ","
    ++ "\"eval_calls\":" ++ toString d.evalCalls ++ ","
    ++ "\"errors\":" ++ toString d.errors ++ ","
    ++ "\"messages\":[" ++ String.intercalate "," msgs ++ "]"
    ++ "}"

private def renderRunJson (queries : List (Nat × List Pattern)) (diag : Diagnostics) : String :=
  let queryEntries :=
    queries.map fun q =>
      let line := q.1
      let results := q.2.map (fun p => "\"" ++ jsonEscape (renderPattern p) ++ "\"")
      "{"
        ++ "\"line\":" ++ toString line ++ ","
        ++ "\"results\":[" ++ String.intercalate "," results ++ "]"
        ++ "}"
  "{"
    ++ "\"queries\":[" ++ String.intercalate "," queryEntries ++ "],"
    ++ "\"diagnostics\":" ++ renderDiagnosticsJson diag
    ++ "}"

private def basenameOfPathString (s : String) : String :=
  (s.splitOn "/").getLastD s

private def insertModuleSource (acc : List (String × String)) (key text : String) :
    List (String × String) :=
  if key.isEmpty || acc.any (fun p => p.1 == key) then
    acc
  else
    (key, text) :: acc

private def collectSiblingModuleSources (path : System.FilePath) : IO (List (String × String)) := do
  let dir := path.parent.getD (System.FilePath.mk ".")
  let nodes ← System.FilePath.walkDir dir
  let entries :=
    (nodes.toList.filter fun p =>
      p.parent == some dir &&
      match p.extension with
      | some ext => ext = "metta"
      | none => false)
  let mut acc : List (String × String) := []
  for entry in entries do
    let txt ← IO.FS.readFile entry
    let base := basenameOfPathString (toString entry)
    let stem := Algorithms.MeTTa.Simple.Semantics.ImportOps.stripMettaExt base
    acc := insertModuleSource acc stem txt
    acc := insertModuleSource acc base txt
  pure acc

private def runScriptFile (path : System.FilePath) : IO (Session × List (Nat × List Pattern)) := do
  let text ← IO.FS.readFile path
  let moduleSources ← collectSiblingModuleSources path
  let sess0 := Session.withModuleSources emptySession moduleSources
  pure (Session.runText sess0 text)

private def printRunHuman (path : System.FilePath) (queries : List (Nat × List Pattern))
    (diag : Diagnostics) : IO Unit := do
  IO.println s!"file: {path}"
  for q in queries do
    IO.println s!"line {q.1}: {renderPatternList q.2}"
  IO.println s!"diagnostics: parsed={diag.parsedLines} applied={diag.appliedStmts} eval={diag.evalCalls} errors={diag.errors}"
  if !diag.messages.isEmpty then do
    IO.println "messages:"
    for m in diag.messages do
      IO.println s!"  - {m}"

private def runFileCommand (path : System.FilePath) (asJson : Bool) : IO UInt32 := do
  let (sess, queries) ← runScriptFile path
  let diag := Session.diagnostics sess
  if asJson then
    IO.println (renderRunJson queries diag)
  else
    printRunHuman path queries diag
  pure (if diag.errors = 0 then 0 else 2)

private def collectMettaFiles (root : System.FilePath) : IO (List System.FilePath) := do
  let nodes ← System.FilePath.walkDir root
  pure <| (nodes.toList.filter fun p =>
    match p.extension with
    | some ext => ext = "metta"
    | none => false)

private def sortFiles (files : List System.FilePath) : List System.FilePath :=
  (files.toArray.qsort (fun a b => toString a < toString b)).toList

private def nthNat (xs : List Nat) (idx : Nat) : Nat :=
  xs.getD idx 0

private def medianMs (xs : List Nat) : Float :=
  let ys := (xs.toArray.qsort (fun a b => a < b)).toList
  let n := ys.length
  if n = 0 then
    0.0
  else if n % 2 = 1 then
    Float.ofNat (nthNat ys (n / 2))
  else
    let a := Float.ofNat (nthNat ys (n / 2 - 1))
    let b := Float.ofNat (nthNat ys (n / 2))
    (a + b) / 2.0

private def p95Ms (xs : List Nat) : Nat :=
  let ys := (xs.toArray.qsort (fun a b => a < b)).toList
  let n := ys.length
  if n = 0 then
    0
  else
    let idxRaw := (n * 95 + 99) / 100
    let idx :=
      if idxRaw = 0 then 0 else idxRaw - 1
    nthNat ys idx

private def relativizeToRoot (root path : System.FilePath) : String :=
  let rootStr := toString root
  let pathStr := toString path
  if pathStr.startsWith rootStr then
    let suffix := (pathStr.drop rootStr.length).toString
    if suffix.startsWith "/" then
      (suffix.drop 1).toString
    else
      suffix
  else
    pathStr

private def writeSplitFiles (outDir root : System.FilePath)
    (passing failing : List System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  let passingPath := outDir / "lean_petta_strict_positive.txt"
  let failingPath := outDir / "lean_petta_strict_failing.txt"
  let passingText :=
    String.intercalate "\n" (passing.map (relativizeToRoot root)) ++ "\n"
  let failingText :=
    String.intercalate "\n" (failing.map (relativizeToRoot root)) ++ "\n"
  IO.FS.writeFile passingPath passingText
  IO.FS.writeFile failingPath failingText

private def containsAny (hay : String) (needles : List String) : Bool :=
  needles.any (fun n => hay.contains n)

private def classifyFeatures (path text : String) : Bool × Bool × Bool :=
  let s := path ++ "\n" ++ text
  let booleanNeedles :=
    [ "(if", "(and", "(or", "(not", "(xor", " True", " False", " true", " false" ]
  let arithmeticNeedles :=
    [ "pow-math", "sqrt-math", "abs-math", "log-math"
    , "trunc-math", "ceil-math", "floor-math", "round-math"
    , "sin-math", "asin-math", "cos-math", "acos-math", "tan-math", "atan-math"
    , "(+", "(-", "(*", "(/", "(%", "(==", "(!=", "(<", "(>", "(<=", "(>="
    ]
  let matchNeedles :=
    [ "(match", "spaceMatch", "&self", "add-atom", "remove-atom", "get-atoms", "collapse" ]
  (containsAny s booleanNeedles, containsAny s arithmeticNeedles, containsAny s matchNeedles)

private def writeFeatureBuckets (outDir root : System.FilePath)
    (booleanAll arithmeticAll matchAll : List System.FilePath)
    (booleanOk arithmeticOk matchOk : List System.FilePath)
    (booleanMin arithmeticMin matchMin : Nat) : IO Unit := do
  IO.FS.createDirAll outDir
  let rel := relativizeToRoot root
  let writeList (name : String) (xs : List System.FilePath) : IO Unit := do
    let p := outDir / name
    IO.FS.writeFile p (String.intercalate "\n" (xs.map rel) ++ "\n")
  writeList "lean_petta_feature_boolean_all.txt" booleanAll
  writeList "lean_petta_feature_arithmetic_all.txt" arithmeticAll
  writeList "lean_petta_feature_match_all.txt" matchAll
  writeList "lean_petta_feature_boolean_ok.txt" booleanOk
  writeList "lean_petta_feature_arithmetic_ok.txt" arithmeticOk
  writeList "lean_petta_feature_match_ok.txt" matchOk
  let expectedPath := outDir / "lean_petta_feature_gate_expected.txt"
  let expectedText := String.intercalate "\n"
    [ "# strict feature gate minima (generated)"
    , s!"boolean_min_ok={booleanMin}"
    , s!"arithmetic_min_ok={arithmeticMin}"
    , s!"match_min_ok={matchMin}"
    ]
  IO.FS.writeFile expectedPath (expectedText ++ "\n")

private def parseMinLine (line key : String) : Option Nat :=
  if line.startsWith key then
    ((line.drop key.length).toString).toNat?
  else
    none

private def readFeatureGateExpected (path : System.FilePath) : IO (Nat × Nat × Nat) := do
  let text ← IO.FS.readFile path
  let lines := text.splitOn "\n"
  let mut b : Nat := 0
  let mut a : Nat := 0
  let mut m : Nat := 0
  for raw in lines do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then
      pure ()
    else
      match parseMinLine line "boolean_min_ok=" with
      | some n => b := n
      | none =>
          match parseMinLine line "arithmetic_min_ok=" with
          | some n => a := n
          | none =>
              match parseMinLine line "match_min_ok=" with
              | some n => m := n
              | none => pure ()
  pure (b, a, m)

private def runStrictBenchmark (root : System.FilePath)
    (writeSplitDir? : Option System.FilePath := none)
    (writeFeatureDir? : Option System.FilePath := none)
    (featureGateExpected? : Option System.FilePath := none)
    (gateOnly : Bool := false) : IO UInt32 := do
  let files ← collectMettaFiles root
  let files := sortFiles files
  if files.isEmpty then
    IO.println s!"no .metta files found under: {root}"
    return 1
  let mut ok : Nat := 0
  let mut failed : Nat := 0
  let mut sumMs : Nat := 0
  let mut times : List Nat := []
  let mut passing : List System.FilePath := []
  let mut failing : List System.FilePath := []
  let mut booleanTotal : Nat := 0
  let mut booleanOkN : Nat := 0
  let mut arithmeticTotal : Nat := 0
  let mut arithmeticOkN : Nat := 0
  let mut matchTotal : Nat := 0
  let mut matchOkN : Nat := 0
  let mut booleanAll : List System.FilePath := []
  let mut arithmeticAll : List System.FilePath := []
  let mut matchAll : List System.FilePath := []
  let mut booleanOkFiles : List System.FilePath := []
  let mut arithmeticOkFiles : List System.FilePath := []
  let mut matchOkFiles : List System.FilePath := []
  for f in files do
    let src ← IO.FS.readFile f
    let (hasBool, hasArith, hasMatch) := classifyFeatures (toString f) src
    let t0 ← IO.monoMsNow
    let (sess, _queries) ← runScriptFile f
    let t1 ← IO.monoMsNow
    let elapsed := t1 - t0
    let diag := Session.diagnostics sess
    sumMs := sumMs + elapsed
    times := elapsed :: times
    if hasBool then
      booleanTotal := booleanTotal + 1
      booleanAll := f :: booleanAll
    if hasArith then
      arithmeticTotal := arithmeticTotal + 1
      arithmeticAll := f :: arithmeticAll
    if hasMatch then
      matchTotal := matchTotal + 1
      matchAll := f :: matchAll
    if diag.errors = 0 then
      ok := ok + 1
      passing := f :: passing
      if hasBool then
        booleanOkN := booleanOkN + 1
        booleanOkFiles := f :: booleanOkFiles
      if hasArith then
        arithmeticOkN := arithmeticOkN + 1
        arithmeticOkFiles := f :: arithmeticOkFiles
      if hasMatch then
        matchOkN := matchOkN + 1
        matchOkFiles := f :: matchOkFiles
      IO.println s!"[ok] {f} ms={elapsed}"
    else
      failed := failed + 1
      failing := f :: failing
      IO.println s!"[fail] {f} errors={diag.errors} ms={elapsed}"
  match writeSplitDir? with
  | some outDir =>
      writeSplitFiles outDir root passing.reverse failing.reverse
      IO.println s!"wrote split files under: {outDir}"
  | none => pure ()
  match writeFeatureDir? with
  | some outDir =>
      writeFeatureBuckets outDir root
        booleanAll.reverse arithmeticAll.reverse matchAll.reverse
        booleanOkFiles.reverse arithmeticOkFiles.reverse matchOkFiles.reverse
        booleanOkN arithmeticOkN matchOkN
      IO.println s!"wrote feature buckets under: {outDir}"
  | none => pure ()
  let total := files.length
  let passRate :=
    if total = 0 then
      0.0
    else
      (Float.ofNat ok * 100.0) / Float.ofNat total
  let meanMs :=
    if total = 0 then
      0.0
    else
      Float.ofNat sumMs / Float.ofNat total
  let medMs := medianMs times
  let p95 := p95Ms times
  IO.println s!"strict benchmark summary: ok={ok} fail={failed} total={total} pass_rate={passRate}%"
  IO.println s!"timing ms: total={sumMs} mean={meanMs} median={medMs} p95={p95}"
  IO.println s!"feature boolean: ok={booleanOkN} total={booleanTotal}"
  IO.println s!"feature arithmetic: ok={arithmeticOkN} total={arithmeticTotal}"
  IO.println s!"feature match: ok={matchOkN} total={matchTotal}"
  let mut gatePass := true
  match featureGateExpected? with
  | some gatePath =>
      let (minB, minA, minM) ← readFeatureGateExpected gatePath
      let bPass : Bool := decide (booleanOkN >= minB)
      let aPass : Bool := decide (arithmeticOkN >= minA)
      let mPass : Bool := decide (matchOkN >= minM)
      gatePass := bPass && aPass && mPass
      IO.println s!"feature gate expected: boolean>={minB} arithmetic>={minA} match>={minM}"
      IO.println s!"feature gate status: boolean={bPass} arithmetic={aPass} match={mPass}"
  | none => pure ()
  if gateOnly then
    pure (if gatePass then 0 else 3)
  else if !gatePass then
    pure 3
  else
    pure (if failed = 0 then 0 else 2)

private def runCorpus (root : System.FilePath) : IO UInt32 := do
  let files ← collectMettaFiles root
  if files.isEmpty then
    IO.println s!"no .metta files found under: {root}"
    return 1
  let mut ok : Nat := 0
  let mut failed : Nat := 0
  for f in files do
    let (sess, _queries) ← runScriptFile f
    let diag := Session.diagnostics sess
    if diag.errors = 0 then
      ok := ok + 1
      IO.println s!"[ok] {f}"
    else
      failed := failed + 1
      IO.println s!"[fail] {f} errors={diag.errors}"
  IO.println s!"corpus summary: ok={ok} fail={failed} total={files.length}"
  pure (if failed = 0 then 0 else 2)

private partial def replLoop (sess : Session) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStr "metta> "
  out.flush
  let line ← (← IO.getStdin).getLine
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    replLoop sess
  else if trimmed = ":q" || trimmed = ":quit" then
    pure 0
  else if trimmed = ":diag" then
    let d := Session.diagnostics sess
    IO.println s!"parsed={d.parsedLines} applied={d.appliedStmts} eval={d.evalCalls} errors={d.errors}"
    replLoop sess
  else if trimmed = ":space" then
    IO.println s!"rules={sess.bundle.language.rewrites.length}"
    replLoop sess
  else if trimmed.startsWith ":load " then
    let path := ((trimmed.drop 6).trimAscii).toString
    if path.isEmpty then
      IO.println "usage: :load <file.metta>"
      replLoop sess
    else
      try
        let sess' ← Session.loadFile sess path
        IO.println s!"loaded {path}"
        replLoop sess'
      catch e =>
        IO.println s!"load failed: {e}"
        replLoop sess
  else if trimmed.startsWith ":eval " then
    let expr := ((trimmed.drop 6).trimAscii).toString
    match Session.evalExpr sess expr with
    | .ok (sess', out') =>
        IO.println (renderPatternList out')
        replLoop sess'
    | .error err =>
        IO.println s!"eval parse error: {err}"
        replLoop sess
  else
    match Session.parseLine trimmed with
    | .ok stmt =>
        let (sess', out') := Session.applyStmt sess stmt
        if !out'.isEmpty then
          IO.println (renderPatternList out')
        replLoop sess'
    | .error err =>
        IO.println s!"parse error: {err}"
        replLoop sess

private def usage : String :=
  String.intercalate "\n"
    [ "simpleMeTTa commands:"
    , "  run <file.metta>"
    , "  run --json <file.metta>"
    , "  test-corpus <path>"
    , "  strict-benchmark <path>"
    , "  strict-benchmark --write-split <out-dir> <path>"
    , "  strict-benchmark --write-feature-buckets <out-dir> <path>"
    , "  strict-gate <expected-file> <path>"
    , "  syntax-spec export <he|petta> <out-dir>"
    , "  syntax-spec export-all <out-dir>"
    , "  syntax-spec check <he|petta> <out-dir>"
    , "  syntax-spec check-all <out-dir>"
    , "  syntax-spec export-grammar <he|petta> <out-dir>"
    , "  syntax-spec export-grammar-all <out-dir>"
    , "  syntax-spec check-grammar <he|petta> <out-dir>"
    , "  syntax-spec check-grammar-all <out-dir>"
    , "  syntax-spec check-parser-drift <he|petta> <out-dir>"
    , "  syntax-spec check-parser-drift-all <out-dir>"
    , "  lookup-plan export <he|petta> <out-dir>"
    , "  lookup-plan export-all <out-dir>"
    , "  lookup-plan check <he|petta> <out-dir>"
    , "  lookup-plan check-all <out-dir>"
    , "  repl"
    ]

def mainImpl (args : List String) : IO UInt32 := do
  match args with
  | ["run", "--json", file] => runFileCommand file true
  | ["run", file] => runFileCommand file false
  | ["test-corpus", path] => runCorpus path
  | ["strict-benchmark", path] => runStrictBenchmark path
  | ["strict-benchmark", "--write-split", outDir, path] =>
      runStrictBenchmark path (some outDir)
  | ["strict-benchmark", "--write-feature-buckets", outDir, path] =>
      runStrictBenchmark path none (some outDir)
  | ["strict-gate", expected, path] =>
      runStrictBenchmark path none none (some expected) true
  | ["syntax-spec", "export", dialect, outDir] =>
      exportSyntaxSpecCommand dialect outDir
  | ["syntax-spec", "export-all", outDir] =>
      exportAllSyntaxSpecsCommand outDir
  | ["syntax-spec", "check", dialect, outDir] =>
      checkSyntaxSpecCommand dialect outDir
  | ["syntax-spec", "check-all", outDir] =>
      checkAllSyntaxSpecsCommand outDir
  | ["syntax-spec", "export-grammar", dialect, outDir] =>
      exportGrammarSpecCommand dialect outDir
  | ["syntax-spec", "export-grammar-all", outDir] =>
      exportAllGrammarSpecsCommand outDir
  | ["syntax-spec", "check-grammar", dialect, outDir] =>
      checkGrammarSpecCommand dialect outDir
  | ["syntax-spec", "check-grammar-all", outDir] =>
      checkAllGrammarSpecsCommand outDir
  | ["syntax-spec", "check-parser-drift", dialect, outDir] =>
      checkParserDriftCommand dialect outDir
  | ["syntax-spec", "check-parser-drift-all", outDir] =>
      checkAllParserDriftCommand outDir
  | ["lookup-plan", "export", dialect, outDir] =>
      exportLookupPlanCommand dialect outDir
  | ["lookup-plan", "export-all", outDir] =>
      exportAllLookupPlansCommand outDir
  | ["lookup-plan", "check", dialect, outDir] =>
      checkLookupPlanCommand dialect outDir
  | ["lookup-plan", "check-all", outDir] =>
      checkAllLookupPlansCommand outDir
  | ["repl"] => replLoop emptySession
  | [file] => runFileCommand file false
  | _ =>
      IO.println usage
      pure 1

end Algorithms.MeTTa.Simple.Main

def main (args : List String) : IO UInt32 :=
  Algorithms.MeTTa.Simple.Main.mainImpl args
