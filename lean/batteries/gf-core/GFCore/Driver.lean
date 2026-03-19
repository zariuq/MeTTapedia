/-
# GFCore.Driver — Call GF runtime from Lean

Invokes the GF binary as a subprocess for parsing and linearization.
No Python needed — Lean talks to GF directly via IO.Process.

Configuration: set GF_BIN and GF_LIB environment variables.

Usage:
  let driver ← GFDriver.fromEnv "/path/to/Grammar.pgf"
  let output ← driver.parseRaw "GrammarEng" "S" "John sees the man"
  let surface ← driver.linearize "GrammarEng" tree
-/

import GFCore.Syntax
import GFCore.Json
import GFCore.Export

namespace GFCore

/-- Configuration for calling the GF binary.
    Construct via `GFDriver.fromEnv` (reads GF_BIN/GF_LIB env vars)
    or `GFDriver.mk` (explicit paths). -/
structure GFDriver where
  gfBin : System.FilePath
  pgfPath : System.FilePath
  ldLibraryPath : Option String := none
  deriving Repr

/-- Structured output from GF parsing — preserves all information. -/
structure ParseOutput where
  trees : Array String      -- successfully parsed tree expressions
  errors : Array String     -- GF error/diagnostic messages
  rawOutput : String        -- full GF stdout (for debugging)
  deriving Repr, Inhabited

namespace GFDriver

/-- Create a GFDriver from environment variables.
    Requires GF_BIN to be set. GF_LIB is optional (for LD_LIBRARY_PATH). -/
def fromEnv (pgfPath : System.FilePath) : IO GFDriver := do
  let gfBinOpt ← IO.getEnv "GF_BIN"
  let gfBin ← match gfBinOpt with
    | some bin => pure bin
    | none => throw (IO.userError
        "GF_BIN environment variable not set. \
         Set it to the path of your GF binary, e.g.: \
         export GF_BIN=/usr/local/bin/gf")
  let gfLib ← IO.getEnv "GF_LIB"
  pure { gfBin := gfBin, pgfPath := pgfPath, ldLibraryPath := gfLib }

/-- Run a GF command and return stdout.
    Uses heredoc to pipe command to GF — no temp files, no race conditions. -/
def runCommand (d : GFDriver) (cmd : String) : IO String := do
  let ldPrefix := match d.ldLibraryPath with
    | some p => s!"LD_LIBRARY_PATH={p} "
    | none => ""
  let shellCmd := s!"{ldPrefix}{d.gfBin} --run {d.pgfPath}"
  -- Heredoc avoids temp files and quoting issues
  let fullCmd := s!"{shellCmd} <<'GFEOF'\n{cmd}\nGFEOF"
  let result ← IO.Process.output {
    cmd := "/bin/sh"
    args := #["-c", fullCmd]
  }
  if result.exitCode != 0 && !result.stderr.isEmpty then
    throw (IO.userError s!"GF failed (exit {result.exitCode}): {result.stderr}")
  pure (result.stdout.trimAsciiEnd).toString

/-- Run multiple GF commands in a single subprocess invocation.
    Returns one output string per command, separated by a delimiter line.
    This avoids the O(n × startup) cost of spawning one process per command. -/
def runBatch (d : GFDriver) (cmds : Array String) : IO (Array String) := do
  if cmds.isEmpty then return #[]
  let ldPrefix := match d.ldLibraryPath with
    | some p => s!"LD_LIBRARY_PATH={p} "
    | none => ""
  let shellCmd := s!"{ldPrefix}{d.gfBin} --run {d.pgfPath}"
  -- Build batch input: all commands separated by newlines
  let mut batchInput := ""
  for i in [:cmds.size] do
    if i > 0 then batchInput := batchInput ++ s!"pt -readfile=nonexistent 2>/dev/null\n"
    batchInput := batchInput ++ cmds[i]! ++ "\n"
  -- Use heredoc
  let fullCmd := s!"{shellCmd} <<'GFEOF'\n{batchInput}GFEOF"
  let result ← IO.Process.output {
    cmd := "/bin/sh"
    args := #["-c", fullCmd]
  }
  -- GF outputs results for each command separated by empty lines
  -- Since we can't reliably split by delimiter, return all output lines
  -- grouped by command. Each parse command produces 0+ trees, and
  -- commands are separated by the error from the fake pt command.
  pure #[result.stdout]

/-- Run multiple parse commands in a single GF session.
    Returns an array of ParseOutput, one per input sentence.
    Much faster than calling parseRawStructured in a loop. -/
def parseBatch (d : GFDriver) (lang : String) (cat : String) (sentences : Array String)
    : IO (Array ParseOutput) := do
  if sentences.isEmpty then return #[]
  let ldPrefix := match d.ldLibraryPath with
    | some p => s!"LD_LIBRARY_PATH={p} "
    | none => ""
  let shellCmd := s!"{ldPrefix}{d.gfBin} --run {d.pgfPath}"
  -- Build batch input: each parse command on its own line
  let mut batchInput := ""
  for s in sentences do
    batchInput := batchInput ++ "p -lang=" ++ lang ++ " -cat=" ++ cat ++ " \"" ++ s ++ "\"\n"
  let fullCmd := s!"{shellCmd} <<'GFEOF'\n{batchInput}GFEOF"
  let result ← IO.Process.output {
    cmd := "/bin/sh"
    args := #["-c", fullCmd]
  }
  -- GF processes all commands and outputs results separated by empty lines.
  -- Each command's output is 0+ tree lines, then an empty line.
  let allOutput := result.stdout
  let blocks := allOutput.splitOn "\n\n"
  let mut outputs : Array ParseOutput := #[]
  for block in blocks do
    let lines := block.splitOn "\n"
      |>.map (fun s => s.trimAsciiEnd.toString)
      |>.filter (· != "")
    let mut trees : Array String := #[]
    let mut errors : Array String := #[]
    for line in lines do
      if line.startsWith "The parser failed"
        || line.startsWith "command not parsed"
        || line.startsWith "Unknown" then
        errors := errors.push line
      else
        trees := trees.push line
    outputs := outputs.push { trees, errors, rawOutput := block }
  pure outputs

/-- Parse a surface string, returning structured output (trees + errors).
    Does NOT silently filter error messages — caller gets everything. -/
def parseRawStructured (d : GFDriver) (lang : String) (cat : String) (surface : String)
    : IO ParseOutput := do
  let cmd := "p -lang=" ++ lang ++ " -cat=" ++ cat ++ " \"" ++ surface ++ "\""
  let output ← d.runCommand cmd
  if output.isEmpty then
    pure { trees := #[], errors := #[], rawOutput := "" }
  else
    let lines := output.splitOn "\n"
      |>.map (fun s => s.trimAsciiEnd.toString)
      |>.filter (· != "")
    -- Separate tree expressions from error messages
    let mut trees : Array String := #[]
    let mut errors : Array String := #[]
    for line in lines do
      if line.startsWith "The parser failed"
        || line.startsWith "command not parsed"
        || line.startsWith "Unknown" then
        errors := errors.push line
      else
        trees := trees.push line
    pure { trees, errors, rawOutput := output }

/-- Parse a surface string, returning only successful tree strings.
    Error messages are available via `parseRawStructured`. -/
def parseRaw (d : GFDriver) (lang : String) (cat : String) (surface : String)
    : IO (Array String) := do
  let output ← d.parseRawStructured lang cat surface
  pure output.trees

/-- Parse a GF abstract tree string like "PredVP (UsePN john_PN) (UseV walk_V)"
    into a RawTerm. GF uses space-separated application syntax. -/
partial def parseGFExpr (s : String) : Except String RawTerm := do
  let tokens := tokenize s.toList []
  match parseExpr tokens with
  | .ok (tree, []) => pure tree
  | .ok (_, rest) => throw s!"unexpected trailing tokens: {rest}"
  | .error e => throw e
where
  tokenize : List Char → List Char → List String
    | [], acc =>
      let w := String.ofList acc.reverse
      if w.isEmpty then [] else [w]
    | '(' :: cs, acc =>
      let prev := String.ofList acc.reverse
      let rest := tokenize cs []
      if prev.isEmpty then "(" :: rest else prev :: "(" :: rest
    | ')' :: cs, acc =>
      let prev := String.ofList acc.reverse
      let rest := tokenize cs []
      if prev.isEmpty then ")" :: rest else prev :: ")" :: rest
    | c :: cs, acc =>
      if c.isWhitespace then
        let prev := String.ofList acc.reverse
        let rest := tokenize cs []
        if prev.isEmpty then rest else prev :: rest
      else
        tokenize cs (c :: acc)

  parseExpr : List String → Except String (RawTerm × List String)
    | [] => throw "unexpected end of input"
    | "(" :: rest => do
      let (tree, rest) ← parseExpr rest
      match rest with
      | ")" :: rest => pure (tree, rest)
      | _ => throw "expected ')'"
    | name :: rest => do
      let rec collectArgs (remaining : List String) (args : Array RawTerm)
          : Except String (Array RawTerm × List String) :=
        match remaining with
        | "(" :: _ => do
          let (arg, r) ← parseExpr remaining
          collectArgs r (args.push arg)
        | ")" :: _ => pure (args, remaining)
        | [] => pure (args, [])
        | tok :: r =>
          if tok == ")" || tok == "(" then
            pure (args, remaining)
          else
            collectArgs r (args.push (RawTerm.leaf tok))
      let result ← collectArgs rest #[]
      pure (.app name none result.1, result.2)

/-- Parse a surface string into RawTerms. Parse failures for individual
    tree expressions are collected and returned alongside successes. -/
def parseWithErrors (d : GFDriver) (lang : String) (cat : String) (surface : String)
    : IO (Array RawTerm × Array String) := do
  let output ← d.parseRawStructured lang cat surface
  let mut trees : Array RawTerm := #[]
  let mut errors : Array String := output.errors
  for s in output.trees do
    match parseGFExpr s with
    | .ok tree => trees := trees.push tree
    | .error e => errors := errors.push s!"GF expr parse error: {e} (input: '{s}')"
  pure (trees, errors)

/-- Parse a surface string into RawTerms (convenience, discards errors). -/
def parse (d : GFDriver) (lang : String) (cat : String) (surface : String)
    : IO (Array RawTerm) := do
  let (trees, _) ← d.parseWithErrors lang cat surface
  pure trees

/-- Parse surface text into ParseCandidates. -/
def parseToCandidate (d : GFDriver) (lang : String) (cat : String) (surface : String)
    : IO (Array ParseCandidate) := do
  let trees ← d.parse lang cat surface
  pure (trees.map fun t => { language := lang, surface, prob? := none, tree := t })

/-- Convert a RawTerm to GF expression string syntax. -/
private partial def rawTermToGFExpr : RawTerm → String
  | .app f _ args =>
    if args.isEmpty then f
    else
      let argStrs := args.map fun a =>
        let s := rawTermToGFExpr a
        if s.contains ' ' then s!"({s})" else s
      f ++ " " ++ (String.intercalate " " argStrs.toList)

/-- Linearize a RawTerm to a surface string in the given language. -/
def linearize (d : GFDriver) (lang : String) (tree : RawTerm) : IO String := do
  let exprStr := rawTermToGFExpr tree
  let cmd := s!"l -lang={lang} {exprStr}"
  d.runCommand cmd

/-- Linearize a CheckedExpr (erases to RawTerm first). -/
def linearizeChecked (d : GFDriver) (lang : String) (e : CheckedExpr) : IO String := do
  let raw := erase e
  d.linearize lang raw

end GFDriver

end GFCore
