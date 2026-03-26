import Algorithms.MeTTa.Eval.Eval

/-! # LeanPeTTa CLI — Minimal .metta file runner -/

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Eval

-- ─── Pretty printer ──────────────────────────────────────────────────────

private def ppPattern : Pattern → String
  | .apply c [] => c
  | .apply "" args => s!"({" ".intercalate (args.map ppPattern)})"
  | .apply c args => s!"({c} {" ".intercalate (args.map ppPattern)})"
  | .fvar n => s!"${n}"
  | _ => "?"

-- ─── Minimal S-expression parser ─────────────────────────────────────────

private structure ParseState where
  input : String
  pos : Nat := 0

private def ParseState.peek (st : ParseState) : Option Char :=
  if h : st.pos < st.input.length then some (st.input.get ⟨st.pos⟩) else none

private def ParseState.advance (st : ParseState) : ParseState :=
  { st with pos := st.pos + 1 }

private partial def skipWS (st : ParseState) : ParseState :=
  match st.peek with
  | some ' ' | some '\n' | some '\r' | some '\t' => skipWS st.advance
  | some ';' => skipWS (skipLine st.advance)
  | _ => st
where
  skipLine (st : ParseState) : ParseState :=
    match st.peek with
    | some '\n' => st.advance
    | some _ => skipLine st.advance
    | none => st

private partial def parseAtom (st : ParseState) (acc : String := "") : String × ParseState :=
  match st.peek with
  | some c =>
      if c == ' ' || c == '\n' || c == '\r' || c == '\t' || c == '(' || c == ')' || c == ';' then
        (acc, st)
      else parseAtom st.advance (acc.push c)
  | none => (acc, st)

private partial def parseSExpr (st : ParseState) : Option (Pattern × ParseState) :=
  let st := skipWS st
  match st.peek with
  | some '(' =>
      let (elems, st) := parseSExprList st.advance
      let st := skipWS st
      let st := match st.peek with | some ')' => st.advance | _ => st
      match elems with
      | [] => some (.apply "()" [], st)
      | (.apply ctor []) :: args => some (.apply ctor args, st)
      | _ => some (.apply "" elems, st)
  | some '$' =>
      let (name, st) := parseAtom st.advance
      some (.fvar name, st)
  | some '"' =>
      let (str, st) := parseString st.advance
      some (.apply s!"\"{str}\"" [], st)
  | some _ =>
      let (name, st) := parseAtom st
      if name.isEmpty then none
      else some (.apply name [], st)
  | none => none
where
  parseSExprList (st : ParseState) : List Pattern × ParseState :=
    let st := skipWS st
    match st.peek with
    | some ')' | none => ([], st)
    | _ =>
      match parseSExpr st with
      | some (elem, st) =>
          let (rest, st) := parseSExprList st
          (elem :: rest, st)
      | none => ([], st)
  parseString (st : ParseState) (acc : String := "") : String × ParseState :=
    match st.peek with
    | some '"' => (acc, st.advance)
    | some c => parseString st.advance (acc.push c)
    | none => (acc, st)

-- ─── Statement types ─────────────────────────────────────────────────────

private inductive Stmt
  | eval (expr : Pattern)
  | defineEq (lhs rhs : Pattern)
  | fact (p : Pattern)
  | importFile (space : Pattern) (path : Pattern)
  | typeDecl (p : Pattern)  -- (: name type) — type annotations stored as facts
  | empty

private def parseStmt (line : String) : Stmt :=
  let line := line.trim
  if line.isEmpty || line.startsWith ";" then .empty
  else if line.startsWith "!(" then
    match parseSExpr { input := line, pos := 1 } with
    | some (.apply "import!" [space, path], _) => .importFile space path
    | some (expr, _) => .eval expr
    | none => .empty
  else if line.startsWith "(" then
    match parseSExpr { input := line, pos := 0 } with
    | some (.apply "=" [lhs, rhs], _) => .defineEq lhs rhs
    | some (.apply ":" args, _) => .typeDecl (.apply ":" args)
    | some (p, _) => .fact p
    | none => .empty
  else .empty

-- ─── File runner ─────────────────────────────────────────────────────────

/-- Count net open parens in a string. -/
private def parenDepth (s : String) : Int :=
  s.foldl (fun d c => if c == '(' then d + 1 else if c == ')' then d - 1 else d) 0

/-- Split file content into balanced top-level expressions. -/
private def splitTopLevel (content : String) : List (Nat × String) :=
  let lines := content.splitOn "\n"
  go lines 1 "" 0 0 []
where
  go : List String → Nat → String → Int → Nat → List (Nat × String) → List (Nat × String)
    | [], _, acc, _, startLine, result =>
        if acc.isEmpty then result else result ++ [(startLine, acc)]
    | line :: rest, lineNum, acc, depth, startLine, result =>
        let trimmed := line.trim
        if trimmed.isEmpty || (trimmed.startsWith ";" && depth == 0 && acc.isEmpty) then
          go rest (lineNum + 1) acc depth startLine result
        else
          let startLine' := if acc.isEmpty then lineNum else startLine
          let acc' := if acc.isEmpty then trimmed else acc ++ " " ++ trimmed
          let depth' := depth + parenDepth trimmed
          if depth' == 0 && !acc'.isEmpty then
            go rest (lineNum + 1) "" 0 0 (result ++ [(startLine', acc')])
          else
            go rest (lineNum + 1) acc' depth' startLine' result

/-- Load a .metta file's statements into a session (no query output). -/
private partial def loadFile (s : Session) (path : System.FilePath)
    (imported : List String := []) : IO Session := do
  let pathStr := path.toString
  if imported.contains pathStr then return s  -- already imported
  let imported' := pathStr :: imported
  let content ← IO.FS.readFile path |>.catchExceptions fun _ => pure ""
  if content.isEmpty then return s
  let baseDir := path.parent.getD ⟨"."⟩
  let stmts := splitTopLevel content
  let mut s' := s
  for (_, text) in stmts do
    match parseStmt text with
    | .eval expr =>
        let (s'', _results) := evalWithState s' expr
        s' := s''
    | .defineEq lhs rhs =>
        let rule : Rule := { name := s!"rule_{s'.rules.length}", left := lhs, right := rhs }
        s' := { s' with rules := s'.rules ++ [rule] }
    | .fact p =>
        s' := { s' with space := p :: s'.space }
    | .typeDecl p =>
        s' := { s' with space := p :: s'.space }
    | .importFile _space importPath =>
        -- Resolve relative path
        let pathAtom : String := match importPath with
          | .apply p [] => p
          | _ => toString (repr importPath)
        let resolved := baseDir / pathAtom
        -- Try with and without .metta extension
        let resolvedMetta : System.FilePath :=
          if pathAtom.endsWith ".metta" then resolved
          else ⟨resolved.toString ++ ".metta"⟩
        s' ← loadFile s' resolvedMetta imported'
    | .empty => pure ()
  return s'

private def runFile (path : System.FilePath) (json : Bool) : IO UInt32 := do
  let content ← IO.FS.readFile path
  let baseDir := path.parent.getD ⟨"."⟩
  let stmts := splitTopLevel content
  let mut s : Session := { maxFuel := 1000 }
  let mut queries : List (Nat × List Pattern) := []
  let mut evalCalls := 0
  let mut errors := 0

  for (lineNum, text) in stmts do
    match parseStmt text with
    | .eval expr =>
        evalCalls := evalCalls + 1
        -- Handle println! specially (needs IO)
        match expr with
        | .apply "println!" args =>
            let (s', results) := evalWithState s (match args with | [a] => a | _ => .apply "" args)
            s := s'
            let output := results.map ppPattern |> " ".intercalate
            IO.println output
        | _ =>
            let (s', results) := evalWithState s expr
            s := s'
            queries := queries ++ [(lineNum, results)]
    | .defineEq lhs rhs =>
        let rule : Rule := { name := s!"rule_{s.rules.length}", left := lhs, right := rhs }
        s := { s with rules := s.rules ++ [rule] }
    | .fact p =>
        s := { s with space := p :: s.space }
    | .typeDecl p =>
        s := { s with space := p :: s.space }
    | .importFile _space importPath =>
        let pathAtom : String := match importPath with
          | .apply p [] => p
          | _ => toString (repr importPath)
        let resolved : System.FilePath := baseDir / pathAtom
        let resolvedMetta : System.FilePath :=
          if pathAtom.endsWith ".metta" then resolved
          else ⟨resolved.toString ++ ".metta"⟩
        s ← loadFile s resolvedMetta
    | .empty => pure ()

  if json then
    let queriesJson := queries.map fun (ln, results) =>
      let resultsJson := results.map (fun r => s!"\"{ppPattern r}\"") |> ", ".intercalate
      s!"\{\"line\":{ln},\"results\":[{resultsJson}]}"
    IO.println s!"\{\"queries\":[{", ".intercalate queriesJson}],\"diagnostics\":\{\"eval_calls\":{evalCalls},\"errors\":{errors}}}"
  else
    for (ln, results) in queries do
      IO.println s!"[line {ln}] [{" ".intercalate (results.map ppPattern)}]"

  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", path] => runFile ⟨path⟩ false
  | ["run", "--json", path] => runFile ⟨path⟩ true
  | ["test-corpus", dir] =>
      let entries ← System.FilePath.readDir ⟨dir⟩
      let mettaFiles := entries.filter (fun e => e.fileName.endsWith ".metta")
        |>.toList.map (fun e => e.path)
      let mut pass := 0
      let mut total := 0
      for path in mettaFiles do
        total := total + 1
        let _ ← runFile path true  -- just run, don't check
        pass := pass + 1
      IO.println s!"Total: {total}  Ran: {pass}"
      return 0
  | _ =>
      IO.println "leanPeTTa — verified MeTTa evaluator"
      IO.println "  run <file.metta>"
      IO.println "  run --json <file.metta>"
      IO.println "  test-corpus <dir>"
      return 1
