import MeTTailCore

namespace Algorithms.MeTTa.Simple.Parser

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaSyntax

inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr
deriving Repr

abbrev Stmt := SyntaxCommand

structure ParseError where
  message : String
  line : Option Nat := none
  column : Option Nat := none
  near : Option String := none
deriving Repr, DecidableEq, Inhabited

namespace ParseError

def render (e : ParseError) : String :=
  let parts :=
    [ e.line.map (fun n => s!"line={n}")
    , e.column.map (fun n => s!"col={n}")
    , e.near.map (fun tok => s!"near={tok}")
    ].filterMap id
  if parts.isEmpty then
    e.message
  else
    s!"{e.message} ({String.intercalate ", " parts})"

end ParseError

instance : ToString ParseError where
  toString := ParseError.render

private def mkParseError (message : String)
    (line : Option Nat := none) (column : Option Nat := none)
    (near : Option String := none) : ParseError :=
  { message := message, line := line, column := column, near := near }

private structure ParserDialect where
  syntaxSpec : SyntaxSpec
  grammarSpec : GrammarSpec
deriving Repr

private def parserDialectOf (spec : SyntaxSpec) : ParserDialect :=
  { syntaxSpec := spec
    grammarSpec := spec.toGrammarSpec }

private def grammarLineCommentStartChar? (grammarSpec : GrammarSpec) : Option Char :=
  match grammarSpec.lineCommentStart with
  | none => none
  | some s =>
      match s.toList with
      | [c] => some c
      | _ => none

private def grammarSExprOpenChar (grammarSpec : GrammarSpec) : Char :=
  grammarSpec.sexprOpen.toList.getD 0 '('

private def grammarSExprCloseChar (grammarSpec : GrammarSpec) : Char :=
  grammarSpec.sexprClose.toList.getD 0 ')'

private def flushToken (currRev : List Char) (accRev : List String) : List String :=
  if currRev.isEmpty then
    accRev
  else
    String.ofList currRev.reverse :: accRev

private def isLineCommentStart (cfg : ParserDialect) (text : String) : Bool :=
  match cfg.grammarSpec.lineCommentStart with
  | none => false
  | some tok => text.startsWith tok

private def tokenizeAux (lineCommentStart? : Option Char)
    (sexprOpen : Char) (sexprClose : Char) (stringDelim : Char) (escapeChar : Char) :
    List Char → Bool → Bool → List Char → List String → List String
  | [], _inString, _escaped, currRev, accRev =>
      (flushToken currRev accRev).reverse
  | c :: cs, true, escaped, currRev, accRev =>
      let currRev' := c :: currRev
      if escaped then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs true false currRev' accRev
      else if c = escapeChar then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs true true currRev' accRev
      else if c = stringDelim then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs false false [] (flushToken currRev' accRev)
      else
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs true false currRev' accRev
  | c :: cs, false, _escaped, currRev, accRev =>
      if lineCommentStart? = some c then
        (flushToken currRev accRev).reverse
      else if c.isWhitespace then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs false false [] (flushToken currRev accRev)
      else if c = sexprOpen then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs false false [] ("(" :: flushToken currRev accRev)
      else if c = sexprClose then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs false false [] (")" :: flushToken currRev accRev)
      else if c = stringDelim then
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs true false [stringDelim] (flushToken currRev accRev)
      else
        tokenizeAux lineCommentStart? sexprOpen sexprClose stringDelim escapeChar cs false false (c :: currRev) accRev

private def tokenizeWith (cfg : ParserDialect) (input : String) : List String :=
  tokenizeAux
    (grammarLineCommentStartChar? cfg.grammarSpec)
    (grammarSExprOpenChar cfg.grammarSpec)
    (grammarSExprCloseChar cfg.grammarSpec)
    cfg.syntaxSpec.lexer.stringDelimiter
    cfg.syntaxSpec.lexer.escapeChar
    input.toList false false [] []

mutual
  private partial def parseSExprOne : List String → Except ParseError (SExpr × List String)
    | [] => .error (mkParseError "expected expression, found end of input")
    | "(" :: rest => parseSExprList [] rest
    | ")" :: _ => .error (mkParseError "unexpected closing parenthesis" (near := some ")"))
    | tok :: rest => .ok (.atom tok, rest)

  private partial def parseSExprList (accRev : List SExpr) :
      List String → Except ParseError (SExpr × List String)
    | [] => .error (mkParseError "unclosed list expression")
    | ")" :: rest => .ok (.list accRev.reverse, rest)
    | toks => do
        let (x, rest) ← parseSExprOne toks
        parseSExprList (x :: accRev) rest
end

private def parseSingleSExprWith (cfg : ParserDialect) (input : String) : Except ParseError SExpr := do
  let toks := tokenizeWith cfg input
  if toks.isEmpty then
    .error (mkParseError "empty input")
  else
    let (sexpr, rest) ← parseSExprOne toks
    if rest.isEmpty then
      .ok sexpr
    else
      .error (mkParseError s!"unexpected trailing tokens: {rest}" (near := rest.head?))

private def parseSingleSExpr (input : String) : Except ParseError SExpr :=
  parseSingleSExprWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) input

private def atomToPattern (tok : String) : Pattern :=
  if tok.startsWith "$" then
    let name := (tok.drop 1).toString
    if name.isEmpty then .fvar tok else .fvar name
  else
    .apply tok []

partial def sexprToPattern : SExpr → Except ParseError Pattern
  | .atom tok => .ok (atomToPattern tok)
  | .list [] => .ok (.apply "()" [])
  | .list (head :: args) =>
      match head with
      | .atom ctor => do
          let args' ← args.mapM sexprToPattern
          .ok (.apply ctor args')
      | _ => do
          let elems' ← (head :: args).mapM sexprToPattern
          .ok (.apply "Expr" elems')

private def parseNatToken (tok : String) : Except ParseError Nat :=
  match tok.toNat? with
  | some n => .ok n
  | none => .error (mkParseError s!"expected Nat token, found: {tok}" (near := some tok))

private def arityAllowed (cmd : CommandHead) (n : Nat) : Bool :=
  n >= cmd.arityMin &&
    match cmd.arityMax with
    | some m => n <= m
    | none => true

private def commandForHead? (cfg : ParserDialect) (head : String) : Option CommandHead :=
  let canonical := cfg.syntaxSpec.canonicalHead head
  cfg.syntaxSpec.commandHeads.find? fun cmd => cmd.head == canonical

private def fallbackFactOrError (sexpr : SExpr)
    (allowFallback : Bool) (errMsg : String) (near : Option String := none) : Except ParseError Stmt := do
  if allowFallback then
    let p ← sexprToPattern sexpr
    .ok (.fact p)
  else
    .error (mkParseError errMsg (near := near))

private def stmtFromSExpr (cfg : ParserDialect) (sexpr : SExpr) : Except ParseError Stmt :=
  match sexpr with
  | .list (.atom head :: tail) =>
      let canonicalHead := cfg.syntaxSpec.canonicalHead head
      if canonicalHead == cfg.syntaxSpec.loweringHeads.relationFactHead then
        match tail with
        | .atom rel :: args => do
            let args' ← args.mapM sexprToPattern
            .ok (.relationFact rel args')
        | _ =>
            fallbackFactOrError sexpr cfg.syntaxSpec.dispatchPolicy.fallbackUnsupportedCommandToFact
              s!"{head} expects relation name atom as first argument" (near := some head)
      else if canonicalHead == cfg.syntaxSpec.loweringHeads.builtinFactHead then
        match tail with
        | .atom rel :: args => do
            let args' ← args.mapM sexprToPattern
            .ok (.builtinFact rel args')
        | _ =>
            fallbackFactOrError sexpr cfg.syntaxSpec.dispatchPolicy.fallbackUnsupportedCommandToFact
              s!"{head} expects relation name atom as first argument" (near := some head)
      else
        match commandForHead? cfg head with
        | none =>
            fallbackFactOrError sexpr cfg.syntaxSpec.dispatchPolicy.fallbackUnknownHeadToFact
              s!"unknown command head: {head}" (near := some head)
        | some cmd =>
            if !arityAllowed cmd tail.length then
              fallbackFactOrError sexpr cfg.syntaxSpec.dispatchPolicy.fallbackArityMismatchToFact
                s!"command {head} expects arity [{cmd.arityMin}, {cmd.arityMax}], got {tail.length}"
                (near := some head)
            else
              match cmd.command, tail with
              | "defineEq", [lhs, rhs] => do
                  let lhs' ← sexprToPattern lhs
                  let rhs' ← sexprToPattern rhs
                  .ok (.defineEq lhs' rhs')
              | "defineType", [lhs, rhs] => do
                  let lhs' ← sexprToPattern lhs
                  let rhs' ← sexprToPattern rhs
                  .ok (.defineType lhs' rhs')
              | "setFuel", [.atom n] => do
                  let n' ← parseNatToken n
                  .ok (.setFuel n')
              | _, _ =>
                  fallbackFactOrError sexpr cfg.syntaxSpec.dispatchPolicy.fallbackUnsupportedCommandToFact
                    s!"unsupported command lowering: {cmd.command}" (near := some head)
  | _ => do
      let p ← sexprToPattern sexpr
      .ok (.fact p)

def parseExprDetailed (input : String) : Except ParseError Pattern := do
  sexprToPattern (← parseSingleSExpr input)

def parseExprWithDetailed (spec : SyntaxSpec) (input : String) : Except ParseError Pattern := do
  sexprToPattern (← parseSingleSExprWith (parserDialectOf spec) input)

private def shouldTreatBangPrefixedWordAsSymbol (cfg : ParserDialect) (trimmed : String) : Bool :=
  let openTok := cfg.grammarSpec.sexprOpen
  let stringTok := String.singleton cfg.syntaxSpec.lexer.stringDelimiter
  if !cfg.syntaxSpec.evalPrefix.bangPrefixedWordIsSymbol then
    false
  else if !trimmed.startsWith cfg.grammarSpec.evalPrefixToken then
    false
  else
    let tail := (trimmed.drop cfg.grammarSpec.evalPrefixToken.length).toString
    !tail.isEmpty &&
      !tail.contains ' ' &&
      !tail.contains '\t' &&
      !tail.startsWith openTok &&
      !tail.startsWith stringTok &&
      !tail.startsWith cfg.grammarSpec.evalPrefixToken

def parseStmtWithDetailed (spec : SyntaxSpec) (line : String) : Except ParseError Stmt := do
  let cfg := parserDialectOf spec
  let trimmed := line.trimAscii.toString
  let openTok := cfg.grammarSpec.sexprOpen
  if trimmed.isEmpty then
    .ok .empty
  else if isLineCommentStart cfg trimmed then
    .ok .empty
  else if shouldTreatBangPrefixedWordAsSymbol cfg trimmed then
    .ok (.fact (atomToPattern trimmed))
  else if trimmed.startsWith cfg.grammarSpec.evalPrefixToken then
    let payload := ((trimmed.drop cfg.grammarSpec.evalPrefixToken.length).trimAscii).toString
    if payload.isEmpty then
      .error (mkParseError s!"query line requires an expression after '{cfg.grammarSpec.evalPrefixToken}'"
        (near := some cfg.grammarSpec.evalPrefixToken))
    else
      .ok (.eval (← parseExprWithDetailed spec payload))
  else if !trimmed.startsWith openTok then
    let plain := trimmed
    if plain.contains ' ' || plain.contains '\t' then
      .ok .empty
    else
      .ok (.fact (atomToPattern plain))
  else
    stmtFromSExpr cfg (← parseSingleSExprWith cfg trimmed)

def parseStmtWith (spec : SyntaxSpec) (line : String) : Except String Stmt :=
  (parseStmtWithDetailed spec line).mapError ParseError.render

def parseStmt (line : String) : Except String Stmt :=
  parseStmtWith MeTTailCore.MeTTaSyntax.petta line

def parseLineWithDetailed (spec : SyntaxSpec) (line : String) : Except ParseError Stmt :=
  parseStmtWithDetailed spec line

def parseLineWith (spec : SyntaxSpec) (line : String) : Except String Stmt :=
  parseStmtWith spec line

def parseLine (line : String) : Except String Stmt :=
  parseStmtWith MeTTailCore.MeTTaSyntax.petta line

def parseExpr (input : String) : Except String Pattern :=
  (parseExprDetailed input).mapError ParseError.render

def parseExprWith (spec : SyntaxSpec) (input : String) : Except String Pattern :=
  (parseExprWithDetailed spec input).mapError ParseError.render

private structure ProgramScanState where
  line : Nat := 1
  depth : Nat := 0
  inComment : Bool := false
  inString : Bool := false
  escaped : Bool := false
  started : Bool := false
  startLine : Nat := 1
  currRev : List Char := []
  formsRev : List (Nat × String) := []
  err : Option ParseError := none
deriving Repr

private def pushChar (st : ProgramScanState) (c : Char) : ProgramScanState :=
  { st with currRev := c :: st.currRev }

private def markStarted (st : ProgramScanState) : ProgramScanState :=
  if st.started then
    st
  else
    { st with started := true, startLine := st.line }

private def finalizeCurr (st : ProgramScanState) : ProgramScanState :=
  let txt := String.ofList st.currRev.reverse
  let trimmed := txt.trimAscii.toString
  if trimmed.isEmpty then
    { st with currRev := [], started := false, startLine := st.line }
  else
    { st with
      currRev := []
      started := false
      startLine := st.line
      formsRev := (st.startLine, trimmed) :: st.formsRev }

private def stepScan (cfg : ParserDialect) (st : ProgramScanState) (c : Char) : ProgramScanState :=
  let lineCommentStart? := grammarLineCommentStartChar? cfg.grammarSpec
  let stringDelim := cfg.syntaxSpec.lexer.stringDelimiter
  let escapeChar := cfg.syntaxSpec.lexer.escapeChar
  let sexprOpen := grammarSExprOpenChar cfg.grammarSpec
  let sexprClose := grammarSExprCloseChar cfg.grammarSpec
  if st.err.isSome then
    st
  else if st.inComment then
    if c = '\n' then
      { st with inComment := false, line := st.line + 1 }
    else
      st
  else if st.inString then
    let st1 := pushChar st c
    if st.escaped then
      if c = '\n' then
        { st1 with escaped := false, line := st1.line + 1 }
      else
        { st1 with escaped := false }
    else if c = escapeChar then
      { st1 with escaped := true }
    else if c = stringDelim then
      { st1 with inString := false }
    else if c = '\n' then
      { st1 with line := st1.line + 1 }
    else
      st1
  else if lineCommentStart? = some c then
    { st with inComment := true }
  else if c = '\n' then
    if st.depth = 0 then
      let st1 := finalizeCurr st
      { st1 with line := st1.line + 1, startLine := st1.line + 1 }
    else
      { pushChar st c with line := st.line + 1 }
  else if c = stringDelim then
    let st1 := markStarted st |> fun s => pushChar s c
    { st1 with inString := true, escaped := false }
  else if c = sexprOpen then
    let st1 := markStarted st |> fun s => pushChar s c
    { st1 with depth := st.depth + 1 }
  else if c = sexprClose then
    if st.depth = 0 then
      { st with err := some (mkParseError s!"unexpected '{sexprClose}'" (line := some st.line)
        (near := some (String.singleton sexprClose))) }
    else
      let st1 := pushChar st c
      let st2 := { st1 with depth := st.depth - 1 }
      if st2.depth = 0 then
        finalizeCurr st2
      else
        st2
  else
    let st1 := if c.isWhitespace then st else markStarted st
    pushChar st1 c

private def splitProgramForms (cfg : ParserDialect) (text : String) : Except ParseError (List (Nat × String)) :=
  let st := text.toList.foldl (stepScan cfg) {}
  match st.err with
  | some e => .error e
  | none =>
      if st.inString then
        .error (mkParseError "unterminated string" (line := some st.startLine))
      else if st.depth ≠ 0 then
        .error (mkParseError "unclosed parenthesis" (line := some st.startLine))
      else
        .ok (finalizeCurr st).formsRev.reverse

private def coalesceEvalPrefixForms (cfg : ParserDialect) (forms : List (Nat × String)) :
    List (Nat × String) :=
  let tok := cfg.grammarSpec.evalPrefixToken
  let rec go (accRev : List (Nat × String)) (pending? : Option (Nat × String))
      (remaining : List (Nat × String)) : List (Nat × String) :=
    match pending?, remaining with
    | none, [] => accRev.reverse
    | some p, [] => (p :: accRev).reverse
    | none, x :: xs => go accRev (some x) xs
    | some (lineNo, text), (lineNo2, text2) :: xs =>
        if cfg.syntaxSpec.evalPrefix.allowNewlineAfterPrefix && text.trimAscii.toString = tok then
          go accRev (some (lineNo, tok ++ " " ++ text2)) xs
        else
          go ((lineNo, text) :: accRev) (some (lineNo2, text2)) xs
  go [] none forms

def parseProgramWithDetailed (spec : SyntaxSpec) (text : String) : Except ParseError (List (Nat × Stmt)) := do
  let cfg := parserDialectOf spec
  let forms ← splitProgramForms cfg text
  let forms := coalesceEvalPrefixForms cfg forms
  forms.mapM fun (lineNo, formText) => do
    let stmt ←
      match parseStmtWithDetailed spec formText with
      | .ok s => .ok s
      | .error e =>
          if e.line.isNone then
            .error { e with line := some lineNo }
          else
            .error e
    pure (lineNo, stmt)

def parseProgramWith (spec : SyntaxSpec) (text : String) : Except String (List (Nat × Stmt)) :=
  (parseProgramWithDetailed spec text).mapError ParseError.render

def parseProgram (text : String) : Except String (List (Nat × Stmt)) :=
  parseProgramWith MeTTailCore.MeTTaSyntax.petta text

end Algorithms.MeTTa.Simple.Parser
