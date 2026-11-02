import Mettapedia.Logic.Prolog.ReaderProfile

/-!
# Operator-aware Prolog term reader

This module parses located lexer tokens directly into the canonical
`Logic.LP.Term` instantiated by `SourceSignature`. Operator priority and
associativity are read from an explicit `ReaderOperator.Table`; quoted-operator behavior and text interpretation are explicit source-profile choices.

The implementation follows the precedence discipline of SWI-Prolog V10.1.9
`src/pl-read.c`. Function application requires lexical adjacency, arguments
are read below priority 1000, and each anonymous `_` receives a distinct
source occurrence while repeated named variables share one occurrence.
-/

namespace Mettapedia.Logic.Prolog.ReaderTerm

open ReaderLexer ReaderOperator SourceSignature

structure VariableBinding where
  spelling : String
  identity : SourceSignature.Variable
deriving DecidableEq, Repr

/-- State for one read term. Variable sharing never crosses a terminating
full stop because `parseOne` creates this state afresh. -/
structure State where
  remaining : List ReaderLexer.Token
  bindings : List VariableBinding := []
  nextOccurrence : Nat := 0

structure Parsed where
  term : SourceSignature.Term
  precedence : Nat
  state : State

structure Result where
  term : SourceSignature.Term
  bindings : List VariableBinding
  remaining : List ReaderLexer.Token

inductive ErrorKind where
  | lexer (error : ReaderLexer.ErrorKind)
  | number (error : ReaderNumber.Error)
  | unexpectedEnd
  | unexpectedToken (token : ReaderLexer.Kind)
  | expectedPunctuation (punctuation : ReaderLexer.Punctuation)
  | operatorClash (name : String)
  | exhaustedInputMeasure
deriving DecidableEq, Repr

structure Error where
  position : ReaderLexer.Position
  kind : ErrorKind
deriving DecidableEq, Repr

private def errorPosition (state : State) : ReaderLexer.Position :=
  match state.remaining with
  | token :: _ => token.span.start
  | [] => .initial

private def failAt (state : State) (kind : ErrorKind) : Except Error α :=
  .error { position := errorPosition state, kind }

private def tokenStartsTerm : ReaderLexer.Kind -> Bool
  | .atom _ | .quotedAtom _ | .variable _ | .number _
  | .string _ | .backQuoted _ => true
  | .punctuation .leftParen | .punctuation .leftBracket
  | .punctuation .leftBrace => true
  | _ => false

private def adjacent (first second : ReaderLexer.Token) : Bool :=
  first.span.stop.offset = second.span.start.offset

private def operatorName? (profile : ReaderProfile.Profile) : ReaderLexer.Kind -> Option String
  | .atom name => some name
  | .quotedAtom name => if profile.quotedOperator name then some name else none
  | .punctuation .comma => some ","
  | .punctuation .bar => some "|"
  | _ => none

private def eligible (maximum leftPrecedence : Nat)
    (declaration : Declaration) : Bool :=
  declaration.priority.value <= maximum &&
    match declaration.specifier.leftMaximum declaration.priority.value with
    | some leftMaximum => leftPrecedence <= leftMaximum
    | none => false

private def eligiblePrefix (maximum : Nat)
    (declaration : Declaration) : Bool :=
  declaration.priority.value <= maximum && declaration.specifier.isPrefix

private def firstEligiblePrefix (table : Table) (name : String)
    (maximum : Nat) : Option Declaration :=
  (prefixes table name).find? (eligiblePrefix maximum)

private def firstEligiblePostfix (table : Table) (name : String)
    (maximum leftPrecedence : Nat) : Option Declaration :=
  (postfixes table name).find? (eligible maximum leftPrecedence)

private def firstEligibleInfix (table : Table) (name : String)
    (maximum leftPrecedence : Nat) : Option Declaration :=
  (infixes table name).find? (eligible maximum leftPrecedence)

private def consumePunctuation (punctuation : ReaderLexer.Punctuation)
    (state : State) : Except Error State :=
  match state.remaining with
  | { kind := .punctuation actual, .. } :: rest =>
      if actual = punctuation then .ok { state with remaining := rest }
      else failAt state (.expectedPunctuation punctuation)
  | _ => failAt state (.expectedPunctuation punctuation)

def internVariable (spelling : String) (state : State) :
    SourceSignature.Variable × State :=
  if spelling = "_" then
    let identity := { spelling, occurrence := state.nextOccurrence }
    (identity, {
      state with
      bindings := { spelling, identity } :: state.bindings
      nextOccurrence := state.nextOccurrence + 1
    })
  else
    match state.bindings.find? (fun binding => binding.spelling = spelling) with
    | some binding => (binding.identity, state)
    | none =>
        let identity := { spelling, occurrence := state.nextOccurrence }
        (identity, {
          state with
          bindings := { spelling, identity } :: state.bindings
          nextOccurrence := state.nextOccurrence + 1
        })

private def negateConstant : SourceSignature.Constant ->
    Option SourceSignature.Constant
  | .integer value => some (.integer (-value))
  | .floatBits bits => some (.floatBits (bits ^^^ 0x8000000000000000))
  | _ => none


mutual

  private def parseExpressionAux (profile : ReaderProfile.Profile) : Nat -> Table -> Nat -> State ->
      Except Error Parsed
    | 0, _, _, state => failAt state .exhaustedInputMeasure
    | fuel + 1, table, maximum, state => do
        let left <- parsePrefixOrPrimaryAux profile fuel table maximum state
        parseTailAux profile fuel table maximum left

  private def parsePrefixOrPrimaryAux (profile : ReaderProfile.Profile) : Nat -> Table -> Nat -> State ->
      Except Error Parsed
    | 0, _, _, state => failAt state .exhaustedInputMeasure
    | fuel + 1, table, maximum, state =>
        match state.remaining with
        | [] => failAt state .unexpectedEnd
        | operator@{ kind := .atom "-", .. } ::
            number@{ kind := .number lexeme, .. } :: rest =>
            if adjacent operator number then
              match (if profile.numericAllowed lexeme then ReaderNumber.parse lexeme
                    else .error (.invalidInteger lexeme)) with
              | .error error => failAt state (.number error)
              | .ok constant =>
                  match negateConstant constant with
                  | some negative => .ok {
                      term := .const negative
                      precedence := 0
                      state := { state with remaining := rest }
                    }
                  | none => parsePrimaryAux profile fuel table state
            else
              parsePrefixAux profile fuel table maximum state "-"
        | operator@{ kind := .atom name, .. } :: next :: _ =>
            if (match next.kind with
                | .punctuation .leftParen => adjacent operator next
                | _ => false) then
              parsePrimaryAux profile fuel table state
            else if tokenStartsTerm next.kind &&
                (firstEligiblePrefix table name maximum).isSome then
              parsePrefixAux profile fuel table maximum state name
            else
              parsePrimaryAux profile fuel table state
        | operator@{ kind := .quotedAtom name, .. } :: next :: _ =>
            if profile.quotedOperator name && tokenStartsTerm next.kind &&
                (firstEligiblePrefix table name maximum).isSome &&
                !(next.kind == .punctuation .leftParen && adjacent operator next) then
              parsePrefixAux profile fuel table maximum state name
            else parsePrimaryAux profile fuel table state
        | { kind := .atom name, .. } :: [] =>
            if (firstEligiblePrefix table name maximum).isSome then
              parsePrimaryAux profile fuel table state
            else
              parsePrimaryAux profile fuel table state
        | _ => parsePrimaryAux profile fuel table state

  private def parsePrefixAux (profile : ReaderProfile.Profile) (fuel : Nat) (table : Table) (maximum : Nat)
      (state : State) (name : String) : Except Error Parsed := do
    let declaration <- match firstEligiblePrefix table name maximum with
      | some declaration => pure declaration
      | none => failAt state (.operatorClash name)
    let afterOperator := { state with remaining := state.remaining.drop 1 }
    let rightMaximum <- match
        declaration.specifier.rightMaximum declaration.priority.value with
      | some rightMaximum => pure rightMaximum
      | none => failAt state (.operatorClash name)
    let right <- parseExpressionAux profile fuel table rightMaximum afterOperator
    pure {
      term := SourceSignature.compound name [right.term]
      precedence := declaration.priority.value
      state := right.state
    }

  private def parsePrimaryAux (profile : ReaderProfile.Profile) : Nat -> Table -> State -> Except Error Parsed
    | 0, _, state => failAt state .exhaustedInputMeasure
    | fuel + 1, table, state =>
        match state.remaining with
        | [] => failAt state .unexpectedEnd
        | token :: rest =>
            match token.kind with
            | .variable spelling =>
                let (identity, next) := internVariable spelling
                  { state with remaining := rest }
                .ok { term := .var identity, precedence := 0, state := next }
            | .number lexeme =>
                match (if profile.numericAllowed lexeme then ReaderNumber.parse lexeme
                    else .error (.invalidInteger lexeme)) with
                | .error error => failAt state (.number error)
                | .ok constant => .ok {
                    term := .const constant
                    precedence := 0
                    state := { state with remaining := rest }
                  }
            | .string value => .ok {
                term := profile.textTerm profile.doubleQuotes value
                precedence := 0
                state := { state with remaining := rest }
              }
            | .backQuoted value =>
                match profile.backQuotes with
                | none => failAt state (.unexpectedToken (.backQuoted value))
                | some mode => .ok {
                    term := profile.textTerm mode value
                    precedence := 0
                    state := { state with remaining := rest }
                  }
            | .atom name | .quotedAtom name =>
                match rest with
                | left@{ kind := .punctuation .leftParen, .. } :: tail =>
                    if adjacent token left then
                      parseApplicationAux profile fuel table name
                        { state with remaining := tail }
                    else
                      .ok {
                        term := SourceSignature.atom name
                        precedence := 0
                        state := { state with remaining := rest }
                      }
                | _ => .ok {
                    term := SourceSignature.atom name
                    precedence := 0
                    state := { state with remaining := rest }
                  }
            | .punctuation .leftParen => do
                let nested <- parseExpressionAux profile fuel table 1200
                  { state with remaining := rest }
                let after <- consumePunctuation .rightParen nested.state
                pure { term := nested.term, precedence := 0, state := after }
            | .punctuation .leftBracket =>
                parseListAux profile fuel table { state with remaining := rest }
            | .punctuation .leftBrace =>
                match rest with
                | { kind := .punctuation .rightBrace, .. } :: tail => .ok {
                    term := SourceSignature.atom "{}"
                    precedence := 0
                    state := { state with remaining := tail }
                  }
                | _ => do
                    let nested <- parseExpressionAux profile fuel table 1200
                      { state with remaining := rest }
                    let after <- consumePunctuation .rightBrace nested.state
                    pure {
                      term := SourceSignature.compound "{}" [nested.term]
                      precedence := 0
                      state := after
                    }
            | other => failAt state (.unexpectedToken other)

  private def parseApplicationAux (profile : ReaderProfile.Profile) (fuel : Nat) (table : Table)
      (name : String) (state : State) : Except Error Parsed :=
    match state.remaining with
    | { kind := .punctuation .rightParen, .. } :: rest =>
      if !profile.zeroArityCompounds then failAt state (.unexpectedToken (.punctuation .rightParen)) else .ok {
        term := SourceSignature.compound name []
        precedence := 0
        state := { state with remaining := rest }
      }
    | _ => do
        let (arguments, afterArguments) <- parseArgumentsAux profile fuel table state
        let after <- consumePunctuation .rightParen afterArguments
        pure {
          term := SourceSignature.compound name arguments
          precedence := 0
          state := after
        }

  private def parseArgumentsAux (profile : ReaderProfile.Profile) : Nat -> Table -> State ->
      Except Error (List SourceSignature.Term × State)
    | 0, _, state => failAt state .exhaustedInputMeasure
    | fuel + 1, table, state => do
        let argument <- parseExpressionAux profile fuel table 999 state
        match argument.state.remaining with
        | { kind := .punctuation .comma, .. } :: rest => do
            let (arguments, after) <- parseArgumentsAux profile fuel table
              { argument.state with remaining := rest }
            pure (argument.term :: arguments, after)
        | _ => pure ([argument.term], argument.state)

  private def parseListAux (profile : ReaderProfile.Profile) : Nat -> Table -> State -> Except Error Parsed
    | 0, _, state => failAt state .exhaustedInputMeasure
    | fuel + 1, table, state =>
        match state.remaining with
        | { kind := .punctuation .rightBracket, .. } :: rest => .ok {
            term := profile.nil
            precedence := 0
            state := { state with remaining := rest }
          }
        | _ => do
            let head <- parseExpressionAux profile fuel table 999 state
            parseListTailAux profile fuel table [head.term] head.state

  private def parseListTailAux (profile : ReaderProfile.Profile) (fuel : Nat) (table : Table)
      (reversed : List SourceSignature.Term) (state : State) :
      Except Error Parsed :=
    match fuel with
    | 0 => failAt state .exhaustedInputMeasure
    | fuel + 1 =>
        match state.remaining with
        | { kind := .punctuation .comma, .. } :: rest => do
            let next <- parseExpressionAux profile fuel table 999
              { state with remaining := rest }
            parseListTailAux profile fuel table (next.term :: reversed) next.state
        | { kind := .punctuation .bar, .. } :: rest => do
            let tail <- parseExpressionAux profile fuel table 999
              { state with remaining := rest }
            let after <- consumePunctuation .rightBracket tail.state
            pure {
              term := profile.list reversed.reverse tail.term
              precedence := 0
              state := after
            }
        | { kind := .punctuation .rightBracket, .. } :: rest => .ok {
            term := profile.list reversed.reverse
            precedence := 0
            state := { state with remaining := rest }
          }
        | _ => failAt state (.expectedPunctuation .rightBracket)

  private def parseTailAux (profile : ReaderProfile.Profile) : Nat -> Table -> Nat -> Parsed ->
      Except Error Parsed
    | 0, _, _, parsed => failAt parsed.state .exhaustedInputMeasure
    | fuel + 1, table, maximum, left =>
        match left.state.remaining with
        | [] => .ok left
        | operator :: rest =>
            match operatorName? profile operator.kind with
            | none => .ok left
            | some name =>
                let postfixCandidate := firstEligiblePostfix table name maximum
                  left.precedence
                let infixCandidate := firstEligibleInfix table name maximum
                  left.precedence
                let rightStarts := match rest with
                  | next :: _ => tokenStartsTerm next.kind
                  | [] => false
                if rightStarts && infixCandidate.isSome then
                  match infixCandidate with
                  | none => .ok left
                  | some declaration =>
                      match declaration.specifier.rightMaximum
                          declaration.priority.value with
                      | none => failAt left.state (.operatorClash name)
                      | some rightMaximum => do
                          let right <- parseExpressionAux profile fuel table rightMaximum
                            { left.state with remaining := rest }
                          parseTailAux profile fuel table maximum {
                            term := SourceSignature.compound name
                              [left.term, right.term]
                            precedence := declaration.priority.value
                            state := right.state
                          }
                else
                  match postfixCandidate with
                  | some declaration =>
                      parseTailAux profile fuel table maximum {
                        term := SourceSignature.compound name [left.term]
                        precedence := declaration.priority.value
                        state := { left.state with remaining := rest }
                      }
                  | none => .ok left

end

/-- Parse one term from an existing token stream and consume its terminating
full stop. Tokens after the term remain available to the file loader. -/
def parseOneWith (profile : ReaderProfile.Profile) (table : Table) (tokens : List ReaderLexer.Token) :
    Except Error Result := do
  let state : State := { remaining := tokens }
  let parsed <- parseExpressionAux profile (tokens.length * 4 + 8) table 1200 state
  let after <- consumePunctuation .fullStop parsed.state
  pure {
    term := parsed.term
    bindings := parsed.state.bindings.reverse
    remaining := after.remaining
  }

/-- Lex and read exactly one terminated Prolog term. -/
def readOneWith (profile : ReaderProfile.Profile) (table : Table) (source : String) : Except Error Result :=
  match ReaderLexer.scan source with
  | .error error => .error {
      position := error.position
      kind := .lexer error.kind
    }
  | .ok tokens => do
      let result <- parseOneWith profile table tokens
      match result.remaining with
      | [] => pure result
      | token :: _ => .error {
          position := token.span.start
          kind := .unexpectedToken token.kind
        }

/-- Existing callers retain the pinned SWI reading choices. -/
def parseOne (table : Table) (tokens : List ReaderLexer.Token) : Except Error Result :=
  parseOneWith ReaderProfile.swi table tokens

def readOne (table : Table) (source : String) : Except Error Result :=
  readOneWith ReaderProfile.swi table source

end Mettapedia.Logic.Prolog.ReaderTerm
