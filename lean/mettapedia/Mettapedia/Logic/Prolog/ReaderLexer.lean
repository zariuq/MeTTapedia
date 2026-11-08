import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.Prolog.ReaderEscape
import Mettapedia.Logic.Prolog.ReaderUnicode

/-!
# SWI-shaped Prolog source lexer

This lexer is the byte-to-token front of the canonical `Logic.Prolog` reader.
Its token classes and layout rules follow SWI-Prolog V10.1.9 `src/pl-read.c`
and `src/pl-ctype.c`: comments are layout, a terminating full stop is
distinguished from a graphic atom, variables start with uppercase or `_`, and
quoted atoms remain atoms after escape decoding.

Numeric lexemes are retained exactly for the numeric parser; this module does
not round through a host float. Unsupported escapes and unterminated source
forms return located errors rather than being silently repaired.
-/

namespace Mettapedia.Logic.Prolog.ReaderLexer

/-- Prolog layout includes vertical tab and form feed. The syntaxGSLT's
`PlSpace` class uses these same six codepoints. -/
def isLayout (c : Char) : Bool :=
  decide (c = ' ') || decide (c = '\t') || decide (c = '\r') ||
    decide (c = '\n') || decide (c = '\u000b') || decide (c = '\u000c')

structure Position where
  offset : Nat
  line : Nat
  column : Nat
deriving DecidableEq, Repr

namespace Position

def initial : Position := { offset := 0, line := 1, column := 1 }

def advance (position : Position) (character : Char) : Position :=
  if character = '\n' then
    { offset := position.offset + 1, line := position.line + 1, column := 1 }
  else
    { position with
      offset := position.offset + 1
      column := position.column + 1 }

def advanceMany (position : Position) (characters : List Char) : Position :=
  characters.foldl advance position

end Position

structure Span where
  start : Position
  stop : Position
deriving DecidableEq, Repr

inductive Punctuation where
  | leftParen | rightParen
  | leftBracket | rightBracket
  | leftBrace | rightBrace
  | comma | bar | fullStop
deriving DecidableEq, Repr

/-- Lexical tokens before operator parsing. Graphic operators are atoms. -/
inductive Kind where
  | atom (value : String)
  | quotedAtom (value : String)
  | variable (spelling : String)
  | number (lexeme : String)
  | string (value : String)
  | backQuoted (value : String)
  | punctuation (value : Punctuation)
deriving DecidableEq, Repr

structure Token where
  kind : Kind
  span : Span
deriving DecidableEq, Repr

inductive ErrorKind where
  | unexpectedCharacter (character : Char)
  | unsupportedEscape (character : Char)
  | unterminatedQuote (delimiter : Char)
  | unterminatedBlockComment
  | exhaustedInputMeasure
deriving DecidableEq, Repr

structure Error where
  position : Position
  kind : ErrorKind
deriving DecidableEq, Repr

private def takeWhile (predicate : Char -> Bool) :
    List Char -> List Char × List Char
  | [] => ([], [])
  | character :: rest =>
      if predicate character then
        let (taken, suffix) := takeWhile predicate rest
        (character :: taken, suffix)
      else
        ([], character :: rest)

private def isIdentifierContinue (character : Char) : Bool :=
  character.isAlphanum || character = '_' || ReaderUnicode.isNameScalar character

def isGraphic (character : Char) : Bool :=
  ['#', '$', '&', '*', '+', '-', '.', '/', ':', '<', '=', '>', '?', '@', '\\', '^', '~'].contains character

theorem isGraphic_spelling (character : Char) :
    isGraphic character = "#$&*+-./:<=>?@\\^~".toList.contains character := by
  have characters : "#$&*+-./:<=>?@\\^~".toList =
      ['#', '$', '&', '*', '+', '-', '.', '/', ':', '<', '=', '>', '?', '@', '\\', '^', '~'] := by
    decide +kernel
  rw [characters]
  rfl

private def isNumberContinue (previous character : Char) : Bool :=
  character.isAlphanum || character = '_' || character = '\'' ||
    ((character = '+' || character = '-') &&
      (previous = 'e' || previous = 'E'))

private def takeNumberTail : Char -> List Char -> List Char × List Char
  | _, [] => ([], [])
  | previous, character :: rest =>
      if previous = '\'' then
        if character = '\\' then
          match rest with
          | [] => ([character], [])
          | escaped :: tail =>
            match ReaderEscape.numeric? (escaped :: tail) with
            | some decoded => (character :: decoded.consumed, decoded.rest)
            | none => ([character, escaped], tail)
        else
          ([character], rest)
      else if character = '.' then
        match rest with
        | next :: _ =>
            if next.isDigit then
              let (taken, suffix) := takeNumberTail character rest
              (character :: taken, suffix)
            else
              ([], character :: rest)
        | [] => ([], [character])
      else if isNumberContinue previous character then
        let (taken, suffix) := takeNumberTail character rest
        (character :: taken, suffix)
      else
        ([], character :: rest)

def simpleEscape : Char -> Option Char
  | 'a' => some '\u0007'
  | 'b' => some '\u0008'
  | 'e' => some '\u001b'
  | 'f' => some '\u000c'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 's' => some ' '
  | 't' => some '\t'
  | 'v' => some '\u000b'
  | '\\' => some '\\'
  | '\'' => some '\''
  | '"' => some '"'
  | '`' => some '`'
  | _ => none

private def scanQuoted : Nat -> Char -> Position -> List Char -> Position ->
    List Char -> Except Error (String × List Char × Position)
  | 0, delimiter, start, _, _, _ =>
      .error { position := start, kind := .unterminatedQuote delimiter }
  | _ + 1, delimiter, start, [], _, _ =>
      .error { position := start, kind := .unterminatedQuote delimiter }
  | fuel + 1, delimiter, start, character :: rest, position, reversed =>
      if character = delimiter then
        match rest with
        | repeated :: tail =>
            if repeated = delimiter then
              scanQuoted fuel delimiter start tail
                ((position.advance character).advance repeated)
                (delimiter :: reversed)
            else
      .ok (String.ofList reversed.reverse, rest,
                position.advance character)
        | [] =>
            .ok (String.ofList reversed.reverse, [], position.advance character)
      else if character = '\\' then
        match rest with
        | [] => .error { position, kind := .unterminatedQuote delimiter }
        | escaped :: tail =>
            if escaped = '\n' then
              scanQuoted fuel delimiter start tail
                ((position.advance character).advance escaped) reversed
            else
              match simpleEscape escaped with
              | none =>
                  match ReaderEscape.numeric? (escaped :: tail) with
                  | some decoded =>
                      scanQuoted fuel delimiter start decoded.rest
                        ((position.advance character).advanceMany decoded.consumed)
                        (decoded.value :: reversed)
                  | none => .error {
                      position := position.advance character
                      kind := .unsupportedEscape escaped
                    }
              | some decoded =>
                  scanQuoted fuel delimiter start tail
                    ((position.advance character).advance escaped)
                    (decoded :: reversed)
      else
        scanQuoted fuel delimiter start rest (position.advance character)
          (character :: reversed)

private def skipBlockComment : Nat -> Nat -> Position -> List Char ->
    Position -> Except Error (List Char × Position)
  | 0, _, start, _, _ =>
      .error { position := start, kind := .unterminatedBlockComment }
  | _ + 1, _, start, [], _ =>
      .error { position := start, kind := .unterminatedBlockComment }
  | fuel + 1, depth, start, first :: rest, position =>
      match first, rest with
      | '/', '*' :: tail =>
          skipBlockComment fuel (depth + 1) start tail
            ((position.advance '/').advance '*')
      | '*', '/' :: tail =>
          if depth = 1 then
            .ok (tail, (position.advance '*').advance '/')
          else
            skipBlockComment fuel (depth - 1) start tail
              ((position.advance '*').advance '/')
      | character, _ =>
          skipBlockComment fuel depth start rest
            (position.advance character)

private def token (kind : Kind) (start stop : Position) : Token :=
  { kind, span := { start, stop } }

private def fullStopFollows : List Char -> Bool
  | [] => true
  | '/' :: '*' :: _ => true
  | next :: _ => ReaderLexer.isLayout next || next = '%'

private def scanAux : Nat -> List Char -> Position ->
    Except Error (List Token)
  | 0, [], _ => .ok []
  | 0, _ :: _, position =>
      .error { position, kind := .exhaustedInputMeasure }
  | _ + 1, [], _ => .ok []
  | fuel + 1, character :: rest, position =>
      if ReaderLexer.isLayout character then
        let (layout, suffix) := takeWhile ReaderLexer.isLayout rest
        scanAux fuel suffix
          (position.advanceMany (character :: layout))
      else if character = '%' then
        let (comment, suffix) := takeWhile (fun next => next != '\n') rest
        scanAux fuel suffix (position.advanceMany ('%' :: comment))
      else
        match character, rest with
        | '/', '*' :: tail =>
            match skipBlockComment tail.length 1 position tail
                ((position.advance '/').advance '*') with
            | .error error => .error error
            | .ok (suffix, nextPosition) =>
                scanAux fuel suffix nextPosition
        | '\'', tail =>
            match scanQuoted tail.length '\'' position tail
                (position.advance '\'') [] with
            | .error error => .error error
            | .ok (value, suffix, nextPosition) => do
                let following <- scanAux fuel suffix nextPosition
                pure (token (.quotedAtom value) position nextPosition :: following)
        | '"', tail =>
            match scanQuoted tail.length '"' position tail
                (position.advance '"') [] with
            | .error error => .error error
            | .ok (value, suffix, nextPosition) => do
                let following <- scanAux fuel suffix nextPosition
                pure (token (.string value) position nextPosition :: following)
        | '`', tail =>
            match scanQuoted tail.length '`' position tail
                (position.advance '`') [] with
            | .error error => .error error
            | .ok (value, suffix, nextPosition) => do
                let following <- scanAux fuel suffix nextPosition
                pure (token (.backQuoted value) position nextPosition :: following)
        | '(', _ => emitPunctuation fuel .leftParen character rest position
        | ')', _ => emitPunctuation fuel .rightParen character rest position
        | '[', _ => emitPunctuation fuel .leftBracket character rest position
        | ']', _ => emitPunctuation fuel .rightBracket character rest position
        | '{', _ => emitPunctuation fuel .leftBrace character rest position
        | '}', _ => emitPunctuation fuel .rightBrace character rest position
        | ',', _ => emitPunctuation fuel .comma character rest position
        | '|', _ => emitPunctuation fuel .bar character rest position
        | '!', _ => emitAtom fuel "!" character rest position
        | ';', _ => emitAtom fuel ";" character rest position
        | '.', tail =>
            if fullStopFollows tail then
              emitPunctuation fuel .fullStop character tail position
            else
              let (more, suffix) := takeWhile isGraphic tail
              let lexeme := character :: more
              let nextPosition := position.advanceMany lexeme
              do
                let following <- scanAux fuel suffix nextPosition
                pure (token (.atom (String.ofList lexeme)) position nextPosition ::
                  following)
        | first, tail =>
            if first.isDigit then
              let (more, suffix) := takeNumberTail first tail
              let lexeme := first :: more
              let nextPosition := position.advanceMany lexeme
              do
                let following <- scanAux fuel suffix nextPosition
                pure (token (.number (String.ofList lexeme)) position nextPosition ::
                  following)
            else if first.isAlpha || first = '_' || ReaderUnicode.isNameScalar first then
              let (more, suffix) := takeWhile isIdentifierContinue tail
              let lexeme := first :: more
              let nextPosition := position.advanceMany lexeme
              let kind := if first.isUpper || first = '_' || ReaderUnicode.isUpperScalar first.toNat then
                  Kind.variable (String.ofList lexeme)
                else Kind.atom (String.ofList lexeme)
              do
                let following <- scanAux fuel suffix nextPosition
                pure (token kind position nextPosition :: following)
            else if isGraphic first then
              let (more, suffix) := takeWhile isGraphic tail
              let lexeme := first :: more
              let nextPosition := position.advanceMany lexeme
              do
                let following <- scanAux fuel suffix nextPosition
                pure (token (.atom (String.ofList lexeme)) position nextPosition ::
                  following)
            else
              .error { position, kind := .unexpectedCharacter first }
where
  emitPunctuation (fuel : Nat) (value : Punctuation) (character : Char)
      (rest : List Char) (position : Position) : Except Error (List Token) := do
    let nextPosition := position.advance character
    let following <- scanAux fuel rest nextPosition
    pure (token (.punctuation value) position nextPosition :: following)

  emitAtom (fuel : Nat) (value : String) (character : Char)
      (rest : List Char) (position : Position) : Except Error (List Token) := do
    let nextPosition := position.advance character
    let following <- scanAux fuel rest nextPosition
    pure (token (.atom value) position nextPosition :: following)

/-- Tokenize one complete source buffer. -/
def scan (source : String) : Except Error (List Token) :=
  let characters := source.toList
  scanAux characters.length characters Position.initial

example : (scan "\u000b p.\u000c").map (List.map (·.kind)) =
    .ok [.atom "p", .punctuation .fullStop] := by decide_cbv
example : (scan "'\\x3bb\\'.").map (List.map (·.kind)) =
    .ok [.quotedAtom "λ", .punctuation .fullStop] := by decide_cbv
example : (scan "'\\141\\'.").map (List.map (·.kind)) =
    .ok [.quotedAtom "a", .punctuation .fullStop] := by decide_cbv
set_option maxRecDepth 8192 in
/-- Unicode names: SWI reads `café` and `λ` as atoms and `Été` as a variable. -/
example : (scan "w(café, λ, Été).").map (List.map (·.kind)) =
    .ok [.atom "w", .punctuation .leftParen, .atom "café", .punctuation .comma, .atom "λ",
      .punctuation .comma, .variable "Été", .punctuation .rightParen, .punctuation .fullStop] := by decide_cbv
/-- Negative control: an ideographic space is not a name character. -/
example : (scan "a\u3000b.").toOption = none := by decide_cbv

end Mettapedia.Logic.Prolog.ReaderLexer
