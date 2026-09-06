/-!
# Source syntax for SUO-KIF

This module defines the lossless lexical tokens and source-located
S-expression tree needed before SUMO declarations can be checked or lowered
to any logical kernel. It deliberately does not assign logical meaning to a
list merely because it parsed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

/-- A one-indexed source location plus its zero-indexed character offset. -/
structure SourcePos where
  offset : Nat
  line : Nat
  column : Nat
  deriving DecidableEq, Repr

/-- The first position in a source file. -/
def SourcePos.start : SourcePos :=
  ⟨0, 1, 1⟩

/-- Advance by one Unicode scalar. Newlines reset the column. -/
def SourcePos.advance (position : SourcePos) (character : Char) : SourcePos :=
  if character = '\n' then
    ⟨position.offset + 1, position.line + 1, 1⟩
  else
    ⟨position.offset + 1, position.line, position.column + 1⟩

/-- A half-open source interval. -/
structure SourceSpan where
  start : SourcePos
  stop : SourcePos
  deriving DecidableEq, Repr

inductive AtomKind : Type
  | symbol
  | regularVariable
  | sequenceVariable
  | stringLiteral
  deriving DecidableEq, Repr

/-- Lexical token classes. Comments remain in the token stream so that source
tools can retain their location and text; the S-expression parser ignores
them. String contents retain escapes verbatim between the quotes. -/
inductive TokenKind : Type
  | openParen
  | closeParen
  | atom (kind : AtomKind) (text : String)
  | comment (text : String)
  deriving DecidableEq, Repr

structure Token where
  kind : TokenKind
  span : SourceSpan
  deriving DecidableEq, Repr

/-- A located atomic KIF term. -/
structure Atom where
  kind : AtomKind
  text : String
  span : SourceSpan
  deriving DecidableEq, Repr

/-- Concrete S-expression syntax. The span of a list includes both
parentheses. -/
inductive Term : Type
  | atom (value : Atom)
  | list (span : SourceSpan) (children : List Term)
  deriving Repr

namespace Term

def span : Term → SourceSpan
  | .atom value => value.span
  | .list located _ => located

end Term

/-- Lexical failures occur before the token stream is complete. -/
inductive LexErrorKind : Type
  | unclosedString
  | internalFuelExhausted
  deriving DecidableEq, Repr

structure LexError where
  kind : LexErrorKind
  span : SourceSpan
  deriving DecidableEq, Repr

/-- Structural failures are accumulated so one source check can report all
unmatched parentheses. -/
inductive ParseErrorKind : Type
  | unexpectedClose
  | unclosedList
  deriving DecidableEq, Repr

structure ParseError where
  kind : ParseErrorKind
  span : SourceSpan
  deriving DecidableEq, Repr

/-- A complete lexical result retains comments and the final position. -/
structure Lexed where
  tokens : List Token
  eof : SourcePos
  deriving DecidableEq, Repr

/-- A recovering structural parse. `forms` contains every fully closed
top-level form; `errors` records every unmatched close and open parenthesis. -/
structure Parsed where
  forms : List Term
  errors : List ParseError
  deriving Repr

end Mettapedia.Languages.KIF
