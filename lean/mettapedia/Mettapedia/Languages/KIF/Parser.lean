import Mettapedia.Languages.KIF.Lexer

/-!
# Recovering structural parser for SUO-KIF

The parser constructs only located S-expressions. It does not yet decide
whether a form is a declaration, formula, term, row-variable application, or
logical connective. Unmatched closing and opening parentheses are accumulated
in source order so one run can expose every structural defect in a KIF file.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

private structure Frame where
  opening : SourceSpan
  reversedChildren : List Term

private structure ParseState where
  frames : List Frame
  reversedForms : List Term
  reversedErrors : List ParseError

private def ParseState.empty : ParseState :=
  ⟨[], [], []⟩

private def ParseState.addTerm (state : ParseState) (term : Term) : ParseState :=
  match state.frames with
  | [] => { state with reversedForms := term :: state.reversedForms }
  | frame :: rest =>
      { state with
        frames :=
          { frame with reversedChildren := term :: frame.reversedChildren } :: rest }

private def ParseState.openList (state : ParseState) (span : SourceSpan) :
    ParseState :=
  { state with frames := ⟨span, []⟩ :: state.frames }

private def ParseState.closeList (state : ParseState) (closing : SourceSpan) :
    ParseState :=
  match state.frames with
  | [] =>
      { state with
        reversedErrors := ⟨.unexpectedClose, closing⟩ :: state.reversedErrors }
  | frame :: rest =>
      let completed :=
        Term.list ⟨frame.opening.start, closing.stop⟩
          frame.reversedChildren.reverse
      ({ state with frames := rest }).addTerm completed

private def parseTokens : List Token → ParseState → ParseState
  | [], state => state
  | token :: rest, state =>
      let next :=
        match token.kind with
        | .comment _ => state
        | .openParen => state.openList token.span
        | .closeParen => state.closeList token.span
        | .atom kind text => state.addTerm (.atom ⟨kind, text, token.span⟩)
      parseTokens rest next

private def finish (state : ParseState) : Parsed :=
  let unclosed :=
    state.frames.reverse.map fun frame =>
      { kind := ParseErrorKind.unclosedList, span := frame.opening }
  ⟨state.reversedForms.reverse, state.reversedErrors.reverse ++ unclosed⟩

/-- Parse a complete token stream, retaining every fully closed top-level form
and accumulating all unmatched parentheses. -/
def parse (lexed : Lexed) : Parsed :=
  finish (parseTokens lexed.tokens ParseState.empty)

/-- Lex and structurally parse one source string. -/
def parseSource (source : String) : Except LexError Parsed :=
  (lex source).map parse

/-- Token classes without locations, useful for lexer conformance examples. -/
def lexicalKinds (source : String) : Except LexError (List TokenKind) :=
  (lex source).map fun result => result.tokens.map (·.kind)

/-- Structural error classes without locations, useful for recovery examples. -/
def structuralErrorKinds (source : String) : Except LexError (List ParseErrorKind) :=
  (parseSource source).map fun result => result.errors.map (·.kind)

/-- Number of fully closed top-level forms. -/
def topLevelFormCount (source : String) : Except LexError Nat :=
  (parseSource source).map fun result => result.forms.length

/-! ## Positive and negative source canaries -/

example :
    lexicalKinds "(rel ?x @xs \"quoted\\\"value\") ; note\n" =
      .ok [.openParen, .atom .symbol "rel",
        .atom .regularVariable "?x", .atom .sequenceVariable "@xs",
        .atom .stringLiteral "quoted\\\"value", .closeParen,
        .comment "; note"] := by
  rfl

example : topLevelFormCount "(subclass Human Animal)\n(instance Socrates Human)" =
    .ok 2 := by
  rfl

example : structuralErrorKinds ") (a (b)" =
    .ok [.unexpectedClose, .unclosedList] := by
  rfl

example : structuralErrorKinds "(a (b" =
    .ok [.unclosedList, .unclosedList] := by
  rfl

example : parseSource "(documentation Foo \"never closed)" =
    .error
      { kind := .unclosedString,
        span :=
          { start := { offset := 19, line := 1, column := 20 },
            stop := { offset := 33, line := 1, column := 34 } } } := by
  rfl

end Mettapedia.Languages.KIF
