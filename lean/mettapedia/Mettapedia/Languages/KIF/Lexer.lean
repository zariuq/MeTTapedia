import Mettapedia.Languages.KIF.Syntax

/-!
# Total lexer for SUO-KIF S-expressions

The lexer recognizes parentheses, symbols, regular variables (`?x`), sequence
variables (`@xs`), string literals, and semicolon line comments. Every token
has an exact source span. Strings may cross lines and preserve escape
sequences verbatim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.KIF

/-- Consume the longest prefix satisfying `accept`. -/
def consumeWhile (accept : Char → Bool) :
    List Char → SourcePos → List Char → String × List Char × SourcePos
  | [], position, reversed => (String.ofList reversed.reverse, [], position)
  | character :: rest, position, reversed =>
      if accept character then
        consumeWhile accept rest (position.advance character)
          (character :: reversed)
      else
        (String.ofList reversed.reverse, character :: rest, position)

/-- Scan the contents after an opening quote. The returned position is just
after the closing quote. -/
def consumeString (opening : SourcePos) :
    List Char → SourcePos → Bool → List Char →
      Except LexError (String × List Char × SourcePos)
  | [], position, _escaped, _reversed =>
      .error ⟨.unclosedString, ⟨opening, position⟩⟩
  | character :: rest, position, escaped, reversed =>
      let next := position.advance character
      if escaped then
        consumeString opening rest next false (character :: reversed)
      else if character = '\\' then
        consumeString opening rest next true (character :: reversed)
      else if character = '"' then
        .ok (String.ofList reversed.reverse, rest, next)
      else
        consumeString opening rest next false (character :: reversed)

def atomKindOfFirst : Char → AtomKind
  | '?' => .regularVariable
  | '@' => .sequenceVariable
  | _ => .symbol

def isAtomCharacter (character : Char) : Bool :=
  !character.isWhitespace &&
    character != '(' && character != ')' &&
    character != ';' && character != '"'

/-- Lex a character list from a known position. `fuel` is an explicit totality
guard. The public entry point supplies one unit per source character; every
recursive branch consumes at least one character. Exhaustion is reported
rather than silently truncating malformed input. -/
def lexFrom : Nat → List Char → SourcePos → List Token → Except LexError Lexed
  | 0, [], position, reversed => .ok ⟨reversed.reverse, position⟩
  | 0, _ :: _, position, _ =>
      .error ⟨.internalFuelExhausted, ⟨position, position⟩⟩
  | _ + 1, [], position, reversed => .ok ⟨reversed.reverse, position⟩
  | fuel + 1, character :: rest, position, reversed =>
      let next := position.advance character
      if character.isWhitespace then
        lexFrom fuel rest next reversed
      else if character = '(' then
        lexFrom fuel rest next
          (⟨.openParen, ⟨position, next⟩⟩ :: reversed)
      else if character = ')' then
        lexFrom fuel rest next
          (⟨.closeParen, ⟨position, next⟩⟩ :: reversed)
      else if character = ';' then
        let (text, remaining, afterComment) :=
          consumeWhile (fun current => current != '\n')
            (character :: rest) position []
        lexFrom fuel remaining afterComment
          (⟨.comment text, ⟨position, afterComment⟩⟩ :: reversed)
      else if character = '"' then
        match consumeString position rest next false [] with
        | .error failure => .error failure
        | .ok (text, remaining, afterString) =>
            lexFrom fuel remaining afterString
              (⟨.atom .stringLiteral text, ⟨position, afterString⟩⟩ :: reversed)
      else
        let (text, remaining, afterAtom) :=
          consumeWhile isAtomCharacter (character :: rest) position []
        lexFrom fuel remaining afterAtom
          (⟨.atom (atomKindOfFirst character) text,
            ⟨position, afterAtom⟩⟩ :: reversed)

/-- Lex one complete source string. -/
def lex (source : String) : Except LexError Lexed :=
  let characters := source.toList
  lexFrom characters.length characters SourcePos.start []

end Mettapedia.Languages.KIF
