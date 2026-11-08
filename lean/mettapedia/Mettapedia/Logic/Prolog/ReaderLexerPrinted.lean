import Mettapedia.Logic.Prolog.ReaderLexer

/-! The lexer reads printed lexemes back. A quoted atom written with the
canonical escapes lexes to exactly that atom; the other printed lexemes
(variables, words, graphic operators, numbers, punctuation, layout) lex to
their tokens, with spans that record which lexemes touch. -/

set_option autoImplicit false

namespace Mettapedia.Logic.Prolog.ReaderLexer

open private scanQuoted from Mettapedia.Logic.Prolog.ReaderLexer

/-- The canonical spelling of one character inside a quoted atom. -/
def quotedChars : Char → List Char
  | '\'' => ['\'', '\'']
  | '\\' => ['\\', '\\']
  | '\n' => ['\\', 'n']
  | '\r' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | '\u0007' => ['\\', 'a']
  | '\u0008' => ['\\', 'b']
  | '\u000b' => ['\\', 'v']
  | '\u000c' => ['\\', 'f']
  | other => [other]

/-- Each character is spelled as a doubled quote, a backslash escape the
lexer decodes back, or itself. -/
theorem quotedChars_cases (character : Char) :
    (character = '\'' ∧ quotedChars character = ['\'', '\'']) ∨
    (∃ letter, quotedChars character = ['\\', letter] ∧ letter ≠ '\n' ∧ simpleEscape letter = some character) ∨
    (character ≠ '\'' ∧ character ≠ '\\' ∧ quotedChars character = [character]) := by
  unfold quotedChars
  split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr (.inl ⟨'\\', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'n', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'r', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'t', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'a', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'b', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'v', rfl, by decide, rfl⟩)
  · exact .inr (.inl ⟨'f', rfl, by decide, rfl⟩)
  · rename_i quote backslash _ _ _ _ _ _ _
    exact .inr (.inr ⟨quote, backslash, rfl⟩)

theorem Position.advanceMany_append (position : Position) (first second : List Char) :
    position.advanceMany (first ++ second) = (position.advanceMany first).advanceMany second := by
  simp [Position.advanceMany, List.foldl_append]

theorem Position.advanceMany_cons (position : Position) (character : Char) (rest : List Char) :
    position.advanceMany (character :: rest) = (position.advance character).advanceMany rest := rfl

theorem scanQuoted_doubled (fuel : Nat) (start position : Position) (tail reversed : List Char) :
    scanQuoted (fuel + 1) '\'' start ('\'' :: '\'' :: tail) position reversed =
      scanQuoted fuel '\'' start tail ((position.advance '\'').advance '\'') ('\'' :: reversed) := by
  rw [scanQuoted]
  simp

theorem scanQuoted_escape (fuel : Nat) (start position : Position) (letter decoded : Char)
    (tail reversed : List Char) (notNewline : letter ≠ '\n') (decodes : simpleEscape letter = some decoded) :
    scanQuoted (fuel + 1) '\'' start ('\\' :: letter :: tail) position reversed =
      scanQuoted fuel '\'' start tail ((position.advance '\\').advance letter) (decoded :: reversed) := by
  rw [scanQuoted]
  simp [notNewline, decodes]

theorem scanQuoted_raw (fuel : Nat) (start position : Position) (character : Char) (tail reversed : List Char)
    (notQuote : character ≠ '\'') (notBackslash : character ≠ '\\') :
    scanQuoted (fuel + 1) '\'' start (character :: tail) position reversed =
      scanQuoted fuel '\'' start tail (position.advance character) (character :: reversed) := by
  simp only [scanQuoted, notQuote, notBackslash, if_false]

/-- **Quoted atoms read back.** Scanning the canonical spelling of a name and
its closing quote, followed by anything but another quote, gives the name. -/
theorem scanQuoted_printed (start : Position) :
    ∀ (name rest : List Char) (position : Position) (reversed : List Char) (fuel : Nat),
      name.length < fuel → (∀ next, rest.head? = some next → next ≠ '\'') →
      scanQuoted fuel '\'' start (name.flatMap quotedChars ++ '\'' :: rest) position reversed =
        .ok (String.ofList (reversed.reverse ++ name), rest,
          position.advanceMany (name.flatMap quotedChars ++ ['\'']))
  | [], rest, position, reversed, fuel + 1, _, open_ => by
    cases rest with
    | nil => simp [scanQuoted, Position.advanceMany]
    | cons next tail =>
      have different : next ≠ '\'' := open_ next rfl
      simp [scanQuoted, different, Position.advanceMany]
  | character :: name, rest, position, reversed, fuel + 1, bound, open_ => by
    have smaller : name.length < fuel := by simp at bound; omega
    rcases quotedChars_cases character with ⟨rfl, spelled⟩ | ⟨letter, spelled, notNewline, decodes⟩ |
        ⟨notQuote, notBackslash, spelled⟩
    · simp only [List.flatMap_cons, spelled, List.cons_append, List.nil_append]
      rw [scanQuoted_doubled, scanQuoted_printed start name rest _ _ fuel smaller open_]
      simp [Position.advanceMany]
    · simp only [List.flatMap_cons, spelled, List.cons_append, List.nil_append]
      rw [scanQuoted_escape fuel start position letter character _ reversed notNewline decodes,
        scanQuoted_printed start name rest _ _ fuel smaller open_]
      simp [Position.advanceMany]
    · simp only [List.flatMap_cons, spelled, List.cons_append, List.nil_append]
      rw [scanQuoted_raw fuel start position character _ reversed notQuote notBackslash,
        scanQuoted_printed start name rest _ _ fuel smaller open_]
      simp [Position.advanceMany]

/-! ## One printed lexeme at a time -/

section Steps

open private scanAux takeWhile token fullStopFollows isIdentifierContinue takeNumberTail isNumberContinue from Mettapedia.Logic.Prolog.ReaderLexer

theorem takeWhile_stops (predicate : Char → Bool) (rest : List Char)
    (stops : ∀ next, rest.head? = some next → predicate next = false) : takeWhile predicate rest = ([], rest) := by
  cases rest with
  | nil => rfl
  | cons next tail => simp [takeWhile, stops next rfl]

/-- A layout character before a non-layout character is skipped. -/
theorem scanAux_layout (fuel : Nat) (character : Char) (rest : List Char) (position : Position)
    (white : ReaderLexer.isLayout character = true)
    (stops : ∀ next, rest.head? = some next → ReaderLexer.isLayout next = false) :
    scanAux (fuel + 1) (character :: rest) position = scanAux fuel rest (position.advance character) := by
  conv_lhs => unfold scanAux
  simp only [white, if_true, takeWhile_stops _ rest stops]
  rfl

/-- One punctuation character is one token. -/
theorem scanAux_punctuation (fuel : Nat) (character : Char) (value : Punctuation) (rest : List Char)
    (position : Position)
    (spelled : (character, value) ∈ [('(', .leftParen), (')', .rightParen), (',', .comma), ('|', .bar)]) :
    scanAux (fuel + 1) (character :: rest) position =
      (do
        let following ← scanAux fuel rest (position.advance character)
        pure (token (.punctuation value) position (position.advance character) :: following)) := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at spelled
  rcases spelled with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (conv_lhs => unfold scanAux) <;> simp [isLayout, scanAux.emitPunctuation]

/-- A full stop before layout or the end is one token. -/
theorem scanAux_fullStop (fuel : Nat) (rest : List Char) (position : Position)
    (follows : fullStopFollows rest = true) :
    scanAux (fuel + 1) ('.' :: rest) position =
      (do
        let following ← scanAux fuel rest (position.advance '.')
        pure (token (.punctuation .fullStop) position (position.advance '.') :: following)) := by
  conv_lhs => unfold scanAux
  simp [isLayout, follows, scanAux.emitPunctuation]

theorem takeWhile_prefix (predicate : Char → Bool) :
    ∀ (more rest : List Char), (∀ character ∈ more, predicate character = true) →
      (∀ next, rest.head? = some next → predicate next = false) →
      takeWhile predicate (more ++ rest) = (more, rest)
  | [], rest, _, stops => takeWhile_stops predicate rest stops
  | character :: more, rest, all, stops => by
    simp only [List.cons_append, takeWhile, all character List.mem_cons_self, if_true,
      takeWhile_prefix predicate more rest (fun other member => all other (List.mem_cons_of_mem _ member)) stops]

theorem isAlpha_not_digit {character : Char} (alpha : character.isAlpha = true) : character.isDigit = false := by
  cases digit : character.isDigit
  · rfl
  · exfalso
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at digit
    simp only [Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at alpha
    obtain ⟨_, high⟩ := digit
    rcases alpha with ⟨low, _⟩ | ⟨low, _⟩
    · exact absurd (UInt32.le_trans low high) (by decide)
    · exact absurd (UInt32.le_trans low high) (by decide)

/-- An ASCII letter is no Unicode uppercase scalar. -/
theorem isAlpha_upperScalar {character : Char} (alpha : character.isAlpha = true) :
    ReaderUnicode.isUpperScalar character.toNat = false := by
  apply ReaderUnicode.isUpperScalar_ascii
  simp only [Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at alpha
  have bound : character.val ≤ 'z'.val := by
    rcases alpha with ⟨_, high⟩ | ⟨_, high⟩
    · exact UInt32.le_trans high (by decide)
    · exact high
  have small : character.val.toNat ≤ 122 := by
    have := UInt32.le_iff_toNat_le.mp bound
    simpa using this
  show character.val.toNat < 128
  omega

/-- A name: a letter, then identifier characters, before a character that
cannot continue it. -/
theorem scanAux_identifier (fuel : Nat) (first : Char) (more rest : List Char) (position : Position)
    (alpha : first.isAlpha = true)
    (continues : ∀ character ∈ more, isIdentifierContinue character = true)
    (stops : ∀ next, rest.head? = some next → isIdentifierContinue next = false) :
    scanAux (fuel + 1) (first :: more ++ rest) position =
      (do
        let following ← scanAux fuel rest (position.advanceMany (first :: more))
        pure (token (if first.isUpper || first = '_' then Kind.variable (String.ofList (first :: more))
            else Kind.atom (String.ofList (first :: more)))
          position (position.advanceMany (first :: more)) :: following)) := by
  have notWhite : ReaderLexer.isLayout first = false := by
    cases white : ReaderLexer.isLayout first
    · rfl
    · simp only [ReaderLexer.isLayout, Bool.or_eq_true, decide_eq_true_eq] at white
      rcases white with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> simp at alpha
  have notPercent : first ≠ '%' := by rintro rfl; simp at alpha
  have notDigit := isAlpha_not_digit alpha
  conv_lhs => unfold scanAux
  split
  · contradiction
  · contradiction
  · contradiction
  next _ fuelArm characterArm listArm fuelEq listEq =>
  obtain rfl : fuel = fuelArm := Nat.succ.inj fuelEq
  obtain ⟨rfl, rfl⟩ := List.cons.inj listEq
  simp only [notWhite, Bool.false_eq_true, if_false, notPercent]
  split
  all_goals first
    | (simp at alpha)
    | skip
  simp only [notDigit, Bool.false_eq_true, if_false, alpha, Bool.true_or, if_true, List.append_eq,
    takeWhile_prefix isIdentifierContinue more rest continues stops, isAlpha_upperScalar alpha, Bool.or_false]

theorem graphic_cases {character : Char} (graphic : isGraphic character = true) :
    character ∈ ['#', '$', '&', '*', '+', '-', '.', '/', ':', '<', '=', '>', '?', '@', '\\', '^', '~'] := by
  simpa [isGraphic] using graphic

/-- A graphic operator, before a character that cannot continue it. -/
theorem scanAux_graphic (fuel : Nat) (first : Char) (more rest : List Char) (position : Position)
    (graphic : isGraphic first = true) (notDot : first ≠ '.')
    (notComment : first = '/' → (more ++ rest).head? ≠ some '*')
    (continues : ∀ character ∈ more, isGraphic character = true)
    (stops : ∀ next, rest.head? = some next → isGraphic next = false) :
    scanAux (fuel + 1) (first :: more ++ rest) position =
      (do
        let following ← scanAux fuel rest (position.advanceMany (first :: more))
        pure (token (.atom (String.ofList (first :: more))) position (position.advanceMany (first :: more)) ::
          following)) := by
  have member := graphic_cases graphic
  have notWhite : ReaderLexer.isLayout first = false := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  have notPercent : first ≠ '%' := by rintro rfl; simp at member
  have notDigit : first.isDigit = false := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  have notName : (first.isAlpha || decide (first = '_')) = false := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  have notUnicodeName : ReaderUnicode.isNameScalar first = false := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  conv_lhs => unfold scanAux
  split
  · contradiction
  · contradiction
  · contradiction
  next _ fuelArm characterArm listArm fuelEq listEq =>
  obtain rfl : fuel = fuelArm := Nat.succ.inj fuelEq
  obtain ⟨rfl, rfl⟩ := List.cons.inj listEq
  simp only [notWhite, Bool.false_eq_true, if_false, notPercent]
  split
  all_goals first
    | (exact absurd graphic (by decide))
    | (exact absurd rfl notDot)
    | (exfalso; apply notComment rfl; simp_all)
    | skip
  simp only [notDigit, Bool.false_eq_true, if_false, notName, notUnicodeName, Bool.or_false, graphic, if_true,
    List.append_eq, takeWhile_prefix isGraphic more rest continues stops]

/-- What may follow a decimal integer without extending it. -/
def NumberStops : List Char → Prop
  | [] => True
  | next :: tail => (next = '.' → ∀ after, tail.head? = some after → after.isDigit = false) ∧
      (next ≠ '.' → next.isAlphanum = false ∧ next ≠ '_' ∧ next ≠ '\'')

theorem digit_facts {character : Char} (digit : character.isDigit = true) :
    character ≠ '\'' ∧ character ≠ '.' ∧ character.isAlphanum = true := by
  refine ⟨?_, ?_, by simp [Char.isAlphanum, digit]⟩ <;> rintro rfl <;> simp at digit

theorem takeNumberTail_digits :
    ∀ (previous : Char) (more rest : List Char), previous.isDigit = true →
      (∀ character ∈ more, character.isDigit = true) → NumberStops rest →
      takeNumberTail previous (more ++ rest) = (more, rest)
  | previous, [], [], _, _, _ => by simp [takeNumberTail]
  | previous, [], next :: tail, digit, _, stops => by
    obtain ⟨notQuote, _, _⟩ := digit_facts digit
    obtain ⟨afterDot, afterOther⟩ := stops
    by_cases dot : next = '.'
    · subst dot
      cases tail with
      | nil => simp [takeNumberTail, notQuote]
      | cons after rest =>
        have notDigit := afterDot rfl after rfl
        simp [takeNumberTail, notQuote, notDigit]
    · obtain ⟨notAlphanum, notUnderscore, notQuote'⟩ := afterOther dot
      have notLower : previous ≠ 'e' := by rintro rfl; simp at digit
      have notUpper : previous ≠ 'E' := by rintro rfl; simp at digit
      simp [takeNumberTail, notQuote, dot, isNumberContinue, notAlphanum, notUnderscore, notQuote', notLower,
        notUpper]
  | previous, character :: more, rest, digit, digits, stops => by
    obtain ⟨notQuote, _, _⟩ := digit_facts digit
    have here := digits character List.mem_cons_self
    obtain ⟨_, notDot, alphanum⟩ := digit_facts here
    have later := takeNumberTail_digits character more rest here
      (fun other member => digits other (List.mem_cons_of_mem _ member)) stops
    simp [takeNumberTail, notQuote, notDot, isNumberContinue, alphanum, later]

/-- A decimal integer, before a character that cannot extend it. -/
theorem scanAux_number (fuel : Nat) (first : Char) (more rest : List Char) (position : Position)
    (digit : first.isDigit = true) (digits : ∀ character ∈ more, character.isDigit = true)
    (stops : NumberStops rest) :
    scanAux (fuel + 1) (first :: more ++ rest) position =
      (do
        let following ← scanAux fuel rest (position.advanceMany (first :: more))
        pure (token (.number (String.ofList (first :: more))) position (position.advanceMany (first :: more)) ::
          following)) := by
  have notWhite : ReaderLexer.isLayout first = false := by
    cases white : ReaderLexer.isLayout first
    · rfl
    · simp only [ReaderLexer.isLayout, Bool.or_eq_true, decide_eq_true_eq] at white
      rcases white with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> simp at digit
  have notPercent : first ≠ '%' := by rintro rfl; simp at digit
  conv_lhs => unfold scanAux
  split
  · contradiction
  · contradiction
  · contradiction
  next _ fuelArm characterArm listArm fuelEq listEq =>
  obtain rfl : fuel = fuelArm := Nat.succ.inj fuelEq
  obtain ⟨rfl, rfl⟩ := List.cons.inj listEq
  simp only [notWhite, Bool.false_eq_true, if_false, notPercent]
  split
  all_goals first
    | (exact absurd digit (by decide))
    | skip
  simp only [digit, if_true, List.append_eq, takeNumberTail_digits _ more rest digit digits stops]

theorem quotedChars_length (character : Char) : 1 ≤ (quotedChars character).length := by
  rcases quotedChars_cases character with ⟨_, spelled⟩ | ⟨_, spelled, _, _⟩ | ⟨_, _, spelled⟩ <;>
    simp [spelled]

theorem name_length_le (name : List Char) : name.length ≤ (name.flatMap quotedChars).length := by
  induction name with
  | nil => simp
  | cons character rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := quotedChars_length character
    omega

/-- A quoted atom in its canonical spelling, before anything but a quote. -/
theorem scanAux_quoted (fuel : Nat) (name rest : List Char) (position : Position)
    (stops : ∀ next, rest.head? = some next → next ≠ '\'') :
    scanAux (fuel + 1) ('\'' :: name.flatMap quotedChars ++ '\'' :: rest) position =
      (do
        let following ← scanAux fuel rest (position.advanceMany ('\'' :: name.flatMap quotedChars ++ ['\'']))
        pure (token (.quotedAtom (String.ofList name)) position
          (position.advanceMany ('\'' :: name.flatMap quotedChars ++ ['\''])) :: following)) := by
  have bound : name.length < (name.flatMap quotedChars ++ '\'' :: rest).length := by
    have := name_length_le name
    simp only [List.length_append, List.length_cons]
    omega
  conv_lhs => unfold scanAux
  split
  · contradiction
  · contradiction
  · contradiction
  next _ fuelArm characterArm listArm fuelEq listEq =>
  obtain rfl : fuel = fuelArm := Nat.succ.inj fuelEq
  obtain ⟨rfl, rfl⟩ := List.cons.inj listEq
  simp only [show ReaderLexer.isLayout '\'' = false by decide, Bool.false_eq_true, if_false,
    show ('\'' : Char) ≠ '%' by decide, List.append_eq]
  rw [scanQuoted_printed _ name rest _ [] _ bound stops]
  simp [Position.advanceMany]

end Steps

/-! ## Printed lexeme sequences -/

open private isIdentifierContinue fullStopFollows from Mettapedia.Logic.Prolog.ReaderLexer

/-- A printed lexeme. -/
inductive Lexeme where
  | quoted (name : List Char)
  | identifier (first : Char) (more : List Char)
  | graphic (first : Char) (more : List Char)
  | number (first : Char) (more : List Char)
  | punctuation (character : Char) (value : Punctuation)
  | fullStop
  | layout (character : Char)

namespace Lexeme

/-- The characters a lexeme is printed as. -/
def chars : Lexeme → List Char
  | quoted name => '\'' :: name.flatMap quotedChars ++ ['\'']
  | identifier first more => first :: more
  | graphic first more => first :: more
  | number first more => first :: more
  | punctuation character _ => [character]
  | fullStop => ['.']
  | layout character => [character]

/-- The token a lexeme lexes to; layout lexes to none. -/
def kind? : Lexeme → Option Kind
  | quoted name => some (.quotedAtom (String.ofList name))
  | identifier first more => some (if first.isUpper || first = '_' then .variable (String.ofList (first :: more))
      else .atom (String.ofList (first :: more)))
  | graphic first more => some (.atom (String.ofList (first :: more)))
  | number first more => some (.number (String.ofList (first :: more)))
  | punctuation _ value => some (.punctuation value)
  | fullStop => some (.punctuation .fullStop)
  | layout _ => none

/-- The lexeme is spelled as its class requires, and the text after it
cannot extend it. -/
def Reads : Lexeme → List Char → Prop
  | quoted _, rest => ∀ next, rest.head? = some next → next ≠ '\''
  | identifier first more, rest => first.isAlpha = true ∧ (∀ character ∈ more, isIdentifierContinue character = true) ∧
      ∀ next, rest.head? = some next → isIdentifierContinue next = false
  | graphic first more, rest => isGraphic first = true ∧ first ≠ '.' ∧ (first = '/' → (more ++ rest).head? ≠ some '*') ∧
      (∀ character ∈ more, isGraphic character = true) ∧ ∀ next, rest.head? = some next → isGraphic next = false
  | number first more, rest => first.isDigit = true ∧ (∀ character ∈ more, character.isDigit = true) ∧ NumberStops rest
  | punctuation character value, _ =>
      (character, value) ∈ [('(', .leftParen), (')', .rightParen), (',', .comma), ('|', .bar)]
  | fullStop, rest => fullStopFollows rest = true
  | layout character, rest =>
      ReaderLexer.isLayout character = true ∧ ∀ next, rest.head? = some next → ReaderLexer.isLayout next = false

end Lexeme

/-- Every lexeme reads, given the text after it. -/
inductive AllRead : List Lexeme → Prop
  | nil : AllRead []
  | cons {lexeme : Lexeme} {rest : List Lexeme} : lexeme.Reads (rest.flatMap Lexeme.chars) → AllRead rest →
      AllRead (lexeme :: rest)

/-- The tokens of a printed lexeme sequence, with the spans of their characters. -/
def tokensOf : List Lexeme → Position → List Token
  | [], _ => []
  | lexeme :: rest, position =>
    match lexeme.kind? with
    | some kind => { kind, span := ⟨position, position.advanceMany lexeme.chars⟩ } ::
        tokensOf rest (position.advanceMany lexeme.chars)
    | none => tokensOf rest (position.advanceMany lexeme.chars)

section Sequences

open private scanAux token from Mettapedia.Logic.Prolog.ReaderLexer

/-- **Printed lexemes lex back.** -/
theorem scanAux_lexemes : ∀ (lexemes : List Lexeme) (fuel : Nat) (position : Position), AllRead lexemes →
    lexemes.length ≤ fuel → scanAux fuel (lexemes.flatMap Lexeme.chars) position = .ok (tokensOf lexemes position)
  | [], 0, _, _, _ => by unfold scanAux; rfl
  | [], _ + 1, _, _, _ => by unfold scanAux; rfl
  | _ :: _, 0, _, _, bound => by simp at bound
  | lexeme :: rest, fuel + 1, position, .cons reads later, bound => by
    have ih := scanAux_lexemes rest fuel (position.advanceMany lexeme.chars) later (by simp at bound; omega)
    cases lexeme with
    | quoted name =>
      simp only [List.flatMap_cons, Lexeme.chars, List.append_assoc, List.singleton_append]
      rw [scanAux_quoted fuel name _ position reads]
      simp only [Lexeme.chars] at ih
      rw [ih]
      rfl
    | identifier first more =>
      obtain ⟨alpha, continues, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars]
      rw [scanAux_identifier fuel first more _ position alpha continues stops]
      simp only [Lexeme.chars] at ih
      rw [ih]
      rfl
    | graphic first more =>
      obtain ⟨graphic, notDot, notComment, continues, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars]
      rw [scanAux_graphic fuel first more _ position graphic notDot notComment continues stops]
      simp only [Lexeme.chars] at ih
      rw [ih]
      rfl
    | number first more =>
      obtain ⟨digit, digits, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars]
      rw [scanAux_number fuel first more _ position digit digits stops]
      simp only [Lexeme.chars] at ih
      rw [ih]
      rfl
    | punctuation character value =>
      simp only [List.flatMap_cons, Lexeme.chars, List.singleton_append]
      rw [scanAux_punctuation fuel character value _ position reads]
      simp only [Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil] at ih
      rw [ih]
      rfl
    | fullStop =>
      simp only [List.flatMap_cons, Lexeme.chars, List.singleton_append]
      rw [scanAux_fullStop fuel _ position reads]
      simp only [Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil] at ih
      rw [ih]
      rfl
    | layout character =>
      obtain ⟨white, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars, List.singleton_append]
      rw [scanAux_layout fuel character _ position white stops]
      simp only [Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil] at ih
      rw [ih]
      rfl

/-- **Printed text lexes back.** -/
theorem scan_lexemes (lexemes : List Lexeme) (reads : AllRead lexemes) :
    scan (String.ofList (lexemes.flatMap Lexeme.chars)) = .ok (tokensOf lexemes Position.initial) := by
  unfold scan
  simp only [String.toList_ofList]
  apply scanAux_lexemes lexemes _ Position.initial reads
  clear reads
  induction lexemes with
  | nil => simp
  | cons lexeme rest ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have : 1 ≤ lexeme.chars.length := by cases lexeme <;> simp [Lexeme.chars]
    omega

end Sequences

#print axioms scanQuoted_printed
#print axioms scan_lexemes

end Mettapedia.Logic.Prolog.ReaderLexer
