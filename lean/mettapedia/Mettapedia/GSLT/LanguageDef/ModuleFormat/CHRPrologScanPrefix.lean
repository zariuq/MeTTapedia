import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback

/-! Scanning printed text that is cut or continued. Printed lexemes followed
by any text they read before lex to their tokens, then the lexing of that text
(`scanAux_before`). A printed lexeme cut short lexes to an error or to one
token, never a full stop (`scanAux_cut`). `Lexeme.Reads.prefix` and
`Lexeme.Reads.extend` move the reading condition to a shorter or a longer
continuation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback

open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.ReaderLexer
open private scanAux scanQuoted token isIdentifierContinue fullStopFollows from Mettapedia.Logic.Prolog.ReaderLexer

theorem map_then_cons (result : Except ReaderLexer.Error (List Token)) (head : Token) (earlier : List Token) :
    (do
      let following ← result.map (earlier ++ ·)
      pure (head :: following)) = result.map ((head :: earlier) ++ ·) := by
  cases result <;> rfl

/-- **Printed lexemes lex back before any text they read before.** -/
theorem scanAux_before : ∀ (lexemes : List Lexeme) (fuel : Nat) (position : Position) (tail : List Char),
    ReadsBefore lexemes tail →
    scanAux (lexemes.length + fuel) (lexemes.flatMap Lexeme.chars ++ tail) position =
      (scanAux fuel tail (position.advanceMany (lexemes.flatMap Lexeme.chars))).map (tokensOf lexemes position ++ ·)
  | [], fuel, position, tail, _ => by
    simp only [List.length_nil, Nat.zero_add, List.flatMap_nil, List.nil_append, Position.advanceMany,
      List.foldl_nil]
    cases scanAux fuel tail position <;> rfl
  | lexeme :: rest, fuel, position, tail, .cons reads later => by
    have ih := scanAux_before rest fuel (position.advanceMany lexeme.chars) tail later
    have length : (lexeme :: rest).length + fuel = (rest.length + fuel) + 1 := by
      simp only [List.length_cons]
      omega
    rw [length]
    have advanced : position.advanceMany ((lexeme :: rest).flatMap Lexeme.chars) =
        (position.advanceMany lexeme.chars).advanceMany (rest.flatMap Lexeme.chars) := by
      rw [List.flatMap_cons, Position.advanceMany_append]
    rw [advanced]
    cases lexeme with
    | quoted name =>
      simp only [List.flatMap_cons, Lexeme.chars, List.append_assoc, List.cons_append,
        List.nil_append]
      have step := scanAux_quoted (rest.length + fuel) name (rest.flatMap Lexeme.chars ++ tail) position reads
      simp only [List.cons_append] at step
      rw [step]
      simp only [Lexeme.chars, List.cons_append] at ih
      rw [ih, map_then_cons]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars]
      rfl
    | identifier first more =>
      obtain ⟨alpha, continues, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars, List.append_assoc]
      rw [scanAux_identifier _ first more _ position alpha continues stops]
      simp only [Lexeme.chars] at ih
      rw [ih, map_then_cons]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars]
      rfl
    | graphic first more =>
      obtain ⟨graphic, notDot, notComment, continues, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars, List.append_assoc]
      rw [scanAux_graphic _ first more _ position graphic notDot notComment continues stops]
      simp only [Lexeme.chars] at ih
      rw [ih, map_then_cons]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars]
      rfl
    | number first more =>
      obtain ⟨digit, digits, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars, List.append_assoc]
      rw [scanAux_number _ first more _ position digit digits stops]
      simp only [Lexeme.chars] at ih
      rw [ih, map_then_cons]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars]
      rfl
    | punctuation character value =>
      simp only [List.flatMap_cons, Lexeme.chars, List.cons_append, List.nil_append]
      rw [scanAux_punctuation _ character value _ position reads]
      simp only [Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil] at ih
      rw [ih, map_then_cons]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil]
      rfl
    | fullStop =>
      simp only [List.flatMap_cons, Lexeme.chars, List.cons_append, List.nil_append]
      rw [scanAux_fullStop _ _ position reads]
      simp only [Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil] at ih
      rw [ih, map_then_cons]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil]
      rfl
    | layout character =>
      obtain ⟨white, stops⟩ := reads
      simp only [List.flatMap_cons, Lexeme.chars, List.cons_append, List.nil_append]
      rw [scanAux_layout _ character _ position white stops]
      simp only [Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil] at ih
      rw [ih]
      simp only [tokensOf, Lexeme.kind?, Lexeme.chars, Position.advanceMany, List.foldl_cons, List.foldl_nil]

/-! ## A cut-off quoted atom -/

theorem scanQuoted_empty (fuel : Nat) (start position : Position) (reversed : List Char) :
    ∃ error, scanQuoted fuel '\'' start [] position reversed = .error error := by
  cases fuel <;> exact ⟨_, by rw [scanQuoted]⟩

/-- Scanning a cut-off canonical spelling either fails or closes the atom with
no text left. -/
theorem scanQuoted_cut (start : Position) : ∀ (name cut rest : List Char), cut ++ rest = name.flatMap quotedChars →
    ∀ (fuel : Nat) (position : Position) (reversed : List Char),
      (∃ error, scanQuoted fuel '\'' start cut position reversed = .error error) ∨
      ∃ value stop, scanQuoted fuel '\'' start cut position reversed = .ok (value, [], stop)
  | [], cut, rest, split, fuel, position, reversed => by
    have empty : cut = [] := (List.append_eq_nil_iff.mp (by simpa using split)).1
    subst empty
    exact .inl (scanQuoted_empty fuel start position reversed)
  | character :: name, cut, rest, split, fuel, position, reversed => by
    cases fuel with
    | zero => exact .inl ⟨_, by rw [scanQuoted]⟩
    | succ fuel =>
      cases cut with
      | nil => exact .inl (scanQuoted_empty _ start position reversed)
      | cons first cut =>
        rcases quotedChars_cases character with ⟨rfl, spelled⟩ | ⟨letter, spelled, notNewline, decodes⟩ |
            ⟨notQuote, notBackslash, spelled⟩
        · simp only [List.flatMap_cons, spelled, List.cons_append, List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, split⟩ := split
          cases cut with
          | nil =>
            exact .inr ⟨String.ofList reversed.reverse, position.advance '\'', by rw [scanQuoted]; simp⟩
          | cons second cut =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, split⟩ := split
            rw [scanQuoted_doubled]
            exact scanQuoted_cut start name cut rest split fuel _ _
        · simp only [List.flatMap_cons, spelled, List.cons_append, List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, split⟩ := split
          cases cut with
          | nil =>
            exact .inl ⟨{ position := position, kind := .unterminatedQuote '\'' }, by rw [scanQuoted]; simp⟩
          | cons second cut =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, split⟩ := split
            rw [scanQuoted_escape fuel start position second character cut reversed notNewline decodes]
            exact scanQuoted_cut start name cut rest split fuel _ _
        · simp only [List.flatMap_cons, spelled, List.cons_append, List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, split⟩ := split
          rw [scanQuoted_raw fuel start position first cut reversed notQuote notBackslash]
          exact scanQuoted_cut start name cut rest split fuel _ _

theorem scanAux_quote (fuel : Nat) (tail : List Char) (position : Position) :
    scanAux (fuel + 1) ('\'' :: tail) position =
      (match scanQuoted tail.length '\'' position tail (position.advance '\'') [] with
      | .error error => .error error
      | .ok (value, suffix, nextPosition) => do
          let following ← scanAux fuel suffix nextPosition
          pure (token (.quotedAtom value) position nextPosition :: following)) := by
  conv_lhs => unfold scanAux
  rfl

theorem scanAux_nil (fuel : Nat) (position : Position) : scanAux fuel [] position = .ok [] := by
  cases fuel <;> rw [scanAux]

/-- **A printed lexeme cut short** lexes to an error or to one token that is
not a full stop. -/
theorem scanAux_cut {lexeme : Lexeme} {text : List Char} (reads : lexeme.Reads text) {cut more : List Char}
    (split : lexeme.chars = cut ++ more) (started : cut ≠ []) (unfinished : more ≠ []) (fuel : Nat)
    (position : Position) :
    (∃ error, scanAux (fuel + 1) cut position = .error error) ∨
      ∃ token, scanAux (fuel + 1) cut position = .ok [token] ∧ token.kind ≠ .punctuation .fullStop := by
  cases lexeme with
  | quoted name =>
    cases cut with
    | nil => exact absurd rfl started
    | cons first inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, split⟩ := split
      obtain ⟨front, last, rfl⟩ : ∃ front last, more = front ++ [last] := by
        rcases List.eq_nil_or_concat more with empty | ⟨front, last, shape⟩
        · exact absurd empty unfinished
        · exact ⟨front, last, by rw [shape, List.concat_eq_append]⟩
      have encoded : inner ++ front = name.flatMap quotedChars := by
        rw [← List.append_assoc] at split
        exact List.append_inj_left' split.symm rfl
      rcases scanQuoted_cut position name inner front encoded inner.length (position.advance '\'') [] with
        ⟨error, failed⟩ | ⟨value, stop, closed⟩
      · exact .inl ⟨error, by rw [scanAux_quote, failed]⟩
      · have result : scanAux (fuel + 1) ('\'' :: inner) position =
            .ok [token (.quotedAtom value) position stop] := by
          rw [scanAux_quote, closed]
          simp only [scanAux_nil, bind, Except.bind, pure, Except.pure]
        exact .inr ⟨_, result, by simp [token]⟩
  | identifier first all =>
    obtain ⟨alpha, continues, _⟩ := reads
    cases cut with
    | nil => exact absurd rfl started
    | cons head inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, split⟩ := split
      have continues' : ∀ character ∈ inner, isIdentifierContinue character = true :=
        fun character inside => continues character (by rw [split]; exact List.mem_append_left _ inside)
      have shaped := scanAux_identifier fuel first inner [] position alpha continues' (by simp)
      rw [List.append_nil] at shaped
      rw [shaped]
      simp only [scanAux_nil, bind, Except.bind, pure, Except.pure]
      refine .inr ⟨_, rfl, ?_⟩
      simp only [token]
      split <;> simp
  | graphic first all =>
    obtain ⟨graphic, notDot, notComment, continues, _⟩ := reads
    cases cut with
    | nil => exact absurd rfl started
    | cons head inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, split⟩ := split
      have continues' : ∀ character ∈ inner, isGraphic character = true :=
        fun character inside => continues character (by rw [split]; exact List.mem_append_left _ inside)
      have notComment' : first = '/' → (inner ++ []).head? ≠ some '*' := by
        intro slash
        cases inner with
        | nil => simp
        | cons next tail =>
          have := notComment slash
          rw [split] at this
          simpa using this
      have shaped := scanAux_graphic fuel first inner [] position graphic notDot notComment' continues' (by simp)
      rw [List.append_nil] at shaped
      rw [shaped]
      simp only [scanAux_nil, bind, Except.bind, pure, Except.pure]
      exact .inr ⟨_, rfl, by simp [token]⟩
  | number first all =>
    obtain ⟨digit, digits, _⟩ := reads
    cases cut with
    | nil => exact absurd rfl started
    | cons head inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, split⟩ := split
      have digits' : ∀ character ∈ inner, character.isDigit = true :=
        fun character inside => digits character (by rw [split]; exact List.mem_append_left _ inside)
      have shaped := scanAux_number fuel first inner [] position digit digits' trivial
      rw [List.append_nil] at shaped
      rw [shaped]
      simp only [scanAux_nil, bind, Except.bind, pure, Except.pure]
      exact .inr ⟨_, rfl, by simp [token]⟩
  | punctuation character value =>
    cases cut with
    | nil => exact absurd rfl started
    | cons head inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨_, split⟩ := split
      exact absurd (List.append_eq_nil_iff.mp split.symm).2 unfinished
  | fullStop =>
    cases cut with
    | nil => exact absurd rfl started
    | cons head inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨_, split⟩ := split
      exact absurd (List.append_eq_nil_iff.mp split.symm).2 unfinished
  | layout character =>
    cases cut with
    | nil => exact absurd rfl started
    | cons head inner =>
      simp only [Lexeme.chars, List.cons_append, List.cons.injEq] at split
      obtain ⟨_, split⟩ := split
      exact absurd (List.append_eq_nil_iff.mp split.symm).2 unfinished

/-! ## Moving the reading condition -/

/-- A lexeme reads before a prefix of a text it reads before, unless it is a
full stop whose text is not a newline. -/
theorem Lexeme.Reads.prefix {lexeme : Lexeme} {text more : List Char} (reads : lexeme.Reads (text ++ more))
    (stop : lexeme = .fullStop → ∃ after, text ++ more = '\n' :: after) : lexeme.Reads text := by
  have head : ∀ next, text.head? = some next → (text ++ more).head? = some next := by
    intro next found
    cases text with
    | nil => cases found
    | cons first rest => simpa using found
  cases lexeme with
  | quoted name => exact fun next found => reads next (head next found)
  | identifier first all =>
    obtain ⟨alpha, continues, stops⟩ := reads
    exact ⟨alpha, continues, fun next found => stops next (head next found)⟩
  | graphic first all =>
    obtain ⟨graphic, notDot, notComment, continues, stops⟩ := reads
    refine ⟨graphic, notDot, fun slash => ?_, continues, fun next found => stops next (head next found)⟩
    have inner := notComment slash
    cases all with
    | cons next tail => simpa using inner
    | nil =>
      cases text with
      | nil => simp
      | cons next tail => simpa using inner
  | number first all =>
    obtain ⟨digit, digits, stops⟩ := reads
    refine ⟨digit, digits, ?_⟩
    cases text with
    | nil => trivial
    | cons next tail =>
      obtain ⟨dotted, plain⟩ := stops
      refine ⟨fun dot after found => dotted dot after ?_, plain⟩
      cases tail with
      | nil => cases found
      | cons first rest => simpa using found
  | punctuation character value => exact reads
  | fullStop =>
    obtain ⟨after, shape⟩ := stop rfl
    cases text with
    | nil => rfl
    | cons next tail =>
      simp only [List.cons_append, List.cons.injEq] at shape
      rw [shape.1]
      rfl
  | layout character =>
    obtain ⟨white, stops⟩ := reads
    exact ⟨white, fun next found => stops next (head next found)⟩

/-- A lexeme that reads before at least two characters reads before any
continuation of them. -/
theorem Lexeme.Reads.extend {lexeme : Lexeme} {first second : Char} {rest : List Char}
    (reads : lexeme.Reads (first :: second :: rest)) (more : List Char) :
    lexeme.Reads (first :: second :: rest ++ more) := by
  cases lexeme with
  | quoted name => exact fun next found => reads next (by simpa using found)
  | identifier head all =>
    obtain ⟨alpha, continues, stops⟩ := reads
    exact ⟨alpha, continues, fun next found => stops next (by simpa using found)⟩
  | graphic head all =>
    obtain ⟨graphic, notDot, notComment, continues, stops⟩ := reads
    refine ⟨graphic, notDot, fun slash => ?_, continues, fun next found => stops next (by simpa using found)⟩
    have inner := notComment slash
    cases all <;> simpa using inner
  | number head all =>
    obtain ⟨digit, digits, ⟨dotted, plain⟩⟩ := reads
    exact ⟨digit, digits, fun dot after found => dotted dot after (by simpa using found), plain⟩
  | punctuation character value => exact reads
  | fullStop =>
    show fullStopFollows (first :: second :: rest ++ more) = true
    have before : fullStopFollows (first :: second :: rest) = true := reads
    by_cases opening : first = '/' ∧ second = '*'
    · obtain ⟨rfl, rfl⟩ := opening
      rfl
    · have other : ∀ tail : List Char, fullStopFollows (first :: second :: tail) =
          (ReaderLexer.isLayout first || first = '%') := by
        intro tail
        unfold fullStopFollows
        split <;> simp_all
      simp only [List.cons_append]
      rw [other] at before ⊢
      exact before
  | layout character =>
    obtain ⟨white, stops⟩ := reads
    exact ⟨white, fun next found => stops next (by simpa using found)⟩

#print axioms scanAux_before
#print axioms scanAux_cut
#print axioms Lexeme.Reads.prefix
#print axioms Lexeme.Reads.extend

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback
