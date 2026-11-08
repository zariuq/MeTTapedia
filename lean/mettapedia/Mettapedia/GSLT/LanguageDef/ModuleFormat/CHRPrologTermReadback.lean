import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax
import Mettapedia.Logic.Prolog.ReaderLexerPrinted

/-! Printed C0 sentences read back as their source terms. The canonical
printer's sentences lex to tokens whose operator structure the reference
term reader, under the CHR profile, parses into exactly the source terms
that `CHRPrologReadback` lowers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback

open Mettapedia.Logic.Prolog
open Mettapedia.Languages
open Mettapedia.Logic.Prolog.ReaderOperator
open private parseNatBase parseNatBase.loop asciiDigit? from Mettapedia.Logic.Prolog.ReaderNumber

/-! ## Decimal numbers -/

/-- One decimal digit appended to a value. -/
def digitStep (value : Nat) (character : Char) : Nat := value * 10 + (character.toNat - '0'.toNat)

theorem digit_bounds {character : Char} (digit : character.isDigit = true) :
    '0' ≤ character ∧ character ≤ '9' := by
  unfold Char.isDigit at digit
  simp only [Bool.and_eq_true, decide_eq_true_eq] at digit
  exact digit

theorem asciiDigit_digit {character : Char} (digit : character.isDigit = true) :
    asciiDigit? character = some (character.toNat - '0'.toNat) := by
  have bounds := digit_bounds digit
  unfold asciiDigit?
  simp [bounds.1, bounds.2]

theorem digit_value_lt {character : Char} (digit : character.isDigit = true) :
    character.toNat - '0'.toNat < 10 := by
  have bounds := digit_bounds digit
  have low : 48 ≤ character.toNat := bounds.1
  have high : character.toNat ≤ 57 := bounds.2
  show character.toNat - 48 < 10
  omega

theorem loop_digits : ∀ (characters : List Char) (value : Nat) (sawDigit previous : Bool),
    (∀ character ∈ characters, character.isDigit = true) → characters ≠ [] →
      parseNatBase.loop 10 characters value sawDigit previous = .ok (characters.foldl digitStep value)
  | [], _, _, _, _, nonempty => absurd rfl nonempty
  | [character], value, sawDigit, previous, digits, _ => by
    have digit := digits character List.mem_cons_self
    have notSeparator : character ≠ '_' := by rintro rfl; simp at digit
    simp only [parseNatBase.loop, notSeparator, if_false, asciiDigit_digit digit, digit_value_lt digit, if_true]
    simp [digitStep]
  | character :: next :: rest, value, sawDigit, previous, digits, _ => by
    have digit := digits character List.mem_cons_self
    have notSeparator : character ≠ '_' := by rintro rfl; simp at digit
    rw [parseNatBase.loop]
    simp only [notSeparator, if_false, asciiDigit_digit digit, digit_value_lt digit, if_true]
    rw [loop_digits (next :: rest) _ true true (fun other inside => digits other (List.mem_cons_of_mem _ inside))
      (by simp)]
    rfl

theorem digitChar_value {digit : Nat} (small : digit < 10) : (Nat.digitChar digit).toNat - '0'.toNat = digit := by
  interval_cases digit <;> rfl

theorem foldl_toDigits (number : Nat) : (Nat.toDigits 10 number).foldl digitStep 0 = number := by
  induction number using Nat.strong_induction_on with
  | _ number ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · rename_i small
      simp only [List.foldl_cons, List.foldl_nil, digitStep, Nat.zero_mul, Nat.zero_add]
      exact digitChar_value small
    · rename_i large
      rw [List.foldl_append, ih (number / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, digitStep]
      rw [digitChar_value (Nat.mod_lt number (by decide))]
      omega

theorem toDigits_digits (number : Nat) : ∀ character ∈ Nat.toDigits 10 number, character.isDigit = true :=
  fun _ member => Nat.isDigit_of_mem_toDigits (by decide) (by decide) member

theorem parseNatBase_digits (characters : List Char) (digits : ∀ character ∈ characters, character.isDigit = true)
    (nonempty : characters ≠ []) :
    parseNatBase 10 characters = .ok (characters.foldl digitStep 0) :=
  loop_digits characters 0 false false digits nonempty

theorem digit_not_special {character : Char} (digit : character.isDigit = true) :
    (character = '.' || character = 'e' || character = 'E' || character = 'I' || character = 'N' ||
      character = 'r') = false := by
  have bounds := digit_bounds digit
  have low : 48 ≤ character.toNat := bounds.1
  have high : character.toNat ≤ 57 := bounds.2
  have different : ∀ other : Char, (other.toNat < 48 ∨ 57 < other.toNat) → character ≠ other := by
    rintro other outside rfl
    omega
  simp [different '.' (by decide), different 'e' (by decide), different 'E' (by decide),
    different 'I' (by decide), different 'N' (by decide), different 'r' (by decide)]

/-- A nonempty run of decimal digits reads as its value. -/
theorem parse_digits (characters : List Char) (digits : ∀ character ∈ characters, character.isDigit = true)
    (nonempty : characters ≠ []) :
    ReaderNumber.parse (String.ofList characters) = .ok (.integer (Int.ofNat (characters.foldl digitStep 0))) := by
  unfold ReaderNumber.parse
  rw [String.toList_ofList]
  revert digits nonempty
  split
  · intro _ nonempty
    exact absurd rfl nonempty
  · intro digits _
    exact absurd (digits '\'' (by simp)) (by decide)
  · intro digits _
    exact absurd (digits 'x' (by simp)) (by decide)
  · intro digits _
    exact absurd (digits 'X' (by simp)) (by decide)
  · intro digits _
    exact absurd (digits 'o' (by simp)) (by decide)
  · intro digits _
    exact absurd (digits 'O' (by simp)) (by decide)
  · intro digits _
    exact absurd (digits 'b' (by simp)) (by decide)
  · intro digits _
    exact absurd (digits 'B' (by simp)) (by decide)
  · intro digits nonempty
    have noFloat : characters.any (fun character => character = '.' || character = 'e' || character = 'E' ||
        character = 'I' || character = 'N' || character = 'r') = false := by
      rw [List.any_eq_false]
      intro character inside
      rw [digit_not_special (digits character inside)]
      simp
    rw [if_neg (by simp only [noFloat]; decide), parseNatBase_digits characters digits nonempty]

/-- A decimal numeral reads as its value. -/
theorem parse_toString (number : Nat) : ReaderNumber.parse (toString number) = .ok (.integer number) := by
  have listed : toString number = String.ofList (Nat.toDigits 10 number) := by
    apply String.toList_inj.mp
    rw [String.toList_ofList]
    exact Nat.toList_repr
  rw [listed, parse_digits _ (toDigits_digits number) Nat.toDigits_ne_nil, foldl_toDigits]
  rfl

example : ReaderNumber.parse "407" = .ok (.integer 407) := parse_toString 407

#print axioms parse_toString

/-! ## Printed lexemes -/

open Mettapedia.Logic.Prolog.ReaderLexer (Lexeme Token Kind Punctuation Position tokensOf)

namespace Printed

def space : Lexeme := .layout ' '
def newline : Lexeme := .layout '\n'
def comma : Lexeme := .punctuation ',' .comma
def openParen : Lexeme := .punctuation '(' .leftParen
def closeParen : Lexeme := .punctuation ')' .rightParen
def bar : Lexeme := .punctuation '|' .bar

/-- An unquoted name: a word, or a run of graphic characters. -/
def bare (text : String) : Lexeme :=
  match text.toList with
  | first :: more => if first.isAlpha then .identifier first more else .graphic first more
  | [] => .layout ' '

def quoted (text : String) : Lexeme := .quoted text.toList

def numeral (number : Nat) : Lexeme :=
  match (toString number).toList with
  | first :: more => .number first more
  | [] => .layout ' '

def indexed (index : Nat) : Lexeme := .identifier 'V' (toString index).toList

def integer (number : Int) : List Lexeme :=
  if 0 ≤ number then [numeral number.toNat] else [bare "-", numeral number.natAbs]

/-- Items separated by a comma and a space. -/
def separated : List (List Lexeme) → List Lexeme
  | [] => []
  | [single] => single
  | first :: second :: more => first ++ [comma, space] ++ separated (second :: more)

end Printed

open Printed

/-! ## Tokens of printed lexemes -/

theorem tokensOf_append : ∀ (first second : List Lexeme) (position : Position),
    tokensOf (first ++ second) position =
      tokensOf first position ++ tokensOf second (position.advanceMany (first.flatMap Lexeme.chars))
  | [], _, _ => rfl
  | lexeme :: rest, second, position => by
    simp only [List.cons_append, tokensOf, List.flatMap_cons, ReaderLexer.Position.advanceMany_append]
    split <;> simp [tokensOf_append rest second]

/-- The number of tokens a lexeme sequence lexes to. -/
def tokenCount (lexemes : List Lexeme) : Nat := (lexemes.filter fun lexeme => lexeme.kind?.isSome).length

theorem tokensOf_length : ∀ (lexemes : List Lexeme) (position : Position),
    (tokensOf lexemes position).length = tokenCount lexemes
  | [], _ => rfl
  | lexeme :: rest, position => by
    unfold tokensOf tokenCount
    split
    · rename_i kind found
      simp [found, tokensOf_length rest, tokenCount]
    · rename_i none
      simp [none, tokensOf_length rest, tokenCount]

theorem tokenCount_append (first second : List Lexeme) :
    tokenCount (first ++ second) = tokenCount first + tokenCount second := by
  simp [tokenCount, List.filter_append]

/-! ## The CHR reading profile -/

abbrev chr : ReaderProfile.Profile := CHRPrologSyntax.profile

/-- Every prefix operator of the profile is spelled as a bare atom. -/
theorem prefix_bare : ∀ declaration ∈ chr.operators, declaration.specifier.isPrefix = true →
    ReaderProfile.bareAtom declaration.name = true := by
  decide

theorem no_postfix : ∀ declaration ∈ chr.operators, declaration.specifier.isPostfix = false := by
  decide

theorem postfixes_none (name : String) : postfixes chr.operators name = [] := by
  rw [postfixes, List.filter_eq_nil_iff]
  intro declaration inside
  simp [no_postfix declaration inside]

#print axioms prefix_bare

/-! ## One step of the reader -/

open Mettapedia.Logic.Prolog.ReaderTerm (State Parsed)
open private parseExpressionAux parsePrefixOrPrimaryAux parsePrefixAux parsePrimaryAux parseApplicationAux
  parseArgumentsAux parseTailAux consumePunctuation adjacent tokenStartsTerm operatorName? firstEligiblePrefix
  firstEligibleInfix firstEligiblePostfix eligible eligiblePrefix negateConstant from Mettapedia.Logic.Prolog.ReaderTerm

theorem quoted_not_prefix (name : String) (maximum : Nat) (quotedOperator : chr.quotedOperator name = true) :
    firstEligiblePrefix chr.operators name maximum = none := by
  have swi : (chr.dialect == ReaderProfile.Dialect.iso) = false := by decide
  have bare : ReaderProfile.bareAtom name = false := by
    unfold ReaderProfile.Profile.quotedOperator at quotedOperator
    simpa [swi] using quotedOperator
  unfold firstEligiblePrefix
  rw [show prefixes chr.operators name = [] from ?_]
  · rfl
  rw [prefixes, List.filter_eq_nil_iff]
  intro declaration inside both
  simp only [Bool.and_eq_true, decide_eq_true_eq] at both
  have := prefix_bare declaration inside both.1
  rw [both.2] at this
  simp [this] at bare

theorem firstEligiblePostfix_none (name : String) (maximum precedence : Nat) :
    firstEligiblePostfix chr.operators name maximum precedence = none := by
  simp [firstEligiblePostfix, postfixes_none]

/-- The operator loop stops before a token that continues no operator at
this level. -/
theorem tail_stops (fuel maximum : Nat) (left : Parsed) (token : Token) (rest : List Token)
    (remaining : left.state.remaining = token :: rest)
    (stops : ∀ name, operatorName? chr token.kind = some name →
      firstEligibleInfix chr.operators name maximum left.precedence = none) :
    parseTailAux chr (fuel + 1) chr.operators maximum left = .ok left := by
  unfold parseTailAux
  rw [remaining]
  simp only
  cases named : operatorName? chr token.kind with
  | none => rfl
  | some name => simp [stops name named, firstEligiblePostfix_none]

theorem tail_end (fuel maximum : Nat) (left : Parsed) (remaining : left.state.remaining = []) :
    parseTailAux chr (fuel + 1) chr.operators maximum left = .ok left := by
  unfold parseTailAux
  rw [remaining]

/-- The operator loop continues with an infix operator. -/
theorem tail_infix (fuel maximum : Nat) (left : Parsed) (token next : Token) (rest : List Token) (name : String)
    (declaration : Declaration) (rightMaximum : Nat)
    (remaining : left.state.remaining = token :: next :: rest)
    (named : operatorName? chr token.kind = some name)
    (found : firstEligibleInfix chr.operators name maximum left.precedence = some declaration)
    (bounded : declaration.specifier.rightMaximum declaration.priority.value = some rightMaximum)
    (starts : tokenStartsTerm next.kind = true) :
    parseTailAux chr (fuel + 1) chr.operators maximum left = (do
      let right ← parseExpressionAux chr fuel chr.operators rightMaximum { left.state with remaining := next :: rest }
      parseTailAux chr fuel chr.operators maximum
        { term := SourceSignature.compound name [left.term, right.term], precedence := declaration.priority.value,
          state := right.state }) := by
  conv_lhs => unfold parseTailAux
  rw [remaining]
  simp only [named, found, starts, Option.isSome_some, Bool.and_self, if_true, bounded]

theorem expression_step (fuel maximum : Nat) (state : State) :
    parseExpressionAux chr (fuel + 1) chr.operators maximum state = (do
      let left ← parsePrefixOrPrimaryAux chr fuel chr.operators maximum state
      parseTailAux chr fuel chr.operators maximum left) := by
  conv_lhs => unfold parseExpressionAux

/-- A token that is neither a word nor a quoted atom is read as a primary. -/
theorem prefix_other (fuel maximum : Nat) (state : State) (token : Token) (rest : List Token)
    (remaining : state.remaining = token :: rest)
    (notWord : ∀ name, token.kind ≠ .atom name) (notQuoted : ∀ name, token.kind ≠ .quotedAtom name) :
    parsePrefixOrPrimaryAux chr (fuel + 1) chr.operators maximum state =
      parsePrimaryAux chr fuel chr.operators state := by
  conv_lhs => unfold parsePrefixOrPrimaryAux
  rw [remaining]
  rcases token with ⟨kind, span⟩
  cases kind <;> simp_all

/-- A quoted atom never opens a prefix operator under this profile. -/
theorem prefix_quoted (fuel maximum : Nat) (state : State) (name : String) (span : ReaderLexer.Span)
    (rest : List Token) (remaining : state.remaining = ⟨.quotedAtom name, span⟩ :: rest) :
    parsePrefixOrPrimaryAux chr (fuel + 1) chr.operators maximum state =
      parsePrimaryAux chr fuel chr.operators state := by
  conv_lhs => unfold parsePrefixOrPrimaryAux
  rw [remaining]
  cases rest with
  | nil => rfl
  | cons next more =>
    simp only
    by_cases quotedOperator : chr.quotedOperator name = true
    · simp [quoted_not_prefix name maximum quotedOperator]
    · simp [quotedOperator]

/-- A word that is not a prefix operator is read as a primary. -/
theorem prefix_word (fuel maximum : Nat) (state : State) (name : String) (span : ReaderLexer.Span)
    (rest : List Token) (remaining : state.remaining = ⟨.atom name, span⟩ :: rest)
    (notMinus : name ≠ "-") (notPrefix : prefixes chr.operators name = []) :
    parsePrefixOrPrimaryAux chr (fuel + 1) chr.operators maximum state =
      parsePrimaryAux chr fuel chr.operators state := by
  have noPrefix : firstEligiblePrefix chr.operators name maximum = none := by
    simp [firstEligiblePrefix, notPrefix]
  conv_lhs => unfold parsePrefixOrPrimaryAux
  rw [remaining]
  cases rest with
  | nil => simp [noPrefix]
  | cons next more => split <;> rename_i heq <;> simp_all

/-- A word followed directly by an opening parenthesis is read as a primary. -/
theorem prefix_applied (fuel maximum : Nat) (state : State) (name : String) (span : ReaderLexer.Span)
    (paren : Token) (rest : List Token)
    (remaining : state.remaining = ⟨.atom name, span⟩ :: paren :: rest)
    (opens : paren.kind = .punctuation .leftParen) (touches : adjacent ⟨.atom name, span⟩ paren = true) :
    parsePrefixOrPrimaryAux chr (fuel + 1) chr.operators maximum state =
      parsePrimaryAux chr fuel chr.operators state := by
  conv_lhs => unfold parsePrefixOrPrimaryAux
  rw [remaining]
  rcases paren with ⟨kind, parenSpan⟩
  simp only at opens
  subst opens
  split
  all_goals first
    | rfl
    | (rename_i heq; simp at heq; done)
    | (rename_i heq
       simp only [List.cons.injEq, Token.mk.injEq, Kind.atom.injEq] at heq
       obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
       simp [touches])

/-- A minus sign touching a numeral reads as a negative number. -/
theorem prefix_negative (fuel maximum : Nat) (state : State) (minus number : ReaderLexer.Span) (lexeme : String)
    (rest : List Token) (value : Nat)
    (remaining : state.remaining = ⟨.atom "-", minus⟩ :: ⟨.number lexeme, number⟩ :: rest)
    (touches : adjacent ⟨.atom "-", minus⟩ ⟨.number lexeme, number⟩ = true)
    (allowed : chr.numericAllowed lexeme = true) (parsed : ReaderNumber.parse lexeme = .ok (.integer value)) :
    parsePrefixOrPrimaryAux chr (fuel + 1) chr.operators maximum state =
      .ok ⟨.const (.integer (-value)), 0, { state with remaining := rest }⟩ := by
  conv_lhs => unfold parsePrefixOrPrimaryAux
  rw [remaining]
  simp [touches, allowed, parsed, negateConstant]

theorem primary_word (fuel : Nat) (state : State) (kind : Kind) (span : ReaderLexer.Span) (name : String)
    (rest : List Token) (remaining : state.remaining = ⟨kind, span⟩ :: rest)
    (named : kind = .atom name ∨ kind = .quotedAtom name)
    (notApplied : ∀ paren tail, rest = paren :: tail → paren.kind ≠ .punctuation .leftParen) :
    parsePrimaryAux chr (fuel + 1) chr.operators state =
      .ok ⟨SourceSignature.atom name, 0, { state with remaining := rest }⟩ := by
  conv_lhs => unfold parsePrimaryAux
  rw [remaining]
  rcases named with rfl | rfl
  all_goals
    simp only
    cases rest with
    | nil => rfl
    | cons paren tail =>
      rcases paren with ⟨parenKind, parenSpan⟩
      have := notApplied ⟨parenKind, parenSpan⟩ tail rfl
      simp only at this
      split
      · rename_i same
        cases same
        exact absurd rfl this
      · rfl

theorem primary_applied (fuel : Nat) (state : State) (kind : Kind) (span : ReaderLexer.Span) (name : String)
    (paren : Token) (rest : List Token) (remaining : state.remaining = ⟨kind, span⟩ :: paren :: rest)
    (named : kind = .atom name ∨ kind = .quotedAtom name) (opens : paren.kind = .punctuation .leftParen)
    (touches : adjacent ⟨kind, span⟩ paren = true) :
    parsePrimaryAux chr (fuel + 1) chr.operators state =
      parseApplicationAux chr fuel chr.operators name { state with remaining := rest } := by
  conv_lhs => unfold parsePrimaryAux
  rw [remaining]
  rcases paren with ⟨parenKind, parenSpan⟩
  simp only at opens
  subst opens
  rcases named with rfl | rfl <;> simp [touches]

theorem primary_number (fuel : Nat) (state : State) (span : ReaderLexer.Span) (lexeme : String)
    (rest : List Token) (constant : SourceSignature.Constant)
    (remaining : state.remaining = ⟨.number lexeme, span⟩ :: rest)
    (allowed : chr.numericAllowed lexeme = true) (parsed : ReaderNumber.parse lexeme = .ok constant) :
    parsePrimaryAux chr (fuel + 1) chr.operators state =
      .ok ⟨.const constant, 0, { state with remaining := rest }⟩ := by
  conv_lhs => unfold parsePrimaryAux
  rw [remaining]
  simp [allowed, parsed]

theorem application_empty (fuel : Nat) (state : State) (name : String) (span : ReaderLexer.Span)
    (rest : List Token) (remaining : state.remaining = ⟨.punctuation .rightParen, span⟩ :: rest) :
    parseApplicationAux chr fuel chr.operators name state =
      .ok ⟨SourceSignature.compound name [], 0, { state with remaining := rest }⟩ := by
  unfold parseApplicationAux
  rw [remaining]
  rfl

theorem application_arguments (fuel : Nat) (state : State) (name : String)
    (notClosed : ∀ token tail, state.remaining = token :: tail → token.kind ≠ .punctuation .rightParen) :
    parseApplicationAux chr fuel chr.operators name state = (do
      let (arguments, afterArguments) ← parseArgumentsAux chr fuel chr.operators state
      let after ← consumePunctuation .rightParen afterArguments
      pure { term := SourceSignature.compound name arguments, precedence := 0, state := after }) := by
  unfold parseApplicationAux
  split
  · rename_i rest same
    exact absurd rfl (notClosed _ rest same)
  · rfl

theorem consume_close (state : State) (span : ReaderLexer.Span) (rest : List Token)
    (remaining : state.remaining = ⟨.punctuation .rightParen, span⟩ :: rest) :
    consumePunctuation .rightParen state = .ok { state with remaining := rest } := by
  unfold consumePunctuation
  rw [remaining]
  simp

theorem infixes_comma : infixes chr.operators "," = [⟨",", ⟨1000, by decide, by decide⟩, .xfy⟩] := by
  decide

theorem comma_stops (precedence : Nat) :
    firstEligibleInfix chr.operators "," 999 precedence = none := by
  simp [firstEligibleInfix, infixes_comma, eligible]



/-! ## Lexeme kinds -/

theorem tokensOf_kind (lexeme : Lexeme) (kind : Kind) (found : lexeme.kind? = some kind) (rest : List Lexeme)
    (position : Position) :
    tokensOf (lexeme :: rest) position =
      ⟨kind, ⟨position, position.advanceMany lexeme.chars⟩⟩ :: tokensOf rest (position.advanceMany lexeme.chars) := by
  simp [tokensOf, found]

theorem tokensOf_nil (position : Position) : tokensOf [] position = [] := rfl

theorem tokensOf_layout (character : Char) (rest : List Lexeme) (position : Position) :
    tokensOf (.layout character :: rest) position = tokensOf rest (position.advanceMany [character]) := by
  simp [tokensOf, Lexeme.kind?, Lexeme.chars]

theorem quoted_kind (name : String) : (quoted name).kind? = some (.quotedAtom name) := by
  simp [quoted, Lexeme.kind?]

theorem bare_kind (text : String) (first : Char) (more : List Char) (spelled : text.toList = first :: more)
    (notUpper : first.isUpper = false) (notUnderscore : first ≠ '_') : (bare text).kind? = some (.atom text) := by
  have same : String.ofList (first :: more) = text := by rw [← spelled, String.ofList_toList]
  unfold bare
  rw [spelled]
  simp only
  split <;> simp [Lexeme.kind?, notUpper, notUnderscore, same]

theorem numeral_kind (number : Nat) : (numeral number).kind? = some (.number (toString number)) := by
  unfold numeral
  have listed : (toString number).toList = Nat.toDigits 10 number := Nat.toList_repr
  cases digits : (toString number).toList with
  | nil => rw [listed] at digits; exact absurd digits Nat.toDigits_ne_nil
  | cons first more =>
    simp only [Lexeme.kind?, Option.some.injEq, Kind.number.injEq]
    rw [← digits, String.ofList_toList]

theorem indexed_kind (index : Nat) :
    (indexed index).kind? = some (.variable (CHRPrologReadback.variableName index)) := by
  simp [indexed, Lexeme.kind?, CHRPrologReadback.variableName]
  rfl

theorem comma_kind : comma.kind? = some (.punctuation .comma) := rfl
theorem openParen_kind : openParen.kind? = some (.punctuation .leftParen) := rfl
theorem closeParen_kind : closeParen.kind? = some (.punctuation .rightParen) := rfl
theorem bar_kind : bar.kind? = some (.punctuation .bar) := rfl

theorem tuple_kind : (bare "tuple").kind? = some (.atom "tuple") := bare_kind "tuple" 't' "uple".toList rfl rfl (by decide)
theorem minus_kind : (bare "-").kind? = some (.atom "-") := bare_kind "-" '-' [] rfl rfl (by decide)

/-- Two consecutive tokens of a lexeme sequence touch. -/
theorem touching (first second : Kind) (start middle stop : Position) :
    adjacent ⟨first, ⟨start, middle⟩⟩ ⟨second, ⟨middle, stop⟩⟩ = true := by
  simp [adjacent]

/-! ## Values -/

mutual
  def valueLexemes : CHR.Value → List Lexeme
    | .integer number => integer number
    | .atom name => [quoted name]
    | .tuple fields => [bare "tuple", openParen] ++ separated (valuesLexemes fields) ++ [closeParen]
  def valuesLexemes : List CHR.Value → List (List Lexeme)
    | [] => []
    | first :: rest => valueLexemes first :: valuesLexemes rest
end

theorem integer_tokens_nonneg (number : Int) (sign : 0 ≤ number) (position : Position) :
    tokensOf (integer number) position =
      [⟨.number (toString number.toNat), ⟨position, position.advanceMany (numeral number.toNat).chars⟩⟩] := by
  rw [integer, if_pos sign, tokensOf_kind _ _ (numeral_kind _)]
  rfl

theorem integer_tokens_neg (number : Int) (sign : number < 0) (position : Position) :
    tokensOf (integer number) position =
      [⟨.atom "-", ⟨position, position.advanceMany (bare "-").chars⟩⟩,
        ⟨.number (toString number.natAbs), ⟨position.advanceMany (bare "-").chars,
          (position.advanceMany (bare "-").chars).advanceMany (numeral number.natAbs).chars⟩⟩] := by
  rw [integer, if_neg (by omega), tokensOf_kind _ _ minus_kind, tokensOf_kind _ _ (numeral_kind _)]
  rfl

/-- The position after a separating comma and space. -/
def afterComma (position : Position) : Position := (position.advanceMany comma.chars).advanceMany [' ']

theorem tokensOf_separated_cons (first second : List Lexeme) (more : List (List Lexeme)) (position : Position) :
    tokensOf (separated (first :: second :: more)) position =
      tokensOf first position ++
        ⟨.punctuation .comma, ⟨position.advanceMany (first.flatMap Lexeme.chars),
          (position.advanceMany (first.flatMap Lexeme.chars)).advanceMany comma.chars⟩⟩ ::
        tokensOf (separated (second :: more)) (afterComma (position.advanceMany (first.flatMap Lexeme.chars))) := by
  rw [separated, List.append_assoc, tokensOf_append, List.cons_append, tokensOf_kind _ _ comma_kind,
    space, List.cons_append, List.nil_append, tokensOf_layout]
  rfl

theorem tokensOf_separated_single (single : List Lexeme) (position : Position) :
    tokensOf (separated [single]) position = tokensOf single position := by
  rw [separated]

mutual
  theorem value_first : ∀ (datum : CHR.Value) (position : Position),
      ∃ token tail, tokensOf (valueLexemes datum) position = token :: tail ∧
        token.kind ≠ .punctuation .rightParen ∧ token.kind ≠ .punctuation .comma
    | .integer number, position => by
      by_cases sign : 0 ≤ number
      · exact ⟨_, _, by rw [valueLexemes, integer_tokens_nonneg number sign], by simp, by simp⟩
      · exact ⟨_, _, by rw [valueLexemes, integer_tokens_neg number (by omega)], by simp, by simp⟩
    | .atom name, position => ⟨_, _, by rw [valueLexemes, tokensOf_kind _ _ (quoted_kind name)], by simp, by simp⟩
    | .tuple fields, position => ⟨_, _, by rw [valueLexemes, List.append_assoc, List.cons_append,
        tokensOf_kind _ _ tuple_kind], by simp, by simp⟩
  theorem values_first : ∀ (data : List CHR.Value) (position : Position), data ≠ [] →
      ∃ token tail, tokensOf (separated (valuesLexemes data)) position = token :: tail ∧
        token.kind ≠ .punctuation .rightParen
    | [], _, nonempty => absurd rfl nonempty
    | [single], position, _ => by
      obtain ⟨token, tail, listed, notClose, _⟩ := value_first single position
      exact ⟨token, tail, by rw [valuesLexemes, valuesLexemes, tokensOf_separated_single, listed], notClose⟩
    | first :: second :: more, position, _ => by
      obtain ⟨token, tail, firstListed, notClose, _⟩ := value_first first position
      rw [valuesLexemes, valuesLexemes, tokensOf_separated_cons, firstListed, List.cons_append]
      exact ⟨token, _, rfl, notClose⟩
end

/-! ## Reading values -/

open CHRPrologReadback (valueSource valuesSource)

/-- No opening parenthesis follows. -/
def NoParen (rest : List Token) : Prop := ∀ paren tail, rest = paren :: tail → paren.kind ≠ .punctuation .leftParen

theorem numeric_allowed (lexeme : String) : chr.numericAllowed lexeme = true := by
  simp [ReaderProfile.Profile.numericAllowed, chr, CHRPrologSyntax.profile, ReaderProfile.swi]

theorem expression_primary (fuel maximum : Nat) (state : State) (left : Parsed)
    (primary : parsePrefixOrPrimaryAux chr fuel chr.operators maximum state = .ok left) :
    parseExpressionAux chr (fuel + 1) chr.operators maximum state = parseTailAux chr fuel chr.operators maximum left := by
  rw [expression_step, primary]
  rfl

theorem tail_argument_stops (fuel : Nat) (left : Parsed) (token : Token) (rest : List Token)
    (remaining : left.state.remaining = token :: rest)
    (stopper : token.kind = .punctuation .comma ∨ token.kind = .punctuation .rightParen) :
    parseTailAux chr (fuel + 1) chr.operators 999 left = .ok left := by
  apply tail_stops fuel 999 left token rest remaining
  intro name named
  rcases stopper with stop | stop <;> rw [stop] at named <;> simp [operatorName?] at named
  subst named
  exact comma_stops _

theorem value_length (datum : CHR.Value) (position : Position) : 1 ≤ (tokensOf (valueLexemes datum) position).length := by
  obtain ⟨token, tail, listed, _, _⟩ := value_first datum position
  rw [listed]
  simp

theorem tuple_tokens (items : List (List Lexeme)) (position : Position) :
    tokensOf ([bare "tuple", openParen] ++ separated items ++ [closeParen]) position =
      ⟨.atom "tuple", ⟨position, position.advanceMany (bare "tuple").chars⟩⟩ ::
        ⟨.punctuation .leftParen, ⟨position.advanceMany (bare "tuple").chars,
          (position.advanceMany (bare "tuple").chars).advanceMany openParen.chars⟩⟩ ::
        (tokensOf (separated items) ((position.advanceMany (bare "tuple").chars).advanceMany openParen.chars) ++
          [⟨.punctuation .rightParen,
            ⟨((position.advanceMany (bare "tuple").chars).advanceMany openParen.chars).advanceMany
                ((separated items).flatMap Lexeme.chars),
              (((position.advanceMany (bare "tuple").chars).advanceMany openParen.chars).advanceMany
                ((separated items).flatMap Lexeme.chars)).advanceMany closeParen.chars⟩⟩]) := by
  rw [List.append_assoc, List.cons_append, tokensOf_kind _ _ tuple_kind, List.cons_append, List.nil_append,
    tokensOf_kind _ _ openParen_kind, tokensOf_append, tokensOf_kind _ _ closeParen_kind]
  rfl

mutual
  theorem value_reads : ∀ (datum : CHR.Value) (fuel maximum : Nat) (state : State) (position : Position)
      (rest : List Token), NoParen rest →
      3 * (tokensOf (valueLexemes datum) position ++ rest).length + 2 ≤ fuel →
      parsePrefixOrPrimaryAux chr fuel chr.operators maximum
          { state with remaining := tokensOf (valueLexemes datum) position ++ rest } =
        .ok ⟨valueSource datum, 0, { state with remaining := rest }⟩
    | .integer number, fuel, maximum, state, position, rest, noParen, enough => by
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      by_cases sign : 0 ≤ number
      · rw [valueLexemes, integer_tokens_nonneg number sign, List.cons_append, List.nil_append,
          prefix_other fuel maximum _ _ rest rfl (by simp) (by simp)]
        obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by
          rw [valueLexemes, integer_tokens_nonneg number sign] at enough; simp at enough; omega⟩
        rw [primary_number fuel _ _ _ rest _ rfl (numeric_allowed _) (parse_toString _)]
        simp only [valueSource, SourceSignature.integer, Int.toNat_of_nonneg sign]
      · rw [valueLexemes, integer_tokens_neg number (by omega), List.cons_append, List.cons_append, List.nil_append,
          prefix_negative fuel maximum _ _ _ _ rest number.natAbs rfl (touching _ _ _ _ _) (numeric_allowed _)
            (parse_toString _)]
        have value : -(number.natAbs : Int) = number := by omega
        simp only [valueSource, SourceSignature.integer, value]
    | .atom name, fuel, maximum, state, position, rest, noParen, enough => by
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      rw [valueLexemes, tokensOf_kind _ _ (quoted_kind name), tokensOf_nil, List.cons_append, List.nil_append,
        prefix_quoted fuel maximum _ name _ rest rfl]
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      rw [primary_word fuel _ _ _ name rest rfl (.inr rfl) noParen]
      rfl
    | .tuple fields, fuel, maximum, state, position, rest, noParen, enough => by
      rw [valueLexemes, tuple_tokens] at enough ⊢
      simp only [List.cons_append] at enough ⊢
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      rw [prefix_applied fuel maximum _ "tuple" _ _ _ rfl rfl (touching _ _ _ _ _)]
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [primary_applied fuel _ _ _ "tuple" _ _ rfl (.inl rfl) rfl (touching _ _ _ _ _)]
      by_cases empty : fields = []
      · subst empty
        simp only [valuesLexemes, separated, tokensOf, List.nil_append]
        rw [application_empty fuel _ "tuple" _ rest rfl]
        rfl
      · obtain ⟨first, tail, listed, notClose⟩ := values_first fields
          ((position.advanceMany (bare "tuple").chars).advanceMany openParen.chars) empty
        rw [application_arguments fuel _ "tuple" (by
          intro token more same
          rw [listed, List.cons_append, List.cons_append, List.cons.injEq] at same
          rw [← same.1]
          exact notClose)]
        rw [List.append_assoc, List.singleton_append,
          values_read fields fuel state _ _ rest empty (by simp at enough ⊢; omega)]
        simp only [bind, Except.bind]
        rw [consume_close _ _ rest rfl]
        rfl
  theorem values_read : ∀ (data : List CHR.Value) (fuel : Nat) (state : State) (position : Position)
      (closing : ReaderLexer.Span) (rest : List Token), data ≠ [] →
      3 * (tokensOf (separated (valuesLexemes data)) position ++
        ⟨.punctuation .rightParen, closing⟩ :: rest).length + 4 ≤ fuel →
      parseArgumentsAux chr fuel chr.operators
          { state with remaining := tokensOf (separated (valuesLexemes data)) position ++
            ⟨.punctuation .rightParen, closing⟩ :: rest } =
        .ok (valuesSource data, { state with remaining := ⟨.punctuation .rightParen, closing⟩ :: rest })
    | [], _, _, _, _, _, nonempty, _ => absurd rfl nonempty
    | [single], fuel, state, position, closing, rest, _, enough => by
      rw [valuesLexemes, valuesLexemes, tokensOf_separated_single] at enough ⊢
      have long := value_length single position
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      conv_lhs => unfold parseArgumentsAux
      simp only
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [expression_primary fuel 999 _ _ (value_reads single fuel 999 state position _
        (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega))]
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [tail_argument_stops fuel _ _ rest rfl (.inr rfl)]
      rfl
    | first :: second :: more, fuel, state, position, closing, rest, _, enough => by
      rw [valuesLexemes, valuesLexemes, tokensOf_separated_cons] at enough ⊢
      have long := value_length first position
      have longer := value_length second (afterComma (position.advanceMany ((valueLexemes first).flatMap Lexeme.chars)))
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      conv_lhs => unfold parseArgumentsAux
      simp only
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [List.append_assoc, expression_primary fuel 999 _ _ (value_reads first fuel 999 state position _
        (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega))]
      obtain ⟨tailFuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [tail_argument_stops tailFuel _ _ _ rfl (.inl rfl)]
      simp only [bind, Except.bind]
      rw [List.cons_append]
      simp only
      rw [show valueLexemes second :: valuesLexemes more = valuesLexemes (second :: more) from rfl,
        values_read (second :: more) (tailFuel + 1 + 1) state _ closing rest (by simp)
          (by simp only [valuesLexemes, List.length_append, List.length_cons] at enough ⊢; omega)]
      rfl
end

#print axioms value_reads

/-! ## Variables -/

open CHRPrologReadback (termSource termsSource variableName)

/-- Add an index to an order of first occurrences. -/
def orderStep (order : List Nat) (index : Nat) : List Nat := if index ∈ order then order else order ++ [index]

/-- Variable indices in order of first occurrence. -/
def firstOrder (indices : List Nat) : List Nat := indices.foldl orderStep []

theorem firstOrder_snoc (indices : List Nat) (index : Nat) :
    firstOrder (indices ++ [index]) = orderStep (firstOrder indices) index := by
  simp [firstOrder, List.foldl_append]

theorem foldl_orderStep_prefix : ∀ (indices order : List Nat), order <+: indices.foldl orderStep order
  | [], _ => List.prefix_refl _
  | index :: more, order => by
    refine List.IsPrefix.trans ?_ (foldl_orderStep_prefix more (orderStep order index))
    unfold orderStep
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

theorem firstOrder_prefix {first all : List Nat} (prefixed : first <+: all) : firstOrder first <+: firstOrder all := by
  obtain ⟨more, rfl⟩ := prefixed
  rw [firstOrder, firstOrder, List.foldl_append]
  exact foldl_orderStep_prefix more _

theorem mem_orderStep (order : List Nat) (index other : Nat) :
    other ∈ orderStep order index ↔ other ∈ order ∨ other = index := by
  unfold orderStep
  split
  · rename_i inside
    constructor
    · exact .inl
    · rintro (member | rfl)
      · exact member
      · exact inside
  · simp

theorem mem_firstOrder (indices : List Nat) (index : Nat) : index ∈ firstOrder indices ↔ index ∈ indices := by
  induction indices using List.reverseRecOn with
  | nil => simp [firstOrder]
  | append_singleton more last ih =>
    rw [firstOrder_snoc, mem_orderStep, ih]
    simp

theorem idxOf_firstOrder {first all : List Nat} (prefixed : first <+: all) {index : Nat} (inside : index ∈ first) :
    (firstOrder first).idxOf index = (firstOrder all).idxOf index := by
  obtain ⟨more, same⟩ := firstOrder_prefix prefixed
  rw [← same, List.idxOf_append_of_mem ((mem_firstOrder first index).mpr inside)]

theorem variableName_injective {first second : Nat} (same : variableName first = variableName second) :
    first = second := by
  unfold variableName at same
  have lists := congrArg String.toList same
  simp only [String.toList_append] at lists
  have spelled : toString first = toString second := String.toList_inj.mp (List.append_cancel_left lists)
  have parsed := congrArg String.toNat? spelled
  have one : (toString first).toNat? = some first := Nat.toNat?_repr first
  have two : (toString second).toNat? = some second := Nat.toNat?_repr second
  rw [one, two] at parsed
  exact Option.some.inj parsed

/-- The binding the reader keeps for a variable. -/
def binding (order : List Nat) (index : Nat) : ReaderTerm.VariableBinding :=
  ⟨variableName index, ⟨variableName index, order.idxOf index⟩⟩

/-- The reader's state after reading the variable occurrences `seen`. -/
def readerState (remaining : List Token) (seen : List Nat) : State :=
  { remaining, bindings := ((firstOrder seen).map (binding (firstOrder seen))).reverse,
    nextOccurrence := (firstOrder seen).length }

/-- The variable a whole sentence with variable occurrences `all` gives an index. -/
def nameIn (all : List Nat) (index : Nat) : SourceSignature.Variable :=
  ⟨variableName index, (firstOrder all).idxOf index⟩

theorem find_binding (order key : List Nat) (index : Nat) :
    ((order.map (binding key)).reverse.find? fun entry => entry.spelling = variableName index) =
      if index ∈ order then some (binding key index) else none := by
  split
  · rename_i inside
    have witness : ∃ entry ∈ (order.map (binding key)).reverse, (fun entry : ReaderTerm.VariableBinding =>
        decide (entry.spelling = variableName index)) entry = true :=
      ⟨binding key index, List.mem_reverse.mpr (List.mem_map.mpr ⟨index, inside, rfl⟩), by simp [binding]⟩
    obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr witness)
    have member := List.mem_of_find?_eq_some found
    have holds := List.find?_some found
    simp only [List.mem_reverse, List.mem_map] at member
    obtain ⟨other, _, rfl⟩ := member
    simp only [binding] at holds
    rw [found, variableName_injective (of_decide_eq_true holds)]
  · rename_i outside
    rw [List.find?_eq_none]
    intro entry member
    simp only [List.mem_reverse, List.mem_map] at member
    obtain ⟨other, inside, rfl⟩ := member
    simp only [binding]
    intro same
    exact outside (variableName_injective (of_decide_eq_true same) ▸ inside)

theorem variableName_not_anonymous (index : Nat) : variableName index ≠ "_" := by
  intro same
  have := congrArg String.toList same
  simp [variableName] at this

theorem map_binding_snoc (order : List Nat) (index : Nat) :
    order.map (binding (order ++ [index])) = order.map (binding order) := by
  apply List.map_congr_left
  intro other inside
  simp [binding, List.idxOf_append_of_mem inside]

/-- Reading a canonical variable name gives the identity of its first occurrence. -/
theorem intern_canonical (rest : List Token) (seen : List Nat) (index : Nat) :
    ReaderTerm.internVariable (variableName index) (readerState rest seen) =
      (⟨variableName index, (firstOrder (seen ++ [index])).idxOf index⟩, readerState rest (seen ++ [index])) := by
  unfold ReaderTerm.internVariable
  rw [if_neg (variableName_not_anonymous index)]
  simp only [readerState]
  rw [find_binding, firstOrder_snoc]
  by_cases inside : index ∈ firstOrder seen
  · simp [inside, orderStep, binding]
  · simp only [inside, if_false, orderStep]
    have outside : index ∉ firstOrder seen := inside
    simp [List.idxOf_append_of_notMem outside, map_binding_snoc, binding]


theorem primary_variable (fuel : Nat) (state : State) (spelling : String) (span : ReaderLexer.Span)
    (rest : List Token) (identity : SourceSignature.Variable) (next : State)
    (remaining : state.remaining = ⟨.variable spelling, span⟩ :: rest)
    (interned : ReaderTerm.internVariable spelling { state with remaining := rest } = (identity, next)) :
    parsePrimaryAux chr (fuel + 1) chr.operators state = .ok ⟨.var identity, 0, next⟩ := by
  conv_lhs => unfold parsePrimaryAux
  rw [remaining]
  simp only
  rw [interned]

theorem readerState_with (rest more : List Token) (seen : List Nat) :
    readerState more seen = { readerState rest seen with remaining := more } := rfl

theorem readerState_remaining (remaining : List Token) (seen : List Nat) :
    (readerState remaining seen).remaining = remaining := rfl

/-! ## Terms -/

mutual
  def termLexemes : CHR.Term → List Lexeme
    | .value datum => valueLexemes datum
    | .var index => [indexed index]
    | .tuple fields => [bare "tuple", openParen] ++ separated (termsLexemes fields) ++ [closeParen]
  def termsLexemes : List CHR.Term → List (List Lexeme)
    | [] => []
    | first :: rest => termLexemes first :: termsLexemes rest
end

mutual
  theorem term_first : ∀ (term : CHR.Term) (position : Position),
      ∃ token tail, tokensOf (termLexemes term) position = token :: tail ∧
        token.kind ≠ .punctuation .rightParen ∧ token.kind ≠ .punctuation .comma
    | .value datum, position => by
      rw [termLexemes]
      exact value_first datum position
    | .var index, position =>
      ⟨_, _, by rw [termLexemes, tokensOf_kind _ _ (indexed_kind index)], by simp, by simp⟩
    | .tuple fields, position => ⟨_, _, by rw [termLexemes, List.append_assoc, List.cons_append,
        tokensOf_kind _ _ tuple_kind], by simp, by simp⟩
  theorem terms_first : ∀ (terms : List CHR.Term) (position : Position), terms ≠ [] →
      ∃ token tail, tokensOf (separated (termsLexemes terms)) position = token :: tail ∧
        token.kind ≠ .punctuation .rightParen
    | [], _, nonempty => absurd rfl nonempty
    | [single], position, _ => by
      obtain ⟨token, tail, listed, notClose, _⟩ := term_first single position
      exact ⟨token, tail, by rw [termsLexemes, termsLexemes, tokensOf_separated_single, listed], notClose⟩
    | first :: second :: more, position, _ => by
      obtain ⟨token, tail, firstListed, notClose, _⟩ := term_first first position
      rw [termsLexemes, termsLexemes, tokensOf_separated_cons, firstListed, List.cons_append]
      exact ⟨token, _, rfl, notClose⟩
end

theorem term_length (term : CHR.Term) (position : Position) : 1 ≤ (tokensOf (termLexemes term) position).length := by
  obtain ⟨token, tail, listed, _, _⟩ := term_first term position
  rw [listed]
  simp

mutual
  theorem term_reads (all : List Nat) : ∀ (term : CHR.Term) (fuel maximum : Nat) (seen : List Nat)
      (position : Position) (rest : List Token), seen ++ term.variables <+: all → NoParen rest →
      3 * (tokensOf (termLexemes term) position ++ rest).length + 2 ≤ fuel →
      parsePrefixOrPrimaryAux chr fuel chr.operators maximum
          (readerState (tokensOf (termLexemes term) position ++ rest) seen) =
        .ok ⟨termSource (nameIn all) term, 0, readerState rest (seen ++ term.variables)⟩
    | .value datum, fuel, maximum, seen, position, rest, _, noParen, enough => by
      rw [termLexemes] at enough ⊢
      rw [readerState_with rest, value_reads datum fuel maximum (readerState rest seen) position rest noParen enough]
      simp only [termSource, CHR.Term.variables, List.append_nil]
      rfl
    | .var index, fuel, maximum, seen, position, rest, prefixed, noParen, enough => by
      rw [termLexemes, tokensOf_kind _ _ (indexed_kind index), tokensOf_nil, List.cons_append,
        List.nil_append] at enough ⊢
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      rw [prefix_other fuel maximum _ _ rest rfl (by simp) (by simp)]
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [primary_variable fuel _ _ _ rest _ _ rfl (intern_canonical rest seen index)]
      simp only [CHR.Term.variables] at prefixed ⊢
      simp only [termSource, nameIn, idxOf_firstOrder (index := index) prefixed (by simp)]
    | .tuple fields, fuel, maximum, seen, position, rest, prefixed, noParen, enough => by
      rw [termLexemes, tuple_tokens] at enough ⊢
      simp only [List.cons_append] at enough ⊢
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      rw [prefix_applied fuel maximum _ "tuple" _ _ _ rfl rfl (touching _ _ _ _ _)]
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [primary_applied fuel _ _ _ "tuple" _ _ rfl (.inl rfl) rfl (touching _ _ _ _ _)]
      by_cases empty : fields = []
      · subst empty
        simp only [termsLexemes, separated, tokensOf, List.nil_append]
        rw [application_empty fuel _ "tuple" _ rest rfl]
        simp only [termSource, termsSource, CHR.Term.variables, List.flatMap_nil, List.append_nil]
        rfl
      · obtain ⟨first, tail, listed, notClose⟩ := terms_first fields
          ((position.advanceMany (bare "tuple").chars).advanceMany openParen.chars) empty
        rw [application_arguments fuel _ "tuple" (by
          intro token more same
          rw [listed, List.cons_append, List.cons_append, List.cons.injEq] at same
          rw [← same.1]
          exact notClose)]
        simp only [CHR.Term.variables] at prefixed ⊢
        rw [List.append_assoc, List.singleton_append]
        erw [terms_read all fields fuel seen _ _ rest empty prefixed (by simp at enough ⊢; omega)]
        simp only [bind, Except.bind]
        rw [consume_close _ _ rest rfl]
        rfl
  theorem terms_read (all : List Nat) : ∀ (terms : List CHR.Term) (fuel : Nat) (seen : List Nat)
      (position : Position) (closing : ReaderLexer.Span) (rest : List Token), terms ≠ [] →
      seen ++ terms.flatMap CHR.Term.variables <+: all →
      3 * (tokensOf (separated (termsLexemes terms)) position ++
        ⟨.punctuation .rightParen, closing⟩ :: rest).length + 4 ≤ fuel →
      parseArgumentsAux chr fuel chr.operators
          (readerState (tokensOf (separated (termsLexemes terms)) position ++
            ⟨.punctuation .rightParen, closing⟩ :: rest) seen) =
        .ok (termsSource (nameIn all) terms,
          readerState (⟨.punctuation .rightParen, closing⟩ :: rest) (seen ++ terms.flatMap CHR.Term.variables))
    | [], _, _, _, _, _, nonempty, _, _ => absurd rfl nonempty
    | [single], fuel, seen, position, closing, rest, _, prefixed, enough => by
      rw [termsLexemes, termsLexemes, tokensOf_separated_single] at enough ⊢
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at prefixed ⊢
      have long := term_length single position
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      conv_lhs => unfold parseArgumentsAux
      simp only
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [expression_primary fuel 999 _ _ (term_reads all single fuel 999 seen position _ prefixed
        (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega))]
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [tail_argument_stops fuel _ _ rest rfl (.inr rfl)]
      rfl
    | first :: second :: more, fuel, seen, position, closing, rest, _, prefixed, enough => by
      rw [termsLexemes, termsLexemes, tokensOf_separated_cons] at enough ⊢
      have long := term_length first position
      have longer := term_length second (afterComma (position.advanceMany ((termLexemes first).flatMap Lexeme.chars)))
      have firstPrefixed : seen ++ first.variables <+: all :=
        List.IsPrefix.trans (by simp [List.flatMap_cons]) prefixed
      have restPrefixed : (seen ++ first.variables) ++ (second :: more).flatMap CHR.Term.variables <+: all := by
        simpa [List.flatMap_cons, List.append_assoc] using prefixed
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
      conv_lhs => unfold parseArgumentsAux
      simp only
      obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [List.append_assoc, expression_primary fuel 999 _ _ (term_reads all first fuel 999 seen position _
        firstPrefixed (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega))]
      obtain ⟨tailFuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rw [tail_argument_stops tailFuel _ _ _ rfl (.inl rfl)]
      simp only [bind, Except.bind]
      rw [List.cons_append]
      simp only [readerState_remaining]
      rw [show termLexemes second :: termsLexemes more = termsLexemes (second :: more) from rfl]
      erw [terms_read all (second :: more) (tailFuel + 1 + 1) (seen ++ first.variables) _ closing rest (by simp)
          restPrefixed (by simp only [termsLexemes, List.length_append, List.length_cons] at enough ⊢; omega)]
      simp only [List.flatMap_cons, List.append_assoc, termsSource]
      rfl
end

#print axioms term_reads

theorem applied_tokens (lexeme : Lexeme) (kind : Kind) (found : lexeme.kind? = some kind)
    (items : List (List Lexeme)) (position : Position) :
    tokensOf ([lexeme, openParen] ++ separated items ++ [closeParen]) position =
      ⟨kind, ⟨position, position.advanceMany lexeme.chars⟩⟩ ::
        ⟨.punctuation .leftParen, ⟨position.advanceMany lexeme.chars,
          (position.advanceMany lexeme.chars).advanceMany openParen.chars⟩⟩ ::
        (tokensOf (separated items) ((position.advanceMany lexeme.chars).advanceMany openParen.chars) ++
          [⟨.punctuation .rightParen,
            ⟨((position.advanceMany lexeme.chars).advanceMany openParen.chars).advanceMany
                ((separated items).flatMap Lexeme.chars),
              (((position.advanceMany lexeme.chars).advanceMany openParen.chars).advanceMany
                ((separated items).flatMap Lexeme.chars)).advanceMany closeParen.chars⟩⟩]) := by
  rw [List.append_assoc, List.cons_append, tokensOf_kind _ _ found, List.cons_append, List.nil_append,
    tokensOf_kind _ _ openParen_kind, tokensOf_append, tokensOf_kind _ _ closeParen_kind]
  rfl

/-! ## Heads -/

open CHRPrologReadback (headSource expressionSource operatorName comparisonName)

def headLexemes (head : CHR.Head) : List Lexeme :=
  [quoted head.name] ++
    if head.arguments.isEmpty then [] else [openParen] ++ separated (termsLexemes head.arguments) ++ [closeParen]

theorem head_reads (all : List Nat) (head : CHR.Head) (fuel maximum : Nat) (seen : List Nat) (position : Position)
    (rest : List Token) (prefixed : seen ++ head.variables <+: all) (noParen : NoParen rest)
    (enough : 3 * (tokensOf (headLexemes head) position ++ rest).length + 2 ≤ fuel) :
    parsePrefixOrPrimaryAux chr fuel chr.operators maximum
        (readerState (tokensOf (headLexemes head) position ++ rest) seen) =
      .ok ⟨headSource (nameIn all) head, 0, readerState rest (seen ++ head.variables)⟩ := by
  unfold headLexemes at enough ⊢
  by_cases empty : head.arguments.isEmpty
  · have none : head.arguments = [] := List.isEmpty_iff.mp empty
    simp only [empty, if_true, List.append_nil, tokensOf_kind _ _ (quoted_kind head.name), tokensOf_nil,
      List.cons_append, List.nil_append] at enough ⊢
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    rw [prefix_quoted fuel maximum _ head.name _ rest rfl]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [primary_word fuel _ _ _ head.name rest rfl (.inr rfl) noParen]
    simp only [headSource, CHR.Head.variables, none, List.flatMap_nil, List.append_nil]
    rfl
  · have nonempty : head.arguments ≠ [] := by simpa using empty
    have shape : ([quoted head.name] ++ if head.arguments.isEmpty then []
        else [openParen] ++ separated (termsLexemes head.arguments) ++ [closeParen]) =
        [quoted head.name, openParen] ++ separated (termsLexemes head.arguments) ++ [closeParen] := by
      simp [empty]
    rw [shape, applied_tokens _ _ (quoted_kind head.name)] at enough ⊢
    simp only [List.cons_append] at enough ⊢
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    rw [prefix_quoted fuel maximum _ head.name _ _ rfl]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [primary_applied fuel _ _ _ head.name _ _ rfl (.inr rfl) rfl (touching _ _ _ _ _)]
    obtain ⟨first, tail, listed, notClose⟩ := terms_first head.arguments
      ((position.advanceMany (quoted head.name).chars).advanceMany openParen.chars) nonempty
    rw [application_arguments fuel _ head.name (by
      intro token more same
      rw [listed, List.cons_append, List.cons_append, List.cons.injEq] at same
      rw [← same.1]
      exact notClose)]
    rw [List.append_assoc, List.singleton_append]
    erw [terms_read all head.arguments fuel seen _ _ rest nonempty prefixed (by simp at enough ⊢; omega)]
    simp only [bind, Except.bind]
    rw [consume_close _ _ rest rfl]
    simp only [headSource, empty, if_false, Bool.false_eq_true, CHR.Head.variables]
    rfl

/-! ## Arithmetic -/

def expressionLexemes : CHR.IntExpr → List Lexeme
  | .literal number => integer number
  | .index index => [indexed index]
  | .operation operator left right =>
    [openParen] ++ expressionLexemes left ++ [space, bare (operatorName operator), space] ++
      expressionLexemes right ++ [closeParen]

theorem operator_kind (operator : CHR.IntOperator) :
    (bare (operatorName operator)).kind? = some (.atom (operatorName operator)) := by
  cases operator
  · exact bare_kind "+" '+' [] rfl rfl (by decide)
  · exact bare_kind "-" '-' [] rfl rfl (by decide)
  · exact bare_kind "*" '*' [] rfl rfl (by decide)
  · exact bare_kind "//" '/' ['/'] rfl rfl (by decide)
  · exact bare_kind "rem" 'r' ['e', 'm'] rfl rfl (by decide)
  · exact bare_kind "mod" 'm' ['o', 'd'] rfl rfl (by decide)

/-- The priority of an arithmetic operator. -/
def operatorPriority : CHR.IntOperator → Priority
  | .add | .subtract => ⟨500, by decide, by decide⟩
  | .multiply | .quotient | .remainder | .modulo => ⟨400, by decide, by decide⟩

theorem infixes_operator (operator : CHR.IntOperator) :
    infixes chr.operators (operatorName operator) = [⟨operatorName operator, operatorPriority operator, .yfx⟩] := by
  cases operator <;> decide

theorem operator_continues (operator : CHR.IntOperator) :
    firstEligibleInfix chr.operators (operatorName operator) 1200 0 =
      some ⟨operatorName operator, operatorPriority operator, .yfx⟩ := by
  rw [firstEligibleInfix, infixes_operator]
  cases operator <;> rfl

theorem primary_paren (fuel : Nat) (state : State) (span : ReaderLexer.Span) (rest : List Token)
    (remaining : state.remaining = ⟨.punctuation .leftParen, span⟩ :: rest) :
    parsePrimaryAux chr (fuel + 1) chr.operators state = (do
      let nested ← parseExpressionAux chr fuel chr.operators 1200 { state with remaining := rest }
      let after ← consumePunctuation .rightParen nested.state
      pure { term := nested.term, precedence := 0, state := after }) := by
  conv_lhs => unfold parsePrimaryAux
  rw [remaining]

theorem tail_closes (fuel maximum : Nat) (left : Parsed) (span : ReaderLexer.Span) (rest : List Token)
    (remaining : left.state.remaining = ⟨.punctuation .rightParen, span⟩ :: rest) :
    parseTailAux chr (fuel + 1) chr.operators maximum left = .ok left :=
  tail_stops fuel maximum left _ rest remaining (by intro name named; simp [operatorName?] at named)

theorem expression_first : ∀ (expression : CHR.IntExpr) (position : Position),
    ∃ token tail, tokensOf (expressionLexemes expression) position = token :: tail ∧
      tokenStartsTerm token.kind = true
  | .literal number, position => by
    by_cases sign : 0 ≤ number
    · exact ⟨_, _, by rw [expressionLexemes, integer_tokens_nonneg number sign], rfl⟩
    · exact ⟨_, _, by rw [expressionLexemes, integer_tokens_neg number (by omega)], rfl⟩
  | .index index, position => ⟨_, _, by rw [expressionLexemes, tokensOf_kind _ _ (indexed_kind index)], rfl⟩
  | .operation operator left right, position =>
    ⟨_, _, by rw [expressionLexemes, List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append,
      tokensOf_kind _ _ openParen_kind], rfl⟩

theorem expression_length (expression : CHR.IntExpr) (position : Position) :
    1 ≤ (tokensOf (expressionLexemes expression) position).length := by
  obtain ⟨token, tail, listed, _⟩ := expression_first expression position
  rw [listed]
  simp

theorem operation_tokens (operator : CHR.IntOperator) (left right : CHR.IntExpr) (position : Position) :
    ∃ openSpan operatorSpan closeSpan afterOpen afterOperator,
      tokensOf (expressionLexemes (.operation operator left right)) position =
        ⟨.punctuation .leftParen, openSpan⟩ :: (tokensOf (expressionLexemes left) afterOpen ++
          ⟨.atom (operatorName operator), operatorSpan⟩ :: (tokensOf (expressionLexemes right) afterOperator ++
            [⟨.punctuation .rightParen, closeSpan⟩])) := by
  rw [expressionLexemes, List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append,
    tokensOf_kind _ _ openParen_kind, tokensOf_append, List.cons_append, space, tokensOf_layout,
    List.cons_append, tokensOf_kind _ _ (operator_kind operator), List.cons_append, List.nil_append,
    tokensOf_layout, tokensOf_append, tokensOf_kind _ _ closeParen_kind, tokensOf_nil]
  exact ⟨_, _, _, _, _, rfl⟩

#print axioms head_reads

theorem expression_reads (all : List Nat) : ∀ (expression : CHR.IntExpr) (fuel maximum : Nat) (seen : List Nat)
    (position : Position) (rest : List Token), seen ++ expression.variables <+: all → NoParen rest →
    3 * (tokensOf (expressionLexemes expression) position ++ rest).length + 2 ≤ fuel →
    parsePrefixOrPrimaryAux chr fuel chr.operators maximum
        (readerState (tokensOf (expressionLexemes expression) position ++ rest) seen) =
      .ok ⟨expressionSource (nameIn all) expression, 0, readerState rest (seen ++ expression.variables)⟩
  | .literal number, fuel, maximum, seen, position, rest, prefixed, noParen, enough => by
    have read := term_reads all (.value (.integer number)) fuel maximum seen position rest
      (by simpa [CHR.Term.variables, CHR.IntExpr.variables] using prefixed) noParen enough
    simp only [CHR.Term.variables, List.append_nil] at read
    simp only [CHR.IntExpr.variables, List.append_nil]
    exact read
  | .index index, fuel, maximum, seen, position, rest, prefixed, noParen, enough => by
    have read := term_reads all (.var index) fuel maximum seen position rest
      (by simpa [CHR.Term.variables, CHR.IntExpr.variables] using prefixed) noParen enough
    simp only [CHR.Term.variables] at read
    simp only [CHR.IntExpr.variables]
    exact read
  | .operation operator left right, fuel, maximum, seen, position, rest, prefixed, noParen, enough => by
    obtain ⟨openSpan, operatorSpan, closeSpan, afterOpen, afterOperator, listed⟩ :=
      operation_tokens operator left right position
    obtain ⟨rightFirst, rightTail, rightListed, rightStarts⟩ := expression_first right afterOperator
    have leftLong := expression_length left afterOpen
    have rightLong := expression_length right afterOperator
    have leftPrefixed : seen ++ left.variables <+: all :=
      List.IsPrefix.trans (by simp [CHR.IntExpr.variables]) prefixed
    have rightPrefixed : (seen ++ left.variables) ++ right.variables <+: all := by
      simpa [CHR.IntExpr.variables, List.append_assoc] using prefixed
    rw [listed] at enough ⊢
    simp only [List.cons_append, List.append_assoc] at enough ⊢
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    rw [prefix_other fuel maximum _ _ _ rfl (by simp) (by simp)]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [primary_paren fuel _ _ _ rfl]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [expression_step]
    erw [expression_reads all left fuel 1200 seen afterOpen _ leftPrefixed
      (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega)]
    simp only [bind, Except.bind]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [rightListed, List.cons_append]
    rw [tail_infix fuel 1200 _ _ rightFirst _ (operatorName operator) _ ((operatorPriority operator).value - 1)
      rfl rfl (operator_continues operator) rfl rightStarts]
    rw [← List.cons_append, ← rightListed]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [expression_step]
    erw [expression_reads all right fuel _ (seen ++ left.variables) afterOperator _ rightPrefixed
      (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega)]
    simp only [bind, Except.bind]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [tail_closes fuel _ _ closeSpan rest rfl]
    simp only
    rw [tail_closes (fuel + 1) _ _ closeSpan rest rfl]
    simp only
    rw [consume_close _ closeSpan rest rfl]
    simp only [expressionSource, CHR.IntExpr.variables, List.append_assoc]
    rfl

#print axioms expression_reads

/-! ## The operator table above the arithmetic -/

theorem infixes_bar : infixes chr.operators "|" = [⟨"|", ⟨1105, by decide, by decide⟩, .xfy⟩] := by decide
theorem infixes_backslash : infixes chr.operators "\\" = [⟨"\\", ⟨1100, by decide, by decide⟩, .xfx⟩] := by decide
theorem infixes_simplify : infixes chr.operators "<=>" = [⟨"<=>", ⟨1180, by decide, by decide⟩, .xfx⟩] := by decide
theorem infixes_propagate : infixes chr.operators "==>" =
    [⟨"==>", ⟨1180, by decide, by decide⟩, .xfx⟩, ⟨"==>", ⟨1200, by decide, by decide⟩, .xfx⟩] := by decide
theorem infixes_named : infixes chr.operators "@" = [⟨"@", ⟨1200, by decide, by decide⟩, .xfx⟩] := by decide
theorem infixes_slash : infixes chr.operators "/" = [⟨"/", ⟨400, by decide, by decide⟩, .yfx⟩] := by decide

/-- A 700-level comparison operator of the profile. -/
abbrev Comparing (name : String) : Prop :=
  infixes chr.operators name = [⟨name, ⟨700, by decide, by decide⟩, .xfx⟩]

theorem comparing_identical : Comparing "==" := by decide
theorem comparing_distinct : Comparing "\\==" := by decide
theorem comparing_is : Comparing "is" := by decide
theorem comparing_comparison (comparison : CHR.Comparison) : Comparing (comparisonName comparison) := by
  cases comparison <;> decide

/-- Tokens that end a conjunction item. -/
def Closes (kind : Kind) : Prop :=
  kind = .punctuation .comma ∨ kind = .punctuation .bar ∨ kind = .punctuation .fullStop ∨
    kind = .atom "\\" ∨ kind = .atom "<=>" ∨ kind = .atom "==>"

theorem closes_noParen {token : Token} {rest : List Token} (closes : Closes token.kind) : NoParen (token :: rest) := by
  intro paren tail same
  cases same
  rcases closes with h | h | h | h | h | h <;> rw [h] <;> simp

/-- The operator loop below 1000 stops before any token that ends an item. -/
theorem tail_closes_low (fuel maximum : Nat) (left : Parsed) (token : Token) (rest : List Token)
    (remaining : left.state.remaining = token :: rest) (closes : Closes token.kind) (low : maximum < 1000) :
    parseTailAux chr (fuel + 1) chr.operators maximum left = .ok left := by
  apply tail_stops fuel maximum left token rest remaining
  intro name named
  rcases closes with h | h | h | h | h | h <;> rw [h] at named <;> simp [operatorName?] at named <;> subst named <;>
    simp [firstEligibleInfix, infixes_comma, infixes_bar, infixes_backslash, infixes_simplify, infixes_propagate,
      eligible] <;> omega

/-- At 1000 the loop stops before any token that ends a conjunction. -/
theorem tail_closes_conjunction (fuel : Nat) (left : Parsed) (token : Token) (rest : List Token)
    (remaining : left.state.remaining = token :: rest) (closes : Closes token.kind)
    (notComma : token.kind ≠ .punctuation .comma) :
    parseTailAux chr (fuel + 1) chr.operators 1000 left = .ok left := by
  apply tail_stops fuel 1000 left token rest remaining
  intro name named
  rcases closes with h | h | h | h | h | h
  · exact absurd h notComma
  · rw [h] at named
    simp only [operatorName?, Option.some.injEq] at named
    subst named
    simp [firstEligibleInfix, infixes_bar, eligible]
  · rw [h] at named
    simp [operatorName?] at named
  · rw [h] at named
    simp only [operatorName?, Option.some.injEq] at named
    subst named
    simp [firstEligibleInfix, infixes_backslash, eligible]
  · rw [h] at named
    simp only [operatorName?, Option.some.injEq] at named
    subst named
    simp [firstEligibleInfix, infixes_simplify, eligible]
  · rw [h] at named
    simp only [operatorName?, Option.some.injEq] at named
    subst named
    simp [firstEligibleInfix, infixes_propagate, eligible]

/-! ## Operands and items -/

/-- A primary that reads back as `source`, recording `variables`. -/
def PrimaryReads (all : List Nat) (lexemes : List Lexeme) (source : SourceSignature.Term) (indices : List Nat) :
    Prop :=
  ∀ (fuel maximum : Nat) (seen : List Nat) (position : Position) (rest : List Token),
    seen ++ indices <+: all → NoParen rest → 3 * (tokensOf lexemes position ++ rest).length + 2 ≤ fuel →
    parsePrefixOrPrimaryAux chr fuel chr.operators maximum (readerState (tokensOf lexemes position ++ rest) seen) =
      .ok ⟨source, 0, readerState rest (seen ++ indices)⟩

/-- Lexemes whose first token starts a term. -/
def StartsTerm (lexemes : List Lexeme) : Prop :=
  ∀ position, ∃ token tail, tokensOf lexemes position = token :: tail ∧ tokenStartsTerm token.kind = true

/-- A conjunction item that reads back as `source`: from a level of at least
`level`, the reader parses the item and returns to the operator loop with it,
`depth` fuel later. -/
def ItemReads (all : List Nat) (level : Nat) (lexemes : List Lexeme) (source : SourceSignature.Term)
    (precedence depth : Nat) (indices : List Nat) : Prop :=
  ∀ (fuel maximum : Nat) (seen : List Nat) (position : Position) (token : Token) (rest : List Token),
    level ≤ maximum → Closes token.kind → seen ++ indices <+: all →
    3 * (tokensOf lexemes position ++ token :: rest).length + 3 ≤ fuel →
    parseExpressionAux chr fuel chr.operators maximum (readerState (tokensOf lexemes position ++ token :: rest) seen) =
      parseTailAux chr (fuel - depth) chr.operators maximum
        ⟨source, precedence, readerState (token :: rest) (seen ++ indices)⟩

theorem primary_item (all : List Nat) (lexemes : List Lexeme) (source : SourceSignature.Term) (indices : List Nat)
    (reads : PrimaryReads all lexemes source indices) : ItemReads all 0 lexemes source 0 1 indices := by
  intro fuel maximum seen position token rest _ closes prefixed enough
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [expression_primary fuel maximum _ _ (reads fuel maximum seen position (token :: rest) prefixed
    (closes_noParen closes) (by omega))]
  rfl

theorem infix_item (all : List Nat) (leftLexemes rightLexemes : List Lexeme)
    (leftSource rightSource : SourceSignature.Term) (leftIndices rightIndices : List Nat) (name : String)
    (leftReads : PrimaryReads all leftLexemes leftSource leftIndices)
    (rightReads : PrimaryReads all rightLexemes rightSource rightIndices)
    (leftLong : ∀ position, 1 ≤ (tokensOf leftLexemes position).length)
    (rightStarts : StartsTerm rightLexemes)
    (named : (bare name).kind? = some (.atom name)) (comparing : Comparing name) :
    ItemReads all 700 (leftLexemes ++ [space, bare name, space] ++ rightLexemes)
      (SourceSignature.compound name [leftSource, rightSource]) 700 2 (leftIndices ++ rightIndices) := by
  intro fuel maximum seen position token rest level closes prefixed enough
  have leftPrefixed : seen ++ leftIndices <+: all := List.IsPrefix.trans (by simp) prefixed
  have rightPrefixed : (seen ++ leftIndices) ++ rightIndices <+: all := by simpa using prefixed
  set afterLeft := position.advanceMany (leftLexemes.flatMap Lexeme.chars)
  set atOperator := afterLeft.advanceMany [' ']
  set afterOperator := (atOperator.advanceMany (bare name).chars).advanceMany [' ']
  obtain ⟨rightFirst, rightTail, rightListed, starts⟩ := rightStarts afterOperator
  have listed : tokensOf (leftLexemes ++ [space, bare name, space] ++ rightLexemes) position =
      tokensOf leftLexemes position ++ ⟨.atom name, ⟨atOperator, atOperator.advanceMany (bare name).chars⟩⟩ ::
        tokensOf rightLexemes afterOperator := by
    rw [List.append_assoc, tokensOf_append, List.cons_append, space, tokensOf_layout, List.cons_append,
      tokensOf_kind _ _ named, List.cons_append, List.nil_append, tokensOf_layout]
  have longLeft := leftLong position
  have longRight : 1 ≤ (tokensOf rightLexemes afterOperator).length := by rw [rightListed]; simp
  rw [listed] at enough ⊢
  simp only [List.append_assoc, List.cons_append] at enough ⊢
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [expression_primary fuel maximum _ _ (leftReads fuel maximum seen position _ leftPrefixed
    (by intro paren tail same; cases same; simp) (by simp at enough ⊢; omega))]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  have found : firstEligibleInfix chr.operators name maximum 0 = some ⟨name, ⟨700, by decide, by decide⟩, .xfx⟩ := by
    simp only [firstEligibleInfix, comparing]
    simp [eligible]
    exact ⟨level, rfl⟩
  rw [rightListed, List.cons_append]
  rw [tail_infix fuel maximum _ _ rightFirst _ name _ 699 rfl rfl found rfl starts]
  rw [← List.cons_append, ← rightListed]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  erw [expression_primary fuel 699 _ _ (rightReads fuel 699 (seen ++ leftIndices) afterOperator _ rightPrefixed
    (closes_noParen closes) (by simp at enough ⊢; omega))]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  rw [tail_closes_low fuel 699 _ token rest rfl closes (by decide)]
  simp only [bind, Except.bind, List.append_assoc]
  rfl

#print axioms infix_item

theorem ItemReads.mono {all : List Nat} {level higher : Nat} {lexemes : List Lexeme} {source : SourceSignature.Term}
    {precedence depth : Nat} {indices : List Nat} (reads : ItemReads all level lexemes source precedence depth indices)
    (raised : level ≤ higher) : ItemReads all higher lexemes source precedence depth indices :=
  fun fuel maximum seen position token rest above closes prefixed enough =>
    reads fuel maximum seen position token rest (by omega) closes prefixed enough

/-! ## Guards and goals -/

open CHRPrologReadback (guardSource goalSource goalVariables conjunctionSource)

theorem term_starts (term : CHR.Term) : StartsTerm (termLexemes term) := by
  intro position
  match term with
  | .value (.integer number) =>
    by_cases sign : 0 ≤ number
    · exact ⟨_, _, by rw [termLexemes, valueLexemes, integer_tokens_nonneg number sign], rfl⟩
    · exact ⟨_, _, by rw [termLexemes, valueLexemes, integer_tokens_neg number (by omega)], rfl⟩
  | .value (.atom name) => exact ⟨_, _, by rw [termLexemes, valueLexemes, tokensOf_kind _ _ (quoted_kind name)], rfl⟩
  | .value (.tuple fields) =>
    exact ⟨_, _, by rw [termLexemes, valueLexemes, List.append_assoc, List.cons_append, tokensOf_kind _ _ tuple_kind],
      rfl⟩
  | .var index => exact ⟨_, _, by rw [termLexemes, tokensOf_kind _ _ (indexed_kind index)], rfl⟩
  | .tuple fields =>
    exact ⟨_, _, by rw [termLexemes, List.append_assoc, List.cons_append, tokensOf_kind _ _ tuple_kind], rfl⟩

theorem expression_starts (expression : CHR.IntExpr) : StartsTerm (expressionLexemes expression) :=
  expression_first expression

theorem term_primary (all : List Nat) (term : CHR.Term) :
    PrimaryReads all (termLexemes term) (termSource (nameIn all) term) term.variables :=
  fun fuel maximum seen position rest prefixed noParen enough =>
    term_reads all term fuel maximum seen position rest prefixed noParen enough

theorem expression_primary_reads (all : List Nat) (expression : CHR.IntExpr) :
    PrimaryReads all (expressionLexemes expression) (expressionSource (nameIn all) expression) expression.variables :=
  fun fuel maximum seen position rest prefixed noParen enough =>
    expression_reads all expression fuel maximum seen position rest prefixed noParen enough

theorem head_primary (all : List Nat) (head : CHR.Head) :
    PrimaryReads all (headLexemes head) (headSource (nameIn all) head) head.variables :=
  fun fuel maximum seen position rest prefixed noParen enough =>
    head_reads all head fuel maximum seen position rest prefixed noParen enough

theorem variable_primary (all : List Nat) (index : Nat) :
    PrimaryReads all [indexed index] (.var (nameIn all index)) [index] := by
  intro fuel maximum seen position rest prefixed noParen enough
  have read := term_reads all (.var index) fuel maximum seen position rest
    (by simpa [CHR.Term.variables] using prefixed) noParen enough
  simpa [CHR.Term.variables, termLexemes, termSource] using read

theorem fail_kind : (bare "fail").kind? = some (.atom "fail") := bare_kind "fail" 'f' ['a', 'i', 'l'] rfl rfl (by decide)

theorem fail_primary (all : List Nat) : PrimaryReads all [bare "fail"] (SourceSignature.atom "fail") [] := by
  intro fuel maximum seen position rest _ noParen enough
  rw [tokensOf_kind _ _ fail_kind, tokensOf_nil, List.cons_append, List.nil_append] at enough ⊢
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [prefix_word fuel maximum _ "fail" _ rest rfl (by decide) (by decide)]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  rw [primary_word fuel _ _ _ "fail" rest rfl (.inl rfl) noParen]
  simp only [List.append_nil]
  rfl

def guardLexemes : CHR.Guard → List Lexeme
  | .identical left right => termLexemes left ++ [space, bare "==", space] ++ termLexemes right
  | .distinct left right => termLexemes left ++ [space, bare "\\==", space] ++ termLexemes right
  | .compare comparison left right =>
    expressionLexemes left ++ [space, bare (comparisonName comparison), space] ++ expressionLexemes right

theorem comparison_kind (comparison : CHR.Comparison) :
    (bare (comparisonName comparison)).kind? = some (.atom (comparisonName comparison)) := by
  cases comparison
  · exact bare_kind "=:=" '=' [':', '='] rfl rfl (by decide)
  · exact bare_kind "=\\=" '=' ['\\', '='] rfl rfl (by decide)
  · exact bare_kind "<" '<' [] rfl rfl (by decide)
  · exact bare_kind "=<" '=' ['<'] rfl rfl (by decide)
  · exact bare_kind ">" '>' [] rfl rfl (by decide)
  · exact bare_kind ">=" '>' ['='] rfl rfl (by decide)

theorem guard_item (all : List Nat) (guard : CHR.Guard) :
    ItemReads all 700 (guardLexemes guard) (guardSource (nameIn all) guard) 700 2 guard.variables := by
  cases guard with
  | identical left right =>
    exact infix_item all _ _ _ _ _ _ "==" (term_primary all left) (term_primary all right) (term_length left)
      (term_starts right) (bare_kind "==" '=' ['='] rfl rfl (by decide)) comparing_identical
  | distinct left right =>
    exact infix_item all _ _ _ _ _ _ "\\==" (term_primary all left) (term_primary all right) (term_length left)
      (term_starts right) (bare_kind "\\==" '\\' ['=', '='] rfl rfl (by decide)) comparing_distinct
  | compare comparison left right =>
    exact infix_item all _ _ _ _ _ _ (comparisonName comparison) (expression_primary_reads all left)
      (expression_primary_reads all right) (expression_length left) (expression_starts right)
      (comparison_kind comparison) (comparing_comparison comparison)

def goalLexemes : CHR.Goal → List Lexeme
  | .tell head => headLexemes head
  | .assign index expression => [indexed index] ++ [space, bare "is", space] ++ expressionLexemes expression
  | .fail => [bare "fail"]

def goalPrecedence : CHR.Goal → Nat
  | .assign _ _ => 700
  | _ => 0

def goalDepth : CHR.Goal → Nat
  | .assign _ _ => 2
  | _ => 1

theorem goal_item (all : List Nat) (goal : CHR.Goal) :
    ItemReads all 700 (goalLexemes goal) (goalSource (nameIn all) goal) (goalPrecedence goal) (goalDepth goal)
      (goalVariables goal) := by
  cases goal with
  | tell head => exact (primary_item all _ _ _ (head_primary all head)).mono (by decide)
  | assign index expression =>
    exact infix_item all _ _ _ _ _ _ "is" (variable_primary all index) (expression_primary_reads all expression)
      (fun position => by rw [tokensOf_kind _ _ (indexed_kind index)]; simp) (expression_starts expression)
      (bare_kind "is" 'i' ['s'] rfl rfl (by decide)) comparing_is
  | fail => exact (primary_item all _ _ _ (fail_primary all)).mono (by decide)

#print axioms guard_item
#print axioms goal_item

/-! ## Conjunctions -/

theorem comma_continues (maximum precedence : Nat) (level : 1000 ≤ maximum) (low : precedence ≤ 999) :
    firstEligibleInfix chr.operators "," maximum precedence = some ⟨",", ⟨1000, by decide, by decide⟩, .xfy⟩ := by
  simp only [firstEligibleInfix, infixes_comma]
  simp only [List.find?_cons, eligible]
  have fits : decide (precedence ≤ 1000 - 1) = true := by simp; omega
  simp [level, Specifier.leftMaximum, fits]

theorem separated_starts (first : List Lexeme) (more : List (List Lexeme)) (position : Position)
    (starts : StartsTerm first) :
    ∃ token tail, tokensOf (separated (first :: more)) position = token :: tail ∧ tokenStartsTerm token.kind = true := by
  obtain ⟨token, tail, listed, startsToken⟩ := starts position
  cases more with
  | nil => exact ⟨token, tail, by rw [tokensOf_separated_single, listed], startsToken⟩
  | cons second rest =>
    rw [tokensOf_separated_cons, listed, List.cons_append]
    exact ⟨token, _, rfl, startsToken⟩

theorem conjunction_reads (all : List Nat) {α : Type} (lexemesOf : α → List Lexeme)
    (sourceOf : α → SourceSignature.Term) (precedenceOf depthOf : α → Nat) (indicesOf : α → List Nat)
    (reads : ∀ item, ItemReads all 700 (lexemesOf item) (sourceOf item) (precedenceOf item) (depthOf item)
      (indicesOf item))
    (low : ∀ item, precedenceOf item ≤ 999)
    (shallow : ∀ item position, depthOf item ≤ (tokensOf (lexemesOf item) position).length)
    (starts : ∀ item, StartsTerm (lexemesOf item)) :
    ∀ (items : List α) (fuel maximum : Nat) (seen : List Nat) (position : Position) (token : Token)
      (rest : List Token), items ≠ [] → 1000 ≤ maximum → Closes token.kind → token.kind ≠ .punctuation .comma →
      seen ++ items.flatMap indicesOf <+: all →
      3 * (tokensOf (separated (items.map lexemesOf)) position ++ token :: rest).length + 3 ≤ fuel →
      ∃ spent precedence, spent ≤ (tokensOf (separated (items.map lexemesOf)) position).length ∧
        precedence ≤ 1000 ∧
        parseExpressionAux chr fuel chr.operators maximum
            (readerState (tokensOf (separated (items.map lexemesOf)) position ++ token :: rest) seen) =
          parseTailAux chr (fuel - spent) chr.operators maximum
            ⟨conjunctionSource (items.map sourceOf), precedence,
              readerState (token :: rest) (seen ++ items.flatMap indicesOf)⟩
  | [], _, _, _, _, _, _, nonempty, _, _, _, _, _ => absurd rfl nonempty
  | [single], fuel, maximum, seen, position, token, rest, _, level, closes, _, prefixed, enough => by
    simp only [List.map_cons, List.map_nil, tokensOf_separated_single, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at prefixed enough ⊢
    refine ⟨depthOf single, precedenceOf single, shallow single position, by have := low single; omega, ?_⟩
    rw [reads single fuel maximum seen position token rest (by omega) closes prefixed enough]
    rfl
  | first :: second :: more, fuel, maximum, seen, position, token, rest, _, level, closes, notComma, prefixed,
      enough => by
    simp only [List.map_cons] at enough ⊢
    rw [tokensOf_separated_cons] at enough ⊢
    have firstPrefixed : seen ++ indicesOf first <+: all :=
      List.IsPrefix.trans (by simp [List.flatMap_cons]) prefixed
    have restPrefixed : (seen ++ indicesOf first) ++ (second :: more).flatMap indicesOf <+: all := by
      simpa [List.flatMap_cons, List.append_assoc] using prefixed
    have deep := shallow first position
    obtain ⟨nextFirst, nextTail, nextListed, nextStarts⟩ := separated_starts (lexemesOf second)
      (more.map lexemesOf) (afterComma (position.advanceMany ((lexemesOf first).flatMap Lexeme.chars)))
      (starts second)
    obtain ⟨spent, precedence, bound, inner⟩ : ∃ spent precedence, spent ≤ _ ∧ precedence ≤ 1000 ∧ _ :=
      conjunction_reads all lexemesOf sourceOf precedenceOf depthOf indicesOf reads low shallow starts
        (second :: more) (fuel - depthOf first - 1) 1000 (seen ++ indicesOf first)
        (afterComma (position.advanceMany ((lexemesOf first).flatMap Lexeme.chars))) token rest (by simp)
        le_rfl closes notComma restPrefixed (by simp only [List.map_cons] at enough ⊢; simp at enough ⊢; omega)
    simp only [List.map_cons] at bound inner
    refine ⟨depthOf first + 1, 1000, by simp; omega, le_rfl, ?_⟩
    rw [List.append_assoc, List.cons_append,
      reads first fuel maximum seen position _ _ (by omega) (.inl rfl) firstPrefixed
        (by simp at enough ⊢; omega)]
    obtain ⟨loopFuel, loopEq⟩ : ∃ smaller, fuel - depthOf first = smaller + 1 :=
      ⟨fuel - depthOf first - 1, by simp at enough; omega⟩
    rw [loopEq, nextListed, List.cons_append,
      tail_infix loopFuel maximum _ _ nextFirst _ "," _ 1000 rfl rfl (comma_continues maximum _ level (low first))
        rfl nextStarts, ← List.cons_append, ← nextListed]
    have sameFuel : fuel - depthOf first - 1 = loopFuel := by omega
    rw [sameFuel] at inner
    erw [inner.2]
    obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, loopFuel - spent = smaller + 1 := ⟨loopFuel - spent - 1, by
      simp at enough bound; omega⟩
    rw [stopEq, tail_closes_conjunction stopFuel _ token rest rfl closes notComma]
    simp only [bind, Except.bind]
    have total : fuel - (depthOf first + 1) = loopFuel := by omega
    rw [total, conjunctionSource, List.flatMap_cons, List.append_assoc]
    rfl

#print axioms conjunction_reads

/-! ## Rule bodies -/

/-- A conjunction as the canonical printer writes it: `true` when empty. -/
def conjunctionLexemes (items : List (List Lexeme)) : List Lexeme :=
  if items.isEmpty then [bare "true"] else separated items

theorem true_kind : (bare "true").kind? = some (.atom "true") := bare_kind "true" 't' ['r', 'u', 'e'] rfl rfl (by decide)

theorem true_primary (all : List Nat) : PrimaryReads all [bare "true"] (SourceSignature.atom "true") [] := by
  intro fuel maximum seen position rest _ noParen enough
  rw [tokensOf_kind _ _ true_kind, tokensOf_nil, List.cons_append, List.nil_append] at enough ⊢
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [prefix_word fuel maximum _ "true" _ rest rfl (by decide) (by decide)]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  rw [primary_word fuel _ _ _ "true" rest rfl (.inl rfl) noParen]
  simp only [List.append_nil]
  rfl

theorem tail_full_stop (fuel maximum : Nat) (left : Parsed) (span : ReaderLexer.Span) (rest : List Token)
    (remaining : left.state.remaining = ⟨.punctuation .fullStop, span⟩ :: rest) :
    parseTailAux chr (fuel + 1) chr.operators maximum left = .ok left :=
  tail_stops fuel maximum left _ rest remaining (by intro name named; simp [operatorName?] at named)

theorem goal_shallow (goal : CHR.Goal) (position : Position) :
    goalDepth goal ≤ (tokensOf (goalLexemes goal) position).length := by
  cases goal with
  | tell head =>
    obtain ⟨token, tail, listed, _⟩ : ∃ token tail, tokensOf (headLexemes head) position = token :: tail ∧
        True := by
      unfold headLexemes
      rw [List.singleton_append, tokensOf_kind _ _ (quoted_kind head.name)]
      exact ⟨_, _, rfl, trivial⟩
    simp [goalDepth, goalLexemes, listed]
  | assign index expression =>
    have := expression_length expression
      (((position.advanceMany (indexed index).chars).advanceMany [' ']).advanceMany (bare "is").chars |>.advanceMany [' '])
    simp only [goalDepth, goalLexemes, List.cons_append, tokensOf_kind _ _ (indexed_kind index),
      space, tokensOf_layout, tokensOf_kind _ _ (bare_kind "is" 'i' ['s'] rfl rfl (by decide)), List.nil_append,
      List.length_cons]
    omega
  | fail => simp [goalDepth, goalLexemes, tokensOf_kind _ _ fail_kind]

theorem goal_starts (goal : CHR.Goal) : StartsTerm (goalLexemes goal) := by
  intro position
  cases goal with
  | tell head =>
    rw [goalLexemes, headLexemes, List.singleton_append, tokensOf_kind _ _ (quoted_kind head.name)]
    exact ⟨_, _, rfl, rfl⟩
  | assign index expression =>
    rw [goalLexemes, List.append_assoc, List.singleton_append, tokensOf_kind _ _ (indexed_kind index)]
    exact ⟨_, _, rfl, rfl⟩
  | fail =>
    rw [goalLexemes, tokensOf_kind _ _ fail_kind]
    exact ⟨_, _, rfl, rfl⟩

theorem goal_low (goal : CHR.Goal) : goalPrecedence goal ≤ 999 := by
  cases goal <;> simp [goalPrecedence]

/-- A rule body reads back, from any level of at least 1000, before the full stop. -/
theorem body_reads (all : List Nat) (body : List CHR.Goal) (fuel maximum : Nat) (seen : List Nat)
    (position : Position) (span : ReaderLexer.Span) (tail : List Token) (level : 1000 ≤ maximum)
    (prefixed : seen ++ body.flatMap goalVariables <+: all)
    (enough : 3 * (tokensOf (conjunctionLexemes (body.map goalLexemes)) position ++
      ⟨.punctuation .fullStop, span⟩ :: tail).length + 3 ≤ fuel) :
    ∃ precedence, parseExpressionAux chr fuel chr.operators maximum
        (readerState (tokensOf (conjunctionLexemes (body.map goalLexemes)) position ++
          ⟨.punctuation .fullStop, span⟩ :: tail) seen) =
      .ok ⟨conjunctionSource (body.map (goalSource (nameIn all))), precedence,
        readerState (⟨.punctuation .fullStop, span⟩ :: tail) (seen ++ body.flatMap goalVariables)⟩ := by
  by_cases empty : body = []
  · subst empty
    simp only [List.map_nil, conjunctionLexemes, List.isEmpty_nil, if_true, List.flatMap_nil,
      List.append_nil] at enough prefixed ⊢
    refine ⟨0, ?_⟩
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    rw [expression_primary fuel maximum _ _ (true_primary all fuel maximum seen position
      (⟨.punctuation .fullStop, span⟩ :: tail) (by simpa using prefixed)
      (by intro paren more same; cases same; simp) (by omega))]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp [tokensOf_kind _ _ true_kind] at enough; omega⟩
    rw [tail_full_stop fuel maximum _ span tail rfl]
    simp [conjunctionSource]
  · have nonempty : (body.map goalLexemes).isEmpty = false := by simpa using empty
    simp only [conjunctionLexemes, nonempty, Bool.false_eq_true, if_false] at enough ⊢
    obtain ⟨spent, precedence, bound, _, reads⟩ := conjunction_reads all goalLexemes (goalSource (nameIn all))
      goalPrecedence goalDepth goalVariables (goal_item all) goal_low goal_shallow goal_starts body fuel maximum seen
      position _ tail empty level (.inr (.inr (.inl rfl))) (by simp) prefixed enough
    refine ⟨precedence, ?_⟩
    rw [reads]
    obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, fuel - spent = smaller + 1 := ⟨fuel - spent - 1, by simp at enough; omega⟩
    rw [stopEq, tail_full_stop stopFuel maximum _ span tail rfl]

#print axioms body_reads

/-! ## Guarded bodies -/

theorem infix_continues (name : String) (priority : Priority) (specifier : Specifier) (maximum precedence : Nat)
    (table : infixes chr.operators name = [⟨name, priority, specifier⟩])
    (fits : eligible maximum precedence ⟨name, priority, specifier⟩ = true) :
    firstEligibleInfix chr.operators name maximum precedence = some ⟨name, priority, specifier⟩ := by
  simp [firstEligibleInfix, table, fits]

theorem bar_eligible (precedence : Nat) (low : precedence ≤ 1104) :
    eligible 1179 precedence ⟨"|", ⟨1105, by decide, by decide⟩, .xfy⟩ = true := by
  simp [eligible, Specifier.leftMaximum]
  omega

theorem guard_shallow (guard : CHR.Guard) (position : Position) :
    2 ≤ (tokensOf (guardLexemes guard) position).length := by
  cases guard with
  | identical left right =>
    simp only [guardLexemes, List.append_assoc, tokensOf_append, List.cons_append, space, tokensOf_layout,
      tokensOf_kind _ _ (bare_kind "==" '=' ['='] rfl rfl (by decide)), List.nil_append, List.length_append,
      List.length_cons]
    have := term_length left position
    omega
  | distinct left right =>
    simp only [guardLexemes, List.append_assoc, tokensOf_append, List.cons_append, space, tokensOf_layout,
      tokensOf_kind _ _ (bare_kind "\\==" '\\' ['=', '='] rfl rfl (by decide)), List.nil_append, List.length_append,
      List.length_cons]
    have := term_length left position
    omega
  | compare comparison left right =>
    simp only [guardLexemes, List.append_assoc, tokensOf_append, List.cons_append, space, tokensOf_layout,
      tokensOf_kind _ _ (comparison_kind comparison), List.nil_append, List.length_append, List.length_cons]
    have := expression_length left position
    omega

theorem guard_starts (guard : CHR.Guard) : StartsTerm (guardLexemes guard) := by
  intro position
  cases guard with
  | identical left right =>
    obtain ⟨token, tail, listed, starts⟩ := term_starts left position
    rw [guardLexemes, List.append_assoc, tokensOf_append, listed, List.cons_append]
    exact ⟨token, _, rfl, starts⟩
  | distinct left right =>
    obtain ⟨token, tail, listed, starts⟩ := term_starts left position
    rw [guardLexemes, List.append_assoc, tokensOf_append, listed, List.cons_append]
    exact ⟨token, _, rfl, starts⟩
  | compare comparison left right =>
    obtain ⟨token, tail, listed, starts⟩ := expression_starts left position
    rw [guardLexemes, List.append_assoc, tokensOf_append, listed, List.cons_append]
    exact ⟨token, _, rfl, starts⟩

theorem body_starts (body : List CHR.Goal) : StartsTerm (conjunctionLexemes (body.map goalLexemes)) := by
  intro position
  cases body with
  | nil =>
    simp only [List.map_nil, conjunctionLexemes, List.isEmpty_nil, if_true]
    rw [tokensOf_kind _ _ true_kind]
    exact ⟨_, _, rfl, rfl⟩
  | cons goal more =>
    simp only [List.map_cons, conjunctionLexemes, List.isEmpty_cons, Bool.false_eq_true, if_false]
    exact separated_starts _ _ position (goal_starts goal)

/-- The part of a rule after its arrow: guards, a bar, and the body. -/
def rightLexemes (rule : CHR.Rule) : List Lexeme :=
  (if rule.guards.isEmpty then [] else conjunctionLexemes (rule.guards.map guardLexemes) ++ [space, bar, space]) ++
    conjunctionLexemes (rule.body.map goalLexemes)

/-- The source the canonical printer writes after a rule's arrow. -/
def rightSource (name : Nat → SourceSignature.Variable) (rule : CHR.Rule) : SourceSignature.Term :=
  if rule.guards.isEmpty then conjunctionSource (rule.body.map (goalSource name))
  else SourceSignature.compound "|" [conjunctionSource (rule.guards.map (guardSource name)),
    conjunctionSource (rule.body.map (goalSource name))]

theorem right_reads (all : List Nat) (rule : CHR.Rule) (fuel : Nat) (seen : List Nat) (position : Position)
    (span : ReaderLexer.Span) (tail : List Token)
    (prefixed : seen ++ (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables) <+: all)
    (enough : 3 * (tokensOf (rightLexemes rule) position ++ ⟨.punctuation .fullStop, span⟩ :: tail).length + 3 ≤ fuel) :
    ∃ precedence, parseExpressionAux chr fuel chr.operators 1179
        (readerState (tokensOf (rightLexemes rule) position ++ ⟨.punctuation .fullStop, span⟩ :: tail) seen) =
      .ok ⟨rightSource (nameIn all) rule, precedence, readerState (⟨.punctuation .fullStop, span⟩ :: tail)
        (seen ++ (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables))⟩ := by
  unfold rightLexemes rightSource at *
  by_cases empty : rule.guards.isEmpty
  · have none : rule.guards = [] := List.isEmpty_iff.mp empty
    simp only [List.nil_append, none, List.flatMap_nil] at enough prefixed ⊢
    exact body_reads all rule.body fuel 1179 seen position span tail (by decide) prefixed enough
  · have some : rule.guards ≠ [] := by simpa using empty
    have mapped : (rule.guards.map guardLexemes).isEmpty = false := by simpa using empty
    simp only [empty, if_false, Bool.false_eq_true, conjunctionLexemes, mapped] at enough ⊢
    set afterGuards := position.advanceMany ((separated (rule.guards.map guardLexemes)).flatMap Lexeme.chars)
    set atBar := afterGuards.advanceMany [' ']
    set afterBar := (atBar.advanceMany bar.chars).advanceMany [' ']
    have listed : tokensOf (separated (rule.guards.map guardLexemes) ++ [space, bar, space] ++
          (if (rule.body.map goalLexemes).isEmpty then [bare "true"] else separated (rule.body.map goalLexemes)))
          position =
        tokensOf (separated (rule.guards.map guardLexemes)) position ++
          ⟨.punctuation .bar, ⟨atBar, atBar.advanceMany bar.chars⟩⟩ ::
            tokensOf (conjunctionLexemes (rule.body.map goalLexemes)) afterBar := by
      rw [List.append_assoc, tokensOf_append, List.cons_append, space, tokensOf_layout, List.cons_append,
        tokensOf_kind _ _ bar_kind, List.cons_append, List.nil_append, tokensOf_layout]
      rfl
    rw [listed] at enough ⊢
    simp only [List.append_assoc, List.cons_append] at enough ⊢
    have guardsPrefixed : seen ++ rule.guards.flatMap CHR.Guard.variables <+: all :=
      List.IsPrefix.trans (by simp) prefixed
    have bodyPrefixed : (seen ++ rule.guards.flatMap CHR.Guard.variables) ++ rule.body.flatMap goalVariables <+: all := by
      simpa [List.append_assoc] using prefixed
    obtain ⟨bodyFirst, bodyTail, bodyListed, bodyStarts⟩ := body_starts rule.body afterBar
    obtain ⟨spent, precedence, bound, low, guardsRead⟩ := conjunction_reads all guardLexemes
      (guardSource (nameIn all)) (fun _ => 700) (fun _ => 2) CHR.Guard.variables (guard_item all) (fun _ => by decide)
      (fun guard position => guard_shallow guard position) guard_starts rule.guards fuel 1179 seen position
      ⟨.punctuation .bar, ⟨atBar, atBar.advanceMany bar.chars⟩⟩
      (tokensOf (conjunctionLexemes (rule.body.map goalLexemes)) afterBar ++ ⟨.punctuation .fullStop, span⟩ :: tail)
      some (by decide) (.inr (.inl rfl)) (by simp) guardsPrefixed (by simp at enough ⊢; omega)
    rw [guardsRead]
    obtain ⟨loopFuel, loopEq⟩ : ∃ smaller, fuel - spent = smaller + 1 := ⟨fuel - spent - 1, by simp at enough; omega⟩
    rw [loopEq, bodyListed, List.cons_append,
      tail_infix loopFuel 1179 _ _ bodyFirst _ "|" _ 1105 rfl rfl
        (infix_continues "|" _ .xfy 1179 precedence infixes_bar (bar_eligible precedence (by omega))) rfl bodyStarts,
      ← List.cons_append, ← bodyListed]
    obtain ⟨bodyPrecedence, bodyRead⟩ := body_reads all rule.body loopFuel 1105 (seen ++ rule.guards.flatMap CHR.Guard.variables)
      afterBar span tail (by decide) bodyPrefixed (by simp at enough ⊢; omega)
    erw [bodyRead]
    obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, loopFuel = smaller + 1 := ⟨loopFuel - 1, by simp at enough; omega⟩
    simp only [bind, Except.bind]
    rw [stopEq, tail_full_stop stopFuel 1179 _ span tail rfl]
    refine ⟨1105, ?_⟩
    simp only [List.append_assoc]

#print axioms right_reads

/-! ## Rules -/

open CHRPrologReadback (headsSource ruleSource ruleVariables)

def headsLexemes (rule : CHR.Rule) : List Lexeme :=
  if rule.removed.isEmpty then conjunctionLexemes (rule.kept.map headLexemes)
  else if rule.kept.isEmpty then conjunctionLexemes (rule.removed.map headLexemes)
  else conjunctionLexemes (rule.kept.map headLexemes) ++ [space, bare "\\", space] ++
    conjunctionLexemes (rule.removed.map headLexemes)

def arrowName (rule : CHR.Rule) : String := if rule.removed.isEmpty then "==>" else "<=>"

def ruleLexemes (rule : CHR.Rule) : List Lexeme :=
  [quoted rule.name, space, bare "@", space] ++ headsLexemes rule ++ [space, bare (arrowName rule), space] ++
    rightLexemes rule ++ [.fullStop, newline]

theorem head_item (all : List Nat) (head : CHR.Head) :
    ItemReads all 700 (headLexemes head) (headSource (nameIn all) head) 0 1 head.variables :=
  (primary_item all _ _ _ (head_primary all head)).mono (by decide)

theorem head_starts (head : CHR.Head) : StartsTerm (headLexemes head) := by
  intro position
  rw [headLexemes, List.singleton_append, tokensOf_kind _ _ (quoted_kind head.name)]
  exact ⟨_, _, rfl, rfl⟩

theorem head_shallow (head : CHR.Head) (position : Position) : 1 ≤ (tokensOf (headLexemes head) position).length := by
  obtain ⟨token, tail, listed, _⟩ := head_starts head position
  rw [listed]
  simp

theorem heads_reads (all : List Nat) (heads : List CHR.Head) (fuel maximum : Nat) (seen : List Nat)
    (position : Position) (token : Token) (rest : List Token) (nonempty : heads ≠ []) (level : 1000 ≤ maximum)
    (closes : Closes token.kind) (notComma : token.kind ≠ .punctuation .comma)
    (prefixed : seen ++ heads.flatMap CHR.Head.variables <+: all)
    (enough : 3 * (tokensOf (conjunctionLexemes (heads.map headLexemes)) position ++ token :: rest).length + 3 ≤ fuel) :
    ∃ spent precedence, spent ≤ (tokensOf (conjunctionLexemes (heads.map headLexemes)) position).length ∧
      precedence ≤ 1000 ∧
      parseExpressionAux chr fuel chr.operators maximum
          (readerState (tokensOf (conjunctionLexemes (heads.map headLexemes)) position ++ token :: rest) seen) =
        parseTailAux chr (fuel - spent) chr.operators maximum
          ⟨headsSource (nameIn all) heads, precedence,
            readerState (token :: rest) (seen ++ heads.flatMap CHR.Head.variables)⟩ := by
  have mapped : (heads.map headLexemes).isEmpty = false := by simpa using nonempty
  simp only [conjunctionLexemes, mapped, Bool.false_eq_true, if_false] at enough ⊢
  exact conjunction_reads all headLexemes (headSource (nameIn all)) (fun _ => 0) (fun _ => 1) CHR.Head.variables
    (head_item all) (fun _ => by decide) head_shallow head_starts heads fuel maximum seen position token rest nonempty
    level closes notComma prefixed enough

theorem heads_starts (heads : List CHR.Head) (nonempty : heads ≠ []) :
    StartsTerm (conjunctionLexemes (heads.map headLexemes)) := by
  intro position
  cases heads with
  | nil => exact absurd rfl nonempty
  | cons head more =>
    simp only [List.map_cons, conjunctionLexemes, List.isEmpty_cons, Bool.false_eq_true, if_false]
    exact separated_starts _ _ position (head_starts head)

theorem right_starts (rule : CHR.Rule) : StartsTerm (rightLexemes rule) := by
  intro position
  unfold rightLexemes
  by_cases empty : rule.guards.isEmpty
  · simp only [empty, if_true, List.nil_append]
    exact body_starts rule.body position
  · simp only [empty, if_false, Bool.false_eq_true]
    cases guards : rule.guards with
    | nil => simp [guards] at empty
    | cons guard more =>
      simp only [List.map_cons, conjunctionLexemes, List.isEmpty_cons, Bool.false_eq_true, if_false]
      obtain ⟨token, tail, listed, starts⟩ := separated_starts _ (more.map guardLexemes) position (guard_starts guard)
      rw [List.append_assoc, tokensOf_append, listed, List.cons_append]
      exact ⟨token, _, rfl, starts⟩

theorem arrow_eligible (precedence : Nat) (low : precedence ≤ 1179) (priority : Priority) (fits : priority.value = 1180) :
    eligible 1199 precedence ⟨"<=>", priority, .xfx⟩ = true := by
  simp [eligible, Specifier.leftMaximum, fits]
  omega

theorem simplify_continues (precedence : Nat) (low : precedence ≤ 1179) :
    firstEligibleInfix chr.operators "<=>" 1199 precedence = some ⟨"<=>", ⟨1180, by decide, by decide⟩, .xfx⟩ :=
  infix_continues "<=>" _ .xfx 1199 precedence infixes_simplify (arrow_eligible precedence low _ rfl)

theorem propagate_continues (precedence : Nat) (low : precedence ≤ 1179) :
    firstEligibleInfix chr.operators "==>" 1199 precedence = some ⟨"==>", ⟨1180, by decide, by decide⟩, .xfx⟩ := by
  simp [firstEligibleInfix, infixes_propagate, eligible, Specifier.leftMaximum]
  omega

theorem propagate_continues' (precedence : Nat) (low : precedence ≤ 1000) :
    firstEligibleInfix chr.operators "==>" 1199 precedence = some ⟨"==>", ⟨1180, by decide, by decide⟩, .xfx⟩ :=
  propagate_continues precedence (by omega)

theorem simplify_continues' (precedence : Nat) (low : precedence ≤ 1000) :
    firstEligibleInfix chr.operators "<=>" 1199 precedence = some ⟨"<=>", ⟨1180, by decide, by decide⟩, .xfx⟩ :=
  simplify_continues precedence (by omega)

theorem backslash_continues (precedence : Nat) (low : precedence ≤ 1099) :
    firstEligibleInfix chr.operators "\\" 1199 precedence = some ⟨"\\", ⟨1100, by decide, by decide⟩, .xfx⟩ := by
  simp [firstEligibleInfix, infixes_backslash, eligible, Specifier.leftMaximum]
  omega

theorem tail_before_arrow (fuel : Nat) (left : Parsed) (span : ReaderLexer.Span) (rest : List Token)
    (remaining : left.state.remaining = ⟨.atom "<=>", span⟩ :: rest) :
    parseTailAux chr (fuel + 1) chr.operators 1099 left = .ok left :=
  tail_stops fuel 1099 left _ rest remaining (by
    intro name named
    simp only [operatorName?, Option.some.injEq] at named
    subst named
    simp [firstEligibleInfix, infixes_simplify, eligible])

#print axioms heads_reads

theorem infix_tokens (first second : List Lexeme) (name : String) (named : (bare name).kind? = some (.atom name))
    (position : Position) :
    tokensOf (first ++ [space, bare name, space] ++ second) position =
      tokensOf first position ++
        ⟨.atom name, ⟨(position.advanceMany (first.flatMap Lexeme.chars)).advanceMany [' '],
          ((position.advanceMany (first.flatMap Lexeme.chars)).advanceMany [' ']).advanceMany (bare name).chars⟩⟩ ::
        tokensOf second ((((position.advanceMany (first.flatMap Lexeme.chars)).advanceMany [' ']).advanceMany
          (bare name).chars).advanceMany [' ']) := by
  rw [List.append_assoc, tokensOf_append, List.cons_append, space, tokensOf_layout, List.cons_append,
    tokensOf_kind _ _ named, List.cons_append, List.nil_append, tokensOf_layout]

theorem backslash_kind : (bare "\\").kind? = some (.atom "\\") := bare_kind "\\" '\\' [] rfl rfl (by decide)
theorem propagate_kind : (bare "==>").kind? = some (.atom "==>") := bare_kind "==>" '=' ['=', '>'] rfl rfl (by decide)
theorem simplify_kind : (bare "<=>").kind? = some (.atom "<=>") := bare_kind "<=>" '<' ['=', '>'] rfl rfl (by decide)
theorem named_kind : (bare "@").kind? = some (.atom "@") := bare_kind "@" '@' [] rfl rfl (by decide)

/-- The source the canonical printer writes before a rule's arrow. -/
def leftSource (name : Nat → SourceSignature.Variable) (rule : CHR.Rule) : SourceSignature.Term :=
  if rule.removed.isEmpty then headsSource name rule.kept
  else if rule.kept.isEmpty then headsSource name rule.removed
  else SourceSignature.compound "\\" [headsSource name rule.kept, headsSource name rule.removed]

/-- One arrow joins the heads read at 1199 to the guarded body read at 1179. -/
theorem arrow_join (all : List Nat) (rule : CHR.Rule) (arrow : String)
    (left : SourceSignature.Term) (leftPrecedence : Nat) (leftIndices : List Nat) (fuel : Nat) (seen : List Nat)
    (arrowPosition rightPosition : Position) (span : ReaderLexer.Span) (tail : List Token)
    (continues : firstEligibleInfix chr.operators arrow 1199 leftPrecedence =
      some ⟨arrow, ⟨1180, by decide, by decide⟩, .xfx⟩)
    (prefixed : (seen ++ leftIndices) ++ (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables) <+: all)
    (enough : 3 * (tokensOf (rightLexemes rule) rightPosition ++ ⟨.punctuation .fullStop, span⟩ :: tail).length + 6 ≤ fuel) :
    parseTailAux chr (fuel + 1) chr.operators 1199
        ⟨left, leftPrecedence, readerState (⟨.atom arrow, ⟨arrowPosition, arrowPosition.advanceMany (bare arrow).chars⟩⟩ ::
          (tokensOf (rightLexemes rule) rightPosition ++ ⟨.punctuation .fullStop, span⟩ :: tail)) (seen ++ leftIndices)⟩ =
      .ok ⟨SourceSignature.compound arrow [left, rightSource (nameIn all) rule], 1180,
        readerState (⟨.punctuation .fullStop, span⟩ :: tail)
          ((seen ++ leftIndices) ++ (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables))⟩ := by
  obtain ⟨rightFirst, rightTail, rightListed, starts⟩ := right_starts rule rightPosition
  rw [rightListed, List.cons_append,
    tail_infix fuel 1199 _ _ rightFirst _ arrow _ 1179 rfl rfl continues rfl starts, ← List.cons_append, ← rightListed]
  obtain ⟨rightPrecedence, rightRead⟩ := right_reads all rule fuel (seen ++ leftIndices) rightPosition span tail
    prefixed (by omega)
  erw [rightRead]
  obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  simp only [bind, Except.bind]
  rw [stopEq, tail_full_stop stopFuel 1199 _ span tail rfl]

#print axioms arrow_join

/-- The heads, one arrow and the guarded body, for one head conjunction. -/
theorem arrow_single (all : List Nat) (rule : CHR.Rule) (heads : List CHR.Head) (arrow : String)
    (named : (bare arrow).kind? = some (.atom arrow))
    (continues : ∀ precedence, precedence ≤ 1000 → firstEligibleInfix chr.operators arrow 1199 precedence =
      some ⟨arrow, ⟨1180, by decide, by decide⟩, .xfx⟩)
    (closes : Closes (.atom arrow)) (notComma : Kind.atom arrow ≠ .punctuation .comma)
    (nonempty : heads ≠ []) (fuel : Nat) (seen : List Nat) (position : Position) (span : ReaderLexer.Span)
    (tail : List Token)
    (prefixed : seen ++ (heads.flatMap CHR.Head.variables ++
      (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables)) <+: all)
    (enough : 3 * (tokensOf (conjunctionLexemes (heads.map headLexemes) ++ [space, bare arrow, space] ++
      rightLexemes rule) position ++ ⟨.punctuation .fullStop, span⟩ :: tail).length + 3 ≤ fuel) :
    parseExpressionAux chr fuel chr.operators 1199
        (readerState (tokensOf (conjunctionLexemes (heads.map headLexemes) ++ [space, bare arrow, space] ++
          rightLexemes rule) position ++ ⟨.punctuation .fullStop, span⟩ :: tail) seen) =
      .ok ⟨SourceSignature.compound arrow [headsSource (nameIn all) heads, rightSource (nameIn all) rule], 1180,
        readerState (⟨.punctuation .fullStop, span⟩ :: tail) (seen ++ (heads.flatMap CHR.Head.variables ++
          (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables)))⟩ := by
  rw [infix_tokens _ _ arrow named] at enough ⊢
  set arrowPosition := (position.advanceMany ((conjunctionLexemes (heads.map headLexemes)).flatMap Lexeme.chars)).advanceMany
    [' ']
  set rightPosition := (arrowPosition.advanceMany (bare arrow).chars).advanceMany [' ']
  simp only [List.append_assoc, List.cons_append] at enough ⊢
  have headsPrefixed : seen ++ heads.flatMap CHR.Head.variables <+: all := List.IsPrefix.trans (by simp) prefixed
  have headsLong : 1 ≤ (tokensOf (conjunctionLexemes (heads.map headLexemes)) position).length := by
    obtain ⟨token, rest, listed, _⟩ := heads_starts heads nonempty position
    rw [listed]
    simp
  obtain ⟨spent, precedence, bound, low, headsRead⟩ := heads_reads all heads fuel 1199 seen position
    ⟨.atom arrow, ⟨arrowPosition, arrowPosition.advanceMany (bare arrow).chars⟩⟩
    (tokensOf (rightLexemes rule) rightPosition ++ ⟨.punctuation .fullStop, span⟩ :: tail) nonempty (by decide)
    closes notComma headsPrefixed (by simp at enough ⊢; omega)
  rw [headsRead]
  obtain ⟨loopFuel, loopEq⟩ : ∃ smaller, fuel - spent = smaller + 1 := ⟨fuel - spent - 1, by simp at enough; omega⟩
  rw [loopEq, arrow_join all rule arrow _ precedence _ loopFuel seen _ _ span tail (continues precedence low)
    (by simpa [List.append_assoc] using prefixed) (by simp at enough ⊢; omega)]
  simp only [List.append_assoc]

theorem arrow_simpagation (all : List Nat) (rule : CHR.Rule) (kept : rule.kept ≠ []) (removed : rule.removed ≠ [])
    (fuel : Nat) (seen : List Nat) (position : Position) (span : ReaderLexer.Span) (tail : List Token)
    (prefixed : seen ++ (rule.kept.flatMap CHR.Head.variables ++ (rule.removed.flatMap CHR.Head.variables ++
      (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables))) <+: all)
    (enough : 3 * (tokensOf ((conjunctionLexemes (rule.kept.map headLexemes) ++ [space, bare "\\", space] ++
      conjunctionLexemes (rule.removed.map headLexemes)) ++ [space, bare "<=>", space] ++ rightLexemes rule) position ++
        ⟨.punctuation .fullStop, span⟩ :: tail).length + 3 ≤ fuel) :
    parseExpressionAux chr fuel chr.operators 1199
        (readerState (tokensOf ((conjunctionLexemes (rule.kept.map headLexemes) ++ [space, bare "\\", space] ++
          conjunctionLexemes (rule.removed.map headLexemes)) ++ [space, bare "<=>", space] ++ rightLexemes rule)
            position ++ ⟨.punctuation .fullStop, span⟩ :: tail) seen) =
      .ok ⟨SourceSignature.compound "<=>" [SourceSignature.compound "\\" [headsSource (nameIn all) rule.kept,
          headsSource (nameIn all) rule.removed], rightSource (nameIn all) rule], 1180,
        readerState (⟨.punctuation .fullStop, span⟩ :: tail) (seen ++ (rule.kept.flatMap CHR.Head.variables ++
          (rule.removed.flatMap CHR.Head.variables ++
            (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables))))⟩ := by
  rw [infix_tokens _ _ "<=>" simplify_kind, infix_tokens _ _ "\\" backslash_kind] at enough ⊢
  set slashPosition := (position.advanceMany ((conjunctionLexemes (rule.kept.map headLexemes)).flatMap
    Lexeme.chars)).advanceMany [' ']
  set removedPosition := (slashPosition.advanceMany (bare "\\").chars).advanceMany [' ']
  set arrowPosition := (position.advanceMany ((conjunctionLexemes (rule.kept.map headLexemes) ++ [space, bare "\\", space] ++
    conjunctionLexemes (rule.removed.map headLexemes)).flatMap Lexeme.chars)).advanceMany [' ']
  set rightPosition := (arrowPosition.advanceMany (bare "<=>").chars).advanceMany [' ']
  simp only [List.append_assoc, List.cons_append] at enough ⊢
  have keptPrefixed : seen ++ rule.kept.flatMap CHR.Head.variables <+: all := List.IsPrefix.trans (by simp) prefixed
  have removedPrefixed : (seen ++ rule.kept.flatMap CHR.Head.variables) ++ rule.removed.flatMap CHR.Head.variables <+:
      all := List.IsPrefix.trans (by simp) prefixed
  obtain ⟨spent, precedence, bound, low, keptRead⟩ := heads_reads all rule.kept fuel 1199 seen position
    ⟨.atom "\\", ⟨slashPosition, slashPosition.advanceMany (bare "\\").chars⟩⟩
    (tokensOf (conjunctionLexemes (rule.removed.map headLexemes)) removedPosition ++
      ⟨.atom "<=>", ⟨arrowPosition, arrowPosition.advanceMany (bare "<=>").chars⟩⟩ ::
        (tokensOf (rightLexemes rule) rightPosition ++ ⟨.punctuation .fullStop, span⟩ :: tail))
    kept (by decide) (.inr (.inr (.inr (.inl rfl)))) (by simp) keptPrefixed (by simp at enough ⊢; omega)
  rw [keptRead]
  obtain ⟨loopFuel, loopEq⟩ : ∃ smaller, fuel - spent = smaller + 1 := ⟨fuel - spent - 1, by simp at enough; omega⟩
  obtain ⟨removedFirst, removedTail, removedListed, removedStarts⟩ := heads_starts rule.removed removed removedPosition
  rw [loopEq, removedListed, List.cons_append,
    tail_infix loopFuel 1199 _ _ removedFirst _ "\\" _ 1099 rfl rfl (backslash_continues precedence (by omega)) rfl
      removedStarts, ← List.cons_append, ← removedListed]
  obtain ⟨removedSpent, removedPrecedence, removedBound, _, removedRead⟩ := heads_reads all rule.removed loopFuel 1099
    (seen ++ rule.kept.flatMap CHR.Head.variables) removedPosition
    ⟨.atom "<=>", ⟨arrowPosition, arrowPosition.advanceMany (bare "<=>").chars⟩⟩
    (tokensOf (rightLexemes rule) rightPosition ++ ⟨.punctuation .fullStop, span⟩ :: tail)
    removed (by decide) (.inr (.inr (.inr (.inr (.inl rfl))))) (by simp) removedPrefixed (by simp at enough ⊢; omega)
  erw [removedRead]
  obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, loopFuel - removedSpent = smaller + 1 := ⟨loopFuel - removedSpent - 1, by
    simp at enough removedBound; omega⟩
  rw [stopEq, tail_before_arrow stopFuel _ _ _ rfl]
  simp only [bind, Except.bind]
  obtain ⟨joinFuel, joinEq⟩ : ∃ smaller, loopFuel = smaller + 1 := ⟨loopFuel - 1, by simp at enough; omega⟩
  rw [joinEq, arrow_join all rule "<=>" _ 1100 (rule.removed.flatMap CHR.Head.variables) joinFuel
    (seen ++ rule.kept.flatMap CHR.Head.variables) _ _ span tail (simplify_continues 1100 (by decide))
    (by simpa [List.append_assoc] using prefixed) (by simp at enough ⊢; omega)]
  simp only [List.append_assoc]

#print axioms arrow_single
#print axioms arrow_simpagation

theorem arrow_reads (all : List Nat) (rule : CHR.Rule) (heads : rule.kept ++ rule.removed ≠ []) (fuel : Nat)
    (seen : List Nat) (position : Position) (span : ReaderLexer.Span) (tail : List Token)
    (prefixed : seen ++ ruleVariables rule <+: all)
    (enough : 3 * (tokensOf (headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule) position ++
      ⟨.punctuation .fullStop, span⟩ :: tail).length + 3 ≤ fuel) :
    parseExpressionAux chr fuel chr.operators 1199
        (readerState (tokensOf (headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule)
          position ++ ⟨.punctuation .fullStop, span⟩ :: tail) seen) =
      .ok ⟨SourceSignature.compound (arrowName rule) [leftSource (nameIn all) rule, rightSource (nameIn all) rule], 1180,
        readerState (⟨.punctuation .fullStop, span⟩ :: tail) (seen ++ ruleVariables rule)⟩ := by
  have order : ruleVariables rule = rule.kept.flatMap CHR.Head.variables ++ (rule.removed.flatMap CHR.Head.variables ++
      (rule.guards.flatMap CHR.Guard.variables ++ rule.body.flatMap goalVariables)) := by
    simp [ruleVariables, List.append_assoc]
  rw [order] at prefixed ⊢
  by_cases removedEmpty : rule.removed.isEmpty
  · have none : rule.removed = [] := List.isEmpty_iff.mp removedEmpty
    have kept : rule.kept ≠ [] := by simpa [none] using heads
    simp only [headsLexemes, arrowName, leftSource, removedEmpty, if_true] at enough ⊢
    simp only [none, List.flatMap_nil, List.nil_append] at prefixed ⊢
    exact arrow_single all rule rule.kept "==>" propagate_kind propagate_continues' (.inr (.inr (.inr (.inr (.inr rfl)))))
      (by simp) kept fuel seen position span tail prefixed enough
  · by_cases keptEmpty : rule.kept.isEmpty
    · have none : rule.kept = [] := List.isEmpty_iff.mp keptEmpty
      have removed : rule.removed ≠ [] := by simpa [none] using heads
      simp only [headsLexemes, arrowName, leftSource, removedEmpty, keptEmpty, if_true, if_false,
        Bool.false_eq_true] at enough ⊢
      simp only [none, List.flatMap_nil, List.nil_append] at prefixed ⊢
      exact arrow_single all rule rule.removed "<=>" simplify_kind simplify_continues'
        (.inr (.inr (.inr (.inr (.inl rfl))))) (by simp) removed fuel seen position span tail prefixed enough
    · have kept : rule.kept ≠ [] := by simpa using keptEmpty
      have removed : rule.removed ≠ [] := by simpa using removedEmpty
      simp only [headsLexemes, arrowName, leftSource, removedEmpty, keptEmpty, if_false, Bool.false_eq_true]
        at enough ⊢
      exact arrow_simpagation all rule kept removed fuel seen position span tail prefixed enough

theorem headsLexemes_starts (rule : CHR.Rule) (heads : rule.kept ++ rule.removed ≠ []) :
    StartsTerm (headsLexemes rule) := by
  intro position
  unfold headsLexemes
  by_cases removedEmpty : rule.removed.isEmpty
  · have kept : rule.kept ≠ [] := by simpa [List.isEmpty_iff.mp removedEmpty] using heads
    simp only [removedEmpty, if_true]
    exact heads_starts rule.kept kept position
  · by_cases keptEmpty : rule.kept.isEmpty
    · have removed : rule.removed ≠ [] := by simpa using removedEmpty
      simp only [removedEmpty, keptEmpty, if_true, if_false, Bool.false_eq_true]
      exact heads_starts rule.removed removed position
    · have kept : rule.kept ≠ [] := by simpa using keptEmpty
      simp only [removedEmpty, keptEmpty, if_false, Bool.false_eq_true]
      obtain ⟨token, tail, listed, starts⟩ := heads_starts rule.kept kept position
      rw [List.append_assoc, tokensOf_append, listed, List.cons_append]
      exact ⟨token, _, rfl, starts⟩

theorem ruleSource_shape (name : Nat → SourceSignature.Variable) (rule : CHR.Rule) :
    ruleSource name rule = SourceSignature.compound "@" [SourceSignature.atom rule.name,
      SourceSignature.compound (arrowName rule) [leftSource name rule, rightSource name rule]] := by
  simp only [ruleSource, arrowName, leftSource, rightSource, headsSource]

/-- The tokens of a printed rule: its name, `@`, the rest, and the full stop. -/
theorem rule_tokens (rule : CHR.Rule) (position : Position) :
    ∃ nameSpan namedSpan restPosition stopSpan, tokensOf (ruleLexemes rule) position =
      ⟨.quotedAtom rule.name, nameSpan⟩ :: ⟨.atom "@", namedSpan⟩ ::
        (tokensOf (headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule) restPosition ++
          [⟨.punctuation .fullStop, stopSpan⟩]) := by
  have shape : ruleLexemes rule = [quoted rule.name, space, bare "@", space] ++
      ((headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule) ++ [.fullStop, newline]) := by
    simp [ruleLexemes, List.append_assoc]
  rw [shape, List.cons_append, tokensOf_kind _ _ (quoted_kind rule.name), List.cons_append, space, tokensOf_layout,
    List.cons_append, tokensOf_kind _ _ named_kind, List.cons_append, List.nil_append, tokensOf_layout,
    tokensOf_append, tokensOf_kind _ _ rfl, newline, tokensOf_layout, tokensOf_nil]
  exact ⟨_, _, _, _, rfl⟩

theorem named_continues :
    firstEligibleInfix chr.operators "@" 1200 0 = some ⟨"@", ⟨1200, by decide, by decide⟩, .xfx⟩ := by
  simp [firstEligibleInfix, infixes_named, eligible, Specifier.leftMaximum]

theorem consume_full_stop (state : State) (span : ReaderLexer.Span) (rest : List Token)
    (remaining : state.remaining = ⟨.punctuation .fullStop, span⟩ :: rest) :
    consumePunctuation .fullStop state = .ok { state with remaining := rest } := by
  unfold consumePunctuation
  rw [remaining]
  simp

theorem rule_expression (rule : CHR.Rule) (heads : rule.kept ++ rule.removed ≠ []) (nameSpan namedSpan stopSpan : ReaderLexer.Span)
    (restPosition : Position) (fuel : Nat)
    (enough : 3 * (tokensOf (headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule)
      restPosition ++ [(⟨.punctuation .fullStop, stopSpan⟩ : Token)]).length + 12 ≤ fuel) :
    parseExpressionAux chr fuel chr.operators 1200
        (readerState ((⟨.quotedAtom rule.name, nameSpan⟩ : Token) :: ⟨.atom "@", namedSpan⟩ ::
          (tokensOf (headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule) restPosition ++
            [⟨.punctuation .fullStop, stopSpan⟩])) []) =
      .ok ⟨ruleSource (nameIn (ruleVariables rule)) rule, 1200,
        readerState [⟨.punctuation .fullStop, stopSpan⟩] (ruleVariables rule)⟩ := by
  obtain ⟨restFirst, restTail, restListed, restStarts⟩ :=
    (fun position => by
      obtain ⟨token, tail, listed, starts⟩ := headsLexemes_starts rule heads position
      rw [List.append_assoc, tokensOf_append, listed, List.cons_append]
      exact ⟨token, _, rfl, starts⟩ : StartsTerm (headsLexemes rule ++ [space, bare (arrowName rule), space] ++
        rightLexemes rule)) restPosition
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [expression_step]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [prefix_quoted fuel 1200 _ rule.name _ _ rfl]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [primary_word fuel _ _ _ rule.name _ rfl (.inr rfl) (by intro paren tail same; cases same; simp)]
  simp only [bind, Except.bind]
  rw [restListed, List.cons_append,
    tail_infix (fuel + 1) 1200 _ _ restFirst _ "@" _ 1199 rfl rfl named_continues rfl restStarts,
    ← List.cons_append, ← restListed]
  erw [arrow_reads (ruleVariables rule) rule heads (fuel + 1) [] restPosition stopSpan [] (by simp)
    (by simp at enough ⊢; omega)]
  simp only [bind, Except.bind]
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  rw [tail_full_stop (fuel + 1) 1200 _ stopSpan [] rfl, ruleSource_shape]
  rfl

/-- **A printed rule reads back.** The reference reader, under the CHR
profile, reads the printed rule as its canonical source, every variable at its
first occurrence. -/
theorem rule_parses (rule : CHR.Rule) (heads : rule.kept ++ rule.removed ≠ []) (position : Position) :
    ∃ bindings, ReaderTerm.parseOneWith chr chr.operators (tokensOf (ruleLexemes rule) position) =
      .ok ⟨ruleSource (nameIn (ruleVariables rule)) rule, bindings, []⟩ := by
  obtain ⟨nameSpan, namedSpan, restPosition, stopSpan, listed⟩ := rule_tokens rule position
  refine ⟨(readerState [] (ruleVariables rule)).bindings.reverse, ?_⟩
  unfold ReaderTerm.parseOneWith
  rw [listed]
  dsimp only
  have read := rule_expression rule heads nameSpan namedSpan stopSpan restPosition
    ((⟨.quotedAtom rule.name, nameSpan⟩ :: ⟨.atom "@", namedSpan⟩ ::
      (tokensOf (headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule) restPosition ++
        [⟨.punctuation .fullStop, stopSpan⟩]) : List Token).length * 4 + 8) (by simp; omega)
  erw [read]
  simp only [bind, Except.bind]
  rw [consume_full_stop _ stopSpan [] rfl]
  rfl

#print axioms rule_parses

/-! ## The printer's text is the lexemes' characters -/

theorem bare_chars (text : String) (nonempty : text ≠ "") : (bare text).chars = text.toList := by
  unfold bare
  cases listed : text.toList with
  | nil => exact absurd (String.toList_inj.mp (by simpa using listed)) nonempty
  | cons first more => simp only; split <;> rfl

theorem separated_chars : ∀ items : List (List Lexeme),
    (separated items).flatMap Lexeme.chars = [',', ' '].intercalate (items.map (·.flatMap Lexeme.chars))
  | [] => rfl
  | [single] => by simp [separated]
  | first :: second :: more => by
    rw [separated, List.flatMap_append, List.flatMap_append, separated_chars (second :: more)]
    simp [comma, space, Lexeme.chars, List.intercalate_cons_cons]

theorem intercalate_chars {α : Type} (print : α → String) (lexemesOf : α → List Lexeme)
    (same : ∀ item, (print item).toList = (lexemesOf item).flatMap Lexeme.chars) (items : List α) :
    (String.intercalate ", " (items.map print)).toList = (separated (items.map lexemesOf)).flatMap Lexeme.chars := by
  rw [String.toList_intercalate, separated_chars, List.map_map, List.map_map]
  have pointwise : (String.toList ∘ print) = ((fun lexemes => lexemes.flatMap Lexeme.chars) ∘ lexemesOf) :=
    funext fun item => same item
  rw [pointwise]
  rfl

theorem conjunction_chars {α : Type} (print : α → String) (lexemesOf : α → List Lexeme)
    (same : ∀ item, (print item).toList = (lexemesOf item).flatMap Lexeme.chars) (items : List α) :
    (CHRPrologPrinter.conjunction (items.map print)).toList =
      (conjunctionLexemes (items.map lexemesOf)).flatMap Lexeme.chars := by
  unfold CHRPrologPrinter.conjunction conjunctionLexemes
  by_cases empty : items = []
  · subst empty
    simp [bare_chars "true" (by decide)]
  · have printed : (items.map print).isEmpty = false := by simpa using empty
    have lexed : (items.map lexemesOf).isEmpty = false := by simpa using empty
    simp only [printed, lexed, Bool.false_eq_true, if_false]
    exact intercalate_chars print lexemesOf same items

theorem quoted_chars (text : String) : (CHRPrologPrinter.atom text).toList = (quoted text).chars := by
  unfold CHRPrologPrinter.atom
  simp only [String.toList_append, quoted, Lexeme.chars]
  simp only [String.toList_join, List.flatMap_map]
  rw [show "'".toList = ['\''] from rfl, List.singleton_append, List.cons_append]
  congr 2
  apply List.flatMap_congr
  intro character _
  unfold ReaderLexer.quotedChars
  split <;> (try split) <;> simp_all

theorem numeral_chars (number : Nat) : (numeral number).chars = (toString number).toList := by
  unfold numeral
  have listed : (toString number).toList = Nat.toDigits 10 number := Nat.toList_repr
  cases digits : (toString number).toList with
  | nil => rw [listed] at digits; exact absurd digits Nat.toDigits_ne_nil
  | cons first more => rfl

theorem integer_chars (number : Int) : (toString number).toList = (integer number).flatMap Lexeme.chars := by
  unfold integer
  cases number with
  | ofNat value =>
    have sign : (0 : Int) ≤ Int.ofNat value := Int.natCast_nonneg value
    simp only [sign, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [numeral_chars]
    rfl
  | negSucc value =>
    have sign : ¬ (0 : Int) ≤ Int.negSucc value := by omega
    simp only [sign, if_false, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [bare_chars "-" (by decide), numeral_chars]
    show ("-" ++ toString (value + 1)).toList = _
    rw [String.toList_append]
    rfl

theorem variable_chars (index : Nat) :
    (CHRPrologPrinter.variableName index).toList = (indexed index).chars := by
  simp [CHRPrologPrinter.variableName, indexed, Lexeme.chars]

theorem intercalate_single (text : String) : String.intercalate ", " [text] = text := rfl

mutual
  theorem value_chars : ∀ datum : CHR.Value,
      (CHRPrologPrinter.value datum).toList = (valueLexemes datum).flatMap Lexeme.chars
    | .integer number => by rw [CHRPrologPrinter.value, valueLexemes, integer_chars]
    | .atom name => by simp [CHRPrologPrinter.value, valueLexemes, quoted_chars]
    | .tuple fields => by
      rw [CHRPrologPrinter.value, valueLexemes]
      simp only [CHRPrologPrinter.arguments, String.toList_append, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [bare_chars "tuple" (by decide), values_chars fields]
      simp [openParen, closeParen, Lexeme.chars]
  theorem values_chars : ∀ data : List CHR.Value,
      (String.intercalate ", " (data.map CHRPrologPrinter.value)).toList =
        (separated (valuesLexemes data)).flatMap Lexeme.chars
    | [] => rfl
    | [single] => by
      rw [List.map_cons, List.map_nil, intercalate_single, valuesLexemes, valuesLexemes, separated, value_chars single]
    | first :: second :: more => by
      have unfolded : separated (valuesLexemes (first :: second :: more)) =
          valueLexemes first ++ [comma, space] ++ separated (valuesLexemes (second :: more)) := rfl
      rw [List.map_cons, List.map_cons, String.intercalate_cons_cons, ← List.map_cons, String.toList_append,
        String.toList_append, value_chars first, values_chars (second :: more), unfolded,
        List.flatMap_append, List.flatMap_append]
      rfl
end

#print axioms value_chars

mutual
  theorem term_chars : ∀ term : CHR.Term,
      (CHRPrologPrinter.term term).toList = (termLexemes term).flatMap Lexeme.chars
    | .value datum => by rw [CHRPrologPrinter.term, termLexemes, value_chars]
    | .var index => by simp [CHRPrologPrinter.term, termLexemes, variable_chars]
    | .tuple fields => by
      rw [CHRPrologPrinter.term, termLexemes]
      simp only [CHRPrologPrinter.arguments, String.toList_append, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [bare_chars "tuple" (by decide), terms_chars fields]
      simp [openParen, closeParen, Lexeme.chars]
  theorem terms_chars : ∀ terms : List CHR.Term,
      (String.intercalate ", " (terms.map CHRPrologPrinter.term)).toList =
        (separated (termsLexemes terms)).flatMap Lexeme.chars
    | [] => rfl
    | [single] => by
      rw [List.map_cons, List.map_nil, intercalate_single, termsLexemes, termsLexemes, separated, term_chars single]
    | first :: second :: more => by
      have unfolded : separated (termsLexemes (first :: second :: more)) =
          termLexemes first ++ [comma, space] ++ separated (termsLexemes (second :: more)) := rfl
      rw [List.map_cons, List.map_cons, String.intercalate_cons_cons, ← List.map_cons, String.toList_append,
        String.toList_append, term_chars first, terms_chars (second :: more), unfolded,
        List.flatMap_append, List.flatMap_append]
      rfl
end

theorem head_chars (head : CHR.Head) : (CHRPrologPrinter.head head).toList = (headLexemes head).flatMap Lexeme.chars := by
  unfold CHRPrologPrinter.head headLexemes
  by_cases empty : head.arguments.isEmpty
  · simp only [empty, if_true, String.toList_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      quoted_chars]
    simp
  · simp only [empty, if_false, Bool.false_eq_true, CHRPrologPrinter.arguments, String.toList_append,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, quoted_chars, terms_chars]
    simp [openParen, closeParen, Lexeme.chars]

theorem operator_chars (operator : CHR.IntOperator) :
    (CHRPrologPrinter.operator operator).toList = (bare (operatorName operator)).chars := by
  cases operator <;> rfl

theorem comparison_chars (comparison : CHR.Comparison) :
    (CHRPrologPrinter.comparison comparison).toList = (bare (comparisonName comparison)).chars := by
  cases comparison <;> rfl

theorem expression_chars : ∀ expression : CHR.IntExpr,
    (CHRPrologPrinter.expression expression).toList = (expressionLexemes expression).flatMap Lexeme.chars
  | .literal number => by rw [CHRPrologPrinter.expression, expressionLexemes, integer_chars]
  | .index index => by simp [CHRPrologPrinter.expression, expressionLexemes, variable_chars]
  | .operation operator left right => by
    rw [CHRPrologPrinter.expression, expressionLexemes]
    simp only [String.toList_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      expression_chars left, expression_chars right, operator_chars]
    simp [openParen, closeParen, space, Lexeme.chars, List.append_assoc]

theorem guard_chars (guard : CHR.Guard) :
    (CHRPrologPrinter.guard guard).toList = (guardLexemes guard).flatMap Lexeme.chars := by
  cases guard with
  | identical left right =>
    simp only [CHRPrologPrinter.guard, guardLexemes, String.toList_append, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, term_chars, bare_chars "==" (by decide)]
    simp [space, Lexeme.chars, List.append_assoc]
  | distinct left right =>
    simp only [CHRPrologPrinter.guard, guardLexemes, String.toList_append, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, term_chars, bare_chars "\\==" (by decide)]
    simp [space, Lexeme.chars, List.append_assoc]
  | compare comparison left right =>
    simp only [CHRPrologPrinter.guard, guardLexemes, String.toList_append, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, expression_chars, comparison_chars]
    simp [space, Lexeme.chars, List.append_assoc]

theorem goal_chars (goal : CHR.Goal) :
    (CHRPrologPrinter.goal goal).toList = (goalLexemes goal).flatMap Lexeme.chars := by
  cases goal with
  | tell head => rw [CHRPrologPrinter.goal, goalLexemes, head_chars]
  | assign index expression =>
    simp only [CHRPrologPrinter.goal, goalLexemes, String.toList_append, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, variable_chars, expression_chars, bare_chars "is" (by decide)]
    simp [space, Lexeme.chars, List.append_assoc]
  | fail => simp [CHRPrologPrinter.goal, goalLexemes, bare_chars "fail" (by decide)]

#print axioms goal_chars

theorem space_chars : space.chars = [' '] := rfl
theorem newline_chars : newline.chars = ['\n'] := rfl
theorem bar_chars : bar.chars = ['|'] := rfl
theorem stop_chars : Lexeme.fullStop.chars = ['.'] := rfl
theorem named_chars : (bare "@").chars = ['@'] := rfl
theorem propagate_chars : (bare "==>").chars = ['=', '=', '>'] := rfl
theorem simplify_chars : (bare "<=>").chars = ['<', '=', '>'] := rfl
theorem backslash_chars : (bare "\\").chars = ['\\'] := rfl

/-- The printer's text for a rule is the characters of its lexemes. -/
theorem rule_chars (rule : CHR.Rule) :
    (CHRPrologPrinter.rule rule).toList = (ruleLexemes rule).flatMap Lexeme.chars := by
  have kept := conjunction_chars CHRPrologPrinter.head headLexemes head_chars rule.kept
  have removed := conjunction_chars CHRPrologPrinter.head headLexemes head_chars rule.removed
  have guards := conjunction_chars CHRPrologPrinter.guard guardLexemes guard_chars rule.guards
  have body := conjunction_chars CHRPrologPrinter.goal goalLexemes goal_chars rule.body
  unfold CHRPrologPrinter.rule ruleLexemes headsLexemes arrowName rightLexemes
  by_cases removedEmpty : rule.removed.isEmpty <;> by_cases keptEmpty : rule.kept.isEmpty <;>
    by_cases guardsEmpty : rule.guards.isEmpty <;>
    simp only [removedEmpty, keptEmpty, guardsEmpty, if_true, if_false, Bool.false_eq_true, String.toList_append,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, quoted_chars, kept, removed, guards,
      body] <;>
    simp [space_chars, newline_chars, bar_chars, stop_chars, named_chars, propagate_chars, simplify_chars,
      backslash_chars, List.append_assoc]

#print axioms rule_chars

/-! ## The printed lexemes lex back -/

open private isIdentifierContinue fullStopFollows from Mettapedia.Logic.Prolog.ReaderLexer

/-- Every lexeme of the sequence reads, given the text after the sequence. -/
inductive ReadsBefore : List Lexeme → List Char → Prop
  | nil (text : List Char) : ReadsBefore [] text
  | cons {lexeme : Lexeme} {rest : List Lexeme} {text : List Char} :
      lexeme.Reads (rest.flatMap Lexeme.chars ++ text) → ReadsBefore rest text → ReadsBefore (lexeme :: rest) text

theorem ReadsBefore.append : ∀ {first second : List Lexeme} {text : List Char},
    ReadsBefore first (second.flatMap Lexeme.chars ++ text) → ReadsBefore second text →
      ReadsBefore (first ++ second) text
  | [], _, _, _, later => later
  | _ :: _, _, _, .cons reads rest, later =>
    .cons (by simpa [List.flatMap_append, List.append_assoc] using reads) (ReadsBefore.append rest later)

theorem allRead_of : ∀ {lexemes : List Lexeme}, ReadsBefore lexemes [] → ReaderLexer.AllRead lexemes
  | [], _ => .nil
  | _ :: _, .cons reads rest => .cons (by simpa using reads) (allRead_of rest)

/-- Text that may follow a printed item: nothing, a comma, a space, a closing
parenthesis, or a full stop not followed by a digit. -/
def Separates : List Char → Prop
  | [] => True
  | ',' :: _ => True
  | ' ' :: _ => True
  | ')' :: _ => True
  | '.' :: after => ∀ next, after.head? = some next → next.isDigit = false
  | _ => False

/-- The first character of a printed sequence is not layout. -/
def StartsSolid (lexemes : List Lexeme) : Prop :=
  ∃ first rest, lexemes.flatMap Lexeme.chars = first :: rest ∧ ReaderLexer.isLayout first = false

/-- A printed construct: its lexemes read before any separating text, and it
does not start with layout. -/
structure Printable (lexemes : List Lexeme) : Prop where
  reads : ∀ text, Separates text → ReadsBefore lexemes text
  solid : StartsSolid lexemes

theorem separates_cases {text : List Char} (separates : Separates text) :
    text = [] ∨ (∃ rest, text = ',' :: rest) ∨ (∃ rest, text = ' ' :: rest) ∨ (∃ rest, text = ')' :: rest) ∨
      (∃ after, text = '.' :: after ∧ ∀ next, after.head? = some next → next.isDigit = false) := by
  unfold Separates at separates
  split at separates
  · exact .inl rfl
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inr (.inr (.inl ⟨_, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨_, rfl⟩)))
  · exact .inr (.inr (.inr (.inr ⟨_, rfl, separates⟩)))
  · exact separates.elim

theorem separates_not_quote {text : List Char} (separates : Separates text) :
    ∀ next, text.head? = some next → next ≠ '\'' := by
  rcases separates_cases separates with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> simp

theorem separates_not_continue {text : List Char} (separates : Separates text) :
    ∀ next, text.head? = some next → isIdentifierContinue next = false := by
  rcases separates_cases separates with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;>
    simp [isIdentifierContinue] <;> decide

theorem separates_number {text : List Char} (separates : Separates text) : ReaderLexer.NumberStops text := by
  rcases separates_cases separates with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨after, rfl, stops⟩
  · trivial
  all_goals simp only [ReaderLexer.NumberStops]
  · exact ⟨fun same => absurd same (by decide), fun _ => ⟨by decide, by decide, by decide⟩⟩
  · exact ⟨fun same => absurd same (by decide), fun _ => ⟨by decide, by decide, by decide⟩⟩
  · exact ⟨fun same => absurd same (by decide), fun _ => ⟨by decide, by decide, by decide⟩⟩
  · exact ⟨fun _ => stops, fun different => absurd rfl different⟩

theorem quoted_printable (name : String) : Printable [quoted name] where
  reads text separates := .cons (by simpa [quoted, Lexeme.Reads] using separates_not_quote separates) (.nil text)
  solid := ⟨'\'', _, rfl, by decide⟩

theorem digits_continue {digits : List Char} (all : ∀ c ∈ digits, c.isDigit = true) :
    ∀ c ∈ digits, isIdentifierContinue c = true := by
  intro c inside
  simp [isIdentifierContinue, Char.isAlphanum, all c inside]

theorem toString_digits (number : Nat) : ∀ c ∈ (toString number).toList, c.isDigit = true := by
  show ∀ c ∈ (Nat.repr number).toList, c.isDigit = true
  rw [Nat.toList_repr]
  exact toDigits_digits number

theorem numeral_reads (number : Nat) (text : List Char) (stops : ReaderLexer.NumberStops text) :
    (numeral number).Reads text := by
  have digits := toString_digits number
  unfold numeral
  cases listed : (toString number).toList with
  | nil =>
    have := Nat.toList_repr (n := number)
    rw [show toString number = Nat.repr number from rfl] at listed
    rw [listed] at this
    exact absurd this.symm Nat.toDigits_ne_nil
  | cons first more =>
    rw [listed] at digits
    exact ⟨digits first List.mem_cons_self, fun c inside => digits c (List.mem_cons_of_mem _ inside), stops⟩

theorem numeral_starts (number : Nat) : ∃ first rest, (numeral number).chars = first :: rest ∧ first.isDigit = true := by
  rw [numeral_chars]
  have digits := toString_digits number
  cases listed : (toString number).toList with
  | nil =>
    have := Nat.toList_repr (n := number)
    rw [show toString number = Nat.repr number from rfl] at listed
    rw [listed] at this
    exact absurd this.symm Nat.toDigits_ne_nil
  | cons first rest =>
    rw [listed] at digits
    exact ⟨first, rest, rfl, digits first List.mem_cons_self⟩

theorem digit_solid {c : Char} (digit : c.isDigit = true) : ReaderLexer.isLayout c = false := by
  have bounds := digit_bounds digit
  have low : 48 ≤ c.toNat := bounds.1
  have high : c.toNat ≤ 57 := bounds.2
  unfold ReaderLexer.isLayout
  have notSpace : c ≠ ' ' := by rintro rfl; simp at low
  have notTab : c ≠ '\t' := by rintro rfl; simp at low
  have notReturn : c ≠ '\r' := by rintro rfl; simp at low
  have notNewline : c ≠ '\n' := by rintro rfl; simp at low
  have notVertical : c ≠ '\u000b' := by rintro rfl; simp at low
  have notForm : c ≠ '\u000c' := by rintro rfl; simp at low
  simp [notSpace, notTab, notReturn, notNewline, notVertical, notForm]

theorem digit_not_graphic {c : Char} (digit : c.isDigit = true) : ReaderLexer.isGraphic c = false := by
  have bounds := digit_bounds digit
  have low : 48 ≤ c.toNat := bounds.1
  have high : c.toNat ≤ 57 := bounds.2
  rw [ReaderLexer.isGraphic]
  apply Bool.eq_false_iff.mpr
  intro member
  simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at member
  obtain ⟨x, inside, same⟩ := member
  subst same
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp at low high

theorem integer_printable (number : Int) : Printable (integer number) := by
  unfold integer
  by_cases sign : 0 ≤ number
  · simp only [sign, if_true]
    refine ⟨fun text separates => .cons (by simpa using numeral_reads _ text (separates_number separates)) (.nil text), ?_⟩
    obtain ⟨first, rest, listed, digit⟩ := numeral_starts number.toNat
    exact ⟨first, rest, by simp [listed], digit_solid digit⟩
  · simp only [sign, if_false]
    obtain ⟨first, rest, listed, digit⟩ := numeral_starts number.natAbs
    refine ⟨fun text separates => .cons ?_ (.cons (by simpa using numeral_reads _ text (separates_number separates))
      (.nil text)), ⟨'-', _, rfl, by decide⟩⟩
    show (Lexeme.graphic '-' []).Reads _
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, listed]
    exact ⟨by decide, by decide, fun same => absurd same (by decide), by simp, fun next same => by
      simp at same; rw [← same]; exact digit_not_graphic digit⟩

#print axioms integer_printable

theorem space_reads (text : List Char) (solid : ∀ next, text.head? = some next → ReaderLexer.isLayout next = false) :
    space.Reads text := ⟨by decide, solid⟩

theorem solid_text {lexemes : List Lexeme} (solid : StartsSolid lexemes) (text : List Char) :
    ∀ next, (lexemes.flatMap Lexeme.chars ++ text).head? = some next → ReaderLexer.isLayout next = false := by
  obtain ⟨first, rest, listed, notSpace⟩ := solid
  intro next same
  rw [listed] at same
  simp at same
  rw [← same]
  exact notSpace

theorem solid_append {first : List Lexeme} (solid : StartsSolid first) (more : List Lexeme) :
    StartsSolid (first ++ more) := by
  obtain ⟨c, rest, listed, notSpace⟩ := solid
  exact ⟨c, rest ++ more.flatMap Lexeme.chars, by rw [List.flatMap_append, listed]; rfl, notSpace⟩

theorem separates_space (rest : List Char) : Separates (' ' :: rest) := trivial
theorem separates_comma (rest : List Char) : Separates (',' :: rest) := trivial
theorem separates_close (rest : List Char) : Separates (')' :: rest) := trivial

theorem printable_append_spaced {first second : List Lexeme} (lexeme : Lexeme)
    (firstPrintable : Printable first) (secondPrintable : Printable second)
    (lexemeReads : ∀ text, StartsSolid second → lexeme.Reads (space.chars ++ second.flatMap Lexeme.chars ++ text))
    (lexemeSolid : ∃ c rest, lexeme.chars = c :: rest ∧ ReaderLexer.isLayout c = false) :
    Printable (first ++ [space, lexeme, space] ++ second) where
  reads text separates := by
    rw [List.append_assoc]
    refine ReadsBefore.append (firstPrintable.reads _ (separates_space _)) ?_
    refine .cons (space_reads _ ?_) (.cons ?_ (.cons (space_reads _ ?_) (secondPrintable.reads text separates)))
    · obtain ⟨c, rest, listed, notSpace⟩ := lexemeSolid
      intro next same
      simp [listed] at same
      rw [← same]
      exact notSpace
    · simpa [List.append_assoc] using lexemeReads text secondPrintable.solid
    · simpa using solid_text secondPrintable.solid text
  solid := by
    rw [List.append_assoc]
    exact solid_append firstPrintable.solid _

theorem separated_printable : ∀ (items : List (List Lexeme)), items ≠ [] → (∀ item ∈ items, Printable item) →
    Printable (separated items)
  | [], nonempty, _ => absurd rfl nonempty
  | [single], _, printable => by simpa [separated] using printable single List.mem_cons_self
  | first :: second :: more, _, printable => by
    have firstPrintable := printable first List.mem_cons_self
    have restPrintable := separated_printable (second :: more) (by simp)
      (fun item inside => printable item (List.mem_cons_of_mem _ inside))
    refine ⟨fun text separates => ?_, ?_⟩
    · rw [separated, List.append_assoc]
      refine ReadsBefore.append (firstPrintable.reads _ (separates_comma _)) ?_
      exact .cons (by simp [comma, Lexeme.Reads])
        (.cons (space_reads _ (by simpa using solid_text restPrintable.solid text)) (restPrintable.reads text separates))
    · rw [separated, List.append_assoc]
      exact solid_append firstPrintable.solid _

/-- A name applied to an argument list. -/
theorem applied_printable (lexeme : Lexeme) (items : List (List Lexeme))
    (lexemeReads : ∀ text, lexeme.Reads ('(' :: text))
    (lexemeSolid : ∃ c rest, lexeme.chars = c :: rest ∧ ReaderLexer.isLayout c = false)
    (printable : ∀ item ∈ items, Printable item) :
    Printable ([lexeme, openParen] ++ separated items ++ [closeParen]) where
  reads text separates := by
    rw [List.append_assoc]
    show ReadsBefore (lexeme :: openParen :: (separated items ++ [closeParen])) text
    refine .cons (by simpa [openParen, Lexeme.chars, List.append_assoc] using lexemeReads _) ?_
    refine .cons (by simp [openParen, Lexeme.Reads]) ?_
    by_cases empty : items = []
    · subst empty
      show ReadsBefore [closeParen] text
      exact .cons (by simp [closeParen, Lexeme.Reads]) (.nil text)
    · exact ReadsBefore.append ((separated_printable items empty printable).reads _ (separates_close _))
        (.cons (by simp [closeParen, Lexeme.Reads]) (.nil text))
  solid := by
    obtain ⟨c, rest, listed, notSpace⟩ := lexemeSolid
    exact ⟨c, rest ++ (openParen :: (separated items ++ [closeParen])).flatMap Lexeme.chars,
      by simp [listed, List.flatMap_cons], notSpace⟩

theorem tuple_reads (text : List Char) : (bare "tuple").Reads ('(' :: text) :=
  ⟨by decide, by decide, fun next same => by simp at same; rw [← same]; decide⟩

theorem quoted_applied_reads (name : String) (text : List Char) : (quoted name).Reads ('(' :: text) :=
  fun next same => by simp at same; rw [← same]; decide

mutual
  theorem value_printable : ∀ datum : CHR.Value, Printable (valueLexemes datum)
    | .integer number => by rw [valueLexemes]; exact integer_printable number
    | .atom name => by rw [valueLexemes]; exact quoted_printable name
    | .tuple fields => by
      rw [valueLexemes]
      exact applied_printable _ _ tuple_reads ⟨'t', _, rfl, by decide⟩ (values_printable fields)
  theorem values_printable : ∀ data : List CHR.Value, ∀ item ∈ valuesLexemes data, Printable item
    | [], _, inside => by simp [valuesLexemes] at inside
    | first :: rest, item, inside => by
      rw [valuesLexemes] at inside
      rcases List.mem_cons.mp inside with same | later
      · rw [same]; exact value_printable first
      · exact values_printable rest item later
end

theorem indexed_printable (index : Nat) : Printable [indexed index] where
  reads text separates := .cons ⟨by decide, digits_continue (toString_digits index), separates_not_continue separates⟩
    (.nil text)
  solid := ⟨'V', (toString index).toList, by simp [indexed, Lexeme.chars], by decide⟩

mutual
  theorem term_printable : ∀ term : CHR.Term, Printable (termLexemes term)
    | .value datum => by rw [termLexemes]; exact value_printable datum
    | .var index => by rw [termLexemes]; exact indexed_printable index
    | .tuple fields => by
      rw [termLexemes]
      exact applied_printable _ _ tuple_reads ⟨'t', _, rfl, by decide⟩ (terms_printable fields)
  theorem terms_printable : ∀ terms : List CHR.Term, ∀ item ∈ termsLexemes terms, Printable item
    | [], _, inside => by simp [termsLexemes] at inside
    | first :: rest, item, inside => by
      rw [termsLexemes] at inside
      rcases List.mem_cons.mp inside with same | later
      · rw [same]; exact term_printable first
      · exact terms_printable rest item later
end

theorem head_printable (head : CHR.Head) : Printable (headLexemes head) := by
  unfold headLexemes
  by_cases empty : head.arguments.isEmpty
  · simp only [empty, if_true, List.append_nil]
    exact quoted_printable head.name
  · simp only [empty, if_false, Bool.false_eq_true]
    have shape : [quoted head.name] ++ ([openParen] ++ separated (termsLexemes head.arguments) ++ [closeParen]) =
        [quoted head.name, openParen] ++ separated (termsLexemes head.arguments) ++ [closeParen] := by simp
    rw [shape]
    exact applied_printable _ _ (quoted_applied_reads head.name) ⟨'\'', _, rfl, by decide⟩
      (terms_printable head.arguments)

#print axioms head_printable

theorem parenthesized_printable {inner : List Lexeme} (printable : Printable inner) :
    Printable ([openParen] ++ inner ++ [closeParen]) where
  reads text _ := by
    rw [List.append_assoc]
    show ReadsBefore (openParen :: (inner ++ [closeParen])) text
    exact .cons (by simp [openParen, Lexeme.Reads])
      (ReadsBefore.append (printable.reads _ (separates_close _)) (.cons (by simp [closeParen, Lexeme.Reads]) (.nil text)))
  solid := ⟨'(', (inner ++ [closeParen]).flatMap Lexeme.chars, by simp [openParen, Lexeme.chars], by decide⟩

theorem graphic_reads_space (first : Char) (more rest : List Char) (graphic : ReaderLexer.isGraphic first = true)
    (notDot : first ≠ '.') (notComment : first = '/' → (more ++ ' ' :: rest).head? ≠ some '*')
    (graphics : ∀ c ∈ more, ReaderLexer.isGraphic c = true) : (Lexeme.graphic first more).Reads (' ' :: rest) :=
  ⟨graphic, notDot, notComment, graphics, fun next same => by simp at same; rw [← same]; decide⟩

theorem word_reads_space (first : Char) (more rest : List Char) (alpha : first.isAlpha = true)
    (continues : ∀ c ∈ more, isIdentifierContinue c = true) : (Lexeme.identifier first more).Reads (' ' :: rest) :=
  ⟨alpha, continues, fun next same => by simp at same; rw [← same]; decide⟩

theorem spaced_reads {name : String} (reads : ∀ rest, (bare name).Reads (' ' :: rest)) :
    ∀ (second : List Lexeme) (text : List Char), StartsSolid second →
      (bare name).Reads (space.chars ++ second.flatMap Lexeme.chars ++ text) :=
  fun second text _ => by simpa [space, Lexeme.chars, List.append_assoc] using reads (second.flatMap Lexeme.chars ++ text)

theorem bare_graphic (text : String) (first : Char) (more : List Char) (spelled : text.toList = first :: more)
    (notAlpha : first.isAlpha = false) : bare text = .graphic first more := by
  unfold bare
  rw [spelled]
  simp [notAlpha]

theorem bare_word (text : String) (first : Char) (more : List Char) (spelled : text.toList = first :: more)
    (alpha : first.isAlpha = true) : bare text = .identifier first more := by
  unfold bare
  rw [spelled]
  simp [alpha]

theorem operator_reads (operator : CHR.IntOperator) (rest : List Char) :
    (bare (operatorName operator)).Reads (' ' :: rest) := by
  cases operator
  · exact graphic_reads_space '+' [] rest (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)
  · exact graphic_reads_space '-' [] rest (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)
  · exact graphic_reads_space '*' [] rest (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)
  · exact graphic_reads_space '/' ['/'] rest (by decide) (by decide) (fun _ => by simp) (by simp; decide)
  · exact word_reads_space 'r' ['e', 'm'] rest (by decide) (by simp [isIdentifierContinue])
  · exact word_reads_space 'm' ['o', 'd'] rest (by decide) (by simp [isIdentifierContinue])

theorem operator_solid (operator : CHR.IntOperator) :
    ∃ c rest, (bare (operatorName operator)).chars = c :: rest ∧ ReaderLexer.isLayout c = false := by
  cases operator <;> exact ⟨_, _, rfl, by decide⟩

theorem comparison_reads (comparison : CHR.Comparison) (rest : List Char) :
    (bare (comparisonName comparison)).Reads (' ' :: rest) := by
  cases comparison
  · exact graphic_reads_space '=' [':', '='] rest (by decide) (by decide) (fun same => absurd same (by decide))
      (by simp; decide)
  · exact graphic_reads_space '=' ['\\', '='] rest (by decide) (by decide) (fun same => absurd same (by decide))
      (by simp; decide)
  · exact graphic_reads_space '<' [] rest (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)
  · exact graphic_reads_space '=' ['<'] rest (by decide) (by decide) (fun same => absurd same (by decide))
      (by simp; decide)
  · exact graphic_reads_space '>' [] rest (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)
  · exact graphic_reads_space '>' ['='] rest (by decide) (by decide) (fun same => absurd same (by decide))
      (by simp; decide)

theorem comparison_solid (comparison : CHR.Comparison) :
    ∃ c rest, (bare (comparisonName comparison)).chars = c :: rest ∧ ReaderLexer.isLayout c = false := by
  cases comparison <;> exact ⟨_, _, rfl, by decide⟩

theorem expression_printable : ∀ expression : CHR.IntExpr, Printable (expressionLexemes expression)
  | .literal number => by rw [expressionLexemes]; exact integer_printable number
  | .index index => by rw [expressionLexemes]; exact indexed_printable index
  | .operation operator left right => by
    rw [expressionLexemes]
    have inner := printable_append_spaced (bare (operatorName operator)) (expression_printable left)
      (expression_printable right) (spaced_reads (operator_reads operator) _) (operator_solid operator)
    have shape : [openParen] ++ expressionLexemes left ++ [space, bare (operatorName operator), space] ++
        expressionLexemes right ++ [closeParen] =
        [openParen] ++ (expressionLexemes left ++ [space, bare (operatorName operator), space] ++
          expressionLexemes right) ++ [closeParen] := by simp
    rw [shape]
    exact parenthesized_printable inner

theorem identical_reads (rest : List Char) : (bare "==").Reads (' ' :: rest) := by
  rw [bare_graphic "==" '=' ['='] rfl (by decide)]
  exact graphic_reads_space '=' ['='] rest (by decide) (by decide) (fun same => absurd same (by decide))
    (by simp; decide)

theorem distinct_reads (rest : List Char) : (bare "\\==").Reads (' ' :: rest) := by
  rw [bare_graphic "\\==" '\\' ['=', '='] rfl (by decide)]
  exact graphic_reads_space '\\' ['=', '='] rest (by decide) (by decide) (fun same => absurd same (by decide))
    (by simp; decide)

theorem is_reads (rest : List Char) : (bare "is").Reads (' ' :: rest) := by
  rw [bare_word "is" 'i' ['s'] rfl (by decide)]
  exact word_reads_space 'i' ['s'] rest (by decide) (by simp [isIdentifierContinue])

theorem guard_printable (guard : CHR.Guard) : Printable (guardLexemes guard) := by
  cases guard with
  | identical left right =>
    exact printable_append_spaced (bare "==") (term_printable left) (term_printable right)
      (spaced_reads identical_reads _) ⟨_, _, rfl, by decide⟩
  | distinct left right =>
    exact printable_append_spaced (bare "\\==") (term_printable left) (term_printable right)
      (spaced_reads distinct_reads _) ⟨_, _, rfl, by decide⟩
  | compare comparison left right =>
    exact printable_append_spaced (bare (comparisonName comparison)) (expression_printable left)
      (expression_printable right) (spaced_reads (comparison_reads comparison) _) (comparison_solid comparison)

theorem word_printable (text : String) (first : Char) (more : List Char) (spelled : text.toList = first :: more)
    (alpha : first.isAlpha = true) (continues : ∀ c ∈ more, isIdentifierContinue c = true) :
    Printable [bare text] where
  reads text' separates := by
    rw [bare_word text first more spelled alpha]
    exact .cons ⟨alpha, continues, by simpa using separates_not_continue separates⟩ (.nil text')
  solid := by
    refine ⟨first, more, by rw [bare_word text first more spelled alpha]; simp [Lexeme.chars], ?_⟩
    unfold Char.isAlpha Char.isUpper Char.isLower at alpha
    unfold ReaderLexer.isLayout
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at alpha
    have notSpace : first ≠ ' ' := by rintro rfl; simp at alpha
    have notTab : first ≠ '\t' := by rintro rfl; simp at alpha
    have notReturn : first ≠ '\r' := by rintro rfl; simp at alpha
    have notNewline : first ≠ '\n' := by rintro rfl; simp at alpha
    have notVertical : first ≠ '\u000b' := by rintro rfl; simp at alpha
    have notForm : first ≠ '\u000c' := by rintro rfl; simp at alpha
    simp [notSpace, notTab, notReturn, notNewline, notVertical, notForm]

theorem goal_printable (goal : CHR.Goal) : Printable (goalLexemes goal) := by
  cases goal with
  | tell head => rw [goalLexemes]; exact head_printable head
  | assign index expression =>
    rw [goalLexemes]
    exact printable_append_spaced (bare "is") (indexed_printable index) (expression_printable expression)
      (spaced_reads is_reads _) ⟨_, _, rfl, by decide⟩
  | fail =>
    rw [goalLexemes]
    exact word_printable "fail" 'f' ['a', 'i', 'l'] rfl (by decide) (by simp [isIdentifierContinue])

theorem conjunction_printable (items : List (List Lexeme)) (printable : ∀ item ∈ items, Printable item) :
    Printable (conjunctionLexemes items) := by
  unfold conjunctionLexemes
  by_cases empty : items = []
  · subst empty
    exact word_printable "true" 't' ['r', 'u', 'e'] rfl (by decide) (by simp [isIdentifierContinue])
  · have mapped : items.isEmpty = false := by simpa using empty
    simp only [mapped, Bool.false_eq_true, if_false]
    exact separated_printable items empty printable

#print axioms conjunction_printable

theorem backslash_reads (rest : List Char) : (bare "\\").Reads (' ' :: rest) := by
  rw [bare_graphic "\\" '\\' [] rfl (by decide)]
  exact graphic_reads_space '\\' [] rest (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)

theorem arrow_reads_space (rule : CHR.Rule) (rest : List Char) : (bare (arrowName rule)).Reads (' ' :: rest) := by
  unfold arrowName
  split
  · rw [bare_graphic "==>" '=' ['=', '>'] rfl (by decide)]
    exact graphic_reads_space '=' ['=', '>'] rest (by decide) (by decide) (fun same => absurd same (by decide))
      (by simp; decide)
  · rw [bare_graphic "<=>" '<' ['=', '>'] rfl (by decide)]
    exact graphic_reads_space '<' ['=', '>'] rest (by decide) (by decide) (fun same => absurd same (by decide))
      (by simp; decide)

theorem arrow_solid (rule : CHR.Rule) :
    ∃ c rest, (bare (arrowName rule)).chars = c :: rest ∧ ReaderLexer.isLayout c = false := by
  unfold arrowName
  split <;> exact ⟨_, _, rfl, by decide⟩

theorem heads_printable (rule : CHR.Rule) : Printable (headsLexemes rule) := by
  have items : ∀ heads : List CHR.Head, ∀ item ∈ heads.map headLexemes, Printable item := by
    intro heads item inside
    obtain ⟨head, _, rfl⟩ := List.mem_map.mp inside
    exact head_printable head
  have kept := conjunction_printable _ (items rule.kept)
  have removed := conjunction_printable _ (items rule.removed)
  unfold headsLexemes
  split
  · exact kept
  · split
    · exact removed
    · exact printable_append_spaced (bare "\\") kept removed (spaced_reads backslash_reads _) ⟨_, _, rfl, by decide⟩

theorem right_printable (rule : CHR.Rule) : Printable (rightLexemes rule) := by
  have guards := conjunction_printable (rule.guards.map guardLexemes) (by
    intro item inside
    obtain ⟨guard, _, rfl⟩ := List.mem_map.mp inside
    exact guard_printable guard)
  have body := conjunction_printable (rule.body.map goalLexemes) (by
    intro item inside
    obtain ⟨goal, _, rfl⟩ := List.mem_map.mp inside
    exact goal_printable goal)
  unfold rightLexemes
  split
  · simpa using body
  · rw [List.append_assoc]
    have joined := printable_append_spaced bar guards body (fun text _ => by simp [bar, Lexeme.Reads])
      ⟨'|', [], rfl, by decide⟩
    simpa [List.append_assoc] using joined

theorem rule_reads_before (rule : CHR.Rule) : ReadsBefore (ruleLexemes rule) [] := by
  have inner := printable_append_spaced (bare (arrowName rule)) (heads_printable rule) (right_printable rule)
    (spaced_reads (arrow_reads_space rule) _) (arrow_solid rule)
  have shape : ruleLexemes rule = quoted rule.name :: space :: bare "@" :: space ::
      ((headsLexemes rule ++ [space, bare (arrowName rule), space] ++ rightLexemes rule) ++ [.fullStop, newline]) := by
    simp [ruleLexemes, List.append_assoc]
  rw [shape]
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (ReadsBefore.append (inner.reads _ ?_)
    (.cons ?_ (.cons ?_ (.nil [])))))))
  · intro next same
    simp [space, Lexeme.chars] at same
    rw [← same]
    decide
  · refine space_reads _ fun next same => ?_
    simp [named_chars] at same
    rw [← same]
    decide
  · rw [bare_graphic "@" '@' [] rfl (by decide)]
    simp only [List.flatMap_cons, space_chars, List.cons_append]
    exact graphic_reads_space '@' [] _ (by decide) (by decide) (fun same => absurd same (by decide)) (by simp)
  · have solid := solid_text inner.solid ([Lexeme.fullStop, newline].flatMap Lexeme.chars)
    refine space_reads _ ?_
    rw [List.flatMap_append, List.append_nil]
    exact solid
  · show Separates ('.' :: '\n' :: [])
    intro next same
    simp at same
    rw [← same]
    decide
  · show fullStopFollows ('\n' :: []) = true
    decide
  · exact ⟨by decide, fun next same => by simp at same⟩

theorem rule_text (rule : CHR.Rule) :
    CHRPrologPrinter.rule rule = String.ofList ((ruleLexemes rule).flatMap Lexeme.chars) := by
  apply String.toList_inj.mp
  rw [String.toList_ofList, rule_chars]

/-- **A printed rule reads back through the reference reader.** -/
theorem rule_reads_back (rule : CHR.Rule) (heads : rule.kept ++ rule.removed ≠ []) :
    ∃ bindings, ReaderTerm.readOneWith chr chr.operators (CHRPrologPrinter.rule rule) =
      .ok ⟨ruleSource (nameIn (ruleVariables rule)) rule, bindings, []⟩ := by
  obtain ⟨bindings, parsed⟩ := rule_parses rule heads ReaderLexer.Position.initial
  refine ⟨bindings, ?_⟩
  unfold ReaderTerm.readOneWith
  rw [rule_text, ReaderLexer.scan_lexemes _ (allRead_of (rule_reads_before rule))]
  simp only [parsed, bind, Except.bind]
  rfl

open Mettapedia.Languages.CHR.TupleNormal (normalRule)

/-- **Printed rules read back as their IR in tuple normal form.** -/
theorem rule_reads_and_lowers (rule : CHR.Rule) (printable : CHRPrologReadback.RulePrintable rule) (ordinal : Nat) :
    ∃ result, ReaderTerm.readOneWith chr chr.operators (CHRPrologPrinter.rule rule) = .ok result ∧
      CHRPrologLowering.form ordinal result.term = .ok (.rule (normalRule rule)) := by
  obtain ⟨bindings, read⟩ := rule_reads_back rule printable.heads
  exact ⟨_, read, CHRPrologReadback.rule_form (nameIn (ruleVariables rule)) (fun _ => rfl) ordinal rule printable⟩

#print axioms rule_reads_back
#print axioms rule_reads_and_lowers

/-! ## Directives -/

/-- The library directive reads as its source. -/
theorem library_reads :
    (ReaderTerm.readOneWith chr chr.operators ":- use_module(library(chr)).\n").map (·.term) =
      .ok CHRPrologReadback.libraryDirective := by
  decide_cbv

/-- The profile directive reads as its source. -/
theorem option_reads :
    (ReaderTerm.readOneWith chr chr.operators ":- chr_option(optimize,off).\n").map (·.term) =
      .ok CHRPrologReadback.optionDirective := by
  decide_cbv

#print axioms library_reads
#print axioms option_reads

/-! ## Prefix operators -/

theorem prefix_operator (fuel maximum : Nat) (state : State) (name : String) (span : ReaderLexer.Span)
    (next : Token) (rest : List Token) (declaration : Declaration)
    (remaining : state.remaining = ⟨.atom name, span⟩ :: next :: rest)
    (notApplied : next.kind ≠ .punctuation .leftParen) (notNumber : ∀ lexeme, next.kind ≠ .number lexeme)
    (starts : tokenStartsTerm next.kind = true)
    (found : firstEligiblePrefix chr.operators name maximum = some declaration) :
    parsePrefixOrPrimaryAux chr (fuel + 1) chr.operators maximum state =
      parsePrefixAux chr fuel chr.operators maximum state name := by
  conv_lhs => unfold parsePrefixOrPrimaryAux
  rw [remaining]
  rcases next with ⟨kind, nextSpan⟩
  simp only at notApplied notNumber starts
  split
  · rename_i heq
    simp at heq
  · rename_i heq
    simp only [List.cons.injEq, Token.mk.injEq] at heq
    exact absurd heq.2.1.1 (notNumber _)
  · rename_i heq
    simp only [List.cons.injEq, Token.mk.injEq, Kind.atom.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := heq
    cases kind with
    | punctuation punctuation =>
      cases punctuation
      · exact absurd rfl notApplied
      all_goals simp_all [tokenStartsTerm]
    | number lexeme => exact absurd rfl (notNumber lexeme)
    | _ => simp_all [tokenStartsTerm]
  · rename_i heq
    simp at heq
  · rename_i heq
    simp at heq
  · rename_i _ notAtom _ _
    exfalso
    exact notAtom name span ⟨kind, nextSpan⟩ rest rfl

theorem prefix_aux (fuel maximum : Nat) (state : State) (name : String) (operator : Token) (rest : List Token)
    (declaration : Declaration) (rightMaximum : Nat) (remaining : state.remaining = operator :: rest)
    (found : firstEligiblePrefix chr.operators name maximum = some declaration)
    (bounded : declaration.specifier.rightMaximum declaration.priority.value = some rightMaximum) :
    parsePrefixAux chr fuel chr.operators maximum state name = (do
      let right ← parseExpressionAux chr fuel chr.operators rightMaximum { state with remaining := rest }
      pure (⟨SourceSignature.compound name [right.term], declaration.priority.value, right.state⟩ : Parsed)) := by
  unfold parsePrefixAux
  simp only [found, remaining, List.drop_succ_cons, List.drop_zero, bind, Except.bind, pure, Except.pure]
  simp only [bounded]

theorem prefix_query :
    firstEligiblePrefix chr.operators "?-" 1200 = some ⟨"?-", ⟨1200, by decide, by decide⟩, .fx⟩ := by decide

theorem prefix_directive :
    firstEligiblePrefix chr.operators ":-" 1200 = some ⟨":-", ⟨1200, by decide, by decide⟩, .fx⟩ := by decide

theorem prefix_declaration :
    firstEligiblePrefix chr.operators "chr_constraint" 1199 =
      some ⟨"chr_constraint", ⟨1150, by decide, by decide⟩, .fx⟩ := by decide

#print axioms prefix_operator

/-! ## Declarations -/

open CHRPrologReadback (declarationSource declarationsSource constraintSource querySource)

def declarationLexemes (declaration : CHR.Declaration) : List Lexeme :=
  [quoted declaration.name, bare "/", numeral declaration.arity]

theorem slash_kind : (bare "/").kind? = some (.atom "/") := bare_kind "/" '/' [] rfl rfl (by decide)

theorem slash_continues (maximum : Nat) (level : 400 ≤ maximum) :
    firstEligibleInfix chr.operators "/" maximum 0 = some ⟨"/", ⟨400, by decide, by decide⟩, .yfx⟩ := by
  simp [firstEligibleInfix, infixes_slash, eligible, Specifier.leftMaximum]
  omega

theorem declaration_item (declaration : CHR.Declaration) :
    ItemReads [] 400 (declarationLexemes declaration) (declarationSource declaration) 400 2 [] := by
  intro fuel maximum seen position token rest level closes prefixed enough
  have empty : seen = [] := by simpa using List.eq_nil_of_prefix_nil prefixed
  subst empty
  simp only [declarationLexemes, tokensOf_kind _ _ (quoted_kind declaration.name), tokensOf_kind _ _ slash_kind,
    tokensOf_kind _ _ (numeral_kind declaration.arity), tokensOf_nil, List.cons_append, List.nil_append] at enough ⊢
  obtain ⟨a, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
  rw [expression_step]
  obtain ⟨b, rfl⟩ : ∃ smaller, a = smaller + 1 := ⟨a - 1, by simp at enough; omega⟩
  rw [prefix_quoted b maximum _ declaration.name _ _ rfl]
  obtain ⟨c, rfl⟩ : ∃ smaller, b = smaller + 1 := ⟨b - 1, by simp at enough; omega⟩
  rw [primary_word c _ _ _ declaration.name _ rfl (.inr rfl) (by intro paren tail same; cases same; simp)]
  simp only [bind, Except.bind]
  rw [tail_infix (c + 1) maximum _ _ _ _ "/" _ 399 rfl rfl (slash_continues maximum (by omega)) rfl rfl]
  rw [expression_step]
  obtain ⟨d, rfl⟩ : ∃ smaller, c = smaller + 1 := ⟨c - 1, by simp at enough; omega⟩
  rw [prefix_other d 399 _ _ _ rfl (by simp) (by simp)]
  obtain ⟨e, rfl⟩ : ∃ smaller, d = smaller + 1 := ⟨d - 1, by simp at enough; omega⟩
  rw [primary_number e _ _ _ _ _ rfl (numeric_allowed _) (parse_toString _)]
  simp only [bind, Except.bind]
  rw [tail_closes_low (e + 1) 399 _ token rest rfl closes (by decide)]
  simp only [declarationSource, SourceSignature.integer]
  rw [show e + 1 + 1 + 1 + 1 + 1 - 2 = e + 1 + 1 + 1 from by omega]
  rfl

theorem declaration_starts (declaration : CHR.Declaration) : StartsTerm (declarationLexemes declaration) := by
  intro position
  rw [declarationLexemes, tokensOf_kind _ _ (quoted_kind declaration.name)]
  exact ⟨_, _, rfl, rfl⟩

theorem declaration_shallow (declaration : CHR.Declaration) (position : Position) :
    2 ≤ (tokensOf (declarationLexemes declaration) position).length := by
  simp [declarationLexemes, tokensOf_kind _ _ (quoted_kind declaration.name), tokensOf_kind _ _ slash_kind,
    tokensOf_kind _ _ (numeral_kind declaration.arity)]

theorem flatMap_nothing {α β : Type} : ∀ items : List α, items.flatMap (fun _ => ([] : List β)) = []
  | [] => rfl
  | _ :: rest => by simp [flatMap_nothing rest]

def declarationsLexemes (declarations : List CHR.Declaration) : List Lexeme :=
  [bare ":-", space, bare "chr_constraint", space] ++ separated (declarations.map declarationLexemes) ++
    [.fullStop, newline]

theorem directive_kind : (bare ":-").kind? = some (.atom ":-") := bare_kind ":-" ':' ['-'] rfl rfl (by decide)
theorem constraint_word_kind : (bare "chr_constraint").kind? = some (.atom "chr_constraint") :=
  bare_kind "chr_constraint" 'c' "hr_constraint".toList rfl rfl (by decide)

theorem declarations_expression (declarations : List CHR.Declaration) (nonempty : declarations ≠ [])
    (directiveSpan wordSpan stopSpan : ReaderLexer.Span) (itemsPosition : Position) (fuel : Nat)
    (enough : 3 * (tokensOf (separated (declarations.map declarationLexemes)) itemsPosition ++
      [(⟨.punctuation .fullStop, stopSpan⟩ : Token)]).length + 12 ≤ fuel) :
    parseExpressionAux chr fuel chr.operators 1200
        (readerState ((⟨.atom ":-", directiveSpan⟩ : Token) :: ⟨.atom "chr_constraint", wordSpan⟩ ::
          (tokensOf (separated (declarations.map declarationLexemes)) itemsPosition ++
            [⟨.punctuation .fullStop, stopSpan⟩])) []) =
      .ok ⟨declarationsSource declarations, 1200, readerState [⟨.punctuation .fullStop, stopSpan⟩] []⟩ := by
  obtain ⟨declaration, more, rfl⟩ : ∃ first rest, declarations = first :: rest := by
    cases declarations with
    | nil => exact absurd rfl nonempty
    | cons first rest => exact ⟨first, rest, rfl⟩
  obtain ⟨first, tail, listed, starts⟩ := separated_starts (declarationLexemes declaration)
    (more.map declarationLexemes) itemsPosition (declaration_starts declaration)
  have firstKind : first.kind = .quotedAtom declaration.name := by
    have shape : separated (declarationLexemes declaration :: List.map declarationLexemes more) =
        declarationLexemes declaration ++ (if more.isEmpty then [] else [comma, space] ++
          separated (more.map declarationLexemes)) := by cases more <;> rfl
    rw [shape, tokensOf_append, declarationLexemes, tokensOf_kind _ _ (quoted_kind declaration.name),
      List.cons_append] at listed
    rw [← (List.cons.inj listed).1]
  rw [List.map_cons] at enough ⊢
  rw [listed] at enough ⊢
  simp only [List.cons_append] at enough ⊢
  obtain ⟨f, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [expression_step]
  obtain ⟨g, rfl⟩ : ∃ smaller, f = smaller + 1 := ⟨f - 1, by omega⟩
  rw [prefix_operator g 1200 _ ":-" directiveSpan _ _ _ rfl (by simp) (by simp) rfl prefix_directive,
    prefix_aux g 1200 _ ":-" _ _ _ 1199 rfl prefix_directive rfl]
  obtain ⟨h, rfl⟩ : ∃ smaller, g = smaller + 1 := ⟨g - 1, by omega⟩
  rw [expression_step]
  obtain ⟨i, rfl⟩ : ∃ smaller, h = smaller + 1 := ⟨h - 1, by omega⟩
  rw [prefix_operator i 1199 _ "chr_constraint" wordSpan first _ _ rfl (by rw [firstKind]; simp)
    (by rw [firstKind]; simp) starts prefix_declaration,
    prefix_aux i 1199 _ "chr_constraint" _ _ _ 1149 rfl prefix_declaration rfl]
  rw [← List.cons_append, ← listed]
  obtain ⟨spent, precedence, bound, _, inner⟩ := conjunction_reads [] declarationLexemes declarationSource
    (fun _ => 400) (fun _ => 2) (fun _ => []) (fun item => (declaration_item item).mono (by decide))
    (fun _ => by decide) declaration_shallow declaration_starts (declaration :: more) i 1149 [] itemsPosition
    ⟨.punctuation .fullStop, stopSpan⟩ [] (by simp) (by decide) (.inr (.inr (.inl rfl))) (by simp) (by simp)
    (by rw [List.map_cons, listed]; simp at enough ⊢; omega)
  rw [List.map_cons] at inner bound
  erw [inner]
  obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, i - spent = smaller + 1 := ⟨i - spent - 1, by
    rw [listed] at bound; simp at enough bound; omega⟩
  rw [stopEq, tail_full_stop stopFuel 1149 _ stopSpan [] rfl]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [tail_full_stop i 1199 _ stopSpan [] rfl]
  simp only
  rw [tail_full_stop (i + 1 + 1) 1200 _ stopSpan [] rfl]
  simp only [flatMap_nothing, List.append_nil]
  rfl

/-! ## Queries -/

def constraintLexemes (constraint : CHR.Constraint) : List Lexeme :=
  [quoted constraint.name] ++ if constraint.arguments.isEmpty then [] else
    [openParen] ++ separated (valuesLexemes constraint.arguments) ++ [closeParen]

theorem constraint_primary (constraint : CHR.Constraint) :
    PrimaryReads [] (constraintLexemes constraint) (constraintSource constraint) [] := by
  intro fuel maximum seen position rest prefixed noParen enough
  have empty : seen = [] := by simpa using List.eq_nil_of_prefix_nil prefixed
  subst empty
  unfold constraintLexemes at enough ⊢
  by_cases bare : constraint.arguments.isEmpty
  · have none : constraint.arguments = [] := List.isEmpty_iff.mp bare
    simp only [bare, if_true, List.append_nil, tokensOf_kind _ _ (quoted_kind constraint.name), tokensOf_nil,
      List.cons_append, List.nil_append] at enough ⊢
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    rw [prefix_quoted fuel maximum _ constraint.name _ rest rfl]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [primary_word fuel _ _ _ constraint.name rest rfl (.inr rfl) noParen]
    simp only [constraintSource, bare, if_true]
    rfl
  · have nonempty : constraint.arguments ≠ [] := by simpa using bare
    simp only [bare, if_false, Bool.false_eq_true] at enough ⊢
    have shape : ([quoted constraint.name] ++ ([openParen] ++ separated (valuesLexemes constraint.arguments) ++
        [closeParen])) = [quoted constraint.name, openParen] ++ separated (valuesLexemes constraint.arguments) ++
        [closeParen] := by simp
    rw [shape, applied_tokens _ _ (quoted_kind constraint.name)] at enough ⊢
    simp only [List.cons_append] at enough ⊢
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
    rw [prefix_quoted fuel maximum _ constraint.name _ _ rfl]
    obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by simp at enough; omega⟩
    rw [primary_applied fuel _ _ _ constraint.name _ _ rfl (.inr rfl) rfl (touching _ _ _ _ _)]
    obtain ⟨first, tail, listed, notClose⟩ := values_first constraint.arguments
      ((position.advanceMany (quoted constraint.name).chars).advanceMany openParen.chars) nonempty
    rw [application_arguments fuel _ constraint.name (by
      intro token more same
      rw [listed, List.cons_append, List.cons_append, List.cons.injEq] at same
      rw [← same.1]
      exact notClose)]
    rw [List.append_assoc, List.singleton_append]
    erw [values_read constraint.arguments fuel (readerState rest []) _ _ rest nonempty (by simp at enough ⊢; omega)]
    simp only [bind, Except.bind]
    rw [consume_close _ _ rest rfl]
    simp only [constraintSource, bare, if_false, Bool.false_eq_true, List.append_nil]
    rfl

theorem constraint_starts (constraint : CHR.Constraint) : StartsTerm (constraintLexemes constraint) := by
  intro position
  rw [constraintLexemes, List.singleton_append, tokensOf_kind _ _ (quoted_kind constraint.name)]
  exact ⟨_, _, rfl, rfl⟩

theorem constraint_shallow (constraint : CHR.Constraint) (position : Position) :
    1 ≤ (tokensOf (constraintLexemes constraint) position).length := by
  obtain ⟨token, tail, listed, _⟩ := constraint_starts constraint position
  rw [listed]
  simp

def queryLexemes (inputs : List CHR.Constraint) : List Lexeme :=
  [bare "?-", space] ++ separated (inputs.map constraintLexemes) ++ [.fullStop, newline]

theorem query_kind : (bare "?-").kind? = some (.atom "?-") := bare_kind "?-" '?' ['-'] rfl rfl (by decide)

theorem query_expression (inputs : List CHR.Constraint) (nonempty : inputs ≠ [])
    (querySpan stopSpan : ReaderLexer.Span) (itemsPosition : Position) (fuel : Nat)
    (enough : 3 * (tokensOf (separated (inputs.map constraintLexemes)) itemsPosition ++
      [(⟨.punctuation .fullStop, stopSpan⟩ : Token)]).length + 12 ≤ fuel) :
    parseExpressionAux chr fuel chr.operators 1200
        (readerState ((⟨.atom "?-", querySpan⟩ : Token) ::
          (tokensOf (separated (inputs.map constraintLexemes)) itemsPosition ++
            [⟨.punctuation .fullStop, stopSpan⟩])) []) =
      .ok ⟨querySource inputs, 1200, readerState [⟨.punctuation .fullStop, stopSpan⟩] []⟩ := by
  obtain ⟨input, more, rfl⟩ : ∃ first rest, inputs = first :: rest := by
    cases inputs with
    | nil => exact absurd rfl nonempty
    | cons first rest => exact ⟨first, rest, rfl⟩
  obtain ⟨first, tail, listed, starts⟩ := separated_starts (constraintLexemes input)
    (more.map constraintLexemes) itemsPosition (constraint_starts input)
  have firstKind : first.kind = .quotedAtom input.name := by
    have shape : separated (constraintLexemes input :: List.map constraintLexemes more) =
        constraintLexemes input ++ (if more.isEmpty then [] else [comma, space] ++
          separated (more.map constraintLexemes)) := by
      cases more with
      | nil => simp [separated]
      | cons next rest => simp [separated, List.append_assoc]
    rw [shape, tokensOf_append, constraintLexemes, List.singleton_append, tokensOf_kind _ _ (quoted_kind input.name),
      List.cons_append] at listed
    rw [← (List.cons.inj listed).1]
  rw [List.map_cons] at enough ⊢
  rw [listed] at enough ⊢
  simp only [List.cons_append] at enough ⊢
  obtain ⟨f, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  rw [expression_step]
  obtain ⟨g, rfl⟩ : ∃ smaller, f = smaller + 1 := ⟨f - 1, by omega⟩
  rw [prefix_operator g 1200 _ "?-" querySpan first _ _ rfl (by rw [firstKind]; simp) (by rw [firstKind]; simp)
    starts prefix_query, prefix_aux g 1200 _ "?-" _ _ _ 1199 rfl prefix_query rfl]
  rw [← List.cons_append, ← listed]
  obtain ⟨spent, precedence, bound, _, inner⟩ := conjunction_reads [] constraintLexemes constraintSource
    (fun _ => 0) (fun _ => 1) (fun _ => []) (fun item => (primary_item [] _ _ _ (constraint_primary item)).mono
      (by decide)) (fun _ => by decide) constraint_shallow constraint_starts (input :: more) g 1199 [] itemsPosition
    ⟨.punctuation .fullStop, stopSpan⟩ [] (by simp) (by decide) (.inr (.inr (.inl rfl))) (by simp) (by simp)
    (by rw [List.map_cons, listed]; simp at enough ⊢; omega)
  rw [List.map_cons] at inner bound
  erw [inner]
  obtain ⟨stopFuel, stopEq⟩ : ∃ smaller, g - spent = smaller + 1 := ⟨g - spent - 1, by
    rw [listed] at bound; simp at enough bound; omega⟩
  rw [stopEq, tail_full_stop stopFuel 1199 _ stopSpan [] rfl]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [tail_full_stop g 1200 _ stopSpan [] rfl]
  simp only [flatMap_nothing, List.append_nil]
  rfl

#print axioms query_expression
#print axioms declarations_expression

/-! ## Declaration and query sentences: text -/

/-- The declaration sentence the canonical printer writes. -/
def declarationsText (declarations : List CHR.Declaration) : String :=
  ":- chr_constraint " ++ String.intercalate ", " (declarations.map CHRPrologPrinter.declaration) ++ ".\n"

/-- The query sentence the canonical printer writes. -/
def queryText (inputs : List CHR.Constraint) : String :=
  "?- " ++ CHRPrologPrinter.conjunction (inputs.map CHRPrologPrinter.constraint) ++ ".\n"

theorem declaration_chars (declaration : CHR.Declaration) :
    (CHRPrologPrinter.declaration declaration).toList = (declarationLexemes declaration).flatMap Lexeme.chars := by
  simp only [CHRPrologPrinter.declaration, declarationLexemes, String.toList_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, quoted_chars, numeral_chars, bare_chars "/" (by decide)]
  simp [List.append_assoc]

theorem constraint_chars (constraint : CHR.Constraint) :
    (CHRPrologPrinter.constraint constraint).toList = (constraintLexemes constraint).flatMap Lexeme.chars := by
  unfold CHRPrologPrinter.constraint constraintLexemes
  by_cases empty : constraint.arguments.isEmpty
  · simp only [empty, if_true, String.toList_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      quoted_chars]
    simp
  · have mapped : valuesLexemes constraint.arguments = constraint.arguments.map valueLexemes := by
      clear empty
      induction constraint.arguments with
      | nil => rfl
      | cons first rest ih => simp [valuesLexemes, ih]
    simp only [empty, if_false, Bool.false_eq_true, CHRPrologPrinter.arguments, String.toList_append,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, quoted_chars, values_chars]
    simp [openParen, closeParen, Lexeme.chars]

theorem declarations_chars (declarations : List CHR.Declaration) :
    (declarationsText declarations).toList = (declarationsLexemes declarations).flatMap Lexeme.chars := by
  unfold declarationsText declarationsLexemes
  simp only [String.toList_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    intercalate_chars CHRPrologPrinter.declaration declarationLexemes declaration_chars]
  simp [space_chars, newline_chars, stop_chars, bare_chars ":-" (by decide), bare_chars "chr_constraint" (by decide)]

theorem query_chars (inputs : List CHR.Constraint) (nonempty : inputs ≠ []) :
    (queryText inputs).toList = (queryLexemes inputs).flatMap Lexeme.chars := by
  have mapped : (inputs.map CHRPrologPrinter.constraint).isEmpty = false := by simpa using nonempty
  unfold queryText queryLexemes CHRPrologPrinter.conjunction
  simp only [mapped, Bool.false_eq_true, if_false, String.toList_append, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, intercalate_chars CHRPrologPrinter.constraint constraintLexemes constraint_chars]
  simp [space_chars, newline_chars, stop_chars, bare_chars "?-" (by decide)]

/-! ## Declaration and query sentences: lexing -/

theorem declaration_printable (declaration : CHR.Declaration) : Printable (declarationLexemes declaration) where
  reads text separates := by
    obtain ⟨first, rest, listed, digit⟩ := numeral_starts declaration.arity
    refine .cons ?_ (.cons ?_ (.cons (numeral_reads _ _ (by simpa using separates_number separates)) (.nil text)))
    · intro next same
      simp [bare_chars "/" (by decide)] at same
      rw [← same]
      decide
    · rw [bare_graphic "/" '/' [] rfl (by decide)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, listed]
      exact ⟨by decide, by decide, fun _ => by simp; intro same; rw [same] at digit; simp at digit, by simp,
        fun next same => by simp at same; rw [← same]; exact digit_not_graphic digit⟩
  solid := ⟨'\'', _, rfl, by decide⟩

theorem constraint_printable (constraint : CHR.Constraint) : Printable (constraintLexemes constraint) := by
  unfold constraintLexemes
  by_cases empty : constraint.arguments.isEmpty
  · simp only [empty, if_true, List.append_nil]
    exact quoted_printable constraint.name
  · simp only [empty, if_false, Bool.false_eq_true]
    have shape : [quoted constraint.name] ++ ([openParen] ++ separated (valuesLexemes constraint.arguments) ++
        [closeParen]) = [quoted constraint.name, openParen] ++ separated (valuesLexemes constraint.arguments) ++
        [closeParen] := by simp
    rw [shape]
    exact applied_printable _ _ (quoted_applied_reads constraint.name) ⟨'\'', _, rfl, by decide⟩
      (values_printable constraint.arguments)

theorem sentence_end_reads {body : List Lexeme} (printable : Printable body) :
    ReadsBefore (body ++ [.fullStop, newline]) [] := by
  refine ReadsBefore.append (printable.reads _ ?_) (.cons ?_ (.cons ?_ (.nil [])))
  · show Separates ('.' :: '\n' :: [])
    intro next same
    simp at same
    rw [← same]
    decide
  · show fullStopFollows ('\n' :: []) = true
    decide
  · exact ⟨by decide, fun next same => by simp at same⟩

theorem declarations_reads_before (declarations : List CHR.Declaration) (nonempty : declarations ≠ []) :
    ReadsBefore (declarationsLexemes declarations) [] := by
  have items := separated_printable (declarations.map declarationLexemes) (by simpa using nonempty) (by
    intro item inside
    obtain ⟨declaration, _, rfl⟩ := List.mem_map.mp inside
    exact declaration_printable declaration)
  have shape : declarationsLexemes declarations = bare ":-" :: space :: bare "chr_constraint" :: space ::
      (separated (declarations.map declarationLexemes) ++ [.fullStop, newline]) := by
    simp [declarationsLexemes]
  rw [shape]
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (sentence_end_reads items))))
  · rw [bare_graphic ":-" ':' ['-'] rfl (by decide)]
    simp only [List.flatMap_cons, space_chars, List.cons_append]
    exact graphic_reads_space ':' ['-'] _ (by decide) (by decide) (fun same => absurd same (by decide)) (by simp; decide)
  · refine space_reads _ fun next same => ?_
    simp [bare_chars "chr_constraint" (by decide)] at same
    rw [← same]
    decide
  · rw [bare_word "chr_constraint" 'c' "hr_constraint".toList rfl (by decide)]
    simp only [List.flatMap_cons, space_chars, List.cons_append]
    exact word_reads_space 'c' _ _ (by decide) (by simp [isIdentifierContinue])
  · have solid := solid_text items.solid ([Lexeme.fullStop, newline].flatMap Lexeme.chars)
    refine space_reads _ ?_
    rw [List.flatMap_append, List.append_nil]
    exact solid

theorem query_reads_before (inputs : List CHR.Constraint) (nonempty : inputs ≠ []) :
    ReadsBefore (queryLexemes inputs) [] := by
  have items := separated_printable (inputs.map constraintLexemes) (by simpa using nonempty) (by
    intro item inside
    obtain ⟨constraint, _, rfl⟩ := List.mem_map.mp inside
    exact constraint_printable constraint)
  have shape : queryLexemes inputs = bare "?-" :: space ::
      (separated (inputs.map constraintLexemes) ++ [.fullStop, newline]) := by
    simp [queryLexemes]
  rw [shape]
  refine .cons ?_ (.cons ?_ (sentence_end_reads items))
  · rw [bare_graphic "?-" '?' ['-'] rfl (by decide)]
    simp only [List.flatMap_cons, space_chars, List.cons_append]
    exact graphic_reads_space '?' ['-'] _ (by decide) (by decide) (fun same => absurd same (by decide)) (by simp; decide)
  · have solid := solid_text items.solid ([Lexeme.fullStop, newline].flatMap Lexeme.chars)
    refine space_reads _ ?_
    rw [List.flatMap_append, List.append_nil]
    exact solid

#print axioms declarations_reads_before
#print axioms query_reads_before

/-! ## Declaration and query sentences: reading -/

theorem declarations_tokens (declarations : List CHR.Declaration) (position : Position) :
    ∃ directiveSpan wordSpan itemsPosition stopSpan, tokensOf (declarationsLexemes declarations) position =
      ⟨.atom ":-", directiveSpan⟩ :: ⟨.atom "chr_constraint", wordSpan⟩ ::
        (tokensOf (separated (declarations.map declarationLexemes)) itemsPosition ++
          [⟨.punctuation .fullStop, stopSpan⟩]) := by
  have shape : declarationsLexemes declarations = bare ":-" :: space :: bare "chr_constraint" :: space ::
      (separated (declarations.map declarationLexemes) ++ [.fullStop, newline]) := by
    simp [declarationsLexemes]
  rw [shape, tokensOf_kind _ _ directive_kind, space, tokensOf_layout, tokensOf_kind _ _ constraint_word_kind,
    tokensOf_layout, tokensOf_append, tokensOf_kind _ _ rfl, newline, tokensOf_layout, tokensOf_nil]
  exact ⟨_, _, _, _, rfl⟩

theorem query_tokens (inputs : List CHR.Constraint) (position : Position) :
    ∃ querySpan itemsPosition stopSpan, tokensOf (queryLexemes inputs) position =
      ⟨.atom "?-", querySpan⟩ ::
        (tokensOf (separated (inputs.map constraintLexemes)) itemsPosition ++ [⟨.punctuation .fullStop, stopSpan⟩]) := by
  have shape : queryLexemes inputs = bare "?-" :: space ::
      (separated (inputs.map constraintLexemes) ++ [.fullStop, newline]) := by
    simp [queryLexemes]
  rw [shape, tokensOf_kind _ _ query_kind, space, tokensOf_layout, tokensOf_append, tokensOf_kind _ _ rfl, newline,
    tokensOf_layout, tokensOf_nil]
  exact ⟨_, _, _, rfl⟩

theorem declarations_reads_back (declarations : List CHR.Declaration) (nonempty : declarations ≠ []) :
    ∃ bindings, ReaderTerm.readOneWith chr chr.operators (declarationsText declarations) =
      .ok ⟨declarationsSource declarations, bindings, []⟩ := by
  obtain ⟨directiveSpan, wordSpan, itemsPosition, stopSpan, listed⟩ :=
    declarations_tokens declarations ReaderLexer.Position.initial
  refine ⟨(readerState [] []).bindings.reverse, ?_⟩
  have text : declarationsText declarations =
      String.ofList ((declarationsLexemes declarations).flatMap Lexeme.chars) := by
    apply String.toList_inj.mp
    rw [String.toList_ofList, declarations_chars]
  unfold ReaderTerm.readOneWith
  rw [text, ReaderLexer.scan_lexemes _ (allRead_of (declarations_reads_before declarations nonempty))]
  simp only [bind, Except.bind]
  unfold ReaderTerm.parseOneWith
  rw [listed]
  dsimp only
  erw [declarations_expression declarations nonempty directiveSpan wordSpan stopSpan itemsPosition _
    (by simp; omega)]
  simp only [bind, Except.bind]
  rw [consume_full_stop _ stopSpan [] rfl]
  rfl

theorem query_reads_back (inputs : List CHR.Constraint) (nonempty : inputs ≠ []) :
    ∃ bindings, ReaderTerm.readOneWith chr chr.operators (queryText inputs) =
      .ok ⟨querySource inputs, bindings, []⟩ := by
  obtain ⟨querySpan, itemsPosition, stopSpan, listed⟩ := query_tokens inputs ReaderLexer.Position.initial
  refine ⟨(readerState [] []).bindings.reverse, ?_⟩
  have text : queryText inputs = String.ofList ((queryLexemes inputs).flatMap Lexeme.chars) := by
    apply String.toList_inj.mp
    rw [String.toList_ofList, query_chars inputs nonempty]
  unfold ReaderTerm.readOneWith
  rw [text, ReaderLexer.scan_lexemes _ (allRead_of (query_reads_before inputs nonempty))]
  simp only [bind, Except.bind]
  unfold ReaderTerm.parseOneWith
  rw [listed]
  dsimp only
  erw [query_expression inputs nonempty querySpan stopSpan itemsPosition _ (by simp; omega)]
  simp only [bind, Except.bind]
  rw [consume_full_stop _ stopSpan [] rfl]
  rfl

#print axioms declarations_reads_back
#print axioms query_reads_back

/-! ## Programs -/

open CHRPrologReadback (programForms ProgramPrintable QueryPrintable assemble_forms declarations_form query_form
  library_form option_form libraryDirective optionDirective)
open Mettapedia.Languages.CHR.TupleNormal (normalProgram)

def libraryText : String := ":- use_module(library(chr)).\n"
def optionText : String := ":- chr_option(optimize,off).\n"

/-- The sentences of a program's canonical text. -/
def programSentences (program : CHR.Program) (inputs : List CHR.Constraint) : List String :=
  [libraryText] ++
    (if program.declarations.isEmpty then [] else [declarationsText program.declarations, optionText]) ++
    program.rules.map CHRPrologPrinter.rule ++ (if inputs.isEmpty then [] else [queryText inputs])

/-- The canonical text of a program is its sentences, one after another. -/
theorem program_text (program : CHR.Program) (inputs : List CHR.Constraint) :
    CHRPrologPrinter.program program inputs = String.join (programSentences program inputs) := by
  apply String.toList_inj.mp
  unfold CHRPrologPrinter.program programSentences libraryText optionText declarationsText queryText
  by_cases declared : program.declarations.isEmpty <;> by_cases queried : inputs.isEmpty <;>
    simp [declared, queried, String.toList_join, List.flatMap_map, List.append_assoc]

/-- A sentence that reads back and lowers to `form`. -/
def SentenceReads (text : String) (form : CHRPrologLowering.Form) : Prop :=
  ∃ result, ReaderTerm.readOneWith chr chr.operators text = .ok result ∧
    ∀ ordinal, CHRPrologLowering.form ordinal result.term = .ok form

theorem fixed_sentence (text : String) (source : SourceSignature.Term) (form : CHRPrologLowering.Form)
    (reads : (ReaderTerm.readOneWith chr chr.operators text).map (·.term) = .ok source)
    (lowers : ∀ ordinal, CHRPrologLowering.form ordinal source = .ok form) : SentenceReads text form := by
  cases read : ReaderTerm.readOneWith chr chr.operators text with
  | error reason => simp [read, Except.map] at reads
  | ok result =>
    simp only [read, Except.map, Except.ok.injEq] at reads
    exact ⟨result, read, fun ordinal => reads ▸ lowers ordinal⟩

/-- **A printed program reads back as its IR.** Every sentence of the
canonical text reads, through the reference reader, as the form of the
corresponding part of the program, and those forms assemble to the program in
tuple normal form together with its inputs. -/
theorem program_reads_back (program : CHR.Program) (inputs : List CHR.Constraint)
    (printable : ProgramPrintable program inputs)
    (declared : ∀ constraint ∈ inputs,
      CHR.Admission.declared program ⟨constraint.name, constraint.arguments.map CHR.Term.value⟩ = true)
    (admitted : CHR.Admission.diagnose program = none) :
    CHRPrologPrinter.program program inputs = String.join (programSentences program inputs) ∧
      List.Forall₂ SentenceReads (programSentences program inputs) (programForms program inputs) ∧
      CHRPrologLowering.assemble (programForms program inputs) = .ok ⟨normalProgram program, inputs⟩ := by
  refine ⟨program_text program inputs, ?_, assemble_forms program inputs declared admitted⟩
  unfold programSentences programForms
  have library : SentenceReads libraryText .metadata := fixed_sentence _ _ _ library_reads library_form
  have option : SentenceReads optionText .metadata := fixed_sentence _ _ _ option_reads option_form
  have declarations : List.Forall₂ SentenceReads
      (if program.declarations.isEmpty then [] else [declarationsText program.declarations, optionText])
      (if program.declarations.isEmpty then [] else [.declarations program.declarations, .metadata]) := by
    by_cases empty : program.declarations.isEmpty
    · simp only [empty, if_true]
      exact .nil
    · simp only [empty, if_false, Bool.false_eq_true]
      have nonempty : program.declarations ≠ [] := by simpa using empty
      obtain ⟨bindings, read⟩ := declarations_reads_back program.declarations nonempty
      exact .cons ⟨_, read, fun ordinal => declarations_form ordinal _ nonempty⟩ (.cons option .nil)
  have rules : List.Forall₂ SentenceReads (program.rules.map CHRPrologPrinter.rule)
      (program.rules.map fun rule => .rule (normalRule rule)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun rule inside => ?_
    obtain ⟨result, read, lowers⟩ := rule_reads_and_lowers rule (printable.rules rule inside) 0
    obtain ⟨bindings, exact⟩ := rule_reads_back rule (printable.rules rule inside).heads
    refine ⟨_, exact, fun ordinal => ?_⟩
    exact CHRPrologReadback.rule_form (nameIn (ruleVariables rule)) (fun _ => rfl) ordinal rule
      (printable.rules rule inside)
  have query : List.Forall₂ SentenceReads (if inputs.isEmpty then [] else [queryText inputs])
      (if inputs.isEmpty then [] else [.query inputs]) := by
    by_cases empty : inputs.isEmpty
    · simp only [empty, if_true]
      exact .nil
    · simp only [empty, if_false, Bool.false_eq_true]
      have nonempty : inputs ≠ [] := by simpa using empty
      obtain ⟨bindings, read⟩ := query_reads_back inputs nonempty
      exact .cons ⟨_, read, fun ordinal => query_form ordinal inputs nonempty printable.inputs⟩ .nil
  exact List.rel_append (List.rel_append (List.rel_append (.cons library .nil) declarations) rules) query

#print axioms program_reads_back

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback
