import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.GSLT.Parsing.SourceAccumulatorLex
import Mettapedia.GSLT.Parsing.SourceAccumulatorScan
import Mettapedia.GSLT.Parsing.SourceSExprAdmission
import Mettapedia.GSLT.Parsing.ExactDecimalLexeme

/-!
# Rendering atoms so that the reader reads them back

`render?` writes an atom as MeTTa source text, or refuses it. It writes symbols, variables,
integers, strings and Booleans in spellings that the shared source reader keeps exactly, and
refuses everything else: symbols that would read as variables, commands, Booleans or numbers;
the anonymous variable marker, whose source spelling allocates a fresh occurrence; foreign
grounded values. Ordinary Unicode in strings is retained; characters requiring escaping
use the shared literal codec (`StringLiteral.canonicalBody`).

`Rendered atom characters expression` is the same rendering as a relation, together with the
S-expression the reader's lexer and token parser must produce. Each layer of the reader is proved
once against that relation:

- the lexer emits the expression's tokens (`lex_close`, `lex_space`);
- the token parser rebuilds the expression (`SExprTokenRoundTrip.parse_tokens_whole`);
- the token reader rebuilds the atom (`read_expression`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi
open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing
open Mettapedia.GSLT.Parsing.SExprTokenRoundTrip (tokens childTokens safe childrenSafe)

/-! ## Spellings -/

/-- A character that may occur in a symbol: non-control Unicode, not a delimiter, quote, comment or
escape character. -/
def symbolChar (character : Char) : Bool :=
  0x21 ≤ character.toNat && character.toNat != 0x7f && character != '(' && character != ')' &&
    character != '"' && character != ';' && character != '\\'

/-- A symbol the reader keeps as that symbol. -/
def symbolSafe (symbol : String) : Bool :=
  match symbol.toList with
  | [] => false
  | first :: _ =>
      first != '$' && first != '!' && symbol.toList.all symbolChar &&
        !(["True", "true", "False", "false"] : List String).contains symbol &&
        (ExactDecimalLexeme.parseInteger? symbol).isNone

/-- An exact variable spelling cannot use the anonymous occurrence marker. -/
def variableSafe (name : String) : Bool := symbolSafe name && name != "_"

theorem variableSafe_parts {name : String} (safeName : variableSafe name = true) :
    symbolSafe name = true ∧ name ≠ "_" := by
  simpa only [variableSafe, Bool.and_eq_true, bne_iff_ne] using safeName

def digitChar (digit : Nat) : Char := Char.ofNat (48 + digit)

/-- Decimal digits of a natural number, most significant first. -/
def decimal (value : Nat) : List Char :=
  if value < 10 then [digitChar value] else decimal (value / 10) ++ [digitChar (value % 10)]
termination_by value
decreasing_by omega

def intChars : Int → List Char
  | .ofNat value => decimal value
  | .negSucc value => '-' :: decimal (value + 1)

def joinSpace : List (List Char) → List Char
  | [] => []
  | [part] => part
  | part :: parts => part ++ ' ' :: joinSpace parts

mutual
  /-- The characters of an atom's source spelling, if it has one the reader keeps. -/
  def chars? : Atom → Option (List Char)
    | .symbol symbol => if symbolSafe symbol then some symbol.toList else none
    | .var name => if variableSafe name then some ('$' :: name.toList) else none
    | .grounded (.int value) => some (intChars value)
    | .grounded (.string value) => some ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])
    | .grounded (.bool value) => some (if value then "True".toList else "False".toList)
    | .grounded (.custom _ _) => none
    | .expression items => (charsList? items).map fun parts => '(' :: joinSpace parts ++ [')']

  def charsList? : List Atom → Option (List (List Char))
    | [] => some []
    | item :: items => do
        let first ← chars? item
        let rest ← charsList? items
        pure (first :: rest)
end

/-- An atom's source text. -/
def render? (atom : Atom) : Option String := (chars? atom).map String.ofList

/-! ## The rendering relation -/

mutual
  /-- `Rendered atom characters expression`: the atom is spelled by the characters, and the
  reader's lexer and token parser must produce the expression from them. -/
  inductive Rendered : Atom → List Char → SExpr → Prop
    | symbol (symbol : String) : symbolSafe symbol = true →
        Rendered (.symbol symbol) symbol.toList (.atom (String.ofList symbol.toList))
    | var (name : String) : variableSafe name = true →
        Rendered (.var name) ('$' :: name.toList) (.atom (String.ofList ('$' :: name.toList)))
    | int (value : Int) :
        Rendered (.grounded (.int value)) (intChars value) (.atom (String.ofList (intChars value)))
    | string (value : String) :
        Rendered (.grounded (.string value)) ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])
          (.atom (String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])))
    | bool (value : Bool) :
        Rendered (.grounded (.bool value)) (if value then "True".toList else "False".toList)
          (.atom (String.ofList (if value then "True".toList else "False".toList)))
    | expression {items : List Atom} {parts : List (List Char)} {expressions : List SExpr} :
        RenderedList items parts expressions →
        Rendered (.expression items) ('(' :: joinSpace parts ++ [')']) (.list expressions)

  inductive RenderedList : List Atom → List (List Char) → List SExpr → Prop
    | nil : RenderedList [] [] []
    | cons {item : Atom} {items : List Atom} {part : List Char} {parts : List (List Char)}
        {expression : SExpr} {expressions : List SExpr} :
        Rendered item part expression → RenderedList items parts expressions →
        RenderedList (item :: items) (part :: parts) (expression :: expressions)
end

mutual
  theorem rendered_of_chars : ∀ {atom : Atom} {characters : List Char},
      chars? atom = some characters → ∃ expression, Rendered atom characters expression
    | .symbol symbol, characters, rendered => by
        unfold chars? at rendered
        split at rendered
        · cases rendered
          exact ⟨_, .symbol symbol (by assumption)⟩
        · cases rendered
    | .var name, characters, rendered => by
        unfold chars? at rendered
        split at rendered
        · cases rendered
          exact ⟨_, .var name (by assumption)⟩
        · cases rendered
    | .grounded (.int value), characters, rendered => by
        unfold chars? at rendered
        cases rendered
        exact ⟨_, .int value⟩
    | .grounded (.string value), characters, rendered => by
        unfold chars? at rendered
        cases rendered
        exact ⟨_, .string value⟩
    | .grounded (.bool value), characters, rendered => by
        unfold chars? at rendered
        cases rendered
        exact ⟨_, .bool value⟩
    | .grounded (.custom _ _), characters, rendered => by
        unfold chars? at rendered
        cases rendered
    | .expression items, characters, rendered => by
        unfold chars? at rendered
        cases listed : charsList? items with
        | none => rw [listed] at rendered; cases rendered
        | some parts =>
            rw [listed] at rendered
            cases rendered
            obtain ⟨expressions, children⟩ := renderedList_of_chars listed
            exact ⟨_, .expression children⟩

  theorem renderedList_of_chars : ∀ {items : List Atom} {parts : List (List Char)},
      charsList? items = some parts → ∃ expressions, RenderedList items parts expressions
    | [], parts, rendered => by
        unfold charsList? at rendered
        cases rendered
        exact ⟨[], .nil⟩
    | item :: items, parts, rendered => by
        unfold charsList? at rendered
        cases first : chars? item with
        | none => rw [first] at rendered; cases rendered
        | some part =>
            cases rest : charsList? items with
            | none => rw [first, rest] at rendered; cases rendered
            | some others =>
                rw [first, rest] at rendered
                cases rendered
                obtain ⟨expression, head⟩ := rendered_of_chars first
                obtain ⟨expressions, tail⟩ := renderedList_of_chars rest
                exact ⟨_, .cons head tail⟩
end

/-! ## Decimal numbers read back -/

theorem digitChar_toNat {digit : Nat} (small : digit < 10) : (digitChar digit).toNat = 48 + digit := by
  interval_cases digit <;> rfl

theorem decimalDigit_digitChar {digit : Nat} (small : digit < 10) :
    ExactDecimalLexeme.decimalDigit? (digitChar digit) = some digit := by
  interval_cases digit <;> rfl

theorem parseDigits_append (left right : List Char) (value : Nat) :
    ExactDecimalLexeme.parseDigits? (left ++ right) value =
      (ExactDecimalLexeme.parseDigits? left value).bind (ExactDecimalLexeme.parseDigits? right) := by
  induction left generalizing value with
  | nil => rfl
  | cons character rest ih =>
      simp only [List.cons_append, ExactDecimalLexeme.parseDigits?]
      cases ExactDecimalLexeme.decimalDigit? character with
      | none => rfl
      | some digit => exact ih _

theorem parseDigits_decimal (value : Nat) :
    ExactDecimalLexeme.parseDigits? (decimal value) 0 = some value := by
  induction value using Nat.strong_induction_on with
  | _ value ih =>
    unfold decimal
    split
    · rename_i small
      simp [ExactDecimalLexeme.parseDigits?, decimalDigit_digitChar small]
    · rename_i large
      rw [parseDigits_append, ih (value / 10) (by omega)]
      simp [ExactDecimalLexeme.parseDigits?, decimalDigit_digitChar (Nat.mod_lt value (by omega)),
        Nat.div_add_mod']

theorem decimal_head (value : Nat) : ∃ first rest, decimal value = first :: rest ∧
    (value = 0 → first = '0') ∧ (0 < value → first ≠ '0') := by
  induction value using Nat.strong_induction_on with
  | _ value ih =>
    unfold decimal
    split
    · rename_i small
      refine ⟨digitChar value, [], rfl, fun zero => by subst zero; rfl, fun positive same => ?_⟩
      have codes := congrArg Char.toNat same
      rw [digitChar_toNat small] at codes
      change 48 + value = 48 at codes
      omega
    · rename_i large
      obtain ⟨first, rest, shape, _, nonzero⟩ := ih (value / 10) (by omega)
      exact ⟨first, rest ++ [digitChar (value % 10)], by rw [shape]; rfl, fun zero => by omega,
        fun _ => nonzero (by omega)⟩

theorem decimal_chars (value : Nat) : ∀ character ∈ decimal value,
    0x30 ≤ character.toNat ∧ character.toNat ≤ 0x39 := by
  induction value using Nat.strong_induction_on with
  | _ value ih =>
    unfold decimal
    split
    · rename_i small
      intro character member
      simp only [List.mem_singleton] at member
      subst member
      rw [digitChar_toNat small]
      omega
    · intro character member
      rcases List.mem_append.mp member with earlier | last
      · exact ih (value / 10) (by omega) character earlier
      · simp only [List.mem_singleton] at last
        subst last
        rw [digitChar_toNat (Nat.mod_lt value (by omega))]
        have := Nat.mod_lt value (show 10 > 0 by omega)
        omega

theorem parseUnsigned_decimal (value : Nat) :
    ExactDecimalLexeme.parseUnsignedChars? (decimal value) = some value := by
  obtain ⟨first, rest, shape, zero, nonzero⟩ := decimal_head value
  rcases Nat.eq_zero_or_pos value with isZero | positive
  · subst isZero
    unfold decimal
    decide
  · have digits := parseDigits_decimal value
    rw [shape] at digits ⊢
    have different := nonzero positive
    unfold ExactDecimalLexeme.parseUnsignedChars?
    split
    · rename_i same; cases same
    · rename_i same; cases same; exact absurd rfl different
    · rename_i same; cases same; exact absurd rfl different
    · exact digits

theorem parseInteger_intChars (value : Int) :
    ExactDecimalLexeme.parseIntegerChars? (intChars value) = some value := by
  cases value with
  | ofNat natural =>
    obtain ⟨first, rest, shape, _, _⟩ := decimal_head natural
    have digit := decimal_chars natural first (by rw [shape]; exact List.mem_cons_self)
    show ExactDecimalLexeme.parseIntegerChars? (decimal natural) = some (Int.ofNat natural)
    unfold ExactDecimalLexeme.parseIntegerChars?
    rw [shape]
    split
    · rename_i same; cases same; simp at digit
    · rename_i same; cases same; simp at digit
    · rw [← shape, parseUnsigned_decimal]; rfl
  | negSucc natural =>
    unfold intChars ExactDecimalLexeme.parseIntegerChars?
    simp only [parseUnsigned_decimal, Option.map_some]
    rfl

/-! ## The lexer -/

open SourceAccumulatorLex (Point Agreement initialPoint agreement_append)
open private tokenizeAux flushToken from Algorithms.MeTTa.Simple.Parser

/-- A character the lexer accumulates into the current token outside strings. -/
def tokenChar (character : Char) : Prop :=
  character.isWhitespace = false ∧ character ≠ ';' ∧ character ≠ '(' ∧ character ≠ ')' ∧ character ≠ '"'

instance : DecidablePred tokenChar := fun _ => by unfold tokenChar; infer_instance

theorem lex_token_chars (characters : List Char) (allToken : ∀ character ∈ characters, tokenChar character)
    (current : List Char) :
    Agreement ⟨false, false, current⟩ ⟨false, false, characters.reverse ++ current⟩ characters [] := by
  induction characters generalizing current with
  | nil => intro rest emitted; rfl
  | cons character rest ih =>
    intro remaining emitted
    obtain ⟨white, comment, opening, closing, quote⟩ := allToken character List.mem_cons_self
    have later := ih (fun other member => allToken other (List.mem_cons_of_mem _ member)) (character :: current)
      remaining emitted
    simp only [SourceAccumulatorLex.run, List.cons_append] at later ⊢
    rw [tokenizeAux]
    simp only [Option.some.injEq, white, Bool.false_eq_true, if_false]
    rw [if_neg (Ne.symm comment), if_neg opening, if_neg closing, if_neg quote]
    simpa [List.reverse_cons, List.append_assoc] using later

/-- The tokens a pending token contributes when it ends. -/
def flushed (current : List Char) : List String :=
  if current.isEmpty then [] else [String.ofList current.reverse]

theorem lex_space (current : List Char) :
    Agreement ⟨false, false, current⟩ initialPoint [' '] (flushed current) := by
  intro rest emitted
  simp only [SourceAccumulatorLex.run, initialPoint, List.cons_append, List.nil_append]
  rw [tokenizeAux]
  simp only [Option.some.injEq]
  rw [if_neg (by decide)]
  simp only [show (' ' : Char).isWhitespace = true from rfl, if_true]
  unfold flushed
  cases current <;> simp [flushToken]

theorem lex_close (current : List Char) :
    Agreement ⟨false, false, current⟩ initialPoint [')'] (flushed current ++ [")"]) := by
  intro rest emitted
  simp only [SourceAccumulatorLex.run, initialPoint, List.cons_append, List.nil_append]
  rw [tokenizeAux]
  simp only [Option.some.injEq]
  rw [if_neg (by decide)]
  simp only [show (')' : Char).isWhitespace = false from rfl, Bool.false_eq_true, if_false]
  rw [if_neg (by decide), if_pos trivial]
  unfold flushed
  cases current <;> simp [flushToken]

theorem lex_open : Agreement initialPoint initialPoint ['('] ["("] := by
  intro rest emitted
  simp only [SourceAccumulatorLex.run, initialPoint, List.cons_append, List.nil_append]
  rw [tokenizeAux]
  simp only [Option.some.injEq]
  rw [if_neg (by decide)]
  simp only [show ('(' : Char).isWhitespace = false from rfl, Bool.false_eq_true, if_false]
  rw [if_pos trivial]
  simp [flushToken]

theorem lex_escaped_body {characters : List Char} (body : StringLiteral.EscapedBody characters)
    (current : List Char) :
    Agreement ⟨true, false, current⟩ ⟨true, false, characters.reverse ++ current⟩ characters [] := by
  induction body generalizing current with
  | nil => intro rest emitted; rfl
  | @plain character rest notEscape notQuote _ _ ih =>
    intro remaining emitted
    have later := ih (character :: current) remaining emitted
    simp only [SourceAccumulatorLex.run, List.cons_append] at later ⊢
    rw [tokenizeAux]
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg notEscape, if_neg notQuote]
    simpa [List.reverse_cons, List.append_assoc] using later
  | @escape character rest _ _ ih =>
    intro remaining emitted
    have later := ih (character :: '\\' :: current) remaining emitted
    simp only [SourceAccumulatorLex.run, List.cons_append] at later ⊢
    rw [tokenizeAux]
    simp only [Bool.false_eq_true, if_false]
    rw [if_pos trivial]
    rw [tokenizeAux]
    simp only [↓reduceIte]
    simpa [List.reverse_cons, List.append_assoc] using later

theorem lex_string (value : String) :
    Agreement initialPoint initialPoint ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])
      [String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])] := by
  have opening : Agreement initialPoint ⟨true, false, ['"']⟩ ['"'] [] := by
    intro rest emitted
    simp only [SourceAccumulatorLex.run, initialPoint, List.cons_append, List.nil_append]
    rw [tokenizeAux]
    simp only [Option.some.injEq]
    rw [if_neg (by decide)]
    simp only [show ('"' : Char).isWhitespace = false from rfl, Bool.false_eq_true, if_false]
    rw [if_neg (by decide), if_neg (by decide), if_pos trivial]
    simp [flushToken]
  have closing (current : List Char) :
      Agreement ⟨true, false, current⟩ initialPoint ['"'] [String.ofList ('"' :: current).reverse] := by
    intro rest emitted
    simp only [SourceAccumulatorLex.run, initialPoint, List.cons_append, List.nil_append]
    rw [tokenizeAux]
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (by decide), if_pos trivial]
    simp [flushToken]
  have whole := agreement_append _ _ _ _ _ _ _
    (agreement_append _ _ _ _ _ _ _ opening
      (lex_escaped_body (StringLiteral.canonicalBody_escaped value.toList) ['"']))
    (closing ((StringLiteral.canonicalBody value.toList).reverse ++ ['"']))
  simpa [List.reverse_append, List.append_assoc] using whole

/-- A token atom's characters are accumulated without delimiters. -/
private theorem symbol_token_chars {symbol : String} (safeSymbol : symbolSafe symbol = true) :
    ∀ character ∈ symbol.toList, tokenChar character := by
  intro character member
  unfold symbolSafe at safeSymbol
  split at safeSymbol
  · cases safeSymbol
  · simp only [Bool.and_eq_true] at safeSymbol
    have allSymbol := List.all_eq_true.mp safeSymbol.1.1.2 character member
    simp only [symbolChar, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at allSymbol
    obtain ⟨⟨⟨⟨⟨⟨low, high⟩, opening⟩, closing⟩, quote⟩, comment⟩, _⟩ := allSymbol
    refine ⟨?_, comment, opening, closing, quote⟩
    rw [Char.isWhitespace]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro same <;> subst same <;> simp at low

private theorem decimal_token_chars (value : Nat) : ∀ character ∈ decimal value, tokenChar character := by
  intro character member
  obtain ⟨low, high⟩ := decimal_chars value character member
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Char.isWhitespace]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro same <;> subst same <;> simp at low
  all_goals intro same; subst same; simp at low high

/-- How a rendered atom leaves the lexer: closed, or as an unfinished token. -/
theorem lex_rendered_cases {atom : Atom} {characters : List Char} {expression : SExpr}
    (rendered : Rendered atom characters expression)
    (items : ∀ {children : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList children parts expressions → atom = .expression children →
      Agreement initialPoint initialPoint (joinSpace parts ++ [')']) (childTokens expressions ++ [")"])) :
    Agreement initialPoint initialPoint characters (tokens expression) ∨
      (Agreement initialPoint ⟨false, false, characters.reverse⟩ characters [] ∧ characters ≠ [] ∧
        tokens expression = [String.ofList characters]) := by
  cases rendered with
  | symbol symbol safeSymbol =>
    refine .inr ⟨?_, ?_, rfl⟩
    · simpa [initialPoint] using lex_token_chars symbol.toList (symbol_token_chars safeSymbol) []
    · unfold symbolSafe at safeSymbol
      split at safeSymbol
      · cases safeSymbol
      · rename_i first rest shape
        rw [shape]; simp
  | var name safeName =>
    refine .inr ⟨?_, by simp, rfl⟩
    have token : ∀ character ∈ '$' :: name.toList, tokenChar character := by
      intro character member
      rcases List.mem_cons.mp member with same | rest
      · subst same; exact ⟨rfl, by decide, by decide, by decide, by decide⟩
      · exact symbol_token_chars (variableSafe_parts safeName).1 character rest
    simpa [initialPoint] using lex_token_chars ('$' :: name.toList) token []
  | int value =>
    refine .inr ⟨?_, ?_, rfl⟩
    · have token : ∀ character ∈ intChars value, tokenChar character := by
        cases value with
        | ofNat natural => exact decimal_token_chars natural
        | negSucc natural =>
          intro character member
          rcases List.mem_cons.mp member with same | rest
          · subst same; exact ⟨rfl, by decide, by decide, by decide, by decide⟩
          · exact decimal_token_chars (natural + 1) character rest
      simpa [initialPoint] using lex_token_chars (intChars value) token []
    · cases value with
      | ofNat natural =>
        obtain ⟨first, rest, shape, _⟩ := decimal_head natural
        show decimal natural ≠ []
        rw [shape]; simp
      | negSucc natural => simp [intChars]
  | string value =>
    exact .inl (lex_string value)
  | bool value =>
    refine .inr ⟨?_, by cases value <;> decide, rfl⟩
    have token : ∀ character ∈ (if value then "True".toList else "False".toList), tokenChar character := by
      cases value <;> decide
    simpa [initialPoint] using lex_token_chars _ token []
  | expression children =>
    refine .inl ?_
    have inner := items children rfl
    have whole := agreement_append _ _ _ _ _ _ _ lex_open inner
    simpa [tokens] using whole

mutual
  /-- A rendered atom followed by a closing parenthesis. -/
  theorem lex_then_close : ∀ {atom : Atom} {characters : List Char} {expression : SExpr},
      Rendered atom characters expression →
      Agreement initialPoint initialPoint (characters ++ [')']) (tokens expression ++ [")"])
    | _, _, _, rendered => by
      rcases lex_rendered_cases rendered (fun children _ => lex_items children) with closed |
          ⟨pending, nonempty, single⟩
      · have whole := agreement_append _ _ _ _ _ _ _ closed (lex_close [])
        simpa [flushed] using whole
      · have whole := agreement_append _ _ _ _ _ _ _ pending (lex_close _)
        rw [single]
        simpa [flushed, nonempty] using whole

  /-- A rendered atom followed by a space. -/
  theorem lex_then_space : ∀ {atom : Atom} {characters : List Char} {expression : SExpr},
      Rendered atom characters expression →
      Agreement initialPoint initialPoint (characters ++ [' ']) (tokens expression)
    | _, _, _, rendered => by
      rcases lex_rendered_cases rendered (fun children _ => lex_items children) with closed |
          ⟨pending, nonempty, single⟩
      · have whole := agreement_append _ _ _ _ _ _ _ closed (lex_space [])
        simpa [flushed] using whole
      · have whole := agreement_append _ _ _ _ _ _ _ pending (lex_space _)
        rw [single]
        simpa [flushed, nonempty] using whole

  /-- The items of an expression, each followed by a space or by the closing parenthesis. -/
  theorem lex_items : ∀ {children : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList children parts expressions →
      Agreement initialPoint initialPoint (joinSpace parts ++ [')']) (childTokens expressions ++ [")"])
    | _, _, _, .nil => by
      have whole := lex_close []
      simpa [flushed, joinSpace, childTokens, initialPoint] using whole
    | _, _, _, .cons (parts := []) (expressions := []) head .nil => by
      simpa [joinSpace, childTokens] using lex_then_close head
    | _, _, _, .cons (parts := next :: others) head tail => by
      have whole := agreement_append _ _ _ _ _ _ _ (lex_then_space head) (lex_items tail)
      cases tail with
      | cons nextHead nextTail =>
        simpa [joinSpace, childTokens, List.append_assoc] using whole
end

/-! ## Tokens are safe and read back -/

private theorem ofList_ne_text {characters : List Char} {text : String} {delimiter : Char}
    (spelled : text.toList = [delimiter]) (absent : delimiter ∉ characters) : String.ofList characters ≠ text := by
  intro same
  have lists := congrArg String.toList same
  rw [String.toList_ofList, spelled] at lists
  subst lists
  simp at absent

private theorem ofList_ne_short {characters : List Char} {text : String} {delimiter : Char}
    (spelled : text.toList = [delimiter]) (long : 2 ≤ characters.length) : String.ofList characters ≠ text := by
  intro same
  have lists := congrArg String.toList same
  rw [String.toList_ofList, spelled] at lists
  subst lists
  simp at long

private theorem symbol_parts {symbol : String} (safeSymbol : symbolSafe symbol = true) :
    ∃ first rest, symbol.toList = first :: rest ∧ first ≠ '$' ∧ first ≠ '!' ∧
      (∀ character ∈ symbol.toList, symbolChar character = true) ∧
      ¬ (["True", "true", "False", "false"] : List String).contains symbol ∧
      ExactDecimalLexeme.parseInteger? symbol = none := by
  unfold symbolSafe at safeSymbol
  split at safeSymbol
  · cases safeSymbol
  · rename_i first rest shape
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Option.isNone_iff_eq_none] at safeSymbol
    obtain ⟨⟨⟨⟨notVar, notBang⟩, allChars⟩, notBool⟩, notNumber⟩ := safeSymbol
    exact ⟨first, rest, shape, notVar, notBang, List.all_eq_true.mp allChars,
      by simpa using notBool, notNumber⟩

private theorem symbolChar_not {character : Char} (valid : symbolChar character = true) :
    character ≠ '(' ∧ character ≠ ')' ∧ character ≠ '"' := by
  simp only [symbolChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at valid
  exact ⟨valid.1.1.1.1.2, valid.1.1.1.2, valid.1.1.2⟩

private theorem decimal_not_delimiter {value : Nat} {delimiter : Char} (code : delimiter.toNat < 0x30) :
    delimiter ∉ decimal value := by
  intro member
  have := (decimal_chars value delimiter member).1
  omega

mutual
  theorem rendered_safe : ∀ {atom : Atom} {characters : List Char} {expression : SExpr},
      Rendered atom characters expression → safe expression
    | _, _, _, .symbol symbol safeSymbol => by
        obtain ⟨_, _, _, _, _, allChars, _⟩ := symbol_parts safeSymbol
        refine ⟨ofList_ne_text (by rfl) fun member => ?_, ofList_ne_text (by rfl) fun member => ?_⟩
        · exact (symbolChar_not (allChars _ member)).1 rfl
        · exact (symbolChar_not (allChars _ member)).2.1 rfl
    | _, _, _, .var name safeName => by
        obtain ⟨_, _, _, _, _, allChars, _⟩ := symbol_parts (variableSafe_parts safeName).1
        refine ⟨ofList_ne_text (by rfl) fun member => ?_, ofList_ne_text (by rfl) fun member => ?_⟩
        · rcases List.mem_cons.mp member with same | rest
          · cases same
          · exact (symbolChar_not (allChars _ rest)).1 rfl
        · rcases List.mem_cons.mp member with same | rest
          · cases same
          · exact (symbolChar_not (allChars _ rest)).2.1 rfl
    | _, _, _, .int value => by
        refine ⟨ofList_ne_text (by rfl) ?_, ofList_ne_text (by rfl) ?_⟩ <;>
          · cases value with
            | ofNat natural => exact decimal_not_delimiter (by decide)
            | negSucc natural =>
              intro member
              rcases List.mem_cons.mp member with same | rest
              · cases same
              · exact decimal_not_delimiter (by decide) rest
    | _, _, _, .string value => by
        exact ⟨ofList_ne_short (delimiter := '(') (by rfl) (by simp), ofList_ne_short (delimiter := ')') (by rfl) (by simp)⟩
    | _, _, _, .bool value => by
        cases value <;> exact ⟨by decide, by decide⟩
    | _, _, _, .expression children => renderedList_safe children

  theorem renderedList_safe : ∀ {items : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList items parts expressions → childrenSafe expressions
    | _, _, _, .nil => trivial
    | _, _, _, .cons head tail => ⟨rendered_safe head, renderedList_safe tail⟩
end

open SpaceSemantics (readToken readRawExpression readRawExpressions readExpression readExpressions readPlainString)

private theorem readPlainString_none {token : String} {first : Char} {rest : List Char}
    (shape : token.toList = first :: rest) (notQuote : first ≠ '"') : readPlainString token = none := by
  simp only [readPlainString, shape]
  split
  · rename_i same; cases same; exact absurd rfl notQuote
  · rfl

private theorem startsWith_false {token : String} {first : Char} {rest : List Char}
    (shape : token.toList = first :: rest) {prefixChar : Char} (different : first ≠ prefixChar) :
    token.startsWith (String.singleton prefixChar) = false := by
  rw [String.startsWith_string_eq_false_iff, shape]
  simp only [String.toList_singleton, List.cons_prefix_cons, not_and]
  exact fun same => absurd same.symm different

theorem read_symbol {symbol : String} (safeSymbol : symbolSafe symbol = true) :
    readToken (String.ofList symbol.toList) = .ok (.symbol symbol) := by
  obtain ⟨first, rest, shape, notVar, _, allChars, notBool, notNumber⟩ := symbol_parts safeSymbol
  have notQuote := (symbolChar_not (allChars first (by rw [shape]; exact List.mem_cons_self))).2.2
  rw [String.ofList_toList]
  unfold readToken
  rw [readPlainString_none shape notQuote]
  simp only
  rw [show "$" = String.singleton '$' from rfl, startsWith_false shape notVar,
    show "\"" = String.singleton '"' from rfl, startsWith_false shape notQuote]
  simp only [List.contains_cons, List.contains_nil] at notBool
  have true₁ : symbol ≠ "True" := fun same => notBool (by simp [same])
  have true₂ : symbol ≠ "true" := fun same => notBool (by simp [same])
  have false₁ : symbol ≠ "False" := fun same => notBool (by simp [same])
  have false₂ : symbol ≠ "false" := fun same => notBool (by simp [same])
  simp [true₁, true₂, false₁, false₂, notNumber]

theorem read_var {name : String} (safeName : symbolSafe name = true) :
    readToken (String.ofList ('$' :: name.toList)) = .ok (.var name) := by
  obtain ⟨first, rest, shape, _, _, _, _, _⟩ := symbol_parts safeName
  unfold readToken
  rw [readPlainString_none (show (String.ofList ('$' :: name.toList)).toList = '$' :: name.toList from
    String.toList_ofList) (by decide)]
  simp only
  have copied : (("$" ++ name).drop 1).copy = name := by
    apply String.ext
    simp [String.toList_copy_drop]
  simp [copied]
  intro empty
  rw [empty] at shape
  simp at shape

theorem read_int (value : Int) :
    readToken (String.ofList (intChars value)) = .ok (.grounded (.int value)) := by
  obtain ⟨first, rest, shape, notNumberStart⟩ : ∃ first rest, intChars value = first :: rest ∧
      (first = '-' ∨ (0x30 ≤ first.toNat ∧ first.toNat ≤ 0x39)) := by
    cases value with
    | ofNat natural =>
      obtain ⟨first, rest, shape, _⟩ := decimal_head natural
      exact ⟨first, rest, shape, .inr (decimal_chars natural first (by rw [shape]; exact List.mem_cons_self))⟩
    | negSucc natural => exact ⟨'-', _, rfl, .inl rfl⟩
  have token : (String.ofList (intChars value)).toList = first :: rest := by
    rw [String.toList_ofList, shape]
  have notQuote : first ≠ '"' := by
    rintro rfl; rcases notNumberStart with same | range
    · cases same
    · simp at range
  have notVar : first ≠ '$' := by
    rintro rfl; rcases notNumberStart with same | range
    · cases same
    · simp at range
  unfold readToken
  rw [readPlainString_none token notQuote]
  simp only
  rw [show "$" = String.singleton '$' from rfl, startsWith_false token notVar,
    show "\"" = String.singleton '"' from rfl, startsWith_false token notQuote]
  have notWord (word : String) (wordStart : word.toList.head? = some 'T' ∨ word.toList.head? = some 't' ∨
      word.toList.head? = some 'F' ∨ word.toList.head? = some 'f') : String.ofList (intChars value) ≠ word := by
    intro same
    have heads := congrArg (fun text : String => text.toList.head?) same
    simp only [token, List.head?_cons] at heads
    rw [← heads] at wordStart
    simp only [Option.some.injEq] at wordStart
    rcases notNumberStart with rfl | range
    · rcases wordStart with h | h | h | h <;> cases h
    · rcases wordStart with rfl | rfl | rfl | rfl <;> simp at range
  have parsed : ExactDecimalLexeme.parseInteger? (String.ofList (intChars value)) = some value := by
    unfold ExactDecimalLexeme.parseInteger?
    rw [String.toList_ofList, parseInteger_intChars]
  simp [notWord "True" (by decide), notWord "true" (by decide), notWord "False" (by decide),
    notWord "false" (by decide), parsed]

theorem plainStringCharacter_eq : SpaceSemantics.plainStringCharacter = StringLiteral.plainCharacter := by
  funext character
  rfl

private theorem startsWith_true {token : String} {first : Char} {rest : List Char}
    (shape : token.toList = first :: rest) : token.startsWith (String.singleton first) = true := by
  cases starts : token.startsWith (String.singleton first)
  · rw [String.startsWith_string_eq_false_iff, shape] at starts
    simp at starts
  · rfl

/-- **Every string reads back.** -/
theorem read_string (value : String) :
    readToken (String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])) =
      .ok (.grounded (.string value)) := by
  by_cases plain : value.toList.all SpaceSemantics.plainStringCharacter = true
  · have same : StringLiteral.canonicalBody value.toList = value.toList :=
      StringLiteral.canonicalBody_of_plain (by rw [← plainStringCharacter_eq]; exact plain)
    rw [same]
    have read := SpaceSemantics.readToken_plain_string value.toList plain
    simpa [String.ofList_toList] using read
  · have token : (String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])).toList =
        '"' :: (StringLiteral.canonicalBody value.toList ++ ['"']) := by
      rw [String.toList_ofList, List.cons_append]
    have notPlain : readPlainString (String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])) =
        none := by
      unfold readPlainString
      rw [token]
      have bodyPlain : (StringLiteral.canonicalBody value.toList).all SpaceSemantics.plainStringCharacter = false := by
        rw [plainStringCharacter_eq, StringLiteral.canonicalBody_all_plain, ← plainStringCharacter_eq]
        simpa using plain
      simp [bodyPlain]
    have notWord (word : String) (wordStart : word.toList.head? ≠ some '"') :
        String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"']) ≠ word := by
      intro same
      have heads := congrArg (fun text : String => text.toList.head?) same
      simp only [token, List.head?_cons] at heads
      exact wordStart heads.symm
    have quoted : SpaceSemantics.readQuoted? (String.ofList ('"' :: StringLiteral.canonicalBody value.toList ++ ['"'])) =
        some value := by
      unfold SpaceSemantics.readQuoted?
      rw [token]
      simp [StringLiteral.decodeBody_canonicalBody]
    unfold readToken
    rw [notPlain]
    simp only
    rw [show "$" = String.singleton '$' from rfl, startsWith_false token (by decide),
      show "\"" = String.singleton '"' from rfl, startsWith_true token]
    rw [decide_eq_false (notWord "True" (by decide)), decide_eq_false (notWord "true" (by decide)),
      decide_eq_false (notWord "False" (by decide)), decide_eq_false (notWord "false" (by decide)), quoted]
    rfl

theorem read_bool (value : Bool) :
    readToken (String.ofList (if value then "True".toList else "False".toList)) = .ok (.grounded (.bool value)) := by
  cases value <;> simp [readToken, readPlainString]

mutual
  /-- The lexical reader reconstructs the exact atom before anonymous source
  occurrences are allocated. -/
  theorem read_raw_expression : ∀ {atom : Atom} {characters : List Char} {expression : SExpr},
      Rendered atom characters expression → readRawExpression expression = .ok atom
    | _, _, _, .symbol symbol safeSymbol => by
        rw [readRawExpression]; exact read_symbol safeSymbol
    | _, _, _, .var name safeName => by
        rw [readRawExpression]; exact read_var (variableSafe_parts safeName).1
    | _, _, _, .int value => by
        rw [readRawExpression]; exact read_int value
    | _, _, _, .string value => by
        rw [readRawExpression]; exact read_string value
    | _, _, _, .bool value => by
        rw [readRawExpression]; exact read_bool value
    | _, _, _, .expression children => by
        rw [readRawExpression, read_raw_expressions children]
        rfl

  theorem read_raw_expressions : ∀ {items : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList items parts expressions → readRawExpressions expressions = .ok items
    | _, _, _, .nil => by rw [readRawExpressions]
    | _, _, _, .cons head tail => by
        rw [readRawExpressions, read_raw_expression head, read_raw_expressions tail]
        rfl
end

mutual
  /-- Exact rendered variables are all named; anonymous occurrences are
  intentionally outside the renderer's exact-readback contract. -/
  theorem rendered_named : ∀ {atom : Atom} {characters : List Char} {expression : SExpr},
      Rendered atom characters expression → "_" ∉ MORK.atomFreeVars atom
    | _, _, _, .symbol _ _ => by simp only [MORK.atomFreeVars, List.not_mem_nil, not_false_eq_true]
    | _, _, _, .var name safeName => by
        simpa only [MORK.atomFreeVars, List.mem_singleton] using Ne.symm (variableSafe_parts safeName).2
    | _, _, _, .int _ => by simp only [MORK.atomFreeVars, List.not_mem_nil, not_false_eq_true]
    | _, _, _, .string _ => by simp only [MORK.atomFreeVars, List.not_mem_nil, not_false_eq_true]
    | _, _, _, .bool _ => by simp only [MORK.atomFreeVars, List.not_mem_nil, not_false_eq_true]
    | _, _, _, .expression children => renderedList_named children

  theorem renderedList_named : ∀ {items : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList items parts expressions → "_" ∉ MORK.atomFreeVars (.expression items)
    | _, _, _, .nil => by
        simp only [MORK.atomFreeVars, MORK.atomFreeVars.atomFreeVarsList, List.not_mem_nil, not_false_eq_true]
    | _, _, _, .cons head tail => by
        simpa only [MORK.atomFreeVars, MORK.atomFreeVars.atomFreeVarsList, List.mem_append, not_or] using
          And.intro (rendered_named head) (renderedList_named tail)
end

/-- The scoped reader also reconstructs the exact atom: the renderer has
already excluded the only variable spelling that would allocate a new name. -/
theorem read_expression {atom : Atom} {characters : List Char} {expression : SExpr}
    (rendered : Rendered atom characters expression) : readExpression expression = .ok atom :=
  SpaceSemantics.readExpression_named (read_raw_expression rendered) (rendered_named rendered)

theorem read_expressions {items : List Atom} {parts : List (List Char)} {expressions : List SExpr}
    (rendered : RenderedList items parts expressions) : readExpressions expressions = .ok items := by
  simp only [readExpressions, read_raw_expressions rendered, Except.map,
    SpaceSemantics.Anonymous.resolveList_of_named items (renderedList_named rendered)]

theorem render_named {atom : Atom} {text : String} (rendered : render? atom = some text) :
    "_" ∉ MORK.atomFreeVars atom := by
  unfold render? at rendered
  cases chars : chars? atom with
  | none => simp only [chars, Option.map_none, reduceCtorEq] at rendered
  | some characters =>
      obtain ⟨expression, source⟩ := rendered_of_chars chars
      exact rendered_named source

/-! ## The scanner -/

section Scanner

open SourceScanSegments (makeScanState initialScanState)
open private stepScan parserDialectOf pushChar finalizeCurr markStarted grammarLineCommentStartChar?
  grammarSExprOpenChar grammarSExprCloseChar ParserDialect.grammarSpec ParserDialect.syntaxSpec
  from Algorithms.MeTTa.Simple.Parser

set_option linter.unusedSimpArgs false

private theorem dialect_comment :
    grammarLineCommentStartChar? (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)) = some ';' := rfl
private theorem dialect_open : grammarSExprOpenChar (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)) = '(' := rfl
private theorem dialect_close : grammarSExprCloseChar (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)) = ')' :=
  rfl
private theorem dialect_quote : (ParserDialect.syntaxSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)).lexer.stringDelimiter = '"' :=
  rfl
private theorem dialect_escape : (ParserDialect.syntaxSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)).lexer.escapeChar = '\\' :=
  rfl

/-- Inside a form, outside strings. -/
def inner (line depth start : Nat) : SourceAccumulatorScan.Point := ⟨line, depth, false, false, false, true, start⟩

/-- Inside a string within a form. -/
def quoted (line depth start : Nat) : SourceAccumulatorScan.Point := ⟨line, depth, false, true, false, true, start⟩

private theorem step_inner_token {character : Char} (token : tokenChar character) (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (inner line depth start) (inner line depth start) [character] [character] := by
  obtain ⟨white, comment, opening, closing, quote⟩ := token
  have newline : character ≠ '\n' := by
    intro same; subst same; exact absurd white (by decide)
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, inner, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp [Ne.symm comment, newline, quote, opening, closing, white]

private theorem step_inner_space (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (inner line depth start) (inner line depth start) [' '] [' '] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, inner, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp

private theorem step_inner_open (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (inner line depth start) (inner line (depth + 1) start) ['('] ['('] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, inner, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp

private theorem step_inner_close (line depth start : Nat) (positive : 0 < depth) :
    SourceAccumulatorScan.Agreement (inner line (depth + 1) start) (inner line depth start) [')'] [')'] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, inner, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp [Nat.pos_iff_ne_zero.mp positive]

private theorem step_open_quote (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (inner line depth start) (quoted line depth start) ['"'] ['"'] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, inner, quoted, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp

private theorem step_close_quote (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (quoted line depth start) (inner line depth start) ['"'] ['"'] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, inner, quoted, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp

/-- Inside a string within a form, after an escape character. -/
def quotedEscaped (line depth start : Nat) : SourceAccumulatorScan.Point := ⟨line, depth, false, true, true, true, start⟩

private theorem step_quoted_escape (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (quoted line depth start) (quotedEscaped line depth start) ['\\'] ['\\'] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, quoted, quotedEscaped, SourceAccumulatorScan.Point.state,
    SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp

private theorem step_escaped {character : Char} (newline : character ≠ '\n') (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (quotedEscaped line depth start) (quoted line depth start) [character] [character] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, quoted, quotedEscaped, SourceAccumulatorScan.Point.state,
    SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp [newline]

private theorem step_quoted_plain {character : Char} (notEscape : character ≠ '\\') (notQuote : character ≠ '"')
    (newline : character ≠ '\n') (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (quoted line depth start) (quoted line depth start) [character] [character] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, quoted, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp [notEscape, notQuote, newline]

private theorem scan_token_chars (characters : List Char) (allToken : ∀ character ∈ characters, tokenChar character)
    (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (inner line depth start) (inner line depth start) characters characters := by
  induction characters with
  | nil => exact SourceAccumulatorScan.agreement_empty _
  | cons character rest ih =>
    have whole := SourceAccumulatorScan.agreement_append _ _ _ [character] rest [character] rest
      (step_inner_token (allToken character List.mem_cons_self) line depth start)
      (ih fun other member => allToken other (List.mem_cons_of_mem _ member))
    simpa using whole

private theorem scan_escaped_chars {characters : List Char} (body : StringLiteral.EscapedBody characters)
    (line depth start : Nat) :
    SourceAccumulatorScan.Agreement (quoted line depth start) (quoted line depth start) characters characters := by
  induction body with
  | nil => exact SourceAccumulatorScan.agreement_empty _
  | @plain character rest notEscape notQuote newline _ ih =>
    have whole := SourceAccumulatorScan.agreement_append _ _ _ [character] rest [character] rest
      (step_quoted_plain notEscape notQuote newline line depth start) ih
    simpa using whole
  | @escape character rest newline _ ih =>
    have pair := SourceAccumulatorScan.agreement_append _ _ _ ['\\'] [character] ['\\'] [character]
      (step_quoted_escape line depth start) (step_escaped newline line depth start)
    have whole := SourceAccumulatorScan.agreement_append _ _ _ ['\\', character] rest ['\\', character] rest
      (by simpa using pair) ih
    simpa using whole

private theorem var_token_chars {name : String} (safeName : symbolSafe name = true) :
    ∀ character ∈ '$' :: name.toList, tokenChar character := by
  intro character member
  rcases List.mem_cons.mp member with same | rest
  · subst same; exact ⟨rfl, by decide, by decide, by decide, by decide⟩
  · exact symbol_token_chars safeName character rest

private theorem int_token_chars (value : Int) : ∀ character ∈ intChars value, tokenChar character := by
  cases value with
  | ofNat natural => exact decimal_token_chars natural
  | negSucc natural =>
    intro character member
    rcases List.mem_cons.mp member with same | rest
    · subst same; exact ⟨rfl, by decide, by decide, by decide, by decide⟩
    · exact decimal_token_chars (natural + 1) character rest

private theorem bool_token_chars (value : Bool) :
    ∀ character ∈ (if value then "True".toList else "False".toList), tokenChar character := by
  cases value <;> decide

mutual
  /-- Inside a form, a rendered atom passes through the scanner whole. -/
  theorem scan_rendered : ∀ {atom : Atom} {characters : List Char} {expression : SExpr},
      Rendered atom characters expression → ∀ line depth start, 0 < depth →
      SourceAccumulatorScan.Agreement (inner line depth start) (inner line depth start) characters characters
    | _, _, _, .expression children, line, depth, start, positive => by
      have whole := SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _
        (SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _ (step_inner_open line depth start)
          (scan_items children line (depth + 1) start (by omega)))
        (step_inner_close line depth start positive)
      simpa using whole
    | _, _, _, .string value, line, depth, start, _ => by
      have whole := SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _
        (SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _ (step_open_quote line depth start)
          (scan_escaped_chars (StringLiteral.canonicalBody_escaped value.toList) line depth start))
        (step_close_quote line depth start)
      simpa using whole
    | _, _, _, .symbol symbol safeSymbol, line, depth, start, _ =>
      scan_token_chars _ (symbol_token_chars safeSymbol) line depth start
    | _, _, _, .var name safeName, line, depth, start, _ =>
      scan_token_chars _ (var_token_chars (variableSafe_parts safeName).1) line depth start
    | _, _, _, .int value, line, depth, start, _ =>
      scan_token_chars _ (int_token_chars value) line depth start
    | _, _, _, .bool value, line, depth, start, _ =>
      scan_token_chars _ (bool_token_chars value) line depth start

  theorem scan_items : ∀ {children : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList children parts expressions → ∀ line depth start, 0 < depth →
      SourceAccumulatorScan.Agreement (inner line depth start) (inner line depth start) (joinSpace parts)
        (joinSpace parts)
    | _, _, _, .nil, _, _, _, _ => SourceAccumulatorScan.agreement_empty _
    | _, _, _, .cons (parts := []) head .nil, line, depth, start, positive => by
      simpa [joinSpace] using scan_rendered head line depth start positive
    | _, _, _, .cons (parts := next :: others) head tail, line, depth, start, positive => by
      have whole := SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _
        (SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _ (scan_rendered head line depth start positive)
          (step_inner_space line depth start))
        (scan_items tail line depth start positive)
      simpa [joinSpace, List.append_assoc] using whole
end

/-- Between forms, at the start of a line. -/
def between (line : Nat) : SourceAccumulatorScan.Point := ⟨line, 0, false, false, false, false, line⟩

private theorem step_top_open (line : Nat) :
    SourceAccumulatorScan.Agreement (between line) (inner line 1 line) ['('] ['('] := by
  intro current forms
  simp only [List.foldl_cons, List.foldl_nil, between, inner, SourceAccumulatorScan.Point.state,
    SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, markStarted, Option.isSome_none, Bool.false_eq_true, if_false]
  simp

private theorem trimmed_form (characters : List Char) :
    (String.ofList ('(' :: characters ++ [')'])).trimAscii.toString = String.ofList ('(' :: characters ++ [')']) := by
  apply SourceScanSegments.trimAscii_of_boundary
  · simp [String.toList_ofList]
  · rw [String.toList_ofList, show '(' :: characters ++ [')'] = ('(' :: characters) ++ [')'] from rfl,
      List.getLast?_concat]
    rfl

private theorem empty_trimmed : ("" : String).trimAscii.isEmpty = true := by
  have emptyTrim : "".trimAscii.toString = "" := SourceScanSegments.trimAscii_of_boundary "" rfl rfl
  rw [← String.Slice.isEmpty_copy]
  change "".trimAscii.toString.isEmpty = true
  rw [emptyTrim]
  rfl

private theorem step_top_close (line : Nat) (inside : List Char) (forms : List (Nat × String)) :
    SourceScanSegments.step ((inner line 1 line).state (inside.reverse ++ ['(']) forms) ')' =
      (between line).state [] ((line, String.ofList ('(' :: inside ++ [')'])) :: forms) := by
  have text : String.ofList (')' :: (inside.reverse ++ ['('])).reverse = String.ofList ('(' :: inside ++ [')']) := by
    simp
  have nonempty : (String.ofList ('(' :: inside ++ [')'])).trimAscii.isEmpty = false := by
    rw [← String.Slice.isEmpty_copy]
    change (String.ofList ('(' :: inside ++ [')'])).trimAscii.toString.isEmpty = false
    rw [trimmed_form]
    exact SourceScanSegments.ofList_nonempty _ (by simp)
  simp only [between, inner, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, finalizeCurr, Option.isSome_none, Bool.false_eq_true, if_false]
  simp only [text, trimmed_form, nonempty]
  simp

private theorem step_newline (line : Nat) (forms : List (Nat × String)) :
    SourceScanSegments.step ((between line).state [] forms) '\n' = (between (line + 1)).state [] forms := by
  simp only [between, SourceAccumulatorScan.Point.state, SourceScanSegments.step]
  simp only [stepScan, makeScanState, dialect_comment, dialect_open, dialect_close, dialect_quote, dialect_escape,
    pushChar, finalizeCurr, Option.isSome_none, Bool.false_eq_true, if_false]
  simp [empty_trimmed]

/-- **One rendered expression on one line is one form.** -/
theorem scan_line {items : List Atom} {parts : List (List Char)} {expressions : List SExpr}
    (children : RenderedList items parts expressions) (line : Nat) (forms : List (Nat × String)) :
    (('(' :: joinSpace parts ++ [')']) ++ ['\n']).foldl SourceScanSegments.step ((between line).state [] forms) =
      (between (line + 1)).state [] ((line, String.ofList ('(' :: joinSpace parts ++ [')'])) :: forms) := by
  have opened := SourceAccumulatorScan.agreement_append _ _ _ _ _ _ _ (step_top_open line)
    (scan_items children line 1 line (by omega))
  have shape : ('(' :: joinSpace parts ++ [')']) ++ ['\n'] = (['('] ++ joinSpace parts) ++ [')', '\n'] := by simp
  rw [shape, List.foldl_append, opened [] forms]
  simp only [List.foldl_cons, List.foldl_nil, List.append_nil, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]
  rw [show (joinSpace parts).reverse ++ ['('] = (joinSpace parts).reverse ++ ['('] from rfl, step_top_close,
    step_newline]

/-- A program's text: each form on its own line. -/
def textChars (lines : List (List Char)) : List Char := lines.flatMap (· ++ ['\n'])

/-- The forms the scanner reports, numbered from a line. -/
def numbered (line : Nat) : List (List Char) → List (Nat × String)
  | [] => []
  | characters :: rest => (line, String.ofList characters) :: numbered (line + 1) rest

/-- Every atom is an expression. -/
def AllExpressions (atoms : List Atom) : Prop := ∀ atom ∈ atoms, ∃ items, atom = .expression items

theorem scan_text : ∀ {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr},
    RenderedList atoms lines expressions → AllExpressions atoms → ∀ (line : Nat) (forms : List (Nat × String)),
    (textChars lines).foldl SourceScanSegments.step ((between line).state [] forms) =
      (between (line + lines.length)).state [] ((numbered line lines).reverse ++ forms)
  | _, _, _, .nil, _, line, forms => by simp [textChars, numbered]
  | _, _, _, @RenderedList.cons _ _ _ otherParts _ _ head tail, expressionsOnly, line, forms => by
    obtain ⟨items, same⟩ := expressionsOnly _ List.mem_cons_self
    subst same
    cases head with
    | @expression _ innerParts _ children =>
      have rest := scan_text tail (fun atom member => expressionsOnly atom (List.mem_cons_of_mem _ member))
        (line + 1) ((line, String.ofList ('(' :: joinSpace innerParts ++ [')'])) :: forms)
      rw [show textChars (('(' :: joinSpace innerParts ++ [')']) :: otherParts) =
          (('(' :: joinSpace innerParts ++ [')']) ++ ['\n']) ++ textChars otherParts from rfl, List.foldl_append,
        scan_line children line forms, rest]
      simp [numbered, Nat.add_assoc, Nat.add_comm 1]

open private splitProgramForms from Algorithms.MeTTa.Simple.Parser

/-- **The scanner reports exactly the forms, one per line.** -/
theorem split_text {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr}
    (rendered : RenderedList atoms lines expressions) (expressionsOnly : AllExpressions atoms) :
    splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta) (String.ofList (textChars lines)) =
      .ok (numbered 1 lines) := by
  have scanned := scan_text rendered expressionsOnly 1 []
  have initial : (between 1).state [] [] = SourceScanSegments.initialScanState := rfl
  rw [initial] at scanned
  have actual : (textChars lines).foldl (stepScan (parserDialectOf MeTTailCore.MeTTaSyntax.petta))
      SourceScanSegments.initialScanState =
      (between (1 + lines.length)).state [] ((numbered 1 lines).reverse ++ []) := scanned
  unfold splitProgramForms
  rw [String.toList_ofList]
  simp only [SourceScanSegments.initialScanState, makeScanState] at actual
  rw [actual]
  simp [between, SourceAccumulatorScan.Point.state, makeScanState, finalizeCurr, empty_trimmed]

end Scanner



/-! ## Commands and the program -/

section Commands

open Algorithms.MeTTa.Simple.Parser (ParseError)
open private parserDialectOf coalesceEvalPrefixForms coalesceEvalPrefixForms.go parseSingleSExprWith tokenizeWith
  ParserDialect.grammarSpec ParserDialect.syntaxSpec from Algorithms.MeTTa.Simple.Parser

private theorem trimmed_form' (characters : List Char) :
    (String.ofList ('(' :: characters ++ [')'])).trimAscii.toString = String.ofList ('(' :: characters ++ [')']) := by
  apply SourceScanSegments.trimAscii_of_boundary
  · simp [String.toList_ofList]
  · rw [String.toList_ofList, show '(' :: characters ++ [')'] = ('(' :: characters) ++ [')'] from rfl,
      List.getLast?_concat]
    rfl

private theorem form_ne_bang (characters : List Char) :
    (String.ofList ('(' :: characters ++ [')'])).trimAscii.toString ≠ "!" := by
  rw [trimmed_form']
  intro same
  have heads := congrArg (fun text : String => text.toList.head?) same
  simp at heads

/-- The coalescing pass keeps forms that are not a bare evaluation prefix. -/
private theorem go_keeps (cfg : _) (token : String) :
    ∀ (accumulated : List (Nat × String)) (pending : Nat × String) (rest : List (Nat × String)),
      (∀ form ∈ pending :: rest, form.2.trimAscii.toString ≠ token) →
      coalesceEvalPrefixForms.go cfg token accumulated (some pending) rest =
        accumulated.reverse ++ pending :: rest := by
  intro accumulated pending rest
  induction rest generalizing accumulated pending with
  | nil => intro _; simp [coalesceEvalPrefixForms.go]
  | cons next rest ih =>
    intro different
    obtain ⟨line, text⟩ := pending
    obtain ⟨nextLine, nextText⟩ := next
    have notBang := different (line, text) List.mem_cons_self
    rw [coalesceEvalPrefixForms.go]
    simp only [notBang, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
    rw [ih _ _ fun form member => different form (List.mem_cons_of_mem _ member)]
    simp

/-- A numbered list of rendered forms. -/
def commands (line : Nat) : List SExpr → List (Nat × Bool × SExpr)
  | [] => []
  | expression :: rest => (line, false, expression) :: commands (line + 1) rest

/-- The parse of each rendered form, by the actual per-form step. -/
private theorem mapM_forms {step : Nat × String → Except ParseError (Nat × Bool × SExpr)}
    (each : ∀ (line : Nat) {items : List Atom} {parts : List (List Char)} {expressions : List SExpr},
      RenderedList items parts expressions →
      step (line, String.ofList ('(' :: joinSpace parts ++ [')'])) = .ok (line, false, .list expressions)) :
    ∀ {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr},
      RenderedList atoms lines expressions → AllExpressions atoms → ∀ line,
      (numbered line lines).mapM step = .ok (commands line expressions)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons head tail, expressionsOnly, line => by
    obtain ⟨items, same⟩ := expressionsOnly _ List.mem_cons_self
    subst same
    cases head with
    | expression children =>
      have rest := mapM_forms each tail
        (fun atom member => expressionsOnly atom (List.mem_cons_of_mem _ member)) (line + 1)
      simp only [numbered, List.mapM_cons, each line children, rest, commands]
      rfl

/-- Each rendered form parses to its expression. -/
theorem parse_form {items : List Atom} {parts : List (List Char)} {expressions : List SExpr}
    (children : RenderedList items parts expressions) :
    parseSingleSExprWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta)
      (String.ofList ('(' :: joinSpace parts ++ [')'])) = .ok (.list expressions) := by
  have agreement := agreement_append _ _ _ _ _ _ _ lex_open (lex_items children)
  have lexed : SourceLexSegments.lex ('(' :: joinSpace parts ++ [')']) [] [] = tokens (.list expressions) := by
    have replayed := SourceAccumulatorLex.original_lexer_replay ('(' :: joinSpace parts ++ [')'])
      ("(" :: (childTokens expressions ++ [")"])) (by simpa using agreement)
    simpa [tokens] using replayed
  have tokenized := SourceLexSegments.tokenized_of_initial (String.ofList ('(' :: joinSpace parts ++ [')']))
    ('(' :: joinSpace parts ++ [')']) ('(' :: joinSpace parts ++ [')']) [] [] _ rfl rfl rfl rfl lexed
  exact SourceSExprAdmission.single_of_tokens _ _ (rendered_safe (.expression children)) tokenized

private theorem dialect_prefix :
    (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)).evalPrefixToken = "!" := rfl

/-- The reported forms are rendered expressions. -/
private theorem numbered_forms : ∀ {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr},
    RenderedList atoms lines expressions → AllExpressions atoms → ∀ line, ∀ form ∈ numbered line lines,
      ∃ characters, form.2 = String.ofList ('(' :: characters ++ [')'])
  | _, _, _, .nil, _, _ => by simp [numbered]
  | _, _, _, .cons head tail, expressionsOnly, line => by
    obtain ⟨items, same⟩ := expressionsOnly _ List.mem_cons_self
    subst same
    cases head with
    | @expression _ innerParts _ children =>
      intro form member
      simp only [numbered, List.mem_cons] at member
      rcases member with rfl | later
      · exact ⟨joinSpace innerParts, rfl⟩
      · exact numbered_forms tail (fun atom member => expressionsOnly atom (List.mem_cons_of_mem _ member))
          (line + 1) form later

/-- **The reader's commands are the rendered forms, none of them a query.** -/
theorem commands_text {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr}
    (rendered : RenderedList atoms lines expressions) (expressionsOnly : AllExpressions atoms) :
    Algorithms.MeTTa.Simple.Parser.parseSExprCommandsWithDetailed MeTTailCore.MeTTaSyntax.petta
      (String.ofList (textChars lines)) = .ok (commands 1 expressions) := by
  have coalesced : coalesceEvalPrefixForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta) (numbered 1 lines) =
      numbered 1 lines := by
    have formsShape := numbered_forms rendered expressionsOnly 1
    unfold coalesceEvalPrefixForms
    cases numberedForms : numbered 1 lines with
    | nil => rfl
    | cons first rest =>
      rw [numberedForms] at formsShape
      rw [coalesceEvalPrefixForms.go, go_keeps _ _ [] first rest]
      · rfl
      · intro form member
        obtain ⟨characters, text⟩ := formsShape form member
        rw [text, dialect_prefix]
        exact form_ne_bang characters
  unfold Algorithms.MeTTa.Simple.Parser.parseSExprCommandsWithDetailed
  dsimp only
  rw [split_text rendered expressionsOnly]
  simp only [bind, Except.bind]
  rw [coalesced]
  apply mapM_forms _ rendered expressionsOnly 1
  intro line items parts expressions children
  rw [dialect_prefix]
  split_ifs with query
  · exfalso
    simp only [Bool.and_eq_true] at query
    have prefixed := query.1
    rw [String.startsWith_string_iff] at prefixed
    simp [String.toList_ofList] at prefixed
  · rw [parse_form children]
    simp only [Bool.not_eq_true] at query
    simp only [query]
    rfl

end Commands

/-! ## The program reads back -/

private theorem mapM_ok {α β ε : Type} (f : α → Except ε β) (g : α → β) :
    ∀ items : List α, (∀ item ∈ items, f item = .ok (g item)) → items.mapM f = .ok (items.map g)
  | [], _ => rfl
  | item :: items, each => by
    rw [List.mapM_cons, each item List.mem_cons_self,
      mapM_ok f g items fun other member => each other (List.mem_cons_of_mem _ member)]
    rfl

/-- What the reader keeps of a command: its query flag and its atom. -/
def decodedCommand (command : Nat × Bool × SExpr) : Bool × Atom :=
  (command.2.1, match readExpression command.2.2 with
    | .ok atom => atom
    | .error _ => .symbol "")

private theorem commands_read : ∀ {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr},
    RenderedList atoms lines expressions → ∀ line,
    (∀ command ∈ commands line expressions, readExpression command.2.2 = .ok (decodedCommand command).2) ∧
      (commands line expressions).map decodedCommand = atoms.map fun atom => (false, atom)
  | _, _, _, .nil, _ => ⟨by simp [commands], rfl⟩
  | _, _, _, .cons head tail, line => by
    obtain ⟨later, mapped⟩ := commands_read tail (line + 1)
    have read := read_expression head
    refine ⟨?_, ?_⟩
    · intro command member
      simp only [commands, List.mem_cons] at member
      rcases member with rfl | rest
      · simp [decodedCommand, read]
      · exact later command rest
    · simp only [commands, List.map_cons, mapped, decodedCommand, read]

/-- **Read after render, for a program text.** Lines rendered from expressions read back as
exactly those forms, collected into a program, with no queries. -/
theorem read_text {atoms : List Atom} {lines : List (List Char)} {expressions : List SExpr}
    (rendered : RenderedList atoms lines expressions) (expressionsOnly : AllExpressions atoms) :
    SpaceSemantics.readProgram (String.ofList (textChars lines)) =
      (SpaceSemantics.collect atoms).map fun program => { program with initializers := [] } := by
  obtain ⟨read, mapped⟩ := commands_read rendered 1
  unfold SpaceSemantics.readProgram
  rw [commands_text rendered expressionsOnly]
  simp only [Except.mapError, bind, Except.bind]
  rw [mapM_ok _ decodedCommand (commands 1 expressions) (fun command member => by
    rw [read command member]
    rfl)]
  rw [mapped]
  simp only [List.filter_map, Function.comp_def, Bool.not_false, List.filter_true, List.map_map,
    List.filter_false, List.map_nil]
  simp only [List.map_id']
  cases SpaceSemantics.collect atoms <;> rfl

/-- A program's source text: its loaded forms in order, one per line. -/
def renderProgram? (program : SpaceSemantics.Program) : Option String :=
  (charsList? (SpaceSemantics.loadedAtoms program)).map fun lines => String.ofList (textChars lines)

/-- **Read after render.** A program whose forms are expressions and render reads back as the
program its forms collect to, with no queries. -/
theorem read_render {program : SpaceSemantics.Program} {text : String} (rendered : renderProgram? program = some text)
    (expressionsOnly : AllExpressions (SpaceSemantics.loadedAtoms program)) :
    SpaceSemantics.readProgram text =
      (SpaceSemantics.collect (SpaceSemantics.loadedAtoms program)).map fun read => { read with initializers := [] } := by
  unfold renderProgram? at rendered
  cases listed : charsList? (SpaceSemantics.loadedAtoms program) with
  | none => rw [listed] at rendered; cases rendered
  | some lines =>
    rw [listed] at rendered
    cases rendered
    obtain ⟨expressions, children⟩ := renderedList_of_chars listed
    exact read_text children expressionsOnly

theorem named_variable_roundtrip : readExpression (.atom "$named") = .ok (.var "named") := by
  simpa only [show String.ofList ('$' :: "named".toList) = "$named" by decide] using
    read_expression (Rendered.var "named" (by decide))

theorem anonymous_variable_refused : render? (.var "_") = none := by
  simp only [render?, chars?, variableSafe, bne_self_eq_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, Option.map_none]

theorem underscore_symbol_rendered : render? (.symbol "_") = some "_" := by
  decide

#print axioms read_expression
#print axioms read_expressions
#print axioms render_named
#print axioms read_render
#print axioms named_variable_roundtrip
#print axioms anonymous_variable_refused
#print axioms underscore_symbol_rendered

example : render? (.symbol "λ") = some "λ" := by decide +kernel
example : render? (.var "変数") = some "$変数" := by decide +kernel
example : render? (.symbol "two words") = none := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
