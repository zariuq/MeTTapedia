import Mettapedia.Languages.Chaitin.Syntax
import Mathlib.Data.Nat.Basic

/-!
# Chaitin's binary Lisp reader

The binary `read-exp` reader is the `getbit`/`getrecord`/`getexp` reader in
Chaitin's 1997 `lisp.m`. It reads bytes most-significant bit first until LF,
deletes nonprintable characters, reads only the first S-expression, and supplies
closing parentheses when the record ends. Apostrophes and brackets have no
special meaning in this reader; they belong to the separate source frontend.
-/

namespace Mettapedia.Languages.Chaitin.Reader

def bitNat (bit : Bool) : Nat := if bit then 1 else 0

/-- Fixed-width, most-significant-bit-first binary representation. -/
def encodeBits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value => encodeBits width (value / 2) ++ [decide (value % 2 = 1)]

def encodeByte (value : Nat) : List Bool := encodeBits 8 value

def bitValue (input : List Bool) : Nat :=
  input.foldl (fun accumulated bit => 2 * accumulated + bitNat bit) 0

@[simp] theorem encodeBits_length (width value : Nat) :
    (encodeBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeBits, ih]

@[simp] theorem encodeByte_length (value : Nat) : (encodeByte value).length = 8 :=
  encodeBits_length 8 value

theorem bitNat_remainder (value : Nat) :
    bitNat (decide (value % 2 = 1)) = value % 2 := by
  have small := Nat.mod_lt value (by decide : 0 < 2)
  by_cases one : value % 2 = 1
  · simp [bitNat, one]
  · simp [bitNat, one]
    omega

@[simp] theorem bitValue_append_bit (input : List Bool) (bit : Bool) :
    bitValue (input ++ [bit]) = 2 * bitValue input + bitNat bit := by
  simp [bitValue, List.foldl_append]

theorem bitValue_encodeBits (width value : Nat) :
    bitValue (encodeBits width value) = value % 2 ^ width := by
  induction width generalizing value with
  | zero => simp only [bitValue, encodeBits, List.foldl_nil, Nat.pow_zero, Nat.mod_one]
  | succ width ih =>
      rw [encodeBits, bitValue_append_bit, ih, bitNat_remainder]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ width) 2, Nat.mod_mul]
      omega

theorem bitValue_encodeByte (value : Nat) (small : value < 256) :
    bitValue (encodeByte value) = value := by
  rw [encodeByte, bitValue_encodeBits]
  exact Nat.mod_eq_of_lt small

/-- The byte framing used by `bits`, for the historical ASCII value domain. -/
def bits (expression : SExpr) : List Bool :=
  (expression.render.toList ++ ['\n']).flatMap (fun character => encodeByte character.toNat)

theorem bits_length (expression : SExpr) :
    (bits expression).length = 8 * (expression.render.toList.length + 1) := by
  unfold bits
  have all (characters : List Char) :
      (characters.flatMap (fun character => encodeByte character.toNat)).length =
        8 * characters.length := by
    induction characters with
    | nil => rfl
    | cons head tail ih => simp [ih, Nat.mul_add, Nat.add_comm]
  simpa using all (expression.render.toList ++ ['\n'])

def printable (character : Char) : Bool :=
  decide (32 ≤ character.toNat ∧ character.toNat < 127)

def atomOfChars (characters : List Char) : SExpr :=
  if characters != [] && characters.all Char.isDigit then
    .number (characters.foldl (fun value character => 10 * value + character.toNat - 48) 0)
  else .symbol (String.ofList characters)

def atomOfWord (word : String) : SExpr := atomOfChars word.toList

inductive Token where
  | leftParen
  | rightParen
  | atom (value : SExpr)
deriving Repr

def flushWord (reversedWord : List Char) (reversedTokens : List Token) : List Token :=
  match reversedWord with
  | [] => reversedTokens
  | _ :: _ => .atom (atomOfChars reversedWord.reverse) :: reversedTokens

def tokenizeAux : List Char → List Char → List Token → List Token
  | [], reversedWord, reversedTokens => (flushWord reversedWord reversedTokens).reverse
  | character :: rest, reversedWord, reversedTokens =>
      if character = ' ' then tokenizeAux rest [] (flushWord reversedWord reversedTokens)
      else if character = '(' then
        tokenizeAux rest [] (.leftParen :: flushWord reversedWord reversedTokens)
      else if character = ')' then
        tokenizeAux rest [] (.rightParen :: flushWord reversedWord reversedTokens)
      else tokenizeAux rest (character :: reversedWord) reversedTokens

def tokenize (characters : List Char) : List Token := tokenizeAux characters [] []

/-- Complete an unfinished list, and then all its unfinished ancestors. -/
def closeLists (reversedValues : List SExpr) : List (List SExpr) → SExpr
  | [] => SExpr.nil
  | [_] => .list reversedValues.reverse
  | outer :: next :: rest =>
      closeLists (.list reversedValues.reverse :: outer) (next :: rest)

/-- Stack entries contain the already read children in reverse order. -/
def parseTokensAux : List Token → List (List SExpr) → List SExpr → SExpr
  | [], stack, reversedValues => closeLists reversedValues stack
  | .leftParen :: rest, stack, reversedValues =>
      parseTokensAux rest (reversedValues :: stack) []
  | .rightParen :: _, [], _ => SExpr.nil
  | .rightParen :: _, [_], reversedValues => .list reversedValues.reverse
  | .rightParen :: rest, outer :: next :: stack, reversedValues =>
      parseTokensAux rest (next :: stack) (.list reversedValues.reverse :: outer)
  | .atom value :: _, [], _ => value
  | .atom value :: rest, outer :: stack, reversedValues =>
      parseTokensAux rest (outer :: stack) (value :: reversedValues)

def parseTokens (tokens : List Token) : SExpr := parseTokensAux tokens [] []

def parseRecord (record : String) : SExpr :=
  parseTokens (tokenize (record.toList.filter printable))

@[simp] theorem parseTokens_empty : parseTokens [] = SExpr.nil := rfl

/-- The rest of a record is ignored after its first atomic expression. -/
@[simp] theorem parseTokens_atom (value : SExpr) (surplus : List Token) :
    parseTokens (.atom value :: surplus) = value := rfl

/-- A leading right parenthesis denotes the empty list. -/
@[simp] theorem parseTokens_rightParen (surplus : List Token) :
    parseTokens (.rightParen :: surplus) = SExpr.nil := rfl

structure RecordState where
  partialByte : Nat := 0
  partialBits : Nat := 0
  reversedChars : List Char := []
deriving DecidableEq, Repr

def initialRecord : RecordState := {}

/-- One binary input action. Completion occurs only at a complete LF byte. -/
def feedBit (state : RecordState) (bit : Bool) : Sum RecordState SExpr :=
  let byte := 2 * state.partialByte + bitNat bit
  if state.partialBits + 1 = 8 then
    if byte = 10 then
      .inr (parseTokens (tokenize state.reversedChars.reverse))
    else
      .inl {
        partialByte := 0
        partialBits := 0
        reversedChars := if 32 ≤ byte ∧ byte < 127 then
          Char.ofNat byte :: state.reversedChars else state.reversedChars }
  else
    .inl { state with partialByte := byte, partialBits := state.partialBits + 1 }

/-- Read available bits, retaining every bit after the first complete record. -/
def feedBits : RecordState → List Bool → Sum RecordState (SExpr × List Bool)
  | state, [] => .inl state
  | state, bit :: rest =>
      match feedBit state bit with
      | .inl next => feedBits next rest
      | .inr expression => .inr (expression, rest)

theorem feedBits_append_completed (state : RecordState) (input rest suffix : List Bool)
    (expression : SExpr) (completed : feedBits state input = .inr (expression, rest)) :
    feedBits state (input ++ suffix) = .inr (expression, rest ++ suffix) := by
  induction input generalizing state with
  | nil => cases completed
  | cons bit input ih =>
      cases received : feedBit state bit with
      | inl next =>
          simp only [feedBits, received] at completed
          simpa only [List.cons_append, feedBits, received] using ih next completed
      | inr value =>
          simp only [feedBits, received, Sum.inr.injEq, Prod.mk.injEq] at completed
          rcases completed with ⟨rfl, rfl⟩
          simp only [List.cons_append, feedBits, received]

theorem feedBits_append_waiting (state next : RecordState) (input suffix : List Bool)
    (waiting : feedBits state input = .inl next) :
    feedBits state (input ++ suffix) = feedBits next suffix := by
  induction input generalizing state with
  | nil => cases waiting; rfl
  | cons bit input ih =>
      cases received : feedBit state bit with
      | inl later =>
          simp only [feedBits, received] at waiting
          simpa only [List.cons_append, feedBits, received] using ih later waiting
      | inr value => simp only [feedBits, received] at waiting; cases waiting

theorem empty_record : parseRecord "" = SExpr.nil := by rfl
theorem nested_record : parseRecord "(abc(def ghi)jkl)" =
    .list [.symbol "abc", .list [.symbol "def", .symbol "ghi"], .symbol "jkl"] := by rfl
theorem missing_parentheses : parseRecord "((a" = .list [.list [.symbol "a"]] := by rfl
theorem surplus_record : parseRecord "a b c" = .symbol "a" := by rfl
theorem initial_right_parenthesis : parseRecord ")a" = SExpr.nil := by rfl
theorem leading_zero_numeral : parseRecord "0003" = .number 3 := by rfl
theorem underscores_are_not_digits : parseRecord "1_000" = .symbol "1_000" := by rfl
theorem binary_quote_is_word : parseRecord "'a" = .symbol "'a" := by rfl
theorem binary_brackets_are_words : parseRecord "[x]" = .symbol "[x]" := by rfl
theorem nonprintable_deleted : parseRecord "a\tb" = .symbol "ab" := by rfl
theorem bits_a : bits (.symbol "a") =
    [false, true, true, false, false, false, false, true,
     false, false, false, false, true, false, true, false] := by rfl
theorem read_a : feedBits initialRecord (bits (.symbol "a")) =
    .inr (.symbol "a", []) := by rfl
theorem missing_newline : feedBits initialRecord (encodeByte 97) =
    .inl { reversedChars := ['a'] } := by rfl
theorem discarded_byte : feedBits initialRecord (encodeByte 255 ++ encodeByte 10) =
    .inr (SExpr.nil, []) := by rfl
theorem preserves_later_input (suffix : List Bool) :
    feedBits initialRecord (bits (.symbol "a") ++ suffix) = .inr (.symbol "a", suffix) := by
  simpa using feedBits_append_completed initialRecord (bits (.symbol "a")) [] suffix
    (.symbol "a") read_a

end Mettapedia.Languages.Chaitin.Reader
