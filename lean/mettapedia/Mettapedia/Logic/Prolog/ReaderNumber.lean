import Mettapedia.Logic.Prolog.ReaderLexer

/-!
# Exact numeric-token interpretation

Numeric tokens are converted to the canonical source constants without using
decimal text as a runtime value. Integers use Lean's arbitrary-precision
`Int`; decimal/scientific floats are rounded once by `Float.ofScientific` and
stored by their IEEE-754 bits. ISO `0'c` character-code syntax is decoded
directly to an integer.

Rational and NaN lexical forms remain explicit errors until their SWI value
normalization and identity behavior are represented.
-/

namespace Mettapedia.Logic.Prolog.ReaderNumber

open SourceSignature

inductive Error where
  | empty
  | invalidDigit (character : Char) (base : Nat)
  | invalidInteger (lexeme : String)
  | invalidFloat (lexeme : String)
  | invalidCharacterCode (lexeme : String)
  | unsupportedRational (lexeme : String)
  | unsupportedNaN (lexeme : String)
deriving DecidableEq, Repr

private def asciiDigit? (character : Char) : Option Nat :=
  if '0' <= character && character <= '9' then
    some (character.toNat - '0'.toNat)
  else if 'a' <= character && character <= 'f' then
    some (10 + character.toNat - 'a'.toNat)
  else if 'A' <= character && character <= 'F' then
    some (10 + character.toNat - 'A'.toNat)
  else
    none

private def parseNatBase (base : Nat) (characters : List Char) :
    Except Error Nat := by
  let rec loop : List Char -> Nat -> Bool -> Bool -> Except Error Nat
    | [], value, sawDigit, previousWasDigit =>
        if sawDigit && previousWasDigit then .ok value else .error .empty
    | character :: rest, value, sawDigit, previousWasDigit =>
        if character = '_' then
          if previousWasDigit then
            loop rest value sawDigit false
          else
            .error (.invalidDigit character base)
        else
          match asciiDigit? character with
          | some digit =>
              if digit < base then
                loop rest (value * base + digit) true true
              else .error (.invalidDigit character base)
          | none => .error (.invalidDigit character base)
  exact loop characters 0 false false

private def parseCharacterCode (lexeme : String) : Except Error Constant :=
  match lexeme.toList with
  | ['0', '\'', character] =>
      .ok (.integer (Int.ofNat character.toNat))
  | ['0', '\'', '\\', escaped] =>
      match ReaderLexer.simpleEscape escaped with
      | some character => .ok (.integer (Int.ofNat character.toNat))
      | none => .error (.invalidCharacterCode lexeme)
  | '0' :: '\'' :: '\\' :: body =>
      match ReaderEscape.numeric? body with
      | some decoded =>
          if decoded.rest.isEmpty then .ok (.integer (Int.ofNat decoded.value.toNat))
          else .error (.invalidCharacterCode lexeme)
      | none => .error (.invalidCharacterCode lexeme)
  | _ => .error (.invalidCharacterCode lexeme)

private def removeSeparators (characters : List Char) : List Char :=
  characters.filter (fun character => character != '_')

private def splitExponent : List Char -> List Char × Option (List Char)
  | [] => ([], none)
  | character :: rest =>
      if character = 'e' || character = 'E' then
        ([], some rest)
      else
        let (mantissa, exponent) := splitExponent rest
        (character :: mantissa, exponent)

private def splitDecimal : List Char -> List Char × List Char
  | [] => ([], [])
  | '.' :: rest => ([], rest)
  | character :: rest =>
      let (whole, fraction) := splitDecimal rest
      (character :: whole, fraction)

private def parseFloat (lexeme : String) : Except Error Constant := do
  if lexeme = "1.0Inf" then
    pure (.floatBits 0x7ff0000000000000)
  else if lexeme.toList.any (fun character => character = 'r') then
    throw (.unsupportedRational lexeme)
  else if lexeme.toList.any (fun character => character = 'N') then
    throw (.unsupportedNaN lexeme)
  else
    let cleaned := removeSeparators lexeme.toList
    let (mantissaText, exponentText?) := splitExponent cleaned
    let (whole, fraction) := splitDecimal mantissaText
    let digits := whole ++ fraction
    let mantissa <- parseNatBase 10 digits
    let explicitExponent : Int <-
      match exponentText? with
      | none => pure 0
      | some [] => throw (.invalidFloat lexeme)
      | some characters =>
          match String.ofList characters |>.toInt? with
          | some exponent => pure exponent
          | none => throw (.invalidFloat lexeme)
    let decimalPlaces : Int := Int.ofNat fraction.length
    let scale := explicitExponent - decimalPlaces
    let value :=
      if scale < 0 then
        Float.ofScientific mantissa true scale.natAbs
      else
        Float.ofScientific mantissa false scale.natAbs
    pure (.floatBits value.toBits)

/-- Interpret one numeric token. The lexer has already separated a leading
unary sign, so this function accepts only the unsigned numeric payload. -/
def parse (lexeme : String) : Except Error Constant :=
  match lexeme.toList with
  | [] => .error .empty
  | '0' :: '\'' :: _ => parseCharacterCode lexeme
  | '0' :: 'x' :: digits =>
      (.integer ∘ Int.ofNat) <$> parseNatBase 16 digits
  | '0' :: 'X' :: digits =>
      (.integer ∘ Int.ofNat) <$> parseNatBase 16 digits
  | '0' :: 'o' :: digits =>
      (.integer ∘ Int.ofNat) <$> parseNatBase 8 digits
  | '0' :: 'O' :: digits =>
      (.integer ∘ Int.ofNat) <$> parseNatBase 8 digits
  | '0' :: 'b' :: digits =>
      (.integer ∘ Int.ofNat) <$> parseNatBase 2 digits
  | '0' :: 'B' :: digits =>
      (.integer ∘ Int.ofNat) <$> parseNatBase 2 digits
  | characters =>
      if characters.any (fun character =>
          character = '.' || character = 'e' || character = 'E' ||
            character = 'I' || character = 'N' || character = 'r') then
        parseFloat lexeme
      else
        match parseNatBase 10 characters with
        | .ok value => .ok (.integer (Int.ofNat value))
        | .error _ => .error (.invalidInteger lexeme)

end Mettapedia.Logic.Prolog.ReaderNumber
