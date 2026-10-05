import Mettapedia.Languages.Chaitin.Syntax
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Data.Num.Lemmas

/-!
# Literal historical Lisp data in the authored evaluator grammar

Words are character lists, numbers are binary, and proper lists preserve
order and multiplicity. Guest names are data, never MeTTaIL metavariables or
de Bruijn indices. The decoder provides an inverse on every encoded value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.OSLF.MeTTaIL.Syntax

def encodePositive : PosNum → Pattern
  | .one => .apply "One" []
  | .bit0 number => .apply "Bit0" [encodePositive number]
  | .bit1 number => .apply "Bit1" [encodePositive number]

def decodePositive : Pattern → Option PosNum
  | .apply "One" [] => some .one
  | .apply "Bit0" [number] => PosNum.bit0 <$> decodePositive number
  | .apply "Bit1" [number] => PosNum.bit1 <$> decodePositive number
  | _ => none

@[simp] theorem decodePositive_encodePositive (number : PosNum) :
    decodePositive (encodePositive number) = some number := by
  induction number <;> simp [encodePositive, decodePositive, *]

def encodeNumber : Num → Pattern
  | .zero => .apply "Zero" []
  | .pos number => .apply "Positive" [encodePositive number]

def decodeNumber : Pattern → Option Num
  | .apply "Zero" [] => some .zero
  | .apply "Positive" [number] => Num.pos <$> decodePositive number
  | _ => none

@[simp] theorem decodeNumber_encodeNumber (number : Num) :
    decodeNumber (encodeNumber number) = some number := by
  cases number <;> simp [encodeNumber, decodeNumber]

def encodeNat (number : Nat) : Pattern := encodeNumber (number : Num)

def decodeNat (pattern : Pattern) : Option Nat :=
  (decodeNumber pattern).map (fun number => (number : Nat))

@[simp] theorem decodeNat_encodeNat (number : Nat) :
    decodeNat (encodeNat number) = some number := by simp [decodeNat, encodeNat]

def encodeCharacters : List Char → Pattern
  | [] => .apply "Nil" []
  | first :: rest => .apply "Cons" [encodeNat first.toNat, encodeCharacters rest]

def decodeCharacters : Pattern → Option (List Char)
  | .apply "Nil" [] => some []
  | .apply "Cons" [first, rest] => do
      let number ← decodeNat first
      let characters ← decodeCharacters rest
      pure (Char.ofNat number :: characters)
  | _ => none

@[simp] theorem decodeCharacters_encodeCharacters (characters : List Char) :
    decodeCharacters (encodeCharacters characters) = some characters := by
  induction characters <;> simp [encodeCharacters, decodeCharacters, *]

def encodeWord (word : String) : Pattern := encodeCharacters word.toList

def decodeWord (pattern : Pattern) : Option String :=
  String.ofList <$> decodeCharacters pattern

@[simp] theorem decodeWord_encodeWord (word : String) :
    decodeWord (encodeWord word) = some word := by simp [encodeWord, decodeWord]

mutual

def encode : SExpr → Pattern
  | .symbol word => .apply "Word" [encodeWord word]
  | .number number => .apply "Number" [encodeNat number]
  | .list expressions => .apply "List" [encodeValues expressions]
termination_by expression => sizeOf expression

def encodeValues : List SExpr → Pattern
  | [] => .apply "Nil" []
  | first :: rest => .apply "Cons" [encode first, encodeValues rest]
termination_by expressions => sizeOf expressions

end

mutual

def decode : Pattern → Option SExpr
  | .apply "Word" [word] => SExpr.symbol <$> decodeWord word
  | .apply "Number" [number] => SExpr.number <$> decodeNat number
  | .apply "List" [expressions] => SExpr.list <$> decodeValues expressions
  | _ => none
termination_by pattern => sizeOf pattern

def decodeValues : Pattern → Option (List SExpr)
  | .apply "Nil" [] => some []
  | .apply "Cons" [first, rest] => do
      let value ← decode first
      let values ← decodeValues rest
      pure (value :: values)
  | _ => none
termination_by pattern => sizeOf pattern

end

mutual

@[simp] theorem decode_encode (expression : SExpr) :
    decode (encode expression) = some expression := by
  cases expression with
  | symbol word => simp [encode, decode]
  | number number => simp [encode, decode]
  | list expressions => simp [encode, decode, decodeValues_encodeValues expressions]
termination_by sizeOf expression

@[simp] theorem decodeValues_encodeValues (expressions : List SExpr) :
    decodeValues (encodeValues expressions) = some expressions := by
  cases expressions with
  | nil => simp [encodeValues, decodeValues]
  | cons first rest =>
      simp [encodeValues, decodeValues, decode_encode first, decodeValues_encodeValues rest]
termination_by sizeOf expressions

end

def encodeEnvironment : Environment → Pattern
  | [] => .apply "Nil" []
  | (name, value) :: rest =>
      .apply "Cons" [.apply "Binding" [encode name, encode value], encodeEnvironment rest]

def decodeEnvironment : Pattern → Option Environment
  | .apply "Nil" [] => some []
  | .apply "Cons" [.apply "Binding" [name, value], rest] => do
      let key ← decode name
      let expression ← decode value
      let environment ← decodeEnvironment rest
      pure ((key, expression) :: environment)
  | _ => none

@[simp] theorem decodeEnvironment_encodeEnvironment (environment : Environment) :
    decodeEnvironment (encodeEnvironment environment) = some environment := by
  induction environment with
  | nil => rfl
  | cons binding rest ih => cases binding; simp [encodeEnvironment, decodeEnvironment, ih]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  simpa only [decode_encode, Option.some.injEq] using congrArg decode same

theorem encodeValues_injective : Function.Injective encodeValues := by
  intro first second same
  simpa only [decodeValues_encodeValues, Option.some.injEq] using congrArg decodeValues same

theorem encodeEnvironment_injective : Function.Injective encodeEnvironment := by
  intro first second same
  simpa only [decodeEnvironment_encodeEnvironment, Option.some.injEq] using
    congrArg decodeEnvironment same

theorem word_number_distinct (word : String) (number : Nat) :
    encode (.symbol word) ≠ encode (.number number) := by
  intro same
  cases encode_injective same

theorem guest_variable_is_literal (name : String) :
    decode (encode (.symbol ("$" ++ name))) = some (.symbol ("$" ++ name)) := decode_encode _

end Mettapedia.Languages.Chaitin.GSLT
