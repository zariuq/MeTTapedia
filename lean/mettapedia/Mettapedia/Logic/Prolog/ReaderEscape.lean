import Mathlib.Data.List.Basic

/-! Numeric quoted-character escapes. These are Prolog character codes,
not MeTTa byte escapes: `\x3bb\` denotes one lambda scalar. Keeping the
consumed spelling beside the suffix preserves source positions. -/

namespace Mettapedia.Logic.Prolog.ReaderEscape

def digit? (base : Nat) (c : Char) : Option Nat := do
  let n ← if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
    else none
  if n < base then some n else none

def value? (base : Nat) (digits : List Char) : Option Char := do
  if digits.isEmpty then none else do
    let value ← digits.foldlM (fun n c => do
      let digit ← digit? base c
      let next := base * n + digit
      -- A character code cannot return below the Unicode maximum after
      -- exceeding it. Avoid constructing an enormous intermediate Nat.
      if next ≤ 0x10ffff then some next else none) 0
    if value.isValidChar then some (Char.ofNat value) else none

structure Decoded where
  value : Char
  consumed : List Char
  rest : List Char
  deriving Repr, DecidableEq

def terminated (base : Nat) (marker input : List Char) (optionalTerminator : Bool := false) : Option Decoded := do
  let (digits, suffix) := input.span (fun c => (digit? base c).isSome)
  let value ← value? base digits
  match suffix with
  | '\\' :: rest => some ⟨value, marker ++ digits ++ ['\\'], rest⟩
  | rest => if optionalTerminator then some ⟨value, marker ++ digits, rest⟩ else none

def fixed (count : Nat) (marker input : List Char) : Option Decoded := do
  let digits := input.take count
  if digits.length != count then none else do
    let value ← value? 16 digits
    some ⟨value, marker ++ digits, input.drop count⟩

/-- The input starts immediately after the introducing backslash. Closed
hexadecimal/octal forms are shared by ISO and SWI. Fixed Unicode and omitted
terminators are SWI extensions; ISO source admission uses the narrower grammar. -/
def numeric? : List Char → Option Decoded
  | 'x' :: rest => terminated 16 ['x'] rest true
  | 'u' :: rest => fixed 4 ['u'] rest
  | 'U' :: rest => fixed 8 ['U'] rest
  | first :: rest => if (digit? 8 first).isSome then terminated 8 [] (first :: rest) true else none
  | [] => none

example : (numeric? "x3bb\\rest".toList).map (·.value) = some 'λ' := by decide
example : (numeric? "141\\rest".toList).map (·.value) = some 'a' := by decide
example : (numeric? "U0001f600rest".toList).map (·.value) = some '😀' := by decide
example : numeric? "uD800".toList = none := by decide
example : numeric? "x110000\\".toList = none := by decide
example : (numeric? "xD8000\\".toList).map (·.value.toNat) = some 0xD8000 := by decide
example : (numeric? "x41".toList).map (·.value) = some 'A' := by decide
example : numeric? "x".toList = none := by decide

end Mettapedia.Logic.Prolog.ReaderEscape
