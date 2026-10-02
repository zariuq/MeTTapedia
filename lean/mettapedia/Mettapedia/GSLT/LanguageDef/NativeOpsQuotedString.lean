import Mathlib.Data.List.Basic

/-!
# Quoted catalogue tokens

The source carrier retains quote and escape spelling.  This total decoder
recognizes JSON string escapes, combines UTF-16 surrogate pairs and refuses
isolated surrogate code points.  It supplies the decoded catalogue spelling;
source lexing and exact catalogue authorization are separate checks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOpsQuotedString

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexFour (a b c d : Char) : Option Nat := do
  some ((← hexDigit a) * 4096 + (← hexDigit b) * 256 + (← hexDigit c) * 16 + (← hexDigit d))

def scalar (codepoint : Nat) : Bool :=
  codepoint < 0x110000 && !(0xD800 ≤ codepoint && codepoint < 0xE000)

def body? : List Char → Option (List Char)
  | ['"'] => some []
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
      let high ← hexFour a b c d
      if 0xD800 ≤ high ∧ high < 0xDC00 then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: tail => do
            let low ← hexFour e f g h
            if 0xDC00 ≤ low ∧ low < 0xE000 then
              let codepoint := 0x10000 + (high - 0xD800) * 1024 + (low - 0xDC00)
              if scalar codepoint then (body? tail).map (Char.ofNat codepoint :: ·) else none
            else none
        | _ => none
      else if scalar high then (body? rest).map (Char.ofNat high :: ·) else none
  | '\\' :: escaped :: rest => do
      let decoded ← match escaped with
        | '"' => some '"'
        | '\\' => some '\\'
        | '/' => some '/'
        | 'b' => some (Char.ofNat 8)
        | 'f' => some (Char.ofNat 12)
        | 'n' => some '\n'
        | 'r' => some '\r'
        | 't' => some '\t'
        | _ => none
      (body? rest).map (decoded :: ·)
  | '"' :: _ => none
  | c :: rest => if c.toNat < 32 then none else (body? rest).map (c :: ·)
  | [] => none
termination_by input => input.length
decreasing_by
  all_goals simp_wf
  all_goals omega

def decode (token : String) : Option String :=
  match token.toList with
  | '"' :: rest => (body? rest).map String.ofList
  | _ => none

def PlainCharacter (c : Char) : Prop :=
  c ≠ '"' ∧ c ≠ '\\' ∧ 32 ≤ c.toNat

theorem body_plain (characters : List Char)
    (plain : ∀ c ∈ characters, PlainCharacter c) :
    body? (characters ++ ['"']) = some characters := by
  induction characters with
  | nil => decide +kernel
  | cons c rest ih =>
      have first := plain c (by simp)
      have tail : ∀ character ∈ rest, PlainCharacter character :=
        fun character member => plain character (by simp [member])
      simp only [List.cons_append]
      rw [body?]
      simp only [Nat.not_lt_of_ge first.2.2, if_false, ih tail, Option.map_some]
      all_goals simp_all [PlainCharacter]

theorem decode_plain (characters : List Char)
    (plain : ∀ c ∈ characters, PlainCharacter c) :
    decode (String.ofList ('"' :: characters ++ ['"'])) = some (String.ofList characters) := by
  unfold decode
  rw [String.toList_ofList, List.cons_append]
  split
  · rename_i rest equal
    have same : characters ++ ['"'] = rest := (List.cons.inj equal).2
    rw [← same, body_plain characters plain]
    rfl
  · rename_i impossible
    exact False.elim (impossible (characters ++ ['"']) rfl)

theorem catalogue_identifier_decodes :
    decode "\"cetta_gslt_native_record_word_v1\"" =
      some "cetta_gslt_native_record_word_v1" := by decide +kernel

theorem escaped_identifier_decodes : decode "\"\\u0077ord\"" = some "word" := by decide +kernel

theorem surrogate_pair_decodes : decode "\"\\uD83D\\uDE00\"" = some "😀" := by decide +kernel

theorem isolated_high_surrogate_refuses : decode "\"\\uD83D\"" = none := by decide +kernel

theorem isolated_low_surrogate_refuses : decode "\"\\uDE00\"" = none := by decide +kernel

theorem unknown_escape_refuses : decode "\"\\q\"" = none := by decide +kernel

theorem trailing_string_material_refuses : decode "\"word\"tail" = none := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOpsQuotedString
