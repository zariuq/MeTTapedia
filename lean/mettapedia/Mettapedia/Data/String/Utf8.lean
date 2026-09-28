import Mathlib.Data.List.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Basic

/-!
# Explicit-length UTF-8 decoding with error offsets

The scanner below uses Lean's verified scalar decoder.  Its error offset is the
start of the first undecodable scalar, not the position of a bad continuation
byte inside that scalar.  `DecodePrefix` independently describes the successful
steps before that offset.  This is a byte-buffer specification and executable
reference; it does not assert correspondence with a native C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.Utf8

/-- Decode from a byte boundary, retaining the first error offset. -/
def scan (bytes : ByteArray) (offset : Nat) (acc : Array Char)
    (_bounded : offset ≤ bytes.size) : Except Nat (Array Char) :=
  if offset < bytes.size then
    match decoded : bytes.utf8DecodeChar? offset with
    | none => .error offset
    | some c => scan bytes (offset + c.utf8Size) (acc.push c)
        (ByteArray.le_size_of_utf8DecodeChar?_eq_some decoded)
  else .ok acc
termination_by bytes.size - offset
decreasing_by have := c.utf8Size_pos; omega

/-- Full-buffer scalar decoding; no NUL-terminated-string convention is used. -/
def decode (bytes : ByteArray) : Except Nat (Array Char) :=
  scan bytes 0 #[] (Nat.zero_le _)

/-- Erasing diagnostics gives the existing verified UTF-8 decoder exactly. -/
theorem scan_toOption (bytes : ByteArray) (offset : Nat) (acc : Array Char)
    (bounded : offset ≤ bytes.size) :
    (scan bytes offset acc bounded).toOption =
      ByteArray.utf8Decode?.go bytes offset acc bounded := by
  fun_induction scan with
  | case1 offset acc bounded inside invalid =>
    unfold ByteArray.utf8Decode?.go
    simp only [inside, ↓reduceIte, Except.toOption]
    split
    · rfl
    · rename_i c decoded
      simp [invalid] at decoded
  | case2 offset acc bounded inside c decoded ih =>
    unfold ByteArray.utf8Decode?.go
    simp only [inside, ↓reduceIte]
    split
    · rename_i invalid
      simp [decoded] at invalid
    · rename_i d decoded'
      have same : c = d := Option.some.inj (decoded.symm.trans decoded')
      subst d
      exact ih
  | case3 offset acc bounded outside =>
    unfold ByteArray.utf8Decode?.go
    simp only [outside, ↓reduceIte, Except.toOption]

theorem decode_toOption (bytes : ByteArray) :
    (decode bytes).toOption = bytes.utf8Decode? :=
  scan_toOption bytes 0 #[] (Nat.zero_le _)

/-- Success occurs exactly on the UTF-8 encoding of a list of Unicode scalars. -/
theorem decode_success_iff (bytes : ByteArray) :
    (∃ chars, decode bytes = .ok chars) ↔ bytes.IsValidUTF8 := by
  rw [← ByteArray.isSome_utf8Decode?_iff, ← decode_toOption]
  cases decode bytes <;> simp [Except.toOption]

theorem decode_encoded (chars : List Char) :
    decode chars.utf8Encode = .ok chars.toArray := by
  have h := decode_toOption chars.utf8Encode
  simp only [List.utf8Decode?_utf8Encode] at h
  cases result : decode chars.utf8Encode <;> simp_all [Except.toOption]

/-- A successful decoder preserves every source byte, including embedded NUL. -/
theorem encode_decoded {bytes : ByteArray} {chars : Array Char}
    (decoded : decode bytes = .ok chars) : chars.toList.utf8Encode = bytes := by
  have h : bytes.utf8Decode? = some chars := by
    rw [← decode_toOption, decoded]
    rfl
  have valid : bytes.utf8Decode?.isSome := by simp [h]
  have back := ByteArray.utf8Encode_get_utf8Decode? (b := bytes) (h := valid)
  simpa [h] using back

/-- A prefix of whole, successfully decoded scalar values. -/
inductive DecodePrefix (bytes : ByteArray) : Nat → Nat → List Char → Prop
  | nil (start : Nat) : DecodePrefix bytes start start []
  | cons {start finish : Nat} {c : Char} {rest : List Char}
      (decoded : bytes.utf8DecodeChar? start = some c)
      (tail : DecodePrefix bytes (start + c.utf8Size) finish rest) :
      DecodePrefix bytes start finish (c :: rest)

theorem DecodePrefix.ordered {bytes : ByteArray} {start finish : Nat}
    {chars : List Char} (trace : DecodePrefix bytes start finish chars) :
    start ≤ finish := by
  induction trace with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => omega

/-- Two traversals from the same boundary agree until one stops.  An error
boundary cannot occur strictly before the end of a successful prefix. -/
theorem DecodePrefix.no_earlier_error {bytes : ByteArray} {start finish : Nat}
    {chars : List Char} (trace : DecodePrefix bytes start finish chars)
    {error : Nat} {prefixChars : List Char}
    (before : DecodePrefix bytes start error prefixChars)
    (invalid : bytes.utf8DecodeChar? error = none) : finish ≤ error := by
  induction trace generalizing error prefixChars with
  | nil => exact before.ordered
  | @cons start finish c rest decoded tail ih =>
    cases before with
    | nil => simp [decoded] at invalid
    | @cons _ _ d ds decoded' tail' =>
      have same : c = d := Option.some.inj (decoded.symm.trans decoded')
      subst d
      exact ih tail' invalid

/-- An error certificate is a complete valid prefix followed immediately by
an undecodable scalar start inside the buffer. -/
def FirstError (bytes : ByteArray) (offset : Nat) : Prop :=
  offset < bytes.size ∧ bytes.utf8DecodeChar? offset = none ∧
    ∃ prefixChars, DecodePrefix bytes 0 offset prefixChars

theorem scan_error_prefix {bytes : ByteArray} {offset : Nat} {acc : Array Char}
    {bounded : offset ≤ bytes.size} {error : Nat}
    (failed : scan bytes offset acc bounded = .error error) :
    error < bytes.size ∧ bytes.utf8DecodeChar? error = none ∧
      ∃ prefixChars, DecodePrefix bytes offset error prefixChars := by
  fun_induction scan generalizing error with
  | case1 offset acc bounded inside invalid =>
    cases failed
    exact ⟨inside, invalid, [], .nil offset⟩
  | case2 offset acc bounded inside c decoded ih =>
    obtain ⟨inBounds, invalid, prefixChars, trace⟩ := ih failed
    exact ⟨inBounds, invalid, c :: prefixChars, .cons decoded trace⟩
  | case3 => cases failed

theorem decode_error_first {bytes : ByteArray} {offset : Nat}
    (failed : decode bytes = .error offset) : FirstError bytes offset :=
  scan_error_prefix failed

theorem firstError_unique {bytes : ByteArray} {left right : Nat}
    (hl : FirstError bytes left) (hr : FirstError bytes right) : left = right := by
  obtain ⟨_, invalidLeft, lp, lt⟩ := hl
  obtain ⟨_, invalidRight, rp, rt⟩ := hr
  exact Nat.le_antisymm (lt.no_earlier_error rt invalidRight)
    (rt.no_earlier_error lt invalidLeft)

theorem scan_after_prefix {bytes : ByteArray} {start finish : Nat}
    {chars : List Char} (trace : DecodePrefix bytes start finish chars)
    (bounded : finish ≤ bytes.size) (acc : Array Char) :
    scan bytes start acc (Nat.le_trans trace.ordered bounded) =
      scan bytes finish (acc ++ chars.toArray) bounded := by
  induction trace generalizing acc with
  | nil => simp
  | @cons start finish c rest decoded tail ih =>
    have inside : start < bytes.size := by
      have := ByteArray.le_size_of_utf8DecodeChar?_eq_some decoded
      have := c.utf8Size_pos
      omega
    rw [scan]
    simp only [inside, ↓reduceIte]
    split
    · rename_i invalid
      simp [decoded] at invalid
    · rename_i d decoded'
      have same : c = d := Option.some.inj (decoded.symm.trans decoded')
      subst d
      simpa using ih bounded (acc.push c)

theorem decode_error_iff {bytes : ByteArray} {offset : Nat} :
    decode bytes = .error offset ↔ FirstError bytes offset := by
  refine ⟨decode_error_first, fun first => ?_⟩
  obtain ⟨inside, invalid, prefixChars, trace⟩ := first
  unfold decode
  rw [scan_after_prefix trace (Nat.le_of_lt inside) #[]]
  rw [scan]
  simp only [inside, ↓reduceIte]
  split
  · rfl
  · rename_i c decoded
    simp [invalid] at decoded

/-! Positive and negative controls: ASCII, NUL, multibyte scalars, overlong
encodings, surrogates, truncation, and the exact first-error convention. -/

example : decode ⟨#[0x68, 0xc3, 0xa9, 0x6a]⟩ = .ok #['h', 'é', 'j'] := by
  decide +kernel

example : decode ⟨#[0x61, 0x00, 0x62]⟩ = .ok #['a', '\x00', 'b'] := by
  decide +kernel

example : decode ⟨#[0x61, 0xff, 0x62]⟩ = .error 1 := by decide +kernel
example : decode ⟨#[0x61, 0xe2, 0x28, 0xa1]⟩ = .error 1 := by decide +kernel
example : decode ⟨#[0xc0, 0x80]⟩ = .error 0 := by decide +kernel
example : decode ⟨#[0xed, 0xa0, 0x80]⟩ = .error 0 := by decide +kernel
example : decode ⟨#[0xf4, 0x90, 0x80, 0x80]⟩ = .error 0 := by decide +kernel
example : decode ⟨#[0xf0, 0x9f]⟩ = .error 0 := by decide +kernel

#print axioms decode_toOption
#print axioms decode_success_iff
#print axioms decode_encoded
#print axioms encode_decoded
#print axioms decode_error_iff
#print axioms firstError_unique

end Mettapedia.Data.String.Utf8
