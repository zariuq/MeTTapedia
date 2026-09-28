import Mettapedia.Data.String.Utf8
import Init.Data.String.Length

/-!
# Byte strings, Unicode scalar views, and admitted name spellings

Arbitrary byte buffers and validated Unicode strings are different domains.
Byte slicing preserves bytes without requiring character boundaries.  The
character view uses Unicode scalar values, not grapheme clusters: combining
marks remain separate elements.  Admitted names below are spellings, not
runtime interned symbols or declarations, and decoding grants no binding or
execution authority.
-/

set_option autoImplicit false

namespace Mettapedia.Data.String.ByteString

/-- Half-open, clamped byte slicing has exactly this length. -/
theorem slice_length (bytes : ByteArray) (start stop : Nat) :
    (bytes.extract start stop).size = min stop bytes.size - start :=
  ByteArray.size_extract

theorem slice_slice (bytes : ByteArray) (start stop left right : Nat) :
    (bytes.extract start stop).extract left right =
      bytes.extract (start + left) (min (start + right) stop) :=
  ByteArray.extract_extract

/-- Splitting anywhere, including through a multibyte scalar, loses no byte. -/
theorem split_reconstruct (bytes : ByteArray) (offset : Nat) (bounded : offset ≤ bytes.size) :
    bytes.extract 0 offset ++ bytes.extract offset bytes.size = bytes := by
  rw [ByteArray.extract_append_extract]
  simp [Nat.max_eq_right bounded]

theorem slice_preserves_byte (bytes : ByteArray) (start stop i : Nat)
    (inside : i < (bytes.extract start stop).size) :
    (bytes.extract start stop)[i] =
      bytes[start + i]'(ByteArray.getElem_extract_aux inside) :=
  ByteArray.getElem_extract inside

/-- UTF-8 string decoding succeeds exactly when the entire byte array is
the encoding of the result, not just a prefix ending at a zero byte. -/
theorem fromUTF8?_eq_some_iff (bytes : ByteArray) (text : String) :
    String.fromUTF8? bytes = some text ↔ text.toByteArray = bytes := by
  unfold String.fromUTF8?
  split
  · rename_i valid
    constructor
    · intro exactResult
      have same := Option.some.inj exactResult
      simpa [String.fromUTF8] using (congrArg String.toByteArray same).symm
    · intro sameBytes
      apply congrArg some
      apply String.toByteArray_inj.1
      exact sameBytes.symm
  · rename_i invalid
    constructor
    · intro impossible
      cases impossible
    · intro sameBytes
      exact (invalid (sameBytes ▸ text.isValidUTF8)).elim

theorem fromUTF8?_encoded (text : String) :
    String.fromUTF8? text.toByteArray = some text :=
  (fromUTF8?_eq_some_iff _ _).2 rfl

/-- Scalar decomposition into singleton strings, suitable for ordinary list
patterns while keeping the string carrier at each element. -/
def characters (text : String) : List String :=
  text.toList.map String.singleton

/-- Reject an element unless it denotes exactly one Unicode scalar value. -/
def singletonChar? (text : String) : Option Char :=
  match text.toList with
  | [c] => some c
  | _ => none

def characterList? : List String → Option (List Char)
  | [] => some []
  | text :: rest => do
      let c ← singletonChar? text
      let cs ← characterList? rest
      some (c :: cs)

def fromCharacters? (texts : List String) : Option String :=
  (characterList? texts).map String.ofList

@[simp] theorem singletonChar?_singleton (c : Char) :
    singletonChar? (String.singleton c) = some c := by
  simp [singletonChar?]

theorem characterList?_singletons (chars : List Char) :
    characterList? (chars.map String.singleton) = some chars := by
  induction chars with
  | nil => rfl
  | cons c cs ih => simp [characterList?, ih]

theorem fromCharacters?_characters (text : String) :
    fromCharacters? (characters text) = some text := by
  simp [fromCharacters?, characters, characterList?_singletons]

theorem singletonChar?_exact {text : String} {c : Char}
    (decoded : singletonChar? text = some c) : text = String.singleton c := by
  unfold singletonChar? at decoded
  split at decoded
  · rename_i d hd
    have same : d = c := Option.some.inj decoded
    subst d
    apply String.toList_inj.1
    simpa using hd
  · cases decoded

theorem characterList?_exact {texts : List String} {chars : List Char}
    (decoded : characterList? texts = some chars) :
    texts = chars.map String.singleton := by
  induction texts generalizing chars with
  | nil => simpa [characterList?] using decoded
  | cons text rest ih =>
    unfold characterList? at decoded
    cases headResult : singletonChar? text with
    | none => simp [headResult] at decoded
    | some c =>
      cases tailResult : characterList? rest with
      | none => simp [headResult, tailResult] at decoded
      | some cs =>
        have same : c :: cs = chars := by
          simpa [headResult, tailResult] using decoded
        subst chars
        rw [singletonChar?_exact headResult, ih tailResult]
        rfl

/-- Both directions hold on the checked list-of-singletons domain. -/
theorem characters_fromCharacters? {texts : List String} {text : String}
    (decoded : fromCharacters? texts = some text) : characters text = texts := by
  obtain ⟨chars, charsExact, rfl⟩ := Option.map_eq_some_iff.1 decoded
  simp [characters, characterList?_exact charsExact]

theorem characters_length (text : String) :
    (characters text).length = text.length := by
  simp [characters, String.length_toList]

/-- The byte-buffer entry point validates before exposing scalar strings and
retains the scanner's first-error offset unchanged. -/
def charactersFromBytes (bytes : ByteArray) : Except Nat (List String) :=
  (Utf8.decode bytes).map (fun chars => chars.toList.map String.singleton)

theorem charactersFromBytes_encoded (text : String) :
    charactersFromBytes text.toByteArray = .ok (characters text) := by
  have decoded := Utf8.decode_encoded text.toList
  simp only [String.utf8Encode_toList] at decoded
  simp [charactersFromBytes, decoded, Except.map, characters]

theorem charactersFromBytes_error_iff {bytes : ByteArray} {offset : Nat} :
    charactersFromBytes bytes = .error offset ↔ Utf8.FirstError bytes offset := by
  rw [← Utf8.decode_error_iff]
  unfold charactersFromBytes
  cases Utf8.decode bytes <;> simp [Except.map]

/-- Reassembling a successful scalar view preserves all original bytes. -/
theorem charactersFromBytes_exact {bytes : ByteArray} {texts : List String}
    (decoded : charactersFromBytes bytes = .ok texts) :
    ∃ text, fromCharacters? texts = some text ∧ text.toByteArray = bytes := by
  unfold charactersFromBytes at decoded
  cases result : Utf8.decode bytes with
  | error offset => simp [result, Except.map] at decoded
  | ok chars =>
    have same : chars.toList.map String.singleton = texts := by
      simpa [result, Except.map] using decoded
    subst texts
    refine ⟨String.ofList chars.toList, ?_, ?_⟩
    · simp [fromCharacters?, characterList?_singletons]
    · simpa using Utf8.encode_decoded result

/-- A profile can impose its own name-spelling domain.  This is independent
of any diagnostic pretty-printer and makes rejection explicit. -/
structure AdmittedName (allowed : String → Bool) where
  text : String
  accepted : allowed text = true

def nameFromBytes? (allowed : String → Bool) (bytes : ByteArray) :
    Option (AdmittedName allowed) := do
  let text ← String.fromUTF8? bytes
  if accepted : allowed text = true then some ⟨text, accepted⟩ else none

def nameBytes {allowed : String → Bool} (name : AdmittedName allowed) : ByteArray :=
  name.text.toByteArray

theorem AdmittedName.ext {allowed : String → Bool} {a b : AdmittedName allowed}
    (sameText : a.text = b.text) : a = b := by
  cases a
  cases b
  cases sameText
  rfl

theorem nameFromBytes?_nameBytes {allowed : String → Bool}
    (name : AdmittedName allowed) : nameFromBytes? allowed (nameBytes name) = some name := by
  cases name with
  | mk text accepted =>
    simp [nameFromBytes?, nameBytes, fromUTF8?_encoded, accepted]

theorem nameFromBytes?_exact {allowed : String → Bool} {bytes : ByteArray}
    {name : AdmittedName allowed} (decoded : nameFromBytes? allowed bytes = some name) :
    nameBytes name = bytes := by
  unfold nameFromBytes? at decoded
  cases textResult : String.fromUTF8? bytes with
  | none => simp [textResult] at decoded
  | some text =>
    simp only [textResult] at decoded
    change (if accepted : allowed text = true then some ⟨text, accepted⟩ else none) =
      some name at decoded
    split at decoded
    · have same := Option.some.inj decoded
      subst name
      exact (fromUTF8?_eq_some_iff _ _).1 textResult
    · cases decoded

theorem nameBytes_injective {allowed : String → Bool}
    {left right : AdmittedName allowed} (same : nameBytes left = nameBytes right) :
    left = right := by
  apply AdmittedName.ext
  exact String.toByteArray_inj.1 same

/-! Controls separate bytes, scalar values, and displayed characters. -/

example : ("a\x00b".toByteArray).size = 3 := by decide +kernel
example : String.fromUTF8? ⟨#[0x61, 0, 0x62]⟩ = some "a\x00b" := by decide +kernel
example : ("é".toByteArray).size = 2 := by decide +kernel
example : (characters "é").length = 1 := by decide +kernel
example : (characters "e\u0301").length = 2 := by decide +kernel
example : characters "héj" = ["h", "é", "j"] := by decide +kernel
example : fromCharacters? ["h", "é", "j"] = some "héj" := by decide +kernel
example : fromCharacters? ["ab"] = none := by decide +kernel
example : fromCharacters? [""] = none := by decide +kernel
example : String.fromUTF8? ("é".toByteArray.extract 0 1) = none := by decide +kernel
example : charactersFromBytes ⟨#[0x68, 0xc3, 0xa9, 0x6a]⟩ =
    .ok ["h", "é", "j"] := by decide +kernel
example : charactersFromBytes ⟨#[0x68, 0xe2, 0x28, 0xa1]⟩ = .error 1 := by
  decide +kernel

#print axioms split_reconstruct
#print axioms fromUTF8?_eq_some_iff
#print axioms fromCharacters?_characters
#print axioms characters_fromCharacters?
#print axioms charactersFromBytes_exact
#print axioms charactersFromBytes_error_iff
#print axioms nameFromBytes?_nameBytes
#print axioms nameFromBytes?_exact
#print axioms nameBytes_injective

end Mettapedia.Data.String.ByteString
