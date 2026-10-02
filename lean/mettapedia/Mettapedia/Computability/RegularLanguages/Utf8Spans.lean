import Mettapedia.Computability.RegularLanguages.Search

/-!
# Byte spans of scalar spans

Search positions count Unicode scalars. A span of scalars determines a span
of bytes in the UTF-8 encoding of the input: its start is the encoded length
of the scalars before it, and its end adds the encoded length of the matched
text. The byte span selects exactly the encoding of the matched text, so it
never splits a scalar, and distinct scalar positions have distinct byte
positions.

Byte offsets agree with scalar offsets on ASCII text only.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

/-- The UTF-8 encoding of a word, as a list of bytes. -/
def utf8Bytes (word : List Char) : List UInt8 := word.flatMap String.utf8EncodeChar

/-- The number of bytes in the UTF-8 encoding of a word. -/
def utf8Length (word : List Char) : Nat := (word.map Char.utf8Size).sum

@[simp] theorem utf8Bytes_nil : utf8Bytes [] = [] := rfl

@[simp] theorem utf8Bytes_append (first second : List Char) :
    utf8Bytes (first ++ second) = utf8Bytes first ++ utf8Bytes second := by
  simp [utf8Bytes]

@[simp] theorem utf8Length_nil : utf8Length [] = 0 := rfl

@[simp] theorem utf8Length_cons (c : Char) (word : List Char) :
    utf8Length (c :: word) = c.utf8Size + utf8Length word := by
  simp [utf8Length]

@[simp] theorem utf8Length_append (first second : List Char) :
    utf8Length (first ++ second) = utf8Length first + utf8Length second := by
  simp [utf8Length]

theorem length_utf8Bytes (word : List Char) : (utf8Bytes word).length = utf8Length word := by
  induction word with
  | nil => rfl
  | cons c word ih =>
      change (String.utf8EncodeChar c ++ utf8Bytes word).length = _
      rw [List.length_append, String.length_utf8EncodeChar, ih, utf8Length_cons]

/-- The bytes are those of the encoding function of the core library. -/
theorem utf8Encode_eq_utf8Bytes (word : List Char) :
    word.utf8Encode = (utf8Bytes word).toByteArray := rfl

/-- The bytes of a string are the encoding of its scalars. -/
theorem toByteArray_eq_utf8Bytes (text : String) :
    text.toByteArray = (utf8Bytes text.toList).toByteArray :=
  String.utf8Encode_toList.symm

/-- Every scalar takes at least one byte. -/
theorem length_le_utf8Length (word : List Char) : word.length ≤ utf8Length word := by
  induction word with
  | nil => exact le_rfl
  | cons c word ih =>
      have positive := c.utf8Size_pos
      rw [utf8Length_cons, List.length_cons]
      omega

/-- On ASCII text bytes and scalars are counted alike. -/
theorem utf8Length_eq_length_of_ascii {word : List Char}
    (ascii : ∀ c ∈ word, c.val ≤ 127) : utf8Length word = word.length := by
  induction word with
  | nil => rfl
  | cons c word ih =>
      have one : c.utf8Size = 1 := Char.utf8Size_eq_one_iff.mpr (ascii c List.mem_cons_self)
      rw [utf8Length_cons, List.length_cons, one,
        ih fun other member => ascii other (List.mem_cons_of_mem _ member)]
      omega

/-- The byte offset of a scalar position. -/
def byteOffset (input : List Char) (position : Nat) : Nat := utf8Length (input.take position)

theorem byteOffset_add (input : List Char) (position count : Nat) :
    byteOffset input (position + count) =
      byteOffset input position + utf8Length ((input.drop position).take count) := by
  rw [byteOffset, List.take_add, utf8Length_append]
  rfl

theorem byteOffset_mono (input : List Char) {earlier later : Nat} (ordered : earlier ≤ later) :
    byteOffset input earlier ≤ byteOffset input later := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [byteOffset_add]
  exact Nat.le_add_right _ _

/-- **Distinct scalar positions have distinct byte offsets.** -/
theorem byteOffset_strictMono (input : List Char) {earlier later : Nat}
    (ordered : earlier < later) (bounded : later ≤ input.length) :
    byteOffset input earlier < byteOffset input later := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_add_of_le ordered.le
  rw [byteOffset_add]
  have scalars : ((input.drop earlier).take count).length = count := by
    rw [List.length_take, List.length_drop]
    omega
  have bytes := length_le_utf8Length ((input.drop earlier).take count)
  omega

theorem byteOffset_injective (input : List Char) {first second : Nat}
    (firstBound : first ≤ input.length) (secondBound : second ≤ input.length)
    (same : byteOffset input first = byteOffset input second) : first = second := by
  rcases Nat.lt_trichotomy first second with less | equal | greater
  · exact absurd same (Nat.ne_of_lt (byteOffset_strictMono input less secondBound))
  · exact equal
  · exact absurd same.symm (Nat.ne_of_lt (byteOffset_strictMono input greater firstBound))

namespace MatchSpan

/-- The byte offset of the first scalar of the span. -/
def byteStart (span : MatchSpan) (input : List Char) : Nat := byteOffset input span.start

/-- The byte offset just past the last scalar of the span. -/
def byteEnd (span : MatchSpan) (input : List Char) : Nat :=
  byteOffset input (span.start + span.length)

theorem byteEnd_eq (span : MatchSpan) (input : List Char) :
    span.byteEnd input = span.byteStart input + utf8Length (span.text input) :=
  byteOffset_add input span.start span.length

theorem byteStart_le_byteEnd (span : MatchSpan) (input : List Char) :
    span.byteStart input ≤ span.byteEnd input :=
  byteOffset_mono input (Nat.le_add_right _ _)

/-- **The byte span selects exactly the encoding of the matched text.** -/
theorem utf8Bytes_text (span : MatchSpan) (input : List Char) :
    ((utf8Bytes input).drop (span.byteStart input)).take
        (span.byteEnd input - span.byteStart input) = utf8Bytes (span.text input) := by
  have split : input =
      input.take span.start ++ (span.text input ++ (input.drop span.start).drop span.length) := by
    rw [MatchSpan.text, List.take_append_drop, List.take_append_drop]
  have bytes := congrArg utf8Bytes split
  rw [utf8Bytes_append, utf8Bytes_append] at bytes
  have width : span.byteEnd input - span.byteStart input =
      (utf8Bytes (span.text input)).length := by
    rw [byteEnd_eq, length_utf8Bytes]
    omega
  have before : (utf8Bytes (input.take span.start)).length = span.byteStart input :=
    length_utf8Bytes _
  rw [width, bytes, List.drop_left' before, List.take_left]

/-- The bytes between the two offsets are those of the matched text. -/
theorem byteEnd_sub_byteStart (span : MatchSpan) (input : List Char) :
    span.byteEnd input - span.byteStart input = utf8Length (span.text input) := by
  rw [byteEnd_eq]
  omega

/-- The matched text of a span within the input has the span's length. -/
theorem length_text (span : MatchSpan) (input : List Char)
    (bounded : span.start + span.length ≤ input.length) :
    (span.text input).length = span.length := by
  rw [MatchSpan.text, List.length_take, List.length_drop]
  omega

end MatchSpan

/-- A match as reported in bytes: the offset of its first byte, the offset
just past its last byte, and the matched text. -/
structure ByteMatch where
  start : Nat
  stop : Nat
  text : List Char
  deriving DecidableEq, Repr

/-- The byte report of a scalar span. -/
def MatchSpan.byteMatch (span : MatchSpan) (input : List Char) : ByteMatch :=
  ⟨span.byteStart input, span.byteEnd input, span.text input⟩

/-- The reported offsets delimit the encoding of the reported text. -/
theorem MatchSpan.byteMatch_bytes (span : MatchSpan) (input : List Char) :
    ((utf8Bytes input).drop (span.byteMatch input).start).take
        ((span.byteMatch input).stop - (span.byteMatch input).start) =
      utf8Bytes (span.byteMatch input).text :=
  span.utf8Bytes_text input

namespace Utf8SpanControls

/-- Scalars one to three of `éλλx` are bytes two to six. -/
theorem nonAscii_span :
    (⟨1, 2⟩ : MatchSpan).byteStart "éλλx".toList = 2 ∧
      (⟨1, 2⟩ : MatchSpan).byteEnd "éλλx".toList = 6 := by decide

/-- On ASCII text the two spans coincide. -/
theorem ascii_span :
    (⟨1, 3⟩ : MatchSpan).byteStart "xaaab".toList = 1 ∧
      (⟨1, 3⟩ : MatchSpan).byteEnd "xaaab".toList = 4 := by decide

/-- A scalar of four bytes. -/
theorem four_byte_scalar : utf8Length "🦀".toList = 4 ∧ "🦀".toList.length = 1 := by decide

/-- A scalar offset read as a byte offset would land inside `é`. -/
theorem scalar_offset_is_not_byte_offset :
    (⟨1, 2⟩ : MatchSpan).byteStart "éλλx".toList ≠ (⟨1, 2⟩ : MatchSpan).start := by decide

end Utf8SpanControls

end Mettapedia.Computability.RegularLanguages
