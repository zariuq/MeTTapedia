import Mettapedia.Data.String.Utf8

/-! Lossless MeTTa string-literal decoding. Recognized byte, scalar and
UTF-16 spellings decode; unknown, incomplete and non-scalar escapes retain
 their original spelling. JSON is a separate format: accepting its scalar
spellings here does not make this reader a JSON validator.
The specification is structural; its proved-equal tail-recursive implementation
keeps stack use bounded. Rendering and source-profile selection are separate. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StringLiteral

/-- The value of a hexadecimal digit. -/
def hexValue? (character : Char) : Option Nat :=
  if '0' ≤ character ∧ character ≤ '9' then some (character.toNat - '0'.toNat)
  else if 'a' ≤ character ∧ character ≤ 'f' then some (character.toNat - 'a'.toNat + 10)
  else if 'A' ≤ character ∧ character ≤ 'F' then some (character.toNat - 'A'.toNat + 10)
  else none

/-- The digits of `\u{h…}`: one or more hexadecimal digits, then `}`. Leading
zeros are unlimited; a value beyond the Unicode range is no scalar escape. -/
def scalarDigits : Nat → Nat → List Char → Option (Nat × List Char)
  | count, value, '}' :: rest => if 0 < count then some (value, rest) else none
  | count, value, character :: rest =>
    match hexValue? character with
    | some digit =>
      if value * 16 + digit ≤ 0x10ffff then scalarDigits (count + 1) (value * 16 + digit) rest
      else none
    | none => none
  | _, _, [] => none

theorem scalarDigits_shorter : ∀ (count value : Nat) (characters after : List Char) (scalar : Nat),
    scalarDigits count value characters = some (scalar, after) → after.length < characters.length
  | _, _, [], _, _, found => by simp [scalarDigits] at found
  | count, value, character :: rest, after, scalar, found => by
    by_cases close : character = '}'
    · subst close
      simp only [scalarDigits] at found
      split at found
      · simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨_, rfl⟩ := found
        simp
      · cases found
    · rw [scalarDigits.eq_2 count value character rest close] at found
      split at found
      · split at found
        · have := scalarDigits_shorter _ _ rest after scalar found
          simp only [List.length_cons]
          omega
        · cases found
      · cases found

/-- An escaped character that stands for one character. -/
def simpleEscape : Char → Char
  | 'n' => '\n'
  | 'r' => '\r'
  | 't' => '\t'
  | 'b' => '\u0008'
  | 'f' => '\u000c'
  | other => other

/-- The code unit of a JSON `\uXXXX` escape: four hexadecimal digits. -/
def unitValue? (first second third fourth : Char) : Option Nat := do
  let first ← hexValue? first
  let second ← hexValue? second
  let third ← hexValue? third
  let fourth ← hexValue? fourth
  pure (((first * 16 + second) * 16 + third) * 16 + fourth)

/-- A scalar code unit decodes; an isolated surrogate retains its spelling. -/
def unitBytes (unit : Nat) (spelling : List Char) : List UInt8 :=
  if unit.isValidChar then String.utf8EncodeChar (Char.ofNat unit)
  else spelling.flatMap String.utf8EncodeChar

/-- Unknown escapes remain available to a later consumer, including the slash. -/
def escapeBytes (kind : Char) : List UInt8 :=
  if kind = 'n' ∨ kind = 'r' ∨ kind = 't' ∨ kind = 'b' ∨ kind = 'f' ∨
      kind = '"' ∨ kind = '\\' ∨ kind = '/' ∨ kind = '\'' then
    String.utf8EncodeChar (simpleEscape kind)
  else String.utf8EncodeChar '\\' ++ String.utf8EncodeChar kind

/-- The scalar of a UTF-16 surrogate pair. -/
def pairScalar? (high low : Nat) : Option Nat :=
  if 0xD800 ≤ high ∧ high < 0xDC00 ∧ 0xDC00 ≤ low ∧ low < 0xE000 then
    some (0x10000 + (high - 0xD800) * 1024 + (low - 0xDC00))
  else none

/-- The bytes a string literal's body denotes. -/
def bodyBytes : List Char → List UInt8
  | [] => []
  | ['\\'] => String.utf8EncodeChar '\\'
  | '\\' :: 'x' :: high :: low :: tail =>
    match hexValue? high, hexValue? low with
    | some first, some second => UInt8.ofNat (16 * first + second) :: bodyBytes tail
    | _, _ => (String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'x') ++ bodyBytes (high :: low :: tail)
  | '\\' :: 'u' :: '{' :: tail =>
    match _found : scalarDigits 0 0 tail with
    | some (scalar, after) =>
      if scalar.isValidChar then String.utf8EncodeChar (Char.ofNat scalar) ++ bodyBytes after
      else (String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u') ++ bodyBytes ('{' :: tail)
    | none => (String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u') ++ bodyBytes ('{' :: tail)
  | '\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: tail =>
    match unitValue? a b c d, unitValue? e f g h with
    | some high, some low =>
      match pairScalar? high low with
      | some scalar => String.utf8EncodeChar (Char.ofNat scalar) ++ bodyBytes tail
      | none => unitBytes high ['\\', 'u', a, b, c, d] ++ bodyBytes ('\\' :: 'u' :: e :: f :: g :: h :: tail)
    | some high, none => unitBytes high ['\\', 'u', a, b, c, d] ++ bodyBytes ('\\' :: 'u' :: e :: f :: g :: h :: tail)
    | none, _ => (String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u') ++ bodyBytes (a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: tail)
  | '\\' :: 'u' :: a :: b :: c :: d :: tail =>
    match unitValue? a b c d with
    | some unit => unitBytes unit ['\\', 'u', a, b, c, d] ++ bodyBytes tail
    | none => (String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u') ++ bodyBytes (a :: b :: c :: d :: tail)
  | '\\' :: kind :: rest => escapeBytes kind ++ bodyBytes rest
  | character :: rest => String.utf8EncodeChar character ++ bodyBytes rest
termination_by characters => characters.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first
    | omega
    | (have := scalarDigits_shorter 0 0 tail after scalar _found; omega)

/-- `bodyBytes` with an accumulator. Every call is in tail position, so the
compiled decoder runs in constant stack on long bodies; `bodyBytes_eq_tr`
makes the compiler use it in place of `bodyBytes`. -/
def bodyBytesInto : List Char → Array UInt8 → Array UInt8
  | [], acc => acc
  | ['\\'], acc => acc ++ (String.utf8EncodeChar '\\').toArray
  | '\\' :: 'x' :: high :: low :: tail, acc =>
    match hexValue? high, hexValue? low with
    | some first, some second => bodyBytesInto tail (acc ++ [UInt8.ofNat (16 * first + second)].toArray)
    | _, _ => bodyBytesInto (high :: low :: tail) (acc ++ ((String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'x')).toArray)
  | '\\' :: 'u' :: '{' :: tail, acc =>
    match _found : scalarDigits 0 0 tail with
    | some (scalar, after) =>
      if scalar.isValidChar then bodyBytesInto after (acc ++ (String.utf8EncodeChar (Char.ofNat scalar)).toArray)
      else bodyBytesInto ('{' :: tail) (acc ++ ((String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u')).toArray)
    | none => bodyBytesInto ('{' :: tail) (acc ++ ((String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u')).toArray)
  | '\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: tail, acc =>
    match unitValue? a b c d, unitValue? e f g h with
    | some high, some low =>
      match pairScalar? high low with
      | some scalar => bodyBytesInto tail (acc ++ (String.utf8EncodeChar (Char.ofNat scalar)).toArray)
      | none => bodyBytesInto ('\\' :: 'u' :: e :: f :: g :: h :: tail) (acc ++ (unitBytes high ['\\', 'u', a, b, c, d]).toArray)
    | some high, none => bodyBytesInto ('\\' :: 'u' :: e :: f :: g :: h :: tail) (acc ++ (unitBytes high ['\\', 'u', a, b, c, d]).toArray)
    | none, _ =>
      bodyBytesInto (a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: tail)
        (acc ++ ((String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u')).toArray)
  | '\\' :: 'u' :: a :: b :: c :: d :: tail, acc =>
    match unitValue? a b c d with
    | some unit => bodyBytesInto tail (acc ++ (unitBytes unit ['\\', 'u', a, b, c, d]).toArray)
    | none => bodyBytesInto (a :: b :: c :: d :: tail) (acc ++ ((String.utf8EncodeChar '\\' ++ String.utf8EncodeChar 'u')).toArray)
  | '\\' :: kind :: rest, acc => bodyBytesInto rest (acc ++ (escapeBytes kind).toArray)
  | character :: rest, acc => bodyBytesInto rest (acc ++ (String.utf8EncodeChar character).toArray)
termination_by characters => characters.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first
    | omega
    | (have := scalarDigits_shorter 0 0 tail after scalar _found; omega)

theorem bodyBytesInto_eq (body : List Char) (acc : Array UInt8) :
    bodyBytesInto body acc = acc ++ (bodyBytes body).toArray := by
  fun_induction bodyBytesInto body acc <;> rw [bodyBytes.eq_def] <;>
    first
      | (simp_all [Array.append_assoc]; done)
      | ((simp only; repeat' split) <;>
          first
            | (simp_all [Array.append_assoc]; done)
            | (simp_all [Array.append_assoc, Nat.isValidChar]; omega))

/-- The accumulated decoder, for compiled code. -/
def bodyBytesTR (body : List Char) : List UInt8 := (bodyBytesInto body #[]).toList

@[csimp] theorem bodyBytes_eq_tr : @bodyBytes = @bodyBytesTR := by
  funext body
  simp [bodyBytesTR, bodyBytesInto_eq]

/-- The string a literal's body denotes, when its bytes are valid UTF-8. -/
def decodeBody (body : List Char) : Option String :=
  String.fromUTF8? (bodyBytes body).toByteArray

/-- The body PeTTa's printer writes for a string: the quote and the
backslash escaped, every other character as it is. -/
def escapeBody : List Char → List Char
  | [] => []
  | '"' :: rest => '\\' :: '"' :: escapeBody rest
  | '\\' :: rest => '\\' :: '\\' :: escapeBody rest
  | character :: rest => character :: escapeBody rest

theorem bodyBytes_escapeBody : ∀ characters : List Char,
    bodyBytes (escapeBody characters) = characters.flatMap String.utf8EncodeChar
  | [] => by simp [escapeBody, bodyBytes]
  | character :: rest => by
    have ih := bodyBytes_escapeBody rest
    by_cases quote : character = '"'
    · subst quote
      simp only [escapeBody]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    by_cases backslash : character = '\\'
    · subst backslash
      simp only [escapeBody]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    rw [escapeBody.eq_4 character rest quote backslash, bodyBytes.eq_def]
    split <;> simp_all

/-- **Read after print.** The body PeTTa's printer writes for a string
denotes exactly that string. -/
theorem decodeBody_escapeBody (text : String) : decodeBody (escapeBody text.toList) = some text := by
  have bytes : (bodyBytes (escapeBody text.toList)).toByteArray = text.toByteArray := by
    rw [bodyBytes_escapeBody, ← String.utf8Encode_toList]
    rfl
  unfold decodeBody String.fromUTF8?
  rw [bytes]
  rw [dif_pos text.isValidUTF8]
  congr 1

/-! Examples. -/

example : decodeBody "a\\\"b".toList = some "a\"b" := by decide +kernel
example : decodeBody "\\x41\\u{e9}".toList = some "Aé" := by decide +kernel
/-- A malformed escape retains its complete spelling. -/
example : decodeBody "\\u{zz}".toList = some "\\u{zz}" := by decide +kernel
/-- A byte outside any UTF-8 sequence denotes no string. -/
example : decodeBody "\\xff".toList = none := by decide +kernel
/-- JSON's escapes, as CeTTa's lang library writes them for captured rows. -/
example : decodeBody "a\\u0000b\\r\\n\\b\\f\\/".toList = some "a\u0000b\r\n\u0008\u000c/" := by decide +kernel
/-- A surrogate pair reads as its scalar; a lone surrogate retains its spelling. -/
example : decodeBody "\\uD83D\\uDE00\\u00e9".toList = some "😀é" := by decide +kernel
example : decodeBody "\\uD83Dx\\uDE00".toList = some "\\uD83Dx\\uDE00" := by decide +kernel
/-- Negative control: an incomplete numeric escape is not partly interpreted. -/
example : decodeBody "\\u12".toList = some "\\u12" := by decide +kernel

example : decodeBody "\\q\\x4".toList = some "\\q\\x4" := by decide +kernel
/-- Leading zeros are unlimited. -/
example : decodeBody "\\u{0001F600}\\u{000000041}".toList = some "😀A" := by decide +kernel
/-- Negative controls: no digits, or a value beyond the Unicode range, keep the spelling. -/
example : decodeBody "\\u{}\\u{110000}\\u{0000110000}".toList =
    some "\\u{}\\u{110000}\\u{0000110000}" := by decide +kernel

#print axioms decodeBody_escapeBody

/-! ## Every character by its scalar -/

/-- Non-control Unicode other than the quote and the backslash: written as itself. -/
def plainCharacter (character : Char) : Bool :=
  0x20 ≤ character.toNat && character.toNat != 0x7f && character != '"' && character != '\\'

/-- A lowercase hexadecimal digit. -/
def hexChar (digit : Nat) : Char := if digit < 10 then Char.ofNat (48 + digit) else Char.ofNat (87 + digit)

theorem hexValue_hexChar : ∀ digit, digit < 16 → hexValue? (hexChar digit) = some digit := by decide

theorem hexChar_not_close : ∀ digit, digit < 16 → hexChar digit ≠ '}' := by decide

theorem hexChar_plain : ∀ digit, digit < 16 → plainCharacter (hexChar digit) = true := by decide

/-- A character the canonical spelling writes as `\xhh`. -/
def control (character : Char) : Bool :=
  (character.toNat < 0x20 && character != '\n' && character != '\t' && character != '\r') || character.toNat == 0x7f

/-- One character in the canonical spelling. -/
def canonicalCharacter (character : Char) : List Char :=
  if character = '"' then ['\\', '"']
  else if character = '\\' then ['\\', '\\']
  else if character = '\n' then ['\\', 'n']
  else if character = '\t' then ['\\', 't']
  else if character = '\r' then ['\\', 'r']
  else if control character then ['\\', 'x', hexChar (character.toNat / 16), hexChar (character.toNat % 16)]
  else [character]

/-- A string body in the canonical spelling. -/
def canonicalBody (characters : List Char) : List Char := characters.flatMap canonicalCharacter

theorem utf8EncodeChar_ascii {character : Char} (small : character.toNat < 0x80) :
    String.utf8EncodeChar character = [UInt8.ofNat character.toNat] := by
  simp only [String.utf8EncodeChar]
  rw [if_pos (show character.val.toNat ≤ 127 from Nat.lt_succ_iff.mp small)]
  rfl

theorem bodyBytes_canonicalBody : ∀ characters : List Char,
    bodyBytes (canonicalBody characters) = characters.flatMap String.utf8EncodeChar
  | [] => by simp [canonicalBody, bodyBytes]
  | character :: rest => by
    have ih := bodyBytes_canonicalBody rest
    have unfolded : canonicalBody (character :: rest) = canonicalCharacter character ++ canonicalBody rest := by
      simp [canonicalBody]
    rw [unfolded, List.flatMap_cons]
    by_cases quote : character = '"'
    · subst quote
      rw [show canonicalCharacter '"' = ['\\', '"'] from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    by_cases backslash : character = '\\'
    · subst backslash
      rw [show canonicalCharacter '\\' = ['\\', '\\'] from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    by_cases newline : character = '\n'
    · subst newline
      rw [show canonicalCharacter '\n' = ['\\', 'n'] from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    by_cases tab : character = '\t'
    · subst tab
      rw [show canonicalCharacter '\t' = ['\\', 't'] from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    by_cases carriage : character = '\r'
    · subst carriage
      rw [show canonicalCharacter '\r' = ['\\', 'r'] from rfl]
      simp only [List.cons_append, List.nil_append]
      rw [bodyBytes.eq_def]
      simp [escapeBytes, simpleEscape, ih]
    by_cases controlled : control character = true
    · have small : character.toNat < 0x80 := by
        simp only [control, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at controlled
        omega
      have head : canonicalCharacter character =
          ['\\', 'x', hexChar (character.toNat / 16), hexChar (character.toNat % 16)] := by
        simp [canonicalCharacter, quote, backslash, newline, tab, carriage, controlled]
      rw [head]
      simp only [List.cons_append, List.nil_append]
      rw [bodyBytes.eq_def]
      simp only
      rw [hexValue_hexChar _ (by omega), hexValue_hexChar _ (Nat.mod_lt _ (by decide))]
      simp only
      rw [ih, utf8EncodeChar_ascii small, Nat.div_add_mod]
      rfl
    · have head : canonicalCharacter character = [character] := by
        simp [canonicalCharacter, quote, backslash, newline, tab, carriage, controlled]
      rw [head, List.singleton_append, bodyBytes.eq_def]
      split <;> simp_all

/-- **Read after write.** The data reader decodes a canonical body back to its
string. -/
theorem decodeBody_canonicalBody (text : String) : decodeBody (canonicalBody text.toList) = some text := by
  have bytes : (bodyBytes (canonicalBody text.toList)).toByteArray = text.toByteArray := by
    rw [bodyBytes_canonicalBody, ← String.utf8Encode_toList]
    rfl
  unfold decodeBody String.fromUTF8?
  rw [bytes]
  rw [dif_pos text.isValidUTF8]
  congr 1

/-- A literal body in which every backslash escapes the next character and no
character is a quote, a backslash or a newline otherwise. -/
inductive EscapedBody : List Char → Prop
  | nil : EscapedBody []
  | plain {character : Char} {rest : List Char} : character ≠ '\\' → character ≠ '"' → character ≠ '\n' →
      EscapedBody rest → EscapedBody (character :: rest)
  | escape {character : Char} {rest : List Char} : character ≠ '\n' → EscapedBody rest →
      EscapedBody ('\\' :: character :: rest)

theorem EscapedBody.append {first second : List Char} (one : EscapedBody first) (two : EscapedBody second) :
    EscapedBody (first ++ second) := by
  induction one with
  | nil => exact two
  | plain notBackslash notQuote notNewline _ ih => exact .plain notBackslash notQuote notNewline ih
  | escape notNewline _ ih => exact .escape notNewline ih

theorem EscapedBody.of_plain : ∀ {characters : List Char}, characters.all plainCharacter = true → EscapedBody characters
  | [], _ => .nil
  | character :: rest, allPlain => by
    simp only [List.all_cons, Bool.and_eq_true] at allPlain
    refine .plain ?_ ?_ ?_ (EscapedBody.of_plain allPlain.2)
    all_goals
      intro same
      subst same
      simp [plainCharacter] at allPlain


theorem canonicalCharacter_of_plain {character : Char} (plain : plainCharacter character = true) :
    canonicalCharacter character = [character] := by
  simp only [plainCharacter, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at plain
  obtain ⟨⟨⟨low, notDel⟩, notQuote⟩, notSlash⟩ := plain
  have notNewline : character ≠ '\n' := by intro h; subst h; simp at low
  have notTab : character ≠ '\t' := by intro h; subst h; simp at low
  have notReturn : character ≠ '\r' := by intro h; subst h; simp at low
  simp [canonicalCharacter, control, notQuote, notSlash, notNewline, notTab, notReturn, notDel,
    show ¬character.toNat < 32 from by omega]

theorem canonicalBody_of_plain : ∀ {characters : List Char}, characters.all plainCharacter = true →
    canonicalBody characters = characters
  | [], _ => rfl
  | character :: rest, allPlain => by
    simp only [List.all_cons, Bool.and_eq_true] at allPlain
    simp only [canonicalBody, List.flatMap_cons, canonicalCharacter_of_plain allPlain.1,
      List.singleton_append]
    exact congrArg (character :: ·) (canonicalBody_of_plain allPlain.2)

theorem canonicalCharacter_all_plain (character : Char) :
    (canonicalCharacter character).all plainCharacter = plainCharacter character := by
  by_cases plain : plainCharacter character = true
  · simp [canonicalCharacter_of_plain plain, plain]
  · have no : plainCharacter character = false := by simpa using plain
    unfold canonicalCharacter
    repeat' split
    all_goals simp_all [plainCharacter]

theorem canonicalBody_all_plain (characters : List Char) :
    (canonicalBody characters).all plainCharacter = characters.all plainCharacter := by
  induction characters with
  | nil => rfl
  | cons c cs ih => simp_all [canonicalBody, canonicalCharacter_all_plain]

theorem canonicalCharacter_escaped (character : Char) : EscapedBody (canonicalCharacter character) := by
  by_cases plain : plainCharacter character = true
  · rw [canonicalCharacter_of_plain plain]
    exact EscapedBody.of_plain (by simp [plain])
  · unfold canonicalCharacter
    split
    · exact .escape (by decide) .nil
    split
    · exact .escape (by decide) .nil
    split
    · exact .escape (by decide) .nil
    split
    · exact .escape (by decide) .nil
    split
    · exact .escape (by decide) .nil
    split
    · refine .escape (by decide) (EscapedBody.of_plain ?_)
      simp only [List.all_cons, List.all_nil]
      have small : character.toNat < 128 := by
        rename_i h
        simp only [control, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        omega
      simp [hexChar_plain _ (show character.toNat / 16 < 16 from by omega),
        hexChar_plain _ (Nat.mod_lt _ (by decide))]
    · rename_i h1 h2 h3 h4 h5 h6
      exact .plain h2 h1 h3 .nil

theorem canonicalBody_escaped (characters : List Char) : EscapedBody (canonicalBody characters) := by
  induction characters with
  | nil => exact .nil
  | cons c cs ih => exact EscapedBody.append (canonicalCharacter_escaped c) ih

example : canonicalBody "λé漢字".toList = "λé漢字".toList := by decide +kernel
example : decodeBody (canonicalBody "a\"b\\c\nd é".toList) = some "a\"b\\c\nd é" := decodeBody_canonicalBody _

#print axioms decodeBody_canonicalBody
#print axioms canonicalBody_escaped
#print axioms bodyBytes_eq_tr

end Mettapedia.Languages.MeTTa.PeTTa.StringLiteral
