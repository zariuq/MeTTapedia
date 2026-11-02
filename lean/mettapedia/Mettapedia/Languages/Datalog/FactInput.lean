import Mettapedia.Languages.Datalog.Syntax
import Mettapedia.Languages.Datalog.NumericSpelling
import Mettapedia.Util.DelimitedRecords

/-! The default tab-separated fact-file profile. Record framing preserves
empty symbols and nullary facts; CRLF terminators are normalized. Columns
past the declared arity are ignored, as in the reference's default reader.
Source-language literals and fact-file numeric spellings are separate. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.FactInput

def numberSpace (character : Char) : Bool :=
  character == ' ' || character == '\t' || character == '\r' || character == '\n' ||
    character == Char.ofNat 11 || character == Char.ofNat 12

def signedParts (characters : List Char) : Bool × List Char :=
  match characters.dropWhile numberSpace with
  | '-' :: digits => (true, digits)
  | '+' :: digits => (false, digits)
  | digits => (false, digits)

def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

def readSigned? (text : String) : Option Int :=
  let (negative, digits) := signedParts text.toList
  (NumericSpelling.readDigits? 10 digits).map (signedValue negative)

def Signed (text : String) (value : Int) : Prop :=
  ∃ magnitude, NumericSpelling.Digits 10 (signedParts text.toList).2 magnitude ∧
    value = signedValue (signedParts text.toList).1 magnitude

theorem readSigned_exact (text : String) (value : Int) : readSigned? text = some value ↔ Signed text value := by
  simp only [readSigned?, Signed, Option.map_eq_some_iff, NumericSpelling.readDigits_exact]
  exact ⟨fun ⟨magnitude, digits, same⟩ => ⟨magnitude, digits, same.symm⟩,
    fun ⟨magnitude, digits, same⟩ => ⟨magnitude, digits, same.symm⟩⟩

def unsignedParts (characters : List Char) : Nat × Bool × List Char :=
  match characters with
  | '0' :: 'b' :: rest => (2, signedParts rest)
  | '0' :: 'x' :: rest => (16, false, rest)
  | rest => (10, signedParts rest)

def unsignedValue (negative : Bool) (magnitude : Nat) : Nat :=
  if negative then (2 ^ 64 - magnitude) % (2 ^ 64) else magnitude

def readUnsigned? (text : String) : Option Nat := do
  if text.toList.head? = some '-' then none else do
    let parts := unsignedParts text.toList
    let magnitude ← NumericSpelling.readDigits? parts.1 parts.2.2
    if magnitude < 2 ^ 64 then some (unsignedValue parts.2.1 magnitude) else none

def Unsigned (text : String) (value : Nat) : Prop :=
  text.toList.head? ≠ some '-' ∧ ∃ magnitude,
    NumericSpelling.Digits (unsignedParts text.toList).1 (unsignedParts text.toList).2.2 magnitude ∧
    magnitude < 2 ^ 64 ∧ value = unsignedValue (unsignedParts text.toList).2.1 magnitude

theorem readUnsigned_exact (text : String) (value : Nat) : readUnsigned? text = some value ↔ Unsigned text value := by
  by_cases forbidden : text.toList.head? = some '-'
  · simp [readUnsigned?, Unsigned, forbidden]
  · simp only [readUnsigned?, Unsigned, forbidden]
    change ((NumericSpelling.readDigits? (unsignedParts text.toList).1 (unsignedParts text.toList).2.2).bind
      (fun magnitude => if magnitude < 2 ^ 64 then some (unsignedValue (unsignedParts text.toList).2.1 magnitude) else none)) = some value ↔ _
    rw [Option.bind_eq_some_iff]
    simp only [NumericSpelling.readDigits_exact]
    constructor
    · rintro ⟨magnitude, digits, read⟩
      split at read
      · exact ⟨forbidden, magnitude, digits, by assumption, (Option.some.inj read).symm⟩
      · cases read
    · rintro ⟨_, magnitude, digits, width, rfl⟩
      exact ⟨magnitude, digits, if_pos width⟩

def readField? (kind : AttributeType) (text : String) : Option Value := do
  let value ← match kind with
    | .symbol => some (.symbol text)
    | .number => Value.number <$> readSigned? text
    | .unsigned => Value.unsigned <$> readUnsigned? text
    | .floating => none
  if value.fits64 then some value else none

inductive FieldMeaning : AttributeType → String → Value → Prop where
  | symbol (text : String) : FieldMeaning .symbol text (.symbol text)
  | number {text : String} {value : Int} (digits : Signed text value)
      (width : Value.fits64 (.number value) = true) : FieldMeaning .number text (.number value)
  | unsigned {text : String} {value : Nat} (digits : Unsigned text value)
      (width : Value.fits64 (.unsigned value) = true) : FieldMeaning .unsigned text (.unsigned value)

theorem readField_sound (kind : AttributeType) (text : String) (value : Value)
    (read : readField? kind text = some value) : FieldMeaning kind text value := by
  cases kind with
  | symbol =>
    have same : Value.symbol text = value := by simpa [readField?, Value.fits64] using read
    exact same ▸ FieldMeaning.symbol text
  | floating => simp [readField?] at read
  | number =>
    cases parsed : readSigned? text with
    | none => simp [readField?, parsed] at read
    | some number =>
      by_cases width : Value.fits64 (.number number) = true
      · have same : Value.number number = value := by simpa [readField?, parsed, width] using read
        exact same ▸ FieldMeaning.number ((readSigned_exact _ _).mp parsed) width
      · simp [readField?, parsed, width] at read
  | unsigned =>
    cases parsed : readUnsigned? text with
    | none => simp [readField?, parsed] at read
    | some number =>
      by_cases width : Value.fits64 (.unsigned number) = true
      · have same : Value.unsigned number = value := by simpa [readField?, parsed, width] using read
        exact same ▸ FieldMeaning.unsigned ((readUnsigned_exact _ _).mp parsed) width
      · simp [readField?, parsed, width] at read

theorem readField_complete {kind : AttributeType} {text : String} {value : Value}
    (meaning : FieldMeaning kind text value) : readField? kind text = some value := by
  cases meaning with
  | symbol => rfl
  | number digits width => simp [readField?, (readSigned_exact _ _).mpr digits, width]
  | unsigned digits width => simp [readField?, (readUnsigned_exact _ _).mpr digits, width]

theorem readField_exact (kind : AttributeType) (text : String) (value : Value) :
    readField? kind text = some value ↔ FieldMeaning kind text value :=
  ⟨readField_sound kind text value, readField_complete⟩

def readFields? : List AttributeType → List String → Option (List Value)
  | [], _ => some []
  | _ :: _, [] => none
  | kind :: kinds, field :: fields => do
      pure ((← readField? kind field) :: (← readFields? kinds fields))

inductive FieldsMeaning : List AttributeType → List String → List Value → Prop where
  | nil (remaining : List String) : FieldsMeaning [] remaining []
  | cons {kind : AttributeType} {kinds : List AttributeType} {field : String} {fields : List String}
      {value : Value} {values : List Value} (head : FieldMeaning kind field value)
      (tail : FieldsMeaning kinds fields values) :
      FieldsMeaning (kind :: kinds) (field :: fields) (value :: values)

theorem readFields_sound (types : List AttributeType) (fields : List String) (values : List Value)
    (read : readFields? types fields = some values) : FieldsMeaning types fields values := by
  induction types generalizing fields values with
  | nil => cases Option.some.inj read; exact .nil fields
  | cons kind kinds ih =>
    cases fields with
    | nil => cases read
    | cons field fields =>
      obtain ⟨value, fieldRead, rest⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨tail, tailRead, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      exact .cons (readField_sound _ _ _ fieldRead) (ih _ _ tailRead)

theorem readFields_complete {types : List AttributeType} {fields : List String} {values : List Value}
    (meaning : FieldsMeaning types fields values) : readFields? types fields = some values := by
  induction meaning with
  | nil => rfl
  | cons head tail ih => simp [readFields?, readField_complete head, ih]

theorem readFields_exact (types : List AttributeType) (fields : List String) (values : List Value) :
    readFields? types fields = some values ↔ FieldsMeaning types fields values :=
  ⟨readFields_sound types fields values, readFields_complete⟩

def fields (line : List Char) : List String :=
  let line := if line.getLast? = some '\r' then line.dropLast else line
  (Mettapedia.Util.DelimitedRecords.decode '\t' (line ++ ['\t'])).map String.ofList

def read? (relation : QualifiedName) (types : List AttributeType) (input : String) : Option (List GroundFact) :=
  (Mettapedia.Util.DelimitedRecords.decode '\n' input.toList).mapM fun line => do
    pure ⟨relation, ← readFields? types (fields line)⟩

def Meaning (relation : QualifiedName) (types : List AttributeType) (input : String)
    (facts : List GroundFact) : Prop :=
  ∃ lines, Mettapedia.Util.DelimitedRecords.Framed '\n' input.toList lines ∧
    List.Forall₂ (fun line fact => fact.relation = relation ∧ FieldsMeaning types (fields line) fact.values) lines facts

end Mettapedia.Languages.Datalog.FactInput
