import Mettapedia.GSLT.Parsing.GroundAtomWireV1
import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mettapedia.Languages.MM0.Kernel.Context
import Mettapedia.Languages.MM0.MeTTa.Data.Store

/-!
# Raw MM0 frontend data

The syntax and environment presentations carry names as quoted
`cons (cp n) ... nil` constructor chains, declaration positions as
`NatZeroV1` / `NatSuccV1`, and sort flags as presence constructors.
These codecs use the existing native Atom carrier and Kernel.SortInfo.
They do not evaluate the frontend or authorize a kernel declaration.

An evaluated PeTTa `cons` produces a flat native expression container.
That value is distinct from the quoted constructor chain decoded here.
Source positions are trace metadata; kernel IDs are assigned separately
when the ordered environment is projected into a specification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TextualData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Parsing.ParserProfileSemantics (isUnicodeScalar)
open Kernel (SortInfo)

/-- The raw scalar constructor. Unicode admission is separate. -/
def scalarValue (value : Nat) : Atom :=
  .expression [.symbol "cp", Store.natural value]

def decodeScalar : Atom → Option Nat
  | .expression [.symbol "cp", .grounded (.int value)] =>
      if 0 ≤ value then some value.toNat else none
  | _ => none

@[simp] theorem decodeScalar_scalarValue (value : Nat) :
    decodeScalar (scalarValue value) = some value := by
  simp [scalarValue, decodeScalar, Store.natural]

theorem decodeScalar_reflects (atom : Atom) (value : Nat)
    (decoded : decodeScalar atom = some value) : atom = scalarValue value := by
  unfold decodeScalar at decoded
  split at decoded
  · rename_i integer
    split at decoded
    · rename_i nonnegative
      have output : integer.toNat = value := by simpa using decoded
      subst value
      simp [scalarValue, Store.natural, Int.toNat_of_nonneg nonnegative]
    · simp at decoded
  · simp at decoded

theorem decodeScalar_iff (atom : Atom) (value : Nat) :
    decodeScalar atom = some value ↔ atom = scalarValue value := by
  constructor
  · exact decodeScalar_reflects atom value
  · rintro rfl
    exact decodeScalar_scalarValue value

theorem scalarValue_injective : Function.Injective scalarValue := by
  intro first second same
  have decoded := congrArg decodeScalar same
  simpa using decoded

/-- Exact quoted `cons` / `nil` data, preserving scalar order and multiplicity. -/
def scalarListValue : List Nat → Atom
  | [] => .symbol "nil"
  | scalar :: rest =>
      .expression [.symbol "cons", scalarValue scalar, scalarListValue rest]

def decodeScalarList : Atom → Option (List Nat)
  | .symbol "nil" => some []
  | .expression [.symbol "cons", scalar, rest] => do
      let first ← decodeScalar scalar
      let remaining ← decodeScalarList rest
      pure (first :: remaining)
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeScalarList_scalarListValue (values : List Nat) :
    decodeScalarList (scalarListValue values) = some values := by
  induction values with
  | nil => simp [scalarListValue, decodeScalarList]
  | cons first rest ih => simp [scalarListValue, decodeScalarList, ih]

theorem decodeScalarList_reflects (atom : Atom) (values : List Nat)
    (decoded : decodeScalarList atom = some values) : atom = scalarListValue values := by
  unfold decodeScalarList at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i scalar rest
    cases firstDecoded : decodeScalar scalar with
    | none => simp [firstDecoded] at decoded
    | some first =>
        cases restDecoded : decodeScalarList rest with
        | none => simp [firstDecoded, restDecoded] at decoded
        | some remaining =>
            have output : first :: remaining = values := by
              simpa [firstDecoded, restDecoded] using decoded
            subst values
            rw [decodeScalar_reflects scalar first firstDecoded,
              decodeScalarList_reflects rest remaining restDecoded]
            rfl
  · simp at decoded
termination_by sizeOf atom

theorem decodeScalarList_iff (atom : Atom) (values : List Nat) :
    decodeScalarList atom = some values ↔ atom = scalarListValue values := by
  constructor
  · exact decodeScalarList_reflects atom values
  · rintro rfl
    exact decodeScalarList_scalarListValue values

theorem scalarListValue_injective : Function.Injective scalarListValue := by
  intro first second same
  have decoded := congrArg decodeScalarList same
  simpa using decoded

private theorem unicodeScalar_toNat (character : Char) :
    isUnicodeScalar character.toNat = true := by
  cases character with
  | mk value valid =>
      simp [isUnicodeScalar, Char.toNat] at valid ⊢
      omega

private theorem ofNat_toNat_of_unicodeScalar (value : Nat)
    (valid : isUnicodeScalar value = true) : (Char.ofNat value).toNat = value := by
  have validNatural : value.isValidChar := by
    simp [isUnicodeScalar, Nat.isValidChar] at valid ⊢
    omega
  rw [Char.ofNat, dif_pos validNatural]
  rfl

def nameCharsValue (characters : List Char) : Atom :=
  scalarListValue (characters.map Char.toNat)

/-- Unicode decoding only; MM0 identifier grammar admission remains separate. -/
def decodeNameChars : Atom → Option (List Char)
  | .symbol "nil" => some []
  | .expression [.symbol "cons", scalar, rest] => do
      let first ← decodeScalar scalar
      if isUnicodeScalar first then do
        let remaining ← decodeNameChars rest
        pure (Char.ofNat first :: remaining)
      else none
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeNameChars_nameCharsValue (characters : List Char) :
    decodeNameChars (nameCharsValue characters) = some characters := by
  induction characters with
  | nil => simp [nameCharsValue, scalarListValue, decodeNameChars]
  | cons first rest ih =>
      simp only [nameCharsValue] at ih
      simp [nameCharsValue, scalarListValue, decodeNameChars, unicodeScalar_toNat,
        ih]

theorem decodeNameChars_reflects (atom : Atom) (characters : List Char)
    (decoded : decodeNameChars atom = some characters) : atom = nameCharsValue characters := by
  unfold decodeNameChars at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i scalar rest
    cases firstDecoded : decodeScalar scalar with
    | none => simp [firstDecoded] at decoded
    | some first =>
        simp only [firstDecoded] at decoded
        change (if isUnicodeScalar first then
          (decodeNameChars rest).bind (fun remaining => some (Char.ofNat first :: remaining))
          else none) = some characters at decoded
        split at decoded
        · rename_i valid
          cases restDecoded : decodeNameChars rest with
          | none => simp [restDecoded] at decoded
          | some remaining =>
              have output : Char.ofNat first :: remaining = characters := by
                simpa [restDecoded] using decoded
              subst characters
              rw [decodeScalar_reflects scalar first firstDecoded,
                decodeNameChars_reflects rest remaining restDecoded]
              simp [nameCharsValue, scalarListValue, ofNat_toNat_of_unicodeScalar first valid]
        · simp at decoded
  · simp at decoded
termination_by sizeOf atom

theorem decodeNameChars_iff (atom : Atom) (characters : List Char) :
    decodeNameChars atom = some characters ↔ atom = nameCharsValue characters := by
  constructor
  · exact decodeNameChars_reflects atom characters
  · rintro rfl
    exact decodeNameChars_nameCharsValue characters

def nameValue (value : String) : Atom := nameCharsValue value.toList

def decodeName (atom : Atom) : Option String :=
  (decodeNameChars atom).map String.ofList

@[simp] theorem decodeName_nameValue (value : String) :
    decodeName (nameValue value) = some value := by
  simp [decodeName, nameValue, String.ofList_toList]

theorem decodeName_reflects (atom : Atom) (value : String)
    (decoded : decodeName atom = some value) : atom = nameValue value := by
  obtain ⟨characters, found, same⟩ := Option.map_eq_some_iff.mp decoded
  rw [decodeNameChars_reflects atom characters found]
  simp [nameValue, ← same, String.toList_ofList]

theorem decodeName_iff (atom : Atom) (value : String) :
    decodeName atom = some value ↔ atom = nameValue value := by
  constructor
  · exact decodeName_reflects atom value
  · rintro rfl
    exact decodeName_nameValue value

theorem nameValue_injective : Function.Injective nameValue := by
  intro first second same
  have decoded := congrArg decodeName same
  simpa using decoded

/-- A source position or frontend index, independent of a kernel namespace ID. -/
def indexValue : Nat → Atom
  | 0 => .symbol "NatZeroV1"
  | value + 1 => .expression [.symbol "NatSuccV1", indexValue value]

def decodeIndex : Atom → Option Nat
  | .symbol "NatZeroV1" => some 0
  | .expression [.symbol "NatSuccV1", previous] => (decodeIndex previous).map Nat.succ
  | _ => none
termination_by atom => sizeOf atom

@[simp] theorem decodeIndex_indexValue (value : Nat) :
    decodeIndex (indexValue value) = some value := by
  induction value with
  | zero => simp [indexValue, decodeIndex]
  | succ previous ih => simp [indexValue, decodeIndex, ih]

theorem decodeIndex_reflects (atom : Atom) (value : Nat)
    (decoded : decodeIndex atom = some value) : atom = indexValue value := by
  unfold decodeIndex at decoded
  split at decoded
  · cases decoded
    rfl
  · rename_i previous
    obtain ⟨prior, found, same⟩ := Option.map_eq_some_iff.mp decoded
    rw [decodeIndex_reflects previous prior found, ← same]
    rfl
  · simp at decoded
termination_by sizeOf atom

theorem decodeIndex_iff (atom : Atom) (value : Nat) :
    decodeIndex atom = some value ↔ atom = indexValue value := by
  constructor
  · exact decodeIndex_reflects atom value
  · rintro rfl
    exact decodeIndex_indexValue value

theorem indexValue_injective : Function.Injective indexValue := by
  intro first second same
  have decoded := congrArg decodeIndex same
  simpa using decoded

def modifierValue : Bool → Atom
  | false => .symbol "MM0ModifierAbsentV1"
  | true => .symbol "MM0ModifierPresentV1"

def decodeModifier : Atom → Option Bool
  | .symbol "MM0ModifierAbsentV1" => some false
  | .symbol "MM0ModifierPresentV1" => some true
  | _ => none

@[simp] theorem decodeModifier_modifierValue (value : Bool) :
    decodeModifier (modifierValue value) = some value := by
  cases value <;> simp [modifierValue, decodeModifier]

theorem decodeModifier_reflects (atom : Atom) (value : Bool)
    (decoded : decodeModifier atom = some value) : atom = modifierValue value := by
  unfold decodeModifier at decoded
  split at decoded <;> simp_all [modifierValue]

theorem decodeModifier_iff (atom : Atom) (value : Bool) :
    decodeModifier atom = some value ↔ atom = modifierValue value := by
  constructor
  · exact decodeModifier_reflects atom value
  · rintro rfl
    exact decodeModifier_modifierValue value

theorem modifierValue_injective : Function.Injective modifierValue := by
  intro first second same
  have decoded := congrArg decodeModifier same
  simpa using decoded

def modifiersValue (info : SortInfo) : Atom :=
  .expression [.symbol "MM0SortModifiersV1", modifierValue info.pure,
    modifierValue info.strict, modifierValue info.provable, modifierValue info.free]

def decodeModifiers : Atom → Option SortInfo
  | .expression [.symbol "MM0SortModifiersV1", pureAtom, strict, provable, free] => do
      let pureFlag ← decodeModifier pureAtom
      let strictFlag ← decodeModifier strict
      let provableFlag ← decodeModifier provable
      let freeFlag ← decodeModifier free
      pure ⟨pureFlag, strictFlag, provableFlag, freeFlag⟩
  | _ => none

@[simp] theorem decodeModifiers_modifiersValue (info : SortInfo) :
    decodeModifiers (modifiersValue info) = some info := by
  cases info
  simp [modifiersValue, decodeModifiers]

theorem decodeModifiers_reflects (atom : Atom) (info : SortInfo)
    (decoded : decodeModifiers atom = some info) : atom = modifiersValue info := by
  unfold decodeModifiers at decoded
  split at decoded
  · rename_i pureAtom strict provable free
    obtain ⟨pureFlag, pureDecoded, afterPure⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨strictFlag, strictDecoded, afterStrict⟩ := Option.bind_eq_some_iff.mp afterPure
    obtain ⟨provableFlag, provableDecoded, afterProvable⟩ :=
      Option.bind_eq_some_iff.mp afterStrict
    obtain ⟨freeFlag, freeDecoded, output⟩ := Option.bind_eq_some_iff.mp afterProvable
    have same : (⟨pureFlag, strictFlag, provableFlag, freeFlag⟩ : SortInfo) = info := by
      simpa using output
    subst info
    rw [decodeModifier_reflects pureAtom pureFlag pureDecoded,
      decodeModifier_reflects strict strictFlag strictDecoded,
      decodeModifier_reflects provable provableFlag provableDecoded,
      decodeModifier_reflects free freeFlag freeDecoded]
    rfl
  · simp at decoded

theorem decodeModifiers_iff (atom : Atom) (info : SortInfo) :
    decodeModifiers atom = some info ↔ atom = modifiersValue info := by
  constructor
  · exact decodeModifiers_reflects atom info
  · rintro rfl
    exact decodeModifiers_modifiersValue info

theorem modifiersValue_injective : Function.Injective modifiersValue := by
  intro first second same
  have decoded := congrArg decodeModifiers same
  simpa using decoded

/-- A row of the existing source sort environment, with trace position retained. -/
structure SortEntry where
  name : String
  info : SortInfo
  sourcePosition : Nat
  deriving DecidableEq, Repr

def sortEntryValue (entry : SortEntry) : Atom :=
  .expression [.symbol "MM0SortEntryV1", nameValue entry.name,
    modifiersValue entry.info, indexValue entry.sourcePosition]

def decodeSortEntry : Atom → Option SortEntry
  | .expression [.symbol "MM0SortEntryV1", name, modifiers, position] => do
      let decodedName ← decodeName name
      let info ← decodeModifiers modifiers
      let sourcePosition ← decodeIndex position
      pure ⟨decodedName, info, sourcePosition⟩
  | _ => none

@[simp] theorem decodeSortEntry_sortEntryValue (entry : SortEntry) :
    decodeSortEntry (sortEntryValue entry) = some entry := by
  cases entry
  simp [sortEntryValue, decodeSortEntry]

theorem decodeSortEntry_reflects (atom : Atom) (entry : SortEntry)
    (decoded : decodeSortEntry atom = some entry) : atom = sortEntryValue entry := by
  unfold decodeSortEntry at decoded
  split at decoded
  · rename_i name modifiers position
    obtain ⟨decodedName, nameDecoded, afterName⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨info, infoDecoded, afterInfo⟩ := Option.bind_eq_some_iff.mp afterName
    obtain ⟨sourcePosition, positionDecoded, output⟩ := Option.bind_eq_some_iff.mp afterInfo
    have same : (⟨decodedName, info, sourcePosition⟩ : SortEntry) = entry := by
      simpa using output
    subst entry
    rw [decodeName_reflects name decodedName nameDecoded,
      decodeModifiers_reflects modifiers info infoDecoded,
      decodeIndex_reflects position sourcePosition positionDecoded]
    rfl
  · simp at decoded

theorem decodeSortEntry_iff (atom : Atom) (entry : SortEntry) :
    decodeSortEntry atom = some entry ↔ atom = sortEntryValue entry := by
  constructor
  · exact decodeSortEntry_reflects atom entry
  · rintro rfl
    exact decodeSortEntry_sortEntryValue entry

theorem sortEntryValue_injective : Function.Injective sortEntryValue := by
  intro first second same
  have decoded := congrArg decodeSortEntry same
  simpa using decoded

/-- The existing generic ground wire retains the exact raw source entry. -/
theorem decode_groundWire_sortEntry (entry : SortEntry) :
    (Mettapedia.GSLT.Parsing.GroundAtomWireV1.decode
      (Mettapedia.GSLT.Parsing.GroundAtomWireV1.encode (sortEntryValue entry))).bind
        decodeSortEntry = some entry := by
  rw [Mettapedia.GSLT.Parsing.GroundAtomWireV1.decode_encode]
  simp

/-! ## Shape, scalar-validity and constructor controls -/

theorem repeated_scalars_are_retained :
    decodeScalarList (scalarListValue [0, 0, 1114111]) = some [0, 0, 1114111] := by simp

theorem reordered_scalar_names_differ :
    scalarListValue [97, 98] ≠ scalarListValue [98, 97] := by
  intro same
  have values := scalarListValue_injective same
  cases values

theorem ascii_name_is_decoded :
    decodeName (scalarListValue [115, 101, 116]) = some "set" := by decide +kernel

theorem unicode_name_is_decoded :
    decodeName (scalarListValue [955, 128578]) =
      some (String.ofList [Char.ofNat 955, Char.ofNat 128578]) := by
  decide +kernel

theorem negative_scalar_is_refused :
    decodeScalar (.expression [.symbol "cp", .grounded (.int (-1))]) = none := by
  simp [decodeScalar]

theorem numeric_spelling_is_not_a_scalar :
    decodeScalar (.expression [.symbol "cp", .symbol "97"]) = none ∧
      decodeScalar (.expression [.symbol "cp", .grounded (.string "97")]) = none := by
  simp [decodeScalar]

theorem malformed_scalar_list_is_refused :
    decodeScalarList (.expression [.symbol "cons", scalarValue 97, .symbol "broken"]) = none ∧
      decodeScalarList (.expression [.symbol "cons", scalarValue 97]) = none := by
  simp [decodeScalarList]

theorem unicode_invalid_names_are_refused :
    decodeName (scalarListValue [55296]) = none ∧
      decodeName (scalarListValue [57343]) = none ∧
      decodeName (scalarListValue [1114112]) = none := by decide +kernel

/-- Integer wire decoding does not silently confer Unicode admission. -/
theorem raw_scalars_and_names_have_distinct_admission :
    decodeScalarList (scalarListValue [55296, 1114112]) = some [55296, 1114112] ∧
      decodeName (scalarListValue [55296, 1114112]) = none := by
  constructor
  · simp
  · decide +kernel

theorem native_empty_list_is_refused :
    decodeScalarList (.expression []) = none ∧ decodeName (.expression []) = none := by
  simp [decodeScalarList, decodeName, decodeNameChars]

/-- A native container beginning with a scalar has no raw constructor head. -/
theorem native_cons_list_is_refused (first : Nat) (rest : List Atom) :
    decodeScalarList (.expression (scalarValue first :: rest)) = none ∧
      decodeName (.expression (scalarValue first :: rest)) = none := by
  simp [decodeScalarList, decodeName, decodeNameChars, scalarValue]

theorem native_cons_result_is_distinct (state : Mettapedia.Languages.MeTTa.PeTTa.Effects.State) :
    Mettapedia.Languages.MeTTa.PeTTa.StdLib.apply state "cons" [scalarValue 120, .expression []] =
      .ok (state, [.expression [scalarValue 120]]) ∧
      decodeName (.expression [scalarValue 120]) = none ∧
      decodeName (scalarListValue [120]) = some "x" := by
  constructor
  · rfl
  · constructor
    · exact (native_cons_list_is_refused 120 []).2
    · decide +kernel

theorem grounded_index_is_refused (value : Nat) :
    decodeIndex (Store.natural value) = none := by simp [decodeIndex, Store.natural]

theorem malformed_index_is_refused :
    decodeIndex (.expression [.symbol "NatZeroV1"]) = none ∧
      decodeIndex (.expression [.symbol "NatSuccV1", indexValue 0, indexValue 0]) = none := by
  simp [decodeIndex]

theorem native_booleans_are_not_modifiers :
    decodeModifier (.grounded (.bool true)) = none ∧
      decodeModifier (.symbol "True") = none := by simp [decodeModifier]

theorem swapped_sort_flags_differ :
    modifiersValue ⟨true, false, false, false⟩ ≠
      modifiersValue ⟨false, true, false, false⟩ := by decide +kernel

theorem malformed_modifiers_are_refused :
    decodeModifiers (.expression [.symbol "MM0SortModifiersV1",
      modifierValue false, modifierValue false, modifierValue false]) = none ∧
      decodeModifiers (.expression [.symbol "MM0SortModifiersV1",
        modifierValue false, modifierValue false, .symbol "True", modifierValue false]) = none := by
  simp [decodeModifiers, decodeModifier, modifierValue]

theorem source_position_is_retained :
    decodeSortEntry (sortEntryValue ⟨"set", ⟨false, false, true, false⟩, 9⟩) =
      some ⟨"set", ⟨false, false, true, false⟩, 9⟩ := by simp

theorem malformed_sort_entry_is_refused :
    decodeSortEntry (.expression [.symbol "MM0SortEntryV1", nameValue "set", modifiersValue {}]) = none ∧
      decodeSortEntry (.expression [.symbol "MM0SortEntryV1", nameValue "set",
        modifiersValue {}, Store.natural 0]) = none := by
  simp [decodeSortEntry, decodeIndex, Store.natural]

end Mettapedia.Languages.MM0.MeTTa.TextualData
