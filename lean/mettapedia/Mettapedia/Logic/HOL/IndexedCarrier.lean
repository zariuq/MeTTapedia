import Mathlib.Data.Option.Basic
import Mathlib.Logic.Equiv.Defs

/-! # Inhabited raw carriers for possibly empty indexed families

An option of the dependent sum is inhabited even when every fibre is empty.
The extra value is invalid at every index. Projection checks the index and
returns no value on a mismatch; it never supplies a default fibre inhabitant.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedCarrier

universe u v
variable {Index : Type u} (Family : Index → Type v)

abbrev Raw := Option (Sigma Family)

def encode {index : Index} (value : Family index) : Raw Family := some ⟨index, value⟩

def Valid (index : Index) (raw : Raw Family) : Prop :=
  ∃ value : Family index, raw = encode Family value

noncomputable def decode (index : Index) (raw : Raw Family) : Option (Family index) := by
  classical
  exact match raw with
    | none => none
    | some ⟨actual, value⟩ => if same : actual = index then some (same ▸ value) else none

@[simp] theorem decode_encode {index : Index} (value : Family index) :
    decode Family index (encode Family value) = some value := by
  simp [decode, encode]

theorem encode_injective (index : Index) : Function.Injective (encode Family (index := index)) := by
  intro first second same
  have decoded := congrArg (decode Family index) same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem decode_eq_some_iff {index : Index} {raw : Raw Family} {value : Family index} :
    decode Family index raw = some value ↔ raw = encode Family value := by
  constructor
  · intro decoded
    cases raw with
    | none => cases decoded
    | some entry =>
        rcases entry with ⟨actual, term⟩
        by_cases same : actual = index
        · subst actual
          have values : term = value := by simpa [decode] using decoded
          subst value
          rfl
        · simp [decode, same] at decoded
  · rintro rfl
    exact decode_encode Family value

theorem valid_iff_decodes (index : Index) (raw : Raw Family) :
    Valid Family index raw ↔ ∃ value, decode Family index raw = some value := by
  simp only [Valid, decode_eq_some_iff]

@[simp] theorem invalid_sentinel (index : Index) : ¬Valid Family index none := by
  rintro ⟨value, impossible⟩
  cases impossible

theorem empty_fibre_invalid (index : Index) [IsEmpty (Family index)] (raw : Raw Family) :
    ¬Valid Family index raw := by
  rintro ⟨value, _⟩
  exact isEmptyElim value

theorem empty_fibre_decode (index : Index) [IsEmpty (Family index)] (raw : Raw Family) :
    decode Family index raw = none := by
  cases result : decode Family index raw with
  | none => rfl
  | some value => exact isEmptyElim value

theorem different_index_refused {first second : Index} (different : first ≠ second)
    (value : Family first) : decode Family second (encode Family value) = none := by
  simp [decode, encode, different]

noncomputable def fibreEquiv (index : Index) : Family index ≃ { raw : Raw Family // Valid Family index raw } where
  toFun value := ⟨encode Family value, value, rfl⟩
  invFun raw := Classical.choose raw.property
  left_inv value := encode_injective Family index (Classical.choose_spec (show Valid Family index (encode Family value) from ⟨value, rfl⟩)).symm
  right_inv raw := Subtype.ext (Classical.choose_spec raw.property).symm

namespace Controls

def family : Bool → Type
  | false => Empty
  | true => Nat

instance : IsEmpty (family false) := inferInstanceAs (IsEmpty Empty)

theorem raw_inhabited_empty_fibre :
    Nonempty (Raw family) ∧ ¬∃ raw, Valid family false raw := by
  refine ⟨⟨none⟩, ?_⟩
  rintro ⟨raw, valid⟩
  exact empty_fibre_invalid family false raw valid

theorem existing_value_recovers (number : Nat) :
    decode family true (encode family (index := true) number) = some number :=
  decode_encode family (index := true) number

theorem existing_value_does_not_fill_empty_fibre (number : Nat) :
    decode family false (encode family (index := true) number) = none :=
  empty_fibre_decode family false _

end Controls

#print axioms fibreEquiv
#print axioms Controls.raw_inhabited_empty_fibre

end Mettapedia.Logic.HOL.IndexedCarrier
