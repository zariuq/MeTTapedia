import Mettapedia.Machines.TIsa.Footprint

/-!
# Checked native address formation

The arithmetic guard is a condition on the transform's explicit pointer,
index, displacement and capability inputs. No modular wrap can manufacture
an admitted pointer. The one-past address is allowed for formation; a later
positive-width access still checks its complete byte range.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

def addressSum (pointer index scale : Nat) : Nat := pointer + index * 2 ^ scale

def addressTarget (pointer index scale : Nat) (displacement : Int) : Int :=
  (addressSum pointer index scale : Int) + displacement

def AddressAdmitted (range : ByteRange) (pointer index scale : Nat) (displacement : Int) : Prop :=
  range.valid64 = true ∧
  range.base ≤ pointer ∧ pointer ≤ range.stop ∧
  scale ≤ 3 ∧ index * 2 ^ scale < 2 ^ 64 ∧ addressSum pointer index scale < 2 ^ 64 ∧
  -(2 ^ 31 : Int) ≤ displacement ∧ displacement < 2 ^ 31 ∧
  0 ≤ addressTarget pointer index scale displacement ∧
  addressTarget pointer index scale displacement < 2 ^ 64 ∧
  (range.base : Int) ≤ addressTarget pointer index scale displacement ∧
  addressTarget pointer index scale displacement ≤ (range.stop : Int)

instance (range : ByteRange) (pointer index scale : Nat) (displacement : Int) :
    Decidable (AddressAdmitted range pointer index scale displacement) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkedAddress? (range : ByteRange) (pointer index scale : Nat)
    (displacement : Int) : Option Nat :=
  if AddressAdmitted range pointer index scale displacement then
    some (addressTarget pointer index scale displacement).toNat
  else none

theorem checkedAddress?_iff (range : ByteRange) (pointer index scale address : Nat)
    (displacement : Int) :
    checkedAddress? range pointer index scale displacement = some address ↔
      AddressAdmitted range pointer index scale displacement ∧
      address = (addressTarget pointer index scale displacement).toNat := by
  unfold checkedAddress?
  by_cases admitted : AddressAdmitted range pointer index scale displacement
  · rw [if_pos admitted]
    constructor
    · intro same
      exact ⟨admitted, (Option.some.inj same).symm⟩
    · rintro ⟨_, rfl⟩
      rfl
  · simp [admitted]

theorem checkedAddress_no_wrap (range : ByteRange) (pointer index scale address : Nat)
    (displacement : Int)
    (accepted : checkedAddress? range pointer index scale displacement = some address) :
    index * 2 ^ scale < 2 ^ 64 ∧ addressSum pointer index scale < 2 ^ 64 ∧ address < 2 ^ 64 := by
  obtain ⟨guarded, rfl⟩ := (checkedAddress?_iff range pointer index scale address displacement).mp accepted
  rcases guarded with ⟨_, _, _, _, shift, sum, _, _, nonnegative, bound, _, _⟩
  exact ⟨shift, sum, by omega⟩

theorem checkedAddress_in_capability (range : ByteRange) (pointer index scale address : Nat)
    (displacement : Int)
    (accepted : checkedAddress? range pointer index scale displacement = some address) :
    range.base ≤ address ∧ address ≤ range.stop := by
  obtain ⟨guarded, rfl⟩ := (checkedAddress?_iff range pointer index scale address displacement).mp accepted
  rcases guarded with ⟨_, _, _, _, _, _, _, _, nonnegative, _, lower, upper⟩
  omega

namespace AddressControls

example : checkedAddress? ⟨100, 16⟩ 104 1 3 (-4) = some 108 := by decide

example : checkedAddress? ⟨100, 16⟩ 104 1 3 100 = none := by decide

example : checkedAddress? ⟨0, 16⟩ 0 9223372036854775808 1 0 = none := by decide

example : checkedAddress? ⟨0, 16⟩ 8 18446744073709551615 0 1 = none := by decide

example : checkedAddress? ⟨100, 16⟩ 104 1 3 (-112) = none := by decide

end AddressControls

end Mettapedia.Machines.TIsa
