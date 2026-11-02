import Mettapedia.Languages.OCaml.Primitives

/-! Arithmetic correspondence for the runtime's magnitude-based wrap.
It agrees with the independent signed-integer profile on every integer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

def magnitudeWrap (number : Int) : Int :=
  let remainder := number.natAbs % integerModulus.toNat
  let unsigned : Int := if number < 0 then
    if remainder = 0 then 0 else integerModulus - remainder
    else remainder
  if unsigned < integerHalf then unsigned else unsigned - integerModulus

theorem magnitude_unsigned (number : Int) :
    (if number < 0 then
      if number.natAbs % integerModulus.toNat = 0 then 0
      else integerModulus - (number.natAbs % integerModulus.toNat : Nat)
      else (number.natAbs % integerModulus.toNat : Nat)) = number % integerModulus := by
  have modulusPositive : 0 < integerModulus := by norm_num [integerModulus]
  cases number with
  | ofNat value => simp [integerModulus, Int.natCast_emod]
  | negSucc value =>
    have negative : Int.negSucc value < 0 := by omega
    simp only [negative, if_true, Int.natAbs_negSucc]
    have castRemainder : ((value + 1) % integerModulus.toNat : Nat) =
        ((value + 1 : Nat) : Int) % integerModulus := by norm_num [integerModulus, Int.natCast_emod]
    rw [Int.negSucc_eq, Int.neg_emod]
    by_cases zero : (value + 1) % integerModulus.toNat = 0
    · have divides : integerModulus ∣ ((value + 1 : Nat) : Int) := by
        apply Int.dvd_of_emod_eq_zero
        rw [← castRemainder, zero]
        rfl
      have divides' : integerModulus ∣ (value : Int) + 1 := by simpa using divides
      simp only [zero, if_true, divides']
    · have notDivides : ¬ integerModulus ∣ ((value + 1 : Nat) : Int) := by
        intro divides
        have empty := Int.emod_eq_zero_of_dvd divides
        rw [← castRemainder] at empty
        exact zero (by exact_mod_cast empty)
      have notDivides' : ¬ integerModulus ∣ (value : Int) + 1 := by simpa using notDivides
      simp only [zero, if_false, notDivides']
      rw [castRemainder]
      norm_num [integerModulus]

theorem magnitudeWrap_eq_wrapInteger (number : Int) : magnitudeWrap number = wrapInteger number := by
  have modulusPositive : 0 < integerModulus := by norm_num [integerModulus]
  have halfPositive : 0 < integerHalf := by norm_num [integerHalf]
  have double : integerModulus = integerHalf + integerHalf := by norm_num [integerModulus, integerHalf]
  have low := Int.emod_nonneg number (ne_of_gt modulusPositive)
  have high := Int.emod_lt_of_pos number modulusPositive
  unfold magnitudeWrap
  dsimp only
  rw [magnitude_unsigned]
  unfold wrapInteger
  rw [Int.add_emod, Int.emod_eq_of_lt (by omega : 0 ≤ integerHalf) (by omega : integerHalf < integerModulus)]
  by_cases lower : number % integerModulus < integerHalf
  · have reduced : (number % integerModulus + integerHalf) % integerModulus = number % integerModulus + integerHalf :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [if_pos lower, reduced]
    omega
  · rw [if_neg lower]
    have shifted : (number % integerModulus + integerHalf) % integerModulus =
        number % integerModulus + integerHalf - integerModulus := by
      have lowShift : 0 ≤ number % integerModulus + integerHalf - integerModulus := by omega
      have highShift : number % integerModulus + integerHalf - integerModulus < integerModulus := by omega
      have moved : (number % integerModulus + integerHalf) % integerModulus =
          (number % integerModulus + integerHalf - integerModulus) % integerModulus := by
        rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
      rw [moved, Int.emod_eq_of_lt lowShift highShift]
    rw [shifted]
    omega

example : magnitudeWrap (2 ^ 62) = -(2 ^ 62) := by decide +kernel
example : magnitudeWrap (-1) = -1 := by decide +kernel
example : magnitudeWrap 0 = 0 := by decide +kernel

#print axioms magnitudeWrap_eq_wrapInteger

end Mettapedia.Languages.OCaml
