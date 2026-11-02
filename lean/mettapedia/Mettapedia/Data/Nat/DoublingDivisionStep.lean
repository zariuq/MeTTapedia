import Mettapedia.Data.Nat.DoublingDivision

/-! Recovering one quotient bit from division by a doubled divisor.
The equations characterize the original quotient and remainder uniquely.
-/

set_option autoImplicit false

namespace Mettapedia.Data.Nat.DoublingDivision

theorem result_small (number divisor : Nat) (positive : 0 < divisor) (small : number < divisor) :
    run number divisor = (0, number) := by
  rw [run.eq_def]
  simp only [positive, small, dite_true]

theorem result_growing (number divisor : Nat) (positive : 0 < divisor) (large : divisor ≤ number) :
    run number divisor =
      if (run number (divisor + divisor)).2 < divisor then
        ((run number (divisor + divisor)).1 + (run number (divisor + divisor)).1, (run number (divisor + divisor)).2)
      else ((run number (divisor + divisor)).1 + (run number (divisor + divisor)).1 + 1,
        (run number (divisor + divisor)).2 - divisor) := by
  rw [run.eq_def]
  simp only [positive, Nat.not_lt.mpr large, dite_true, dite_false]

theorem quotient_recovery (number divisor : Nat) (positive : 0 < divisor) :
    (number / (divisor + divisor) + number / (divisor + divisor) +
      if number % (divisor + divisor) < divisor then 0 else 1,
      if number % (divisor + divisor) < divisor then number % (divisor + divisor)
      else number % (divisor + divisor) - divisor) = (number / divisor, number % divisor) := by
  have equation := Nat.mod_add_div number (divisor + divisor)
  have bounded := Nat.mod_lt number (show 0 < divisor + divisor by omega)
  have unique (quotient remainder : Nat) (same : number = divisor * quotient + remainder) (small : remainder < divisor) :
      (quotient, remainder) = (number / divisor, number % divisor) := by
    have div : number / divisor = quotient := by
      conv_lhs => rw [same]
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt small, Nat.zero_add]
    have mod : number % divisor = remainder := by
      conv_lhs => rw [same]
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt small]
    exact Prod.ext div.symm mod.symm
  split
  · rename_i small
    simp only [Nat.add_zero]
    apply unique
    · nlinarith [equation]
    · exact small
  · rename_i large
    apply unique
    · have lower : divisor ≤ number % (divisor + divisor) := by omega
      nlinarith [Nat.sub_add_cancel lower]
    · omega

#print axioms quotient_recovery

end Mettapedia.Data.Nat.DoublingDivision
