import Mettapedia.GSLT.LanguageDef.WaltersZantemaDAMultiplication
import Mettapedia.GSLT.LanguageDef.PeanoExactArithmeticAddBridge

/-!
# Peano, radix, and native addition triangle

The three presentations below are independently authored:

* the two closed Peano clauses;
* the finite Walters--Zantema DA rewrite system at any radix;
* the exact-integer primitive restricted to natural inputs.

Their complete addition graphs coincide.  This is deliberately stronger than
agreement on selected examples or operation names.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

open Mettapedia.GSLT.LanguageDef.PeanoExactArithmeticAddBridge
open Mettapedia.GSLT.LanguageDef.PeanoAddSpecialization

/-- Closed radix rewriting and closed Peano rewriting define the same complete
addition graph. -/
theorem encoded_addition_iff_peanoAdd
    (schema : Schema) (first second result : Nat) :
    MultiStep schema
        (.add (encodeTerm schema first) (encodeTerm schema second))
        (encodeTerm schema result) ↔
      AddRel Symbol.zero Symbol.successor
        (numeral first) (numeral second) (numeral result) := by
  rw [encoded_addition_graph, peanoAdd_iff]

/-- Closed radix rewriting and the explicit exact-integer primitive contract
define the same complete natural-number addition graph. -/
theorem encoded_addition_iff_nativeNatAdd
    (schema : Schema) (first second result : Nat) :
    MultiStep schema
        (.add (encodeTerm schema first) (encodeTerm schema second))
        (encodeTerm schema result) ↔
      NativeNatAdd first second result := by
  rw [encoded_addition_graph, nativeNatAdd_iff]

/-- The specialized Peano evaluator also has exactly the DA addition graph. -/
theorem encoded_addition_iff_specializedPeanoAdd
    (schema : Schema) (first second result : Nat) :
    MultiStep schema
        (.add (encodeTerm schema first) (encodeTerm schema second))
        (encodeTerm schema result) ↔
      evaluate? additionPlan (numeral first) (numeral second) =
        some (numeral result) := by
  rw [encoded_addition_iff_nativeNatAdd,
    specializedPeanoAdd_iff_nativeNatAdd]

/-- Positive cross-presentation calibration. -/
theorem radixTwo_peano_native_two_plus_three :
    MultiStep radixTwo
        (.add (encodeTerm radixTwo 2) (encodeTerm radixTwo 3))
        (encodeTerm radixTwo 5) ∧
      AddRel Symbol.zero Symbol.successor
        (numeral 2) (numeral 3) (numeral 5) ∧
      NativeNatAdd 2 3 5 := by
  exact ⟨(encoded_addition_graph radixTwo 2 3 5).2 rfl,
    (peanoAdd_iff 2 3 5).2 rfl,
    (nativeNatAdd_iff 2 3 5).2 rfl⟩

/-- Negative cross-presentation calibration: none of the three models may
invent six as the result of two plus three. -/
theorem radixTwo_peano_native_two_plus_three_not_six :
    ¬ MultiStep radixTwo
        (.add (encodeTerm radixTwo 2) (encodeTerm radixTwo 3))
        (encodeTerm radixTwo 6) ∧
      ¬ AddRel Symbol.zero Symbol.successor
        (numeral 2) (numeral 3) (numeral 6) ∧
      ¬ NativeNatAdd 2 3 6 := by
  constructor
  · intro invented
    have impossible := (encoded_addition_graph radixTwo 2 3 6).1 invented
    omega
  constructor
  · intro invented
    have impossible := (peanoAdd_iff 2 3 6).1 invented
    omega
  · intro invented
    have impossible := (nativeNatAdd_iff 2 3 6).1 invented
    omega

#print axioms encoded_addition_iff_peanoAdd
#print axioms encoded_addition_iff_nativeNatAdd
#print axioms encoded_addition_iff_specializedPeanoAdd
#print axioms radixTwo_peano_native_two_plus_three_not_six

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
