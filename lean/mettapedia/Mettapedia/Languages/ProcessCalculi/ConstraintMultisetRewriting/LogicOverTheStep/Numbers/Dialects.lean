import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.CanonicalStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.FastPaths

/-!
# What the laws determine for the dialects

The laws: **value** (every admitted observer of a number factors through its value), **coherence**
(a term means the same wherever a silent conversion is inserted), **licence** (a path that reads
storage answers what the value operation answers, or hands over), **no cliffs** (no fixed width is
a boundary of meaning). This module collects, for the measured behaviours of hyperon-experimental,
the theorems that decide which law each meets or breaks (`verdicts`), states the cliff at the
64-bit width against the licensed composite, which has none (`no_cliffs`), and proves the one place
where two behaviours meet every law and differ: **the quotient and remainder of whole numbers**.

## Two lawful quotients, and the principle that chooses

HE truncates toward zero (`(/ -7 2)` is `-3`, `(% -7 2)` is `-1`, `(% 7 -2)` is `1`); CeTTa's `he`
lane and PeTTa floor the remainder (`(% -7 2)` is `1`, `(% 7 -2)` is `-1`). As named operations on
whole values both meet every law: each commutes with the conversion from naturals to whole numbers
(`truncated_commutes`, `floored_commutes`). They differ on negative arguments
(`quotients_differ`), and each keeps a symmetry the other breaks:

* truncation is **odd**: `(-a) ÷ b = -(a ÷ b)` (`truncated_odd`); flooring is not (`floored_not_odd`);
* flooring is **periodic**: shifting the dividend by `k` divisors shifts the quotient by `k` and keeps
  the remainder (`floored_periodic`, `floored_remainder_periodic`); truncation is not
  (`truncated_not_periodic`).

So the principle that would choose is which symmetry a remainder must keep: periodicity (the
remainder is a function of the residue class, as modular arithmetic, hashing and bucketing need) or
oddness (the quotient commutes with negation). No law of this lane decides it; both may be offered
under two names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Dialects

open Distinctions.ObserverConcepts Distinctions.NumberLens Tower
open DialectsAsStrategies.TriangleFootprints.GroundedTables (measuredOutcome)
open Mettapedia.Languages.MeTTa.HE (Bindings)

/-! ## Two lawful quotients -/

/-- **Truncation commutes with the conversion from naturals to whole numbers.** -/
theorem truncated_commutes (m n : ℕ) :
    ((m / n : ℕ) : ℤ) = Int.tdiv m n ∧ ((m % n : ℕ) : ℤ) = Int.tmod m n :=
  ⟨Int.ofNat_tdiv m n, Int.ofNat_tmod m n⟩

/-- **So does flooring.** -/
theorem floored_commutes (m n : ℕ) :
    ((m / n : ℕ) : ℤ) = Int.fdiv m n ∧ ((m % n : ℕ) : ℤ) = Int.fmod m n :=
  ⟨Int.ofNat_fdiv m n, Int.ofNat_fmod m n⟩

/-- **They differ on negative arguments**, as measured: `-7` and `2`, and `7` and `-2`. -/
theorem quotients_differ :
    Int.tdiv (-7) 2 = -3 ∧ Int.fdiv (-7) 2 = -4 ∧ Int.tmod (-7) 2 = -1 ∧ Int.fmod (-7) 2 = 1 ∧
      Int.tmod 7 (-2) = 1 ∧ Int.fmod 7 (-2) = -1 := by
  decide

/-- **Truncation is odd.** -/
theorem truncated_odd (a b : ℤ) : Int.tdiv (-a) b = -Int.tdiv a b := Int.neg_tdiv a b

/-- **Flooring is not**: `-1` and `2`. -/
theorem floored_not_odd : Int.fdiv (-1) 2 ≠ -Int.fdiv 1 2 := by decide

/-- **Flooring is periodic**: shifting the dividend by `k` divisors shifts the quotient by `k`. -/
theorem floored_periodic (a k : ℤ) {b : ℤ} (nonzero : b ≠ 0) :
    Int.fdiv (a + k * b) b = Int.fdiv a b + k :=
  Int.add_mul_fdiv_right a k nonzero

/-- **And keeps the remainder.** -/
theorem floored_remainder_periodic (a k b : ℤ) : Int.fmod (a + k * b) b = Int.fmod a b :=
  Int.add_mul_fmod_self_right a k b

/-- **Truncation does not keep the remainder**: `-1` and `-1 + 2` leave `-1` and `1`. -/
theorem truncated_remainder_not_periodic : Int.tmod (-1 + 1 * 2) 2 ≠ Int.tmod (-1) 2 := by decide

/-- **Truncation is not periodic**: `-1 + 2` divided by `2` is `0`, not `(-1) ÷ 2 + 1 = 1`. -/
theorem truncated_not_periodic : Int.tdiv (-1 + 1 * 2) 2 ≠ Int.tdiv (-1) 2 + 1 := by decide

/-! ## No cliffs -/

/-- **No cliffs**: HE's measured `+` answers at the 64-bit width and errs one step above it; the
licensed composite answers the sum of every two stored integers, inside its region or not. -/
theorem no_cliffs :
    (measuredOutcome (.symbol "+") [.grounded (.int 9223372036854775806), .grounded (.int 1)] =
        .ok [(.grounded (.int 9223372036854775807), Bindings.empty)] ∧
      measuredOutcome (.symbol "+") [.grounded (.int 9223372036854775807), .grounded (.int 1)] =
        .runtimeError "IntegerOverflow") ∧
    ∀ m n : ℤ, value (FastPaths.withFasts (· + ·) [FastPaths.add64] (.int m) (.int n)) =
      (m : ℚ) + (n : ℚ) := by
  refine ⟨⟨?_, ?_⟩, fun m n => ?_⟩
  · have below := ((FastPaths.measured_add 9223372036854775806 1).1 (by decide)).1
    rw [show (9223372036854775806 : ℤ) + 1 = 9223372036854775807 by norm_num] at below
    exact below
  · exact (FastPaths.measured_add 9223372036854775807 1).2.1 (by decide)
  · rw [FastPaths.withFasts_value (FastPaths.singleton_licensed FastPaths.add64_licensed)]
    rfl

/-! ## The verdicts -/

/-- **The verdicts on the measured behaviours**, each a theorem of this lane or of the number lens:

1. storage-dependent `/` (`(/ 5 2)` is `2`, `(/ 5.0 2)` is `2.5`) breaks the value law and
   coherence; exact division and the named quotient meet both, and the named tower is coherent;
2. truncated subtraction at the naturals breaks coherence (HE has no such type: `(- 1 2)` is `-1`);
3. an error outside the 64-bit region (`(* 4611686018427387904 2)` an error, the float product a
   number) and wrapping both break the value law; the licensed composite respects it;
4. a decimal literal of a finite representable type cannot be read through a silent conversion
   from the whole numbers: some two different whole numbers become equal;
5. on the step, a table whose operations respect the value lens leaves every answer unchanged by
   re-storing, and the storage-dependent division has a one-row program whose answer depends on
   storage (measured: `(= (r) (/ 5 2))` gives `(== (r) 2)` `True`, `(= (r) (/ 5.0 2))` gives
   `False`). -/
theorem verdicts :
    (¬ Respects (pairRead valueLens divisorLens) valueLens storedQuotient ∧
      ¬ (Coherence.tower false true).Coherent ∧
      Respects (pairRead valueLens divisorLens) valueLens exactQuotient ∧
      Respects wholeLens valueLens quot ∧ Coherence.named.Coherent) ∧
    ¬ (Coherence.tower true false).Coherent ∧
    (¬ Respects (pairRead valueLens valueLens) FastPaths.outcomeLens
        (fun x : Stored × Stored => FastPaths.checkedMul x.1 x.2) ∧
      ¬ Respects (pairRead valueLens valueLens) valueLens
        (fun x : Stored × Stored => FastPaths.wrapMul x.1 x.2) ∧
      Respects (pairRead valueLens valueLens) valueLens
        (fun x : Stored × Stored => FastPaths.withFasts (· * ·) [FastPaths.mul64] x.1 x.2)) ∧
    (∀ (F : Finset ℚ) (round : ℤ → F), ∃ m n : ℤ, m ≠ n ∧ round m = round n) ∧
    (OnTheStep.TableRespects OnTheStep.exactTable ∧
      ¬ OnTheStep.TableRespects OnTheStep.storedDivTable ∧
      ¬ OnTheStep.Answer OnTheStep.storedDivTable
        (fun _ => .op .divide (.num five) (.num two.1)) OnTheStep.oneRow
        (.count (.op .divide (.num fiveFrac) (.num two.1)) 1)) :=
  ⟨⟨storedQuotient_not_respects, Coherence.storageDiv_incoherent, exactQuotient_respects,
      quot_respects, Coherence.named_coherent⟩,
    Coherence.truncated_incoherent,
    ⟨FastPaths.checkedMul_not_respects, FastPaths.wrapMul_not_respects,
      FastPaths.withFasts_respects (FastPaths.singleton_licensed FastPaths.mul64_licensed)⟩,
    Coherence.rounding_merges,
    ⟨OnTheStep.exactTable_respects, OnTheStep.storedDivTable_not_respects,
      OnTheStep.division_one_row.2⟩⟩

#print axioms truncated_commutes
#print axioms floored_commutes
#print axioms quotients_differ
#print axioms truncated_odd
#print axioms floored_not_odd
#print axioms floored_periodic
#print axioms floored_remainder_periodic
#print axioms truncated_not_periodic
#print axioms truncated_remainder_not_periodic
#print axioms no_cliffs
#print axioms verdicts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Dialects
