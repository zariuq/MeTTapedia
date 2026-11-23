import Mettapedia.GSLT.LanguageDef.ArithmeticExtension

/-!
# Exact integer division in the math library

The six public integer operations select a quotient or remainder from one
of three conventions. A backend presented with both projections of the same
operands can share the division. Applicability depends on the integer domain,
the convention, and the nonzero divisor. The reference uses Lean's three
division laws; the realization starts with one Euclidean quotient, recovers
its remainder by multiplication and subtraction, and adjusts the pair.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerDivisionLibrary

open ArithmeticExtension.ExactInteger (CoreOp)

inductive Convention where
  | truncation
  | euclidean
  | floor
  deriving DecidableEq

def Convention.reference (convention : Convention) (a b : Int) : Int × Int :=
  match convention with
  | .truncation => (CoreOp.tquot.fn a b, CoreOp.trem.fn a b)
  | .euclidean => (a / b, a % b)
  | .floor => (CoreOp.fquot.fn a b, CoreOp.frem.fn a b)

private def adjust (convention : Convention) (a b q r : Int) : Int × Int :=
  match convention with
  | .truncation =>
    if 0 ≤ a ∨ r = 0 then (q, r) else (q + b.sign, r - b.natAbs)
  | .euclidean => (q, r)
  | .floor =>
    if 0 ≤ b ∨ r = 0 then (q, r) else (q - 1, r + b)

/-- The zero-divisor case stays at the dialect's ordinary fault boundary. -/
def run (convention : Convention) (a b : Int) : Option (Int × Int) :=
  if b = 0 then none
  else
    let q := a / b
    some (adjust convention a b q (a - b * q))

private theorem adjust_exact (convention : Convention) (a b : Int) :
    adjust convention a b (a / b) (a % b) = convention.reference a b := by
  cases convention with
  | truncation =>
    simp only [Convention.reference, CoreOp.fn, Int.tdiv_eq_ediv, Int.tmod_eq_emod,
      Int.dvd_iff_emod_eq_zero, adjust]
    split <;> simp_all
  | euclidean => rfl
  | floor =>
    simp only [Convention.reference, CoreOp.fn, Int.fdiv_eq_ediv, Int.fmod_eq_emod,
      Int.dvd_iff_emod_eq_zero, adjust]
    split <;> simp_all

theorem run_exact (convention : Convention) (a b : Int) :
    run convention a b = if b = 0 then none else some (convention.reference a b) := by
  simp only [run, ← Int.emod_def, adjust_exact]

/-- All three admitted pairs obey the same recomposition law. -/
theorem recomposes (convention : Convention) (a b q r : Int)
    (computed : run convention a b = some (q, r)) : b * q + r = a := by
  rw [run_exact] at computed
  split at computed
  · contradiction
  · injection computed with values
    cases convention <;> cases values
    · exact Int.mul_tdiv_add_tmod a b
    · exact Int.mul_ediv_add_emod a b
    · exact Int.mul_fdiv_add_fmod a b

/-- The signed corrections after CeTTa's machine-integer division.
`q` and `r` are the quotient and remainder from truncating division. -/
def fromTruncation (convention : Convention) (b q r : Int) : Int × Int :=
  match convention with
  | .truncation => (q, r)
  | .euclidean =>
    if r < 0 then
      if 0 < b then (q - 1, r + b) else (q + 1, r - b)
    else (q, r)
  | .floor =>
    if r != 0 && (decide (r < 0) != decide (b < 0)) then (q - 1, r + b) else (q, r)

/-- The signed corrections implement both projections on exact integers.
The signed-word representation and its overflow guards are separate from
this arithmetic law. -/
theorem fromTruncation_exact (convention : Convention) (a b : Int) (defined : b ≠ 0) :
    fromTruncation convention b (a.tdiv b) (a.tmod b) = convention.reference a b := by
  have lo := Int.emod_nonneg a defined
  have hi := Int.emod_lt a defined
  cases convention
  · rfl
  all_goals
    simp only [fromTruncation, Convention.reference, CoreOp.fn, Int.tdiv_eq_ediv,
      Int.tmod_eq_emod, Int.fdiv_eq_ediv, Int.fmod_eq_emod, Int.dvd_iff_emod_eq_zero]
    by_cases negative : b < 0
    · have sign := Int.sign_eq_neg_one_of_neg negative
      have magnitude : (b.natAbs : Int) = -b := by omega
      have nonpositive : ¬0 < b := by omega
      have nonnegative : ¬0 ≤ b := by omega
      have below : a % b + b < 0 := by omega
      by_cases dividend : 0 ≤ a <;> by_cases divisible : a % b = 0 <;>
        simp [sign, magnitude, negative, nonpositive, nonnegative, dividend, divisible,
          Int.not_lt_of_ge lo, below]
      all_goals omega
    · have positive : 0 < b := by omega
      have nonnegative : 0 ≤ b := by omega
      have sign := Int.sign_eq_one_of_pos positive
      have magnitude : (b.natAbs : Int) = b := by omega
      have below : a % b - b < 0 := by omega
      by_cases dividend : 0 ≤ a <;> by_cases divisible : a % b = 0 <;>
        simp [sign, magnitude, negative, positive, nonnegative, dividend, divisible,
          Int.not_lt_of_ge lo, below]
      all_goals omega

/-- The original MeTTa body for `math:mod` uses floor division on the
magnitude of the divisor. Interpret that dependency on exact integers. -/
def modBody (a b : Int) : Int :=
  let magnitude : Int := if b < 0 then -b else b
  a - magnitude * a.fdiv magnitude

theorem modBody_exact (a b : Int) : modBody a b = a % b := by
  unfold modBody
  by_cases negative : b < 0
  · rw [if_pos negative, ← Int.fmod_def, Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_neg]
  · rw [if_neg negative, ← Int.fmod_def, Int.fmod_eq_emod_of_nonneg _ (by omega)]

def remBody (a b : Int) : Int :=
  let r := modBody a b
  if a < 0 then if r = 0 then 0 else r - (if b < 0 then -b else b) else r

theorem remBody_exact (a b : Int) : remBody a b = a.tmod b := by
  have magnitude : (if b < 0 then -b else b) = (b.natAbs : Int) := by omega
  simp only [remBody, modBody_exact, magnitude, Int.tmod_eq_emod, Int.dvd_iff_emod_eq_zero]
  by_cases negative : a < 0 <;> by_cases exactDiv : a % b = 0 <;>
    simp [negative, exactDiv, ← Int.not_lt]

def floorModBody (a b : Int) : Int :=
  let r := modBody a b
  if b < 0 then if r = 0 then 0 else r - (if b < 0 then -b else b) else r

theorem floorModBody_exact (a b : Int) : floorModBody a b = a.fmod b := by
  simp only [floorModBody, modBody_exact, Int.fmod_eq_emod, Int.dvd_iff_emod_eq_zero]
  by_cases negative : b < 0 <;> by_cases exactDiv : a % b = 0 <;> simp_all

example :
    run .truncation (-7) (-2) = some (3, -1) ∧
    run .euclidean (-7) (-2) = some (4, 1) ∧
    run .floor (-7) (-2) = some (3, -1) := by decide

example : run .euclidean 7 (-2) ≠ run .floor 7 (-2) := by decide

example (convention : Convention) : run convention 7 0 = none := by simp [run]

#print axioms run_exact
#print axioms recomposes
#print axioms fromTruncation_exact
#print axioms modBody_exact
#print axioms remBody_exact
#print axioms floorModBody_exact

end Mettapedia.GSLT.LanguageDef.IntegerDivisionLibrary
