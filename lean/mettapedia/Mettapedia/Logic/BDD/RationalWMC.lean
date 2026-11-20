import Mettapedia.Logic.BDD.WMC
import Mathlib.Data.ENNReal.Real

/-!
# Executable rational mass for ordered decision diagrams

The rational Shannon recurrence realizes the existing measure-level WMC
for independent Boolean coordinates with rational probabilities.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.RationalWMC

open scoped ENNReal

variable {n : Nat}

def count (p : Fin n → ℚ) : BDD n → ℚ
  | .zero => 0
  | .one => 1
  | .node v lo hi => (1 - p v) * count p lo + p v * count p hi

theorem nonneg (p : Fin n → ℚ) (bounds : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (f : BDD n) :
    0 ≤ count p f := by
  induction f with
  | zero => simp [count]
  | one => simp [count]
  | node v lo hi low high =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (bounds v).2) low)
      (mul_nonneg (bounds v).1 high)

theorem count_eq_wmc (p : Fin n → ℚ) (bounds : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (f : BDD n) :
    ENNReal.ofReal (count p f : ℝ) = bdd_wmc f (fun v => ENNReal.ofReal (p v : ℝ)) := by
  induction f with
  | zero => simp [count, bdd_wmc]
  | one => simp [count, bdd_wmc]
  | node v lo hi low high =>
    have p_nonneg : (0 : ℝ) ≤ (p v : ℝ) := Rat.cast_nonneg.mpr (bounds v).1
    have p_le_one : (p v : ℝ) ≤ 1 := by exact_mod_cast (bounds v).2
    have p_complement : (0 : ℝ) ≤ 1 - (p v : ℝ) := sub_nonneg.mpr p_le_one
    have low_nonneg : (0 : ℝ) ≤ (count p lo : ℝ) := Rat.cast_nonneg.mpr (nonneg p bounds lo)
    have high_nonneg : (0 : ℝ) ≤ (count p hi : ℝ) := Rat.cast_nonneg.mpr (nonneg p bounds hi)
    simp only [count, bdd_wmc, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
    rw [ENNReal.ofReal_add (mul_nonneg p_complement low_nonneg) (mul_nonneg p_nonneg high_nonneg),
      ENNReal.ofReal_mul p_complement, ENNReal.ofReal_mul p_nonneg,
      ENNReal.ofReal_sub 1 p_nonneg, ENNReal.ofReal_one, low, high]

theorem exact (p : Fin n → ℚ) (bounds : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (f : BDD n) (ordered : f.WF) :
    ENNReal.ofReal (count p f : ℝ) =
      weightedSat f.eval (fun v => ENNReal.ofReal (p v : ℝ)) := by
  rw [count_eq_wmc p bounds f, bdd_wmc_correct f ordered]
  intro v
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by exact_mod_cast (bounds v).2)

open scoped BigOperators

def assignmentMass (p : Fin n → ℚ) (world : Fin n → Bool) : ℚ :=
  ∏ i, if world i then p i else 1 - p i

def scoreMass (p : ℚ) (likelihood : Bool → ℚ) : ℚ :=
  p * likelihood true + (1 - p) * likelihood false

/-- Scoring a product law by one coordinate changes just that coordinate and
multiplies the component's mass by its evidence likelihood. -/
theorem score_coordinate (p : Fin n → ℚ) (i : Fin n) (likelihood : Bool → ℚ)
    (possible : scoreMass (p i) likelihood ≠ 0) (world : Fin n → Bool) :
    scoreMass (p i) likelihood *
      assignmentMass (Function.update p i (p i * likelihood true / scoreMass (p i) likelihood))
        world =
      assignmentMass p world * likelihood (world i) := by
  let z := scoreMass (p i) likelihood
  let high := p i * likelihood true / z
  let updated := Function.update p i high
  have split (law : Fin n → ℚ) : assignmentMass law world =
      (if world i then law i else 1 - law i) *
        ∏ j ∈ Finset.univ.erase i, if world j then law j else 1 - law j :=
    (Finset.mul_prod_erase Finset.univ (fun j => if world j then law j else 1 - law j)
      (Finset.mem_univ i)).symm
  have rest : (∏ j ∈ Finset.univ.erase i, if world j then updated j else 1 - updated j) =
      ∏ j ∈ Finset.univ.erase i, if world j then p j else 1 - p j := by
    apply Finset.prod_congr rfl
    intro j member
    simp only [updated, Function.update_of_ne (Finset.ne_of_mem_erase member)]
  have highMass : z * high = p i * likelihood true := by
    have nonzero : z ≠ 0 := possible
    dsimp only [high]
    field_simp
  have lowMass : z * (1 - high) = (1 - p i) * likelihood false := by
    rw [mul_sub, mul_one, highMass]
    dsimp [z, scoreMass]
    ring
  change z * assignmentMass updated world = assignmentMass p world * likelihood (world i)
  rw [split updated, split p, rest]
  simp only [updated, Function.update_self]
  cases world i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← mul_assoc, lowMass]
    ring
  | true =>
    simp only [↓reduceIte]
    rw [← mul_assoc, highMass]
    ring

end Mettapedia.Logic.BDDCore.RationalWMC
