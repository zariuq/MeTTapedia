import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Multiplicity: redexes are selections from the bag

A redex is a choice of the copies it consumes, not a class of equal terms. With
two equal messages a receipt has two ways to fire, and the system runs at
twice the rate of one message.

On a population of messages that are born at a constant rate and each die at
rate `μ`, counting selections gives death rate `μ n` at population `n`, and the
stationary law is a truncated Poisson law. Identifying equal messages gives
death rate `μ` at every positive population, and the stationary law is a
truncated geometric law. Both are the unique stationary laws of their chains up
to normalisation, and they differ from population two on.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.Multiplicity

universe u

/-- The selections of a consumed bag from a bag: for each resource, the ways of
choosing as many of its copies as are consumed. -/
def selections {α : Type u} [DecidableEq α] (bag consumed : Multiset α) : ℕ :=
  ∏ x ∈ consumed.toFinset, (bag.count x).choose (consumed.count x)

/-- **Two equal messages give a receiver two ways to fire.** -/
theorem selections_two_equal_messages :
    selections ({true, true, false} : Multiset Bool) {true, false} = 2 := by
  decide

/-- One message gives one way. -/
theorem selections_one_message :
    selections ({true, false} : Multiset Bool) {true, false} = 1 := by
  decide

/-! ## Birth and death on a bounded population -/

/-- **Global balance** of a birth–death chain on `0, …, N`: at every state the
flow in equals the flow out. -/
def Balanced (birth death : ℕ → ℝ) (law : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ n ≤ N,
    (if n = 0 then 0 else law (n - 1) * birth (n - 1)) +
        (if n < N then law (n + 1) * death (n + 1) else 0) =
      law n * ((if n < N then birth n else 0) + death n)

/-- **Global balance is detailed balance** for a birth–death chain with no death
at zero. -/
theorem balanced_iff_detailed (birth death : ℕ → ℝ) (law : ℕ → ℝ) (N : ℕ)
    (noDeathAtZero : death 0 = 0) :
    Balanced birth death law N ↔ ∀ n < N, law n * birth n = law (n + 1) * death (n + 1) := by
  constructor
  · intro balanced n
    induction n with
    | zero =>
        intro positive
        have atZero := balanced 0 (Nat.zero_le N)
        simp only [↓reduceIte, if_pos positive, noDeathAtZero, add_zero, zero_add] at atZero
        linear_combination -atZero
    | succ n ih =>
        intro below
        have previous := ih (Nat.lt_of_succ_lt below)
        have atNext := balanced (n + 1) below.le
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, if_pos below] at atNext
        linear_combination previous - atNext
  · intro detailed n atMost
    rcases Nat.eq_zero_or_pos n with rfl | positive
    · by_cases below : 0 < N
      · have first := detailed 0 below
        simp only [↓reduceIte, if_pos below, noDeathAtZero, add_zero, zero_add]
        linear_combination -first
      · simp only [↓reduceIte, if_neg below, noDeathAtZero, add_zero, mul_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have inflow := detailed m (by omega)
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
      split_ifs with below
      · linear_combination inflow - detailed (m + 1) below
      · linear_combination inflow

/-- Births at rate `lam` below the bound. -/
def births (lam : ℝ) : ℕ → ℝ := fun _ => lam

/-- Deaths counted by selections: each of the `n` messages may die. -/
def deathsWithMultiplicity (μ : ℝ) : ℕ → ℝ := fun n => μ * n

/-- Deaths with equal messages identified: one way to die at every positive
population. -/
def deathsIdentified (μ : ℝ) : ℕ → ℝ := fun n => if n = 0 then 0 else μ

/-- The truncated Poisson weights. -/
noncomputable def poissonWeight (lam μ : ℝ) (n : ℕ) : ℝ := (lam / μ) ^ n / n.factorial

/-- The truncated geometric weights. -/
noncomputable def geometricWeight (lam μ : ℝ) (n : ℕ) : ℝ := (lam / μ) ^ n

/-- **Counting selections, the stationary law is truncated Poisson**, and it is
the only one up to normalisation. -/
theorem balanced_multiplicity_iff (lam μ : ℝ) (positive : 0 < μ) (N : ℕ) (law : ℕ → ℝ) :
    Balanced (births lam) (deathsWithMultiplicity μ) law N ↔
      ∀ n ≤ N, law n = law 0 * poissonWeight lam μ n := by
  rw [balanced_iff_detailed _ _ _ _ (by simp [deathsWithMultiplicity])]
  constructor
  · intro detailed n
    induction n with
    | zero => intro _; simp [poissonWeight]
    | succ n ih =>
        intro atMost
        have step := detailed n (by omega)
        have previous := ih (by omega)
        simp only [births, deathsWithMultiplicity] at step
        have μn : μ * ((n + 1 : ℕ) : ℝ) ≠ 0 := mul_ne_zero positive.ne' (by positivity)
        have μne : μ ≠ 0 := positive.ne'
        have next : law (n + 1) = law n * lam / (μ * ((n + 1 : ℕ) : ℝ)) :=
          (eq_div_iff μn).mpr step.symm
        have factorialPositive : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
        rw [next, previous, poissonWeight, poissonWeight, Nat.factorial_succ]
        push_cast
        simp only [div_pow]
        field_simp
        ring
  · intro closed n below
    simp only [births, deathsWithMultiplicity]
    have μne : μ ≠ 0 := positive.ne'
    have factorialPositive : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [closed n below.le, closed (n + 1) below, poissonWeight, poissonWeight, Nat.factorial_succ]
    push_cast
    simp only [div_pow]
    field_simp
    ring

/-- **Identifying equal messages, the stationary law is truncated geometric**,
and it is the only one up to normalisation. -/
theorem balanced_identified_iff (lam μ : ℝ) (positive : 0 < μ) (N : ℕ) (law : ℕ → ℝ) :
    Balanced (births lam) (deathsIdentified μ) law N ↔
      ∀ n ≤ N, law n = law 0 * geometricWeight lam μ n := by
  rw [balanced_iff_detailed _ _ _ _ (by simp [deathsIdentified])]
  constructor
  · intro detailed n
    induction n with
    | zero => intro _; simp [geometricWeight]
    | succ n ih =>
        intro atMost
        have step := detailed n (by omega)
        have previous := ih (by omega)
        simp only [births, deathsIdentified, Nat.succ_ne_zero, if_false] at step
        have μne : μ ≠ 0 := positive.ne'
        have next : law (n + 1) = law n * lam / μ := (eq_div_iff positive.ne').mpr step.symm
        rw [next, previous, geometricWeight, geometricWeight, pow_succ]
        field_simp
  · intro closed n below
    simp only [births, deathsIdentified, Nat.succ_ne_zero, if_false]
    have μne : μ ≠ 0 := positive.ne'
    rw [closed n below.le, closed (n + 1) below, geometricWeight, geometricWeight, pow_succ]
    field_simp

/-- **The two laws differ from population two on**: the ratio of the weights of
two and one is `lam / (2 μ)` with multiplicity and `lam / μ` without. -/
theorem poisson_ne_geometric (lam μ : ℝ) (birthPositive : 0 < lam) (deathPositive : 0 < μ) :
    poissonWeight lam μ 2 / poissonWeight lam μ 1 ≠
      geometricWeight lam μ 2 / geometricWeight lam μ 1 := by
  have ratio : 0 < lam / μ := div_pos birthPositive deathPositive
  have poissonRatio : poissonWeight lam μ 2 / poissonWeight lam μ 1 = lam / μ / 2 := by
    simp only [poissonWeight, Nat.factorial_two, Nat.factorial_one, Nat.cast_ofNat, Nat.cast_one,
      div_one, pow_one]
    field_simp
  have geometricRatio : geometricWeight lam μ 2 / geometricWeight lam μ 1 = lam / μ := by
    simp only [geometricWeight, pow_one]
    field_simp
  rw [poissonRatio, geometricRatio]
  intro same
  linarith

end Mettapedia.GSLT.Weighting.Multiplicity
