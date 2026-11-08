import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Charge

/-!
# A Noether theorem for the step, after Baez and Fong

Baez and Fong ("A Noether theorem for Markov processes", J. Math. Phys. 54, 013301, 2013) prove: for an
infinitesimal stochastic generator `H` and a diagonal observable `O`, the commutator `[O, H]` vanishes
exactly when the expected values of `O` and of `O²` are conserved by the master equation. This module
proves the finite-state form and reads it on the step.

* **Infinitesimal stochastic generators** (`InfinitesimalStochastic`): off-diagonal entries are
  nonnegative and every column sums to zero.
* **The theorem** (`baez_fong`): `diagonal O * H = H * diagonal O` exactly when, at every probability
  distribution, the rates of change of the expectations of `O` and of `O²` vanish. Hence the variance is
  conserved too.
* **Commuting means constant along transitions** (`commute_iff_constant`): a diagonal observable
  commutes with any generator exactly when it is equal at the two ends of every transition of nonzero
  rate.
* **On the step** (`zeroFlux_iff`, `step_noether`): a potential is a conserved charge with zero fluxes
  exactly when every admitted firing keeps it. For a finite step and any generator whose transitions
  between distinct states are exactly the step's firings, a potential commutes with the generator
  exactly when it is such a charge. This derives a conserved charge from a symmetry of the generator in
  the paper's sense, and only that sense: the symmetry is a diagonal observable commuting with the
  generator.

## Controls

* **A symmetry without a charge** (`symmetry_without_charge`): on the two-state generator
  `H = [[-1, 1], [1, -1]]` the exchange of the two states commutes with `H`, and a diagonal observable
  `diag(a, b)` commutes with `H` only when `a = b` (`twoState_commute_iff`). A permutation symmetry
  yields no nonconstant conserved charge.
* **The mean alone is not enough** (`mean_not_enough`): on three states, with the middle state jumping
  to either neighbour, the observable `(0, 1, 2)` has conserved expectation, does not have conserved
  second moment, and does not commute with the generator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Matrix

universe uO uT uH uOcc uS uF uA uI

section Markov

variable {ι : Type uS} [Fintype ι] [DecidableEq ι]

/-- **An infinitesimal stochastic matrix**: nonnegative off the diagonal, columns summing to zero. -/
structure InfinitesimalStochastic (H : Matrix ι ι ℝ) : Prop where
  nonneg : ∀ i j, i ≠ j → 0 ≤ H i j
  column : ∀ j, ∑ i, H i j = 0

/-- A probability distribution on the states. -/
def IsDistribution (ψ : ι → ℝ) : Prop := (∀ i, 0 ≤ ψ i) ∧ ∑ i, ψ i = 1

/-- **The expectation of a diagonal observable is conserved by the generator**: its rate of change
vanishes at every probability distribution. -/
def ConservesMean (H : Matrix ι ι ℝ) (O : ι → ℝ) : Prop :=
  ∀ ψ : ι → ℝ, IsDistribution ψ → ∑ i, O i * (H *ᵥ ψ) i = 0

theorem commute_iff_entries (H : Matrix ι ι ℝ) (O : ι → ℝ) :
    diagonal O * H = H * diagonal O ↔ ∀ i j, O i * H i j = H i j * O j := by
  constructor
  · intro commute i j
    have entry := congrFun (congrFun commute i) j
    rwa [diagonal_mul, mul_diagonal] at entry
  · intro entries
    ext i j
    rw [diagonal_mul, mul_diagonal, entries i j]

/-- **Conservation of the mean is a condition on columns.** -/
theorem conservesMean_iff_column (H : Matrix ι ι ℝ) (O : ι → ℝ) :
    ConservesMean H O ↔ ∀ j, ∑ i, O i * H i j = 0 := by
  constructor
  · intro conserves j
    have at_j := conserves (Pi.single j 1)
      ⟨fun i => by by_cases same : i = j <;> simp [same], by simp⟩
    simpa [mulVec, dotProduct, Pi.single_apply] using at_j
  · rintro columns ψ -
    calc ∑ i, O i * (H *ᵥ ψ) i = ∑ i, ∑ j, O i * H i j * ψ j := by
          simp only [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      _ = ∑ j, (∑ i, O i * H i j) * ψ j := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ = 0 := by simp [columns]

/-- **Commuting means constant along transitions of nonzero rate.** -/
theorem commute_iff_constant (H : Matrix ι ι ℝ) (O : ι → ℝ) :
    diagonal O * H = H * diagonal O ↔ ∀ i j, H i j ≠ 0 → O i = O j := by
  rw [commute_iff_entries]
  constructor
  · intro entries i j nonzero
    have vanishes : (O i - O j) * H i j = 0 := by
      rw [sub_mul, entries i j]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp vanishes).resolve_right nonzero)
  · intro constant i j
    by_cases zero : H i j = 0
    · rw [zero]
      ring
    · rw [constant i j zero]
      ring

/-- **Baez–Fong**: a diagonal observable commutes with an infinitesimal stochastic generator exactly
when the expectations of the observable and of its square are conserved. -/
theorem baez_fong {H : Matrix ι ι ℝ} (stochastic : InfinitesimalStochastic H) (O : ι → ℝ) :
    diagonal O * H = H * diagonal O ↔ ConservesMean H O ∧ ConservesMean H fun i => O i ^ 2 := by
  rw [commute_iff_entries, conservesMean_iff_column, conservesMean_iff_column]
  constructor
  · intro entries
    have squared : ∀ i j, O i ^ 2 * H i j = H i j * O j ^ 2 := fun i j => by
      calc O i ^ 2 * H i j = O i * (O i * H i j) := by ring
        _ = O i * (H i j * O j) := by rw [entries i j]
        _ = O j * (O i * H i j) := by ring
        _ = O j * (H i j * O j) := by rw [entries i j]
        _ = H i j * O j ^ 2 := by ring
    refine ⟨fun j => ?_, fun j => ?_⟩
    · calc ∑ i, O i * H i j = ∑ i, H i j * O j := Finset.sum_congr rfl fun i _ => entries i j
        _ = (∑ i, H i j) * O j := (Finset.sum_mul ..).symm
        _ = 0 := by rw [stochastic.column j, zero_mul]
    · calc ∑ i, O i ^ 2 * H i j = ∑ i, H i j * O j ^ 2 := Finset.sum_congr rfl fun i _ => squared i j
        _ = (∑ i, H i j) * O j ^ 2 := (Finset.sum_mul ..).symm
        _ = 0 := by rw [stochastic.column j, zero_mul]
  · rintro ⟨first, second⟩ i j
    have expand : ∀ k, (O k - O j) ^ 2 * H k j = O k ^ 2 * H k j - 2 * O j * (O k * H k j) + O j ^ 2 * H k j :=
      fun k => by ring
    have total : ∑ k, (O k - O j) ^ 2 * H k j = 0 := by
      rw [Finset.sum_congr rfl fun k _ => expand k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, first j, stochastic.column j]
      have squares : ∑ k, O k ^ 2 * H k j = 0 := second j
      rw [squares]
      ring
    have nonneg : ∀ k ∈ Finset.univ, 0 ≤ (O k - O j) ^ 2 * H k j := fun k _ => by
      by_cases same : k = j
      · subst same
        simp
      · exact mul_nonneg (sq_nonneg _) (stochastic.nonneg k j same)
    have each := (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp total i (Finset.mem_univ i)
    rcases mul_eq_zero.mp each with zero | zero
    · have equal : O i = O j := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp zero)
      rw [equal]
      ring
    · rw [zero]
      ring

end Markov

/-! ## On the step -/

section Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **Zero-flux charges are the potentials every admitted firing keeps.** -/
theorem zeroFlux_iff {A : Type uA} [AddCommMonoid A] (P : Step X O State Firing) (V : State → A) :
    (∃ Q : ConservedCharge P A, Q.potential = V ∧ (∀ s f, Q.taken s f = 0) ∧ ∀ s f, Q.made s f = 0) ↔
      ∀ {s : State} (f : Firing s) (admitted : P.Admits f), V (P.result f admitted) = V s := by
  constructor
  · rintro ⟨Q, rfl, taken, made⟩ s f admitted
    have balance := Q.balance f admitted
    rwa [taken, made, add_zero, add_zero] at balance
  · intro kept
    exact ⟨⟨V, fun _ _ => 0, fun _ _ => 0, fun f admitted => by rw [add_zero, add_zero, kept f admitted]⟩,
      rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **A Noether theorem for the step.** For a finite step and a generator whose transitions between
distinct states are exactly the step's firings, a potential commutes with the generator exactly when
every admitted firing keeps it, that is, when it is a conserved charge with zero fluxes. -/
theorem step_noether [Fintype State] [DecidableEq State] (P : Step X O State Firing)
    (H : Matrix State State ℝ)
    (transitions : ∀ i j, i ≠ j → (H i j ≠ 0 ↔ ∃ (f : Firing j) (admitted : P.Admits f), P.result f admitted = i))
    (V : State → ℝ) :
    diagonal V * H = H * diagonal V ↔
      ∀ {s : State} (f : Firing s) (admitted : P.Admits f), V (P.result f admitted) = V s := by
  rw [commute_iff_constant]
  constructor
  · intro constant s f admitted
    by_cases same : P.result f admitted = s
    · rw [same]
    · exact constant _ _ ((transitions _ _ same).mpr ⟨f, admitted, rfl⟩)
  · intro kept i j nonzero
    by_cases same : i = j
    · rw [same]
    · obtain ⟨f, admitted, rfl⟩ := (transitions i j same).mp nonzero
      exact kept f admitted

end Step

/-! ## Controls -/

namespace NoetherControls

/-- The two-state generator `[[-1, 1], [1, -1]]`. -/
def twoState : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => if i = j then -1 else 1

/-- The exchange of the two states. -/
def exchange : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => if i = j then 0 else 1

theorem twoState_stochastic : InfinitesimalStochastic twoState :=
  ⟨fun i j different => by simp [twoState, different],
    fun j => by fin_cases j <;> simp [twoState, Fin.sum_univ_two]⟩

/-- The exchange commutes with the generator. -/
theorem exchange_commutes : exchange * twoState = twoState * exchange := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exchange, twoState, Matrix.mul_apply, Fin.sum_univ_two]

/-- **A diagonal observable commutes with the two-state generator only when it is constant.** -/
theorem twoState_commute_iff (a b : ℝ) :
    diagonal ![a, b] * twoState = twoState * diagonal ![a, b] ↔ a = b := by
  rw [commute_iff_constant]
  constructor
  · intro constant
    simpa using constant 0 1 (by simp [twoState])
  · rintro rfl i j _
    fin_cases i <;> fin_cases j <;> rfl

/-- **A symmetry without a charge**: the exchange commutes with the generator, and every observable
whose expectation and second moment are conserved is constant. -/
theorem symmetry_without_charge :
    exchange * twoState = twoState * exchange ∧ exchange ≠ 1 ∧
      ∀ O : Fin 2 → ℝ, ConservesMean twoState O ∧ ConservesMean twoState (fun i => O i ^ 2) → O 0 = O 1 := by
  refine ⟨exchange_commutes, fun same => ?_, fun O conserved => ?_⟩
  · have entry := congrFun (congrFun same 0) 0
    simp [exchange] at entry
  · exact (commute_iff_constant twoState O).mp ((baez_fong twoState_stochastic O).mpr conserved) 0 1
      (by simp [twoState])

/-- Three states; the middle one jumps to either neighbour at rate one. -/
def spread : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => if j = 1 then (if i = 1 then -2 else 1) else 0

/-- The position observable `(0, 1, 2)`. -/
def position : Fin 3 → ℝ := ![0, 1, 2]

theorem spread_stochastic : InfinitesimalStochastic spread :=
  ⟨fun i j different => by
      fin_cases i <;> fin_cases j <;> simp_all [spread],
    fun j => by fin_cases j <;> norm_num [spread, Fin.sum_univ_three, Fin.ext_iff]⟩

/-- **The mean alone is not enough**: the position has conserved expectation, does not have conserved
second moment, and does not commute with the generator. -/
theorem mean_not_enough :
    ConservesMean spread position ∧ ¬ ConservesMean spread (fun i => position i ^ 2) ∧
      ¬ diagonal position * spread = spread * diagonal position := by
  refine ⟨(conservesMean_iff_column _ _).mpr fun j => ?_, fun conserved => ?_, fun commute => ?_⟩
  · fin_cases j <;> simp [spread, position, Fin.sum_univ_three]
  · have middle := (conservesMean_iff_column _ _).mp conserved 1
    simp [spread, position, Fin.sum_univ_three] at middle
    norm_num at middle
  · have equal := (commute_iff_constant spread position).mp commute 0 1 (by simp [spread])
    simp [position] at equal

end NoetherControls

#print axioms commute_iff_entries
#print axioms conservesMean_iff_column
#print axioms commute_iff_constant
#print axioms baez_fong
#print axioms zeroFlux_iff
#print axioms step_noether
#print axioms NoetherControls.twoState_stochastic
#print axioms NoetherControls.exchange_commutes
#print axioms NoetherControls.twoState_commute_iff
#print axioms NoetherControls.symmetry_without_charge
#print axioms NoetherControls.spread_stochastic
#print axioms NoetherControls.mean_not_enough

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
