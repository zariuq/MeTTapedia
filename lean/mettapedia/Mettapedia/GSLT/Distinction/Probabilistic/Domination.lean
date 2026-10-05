import Mettapedia.GSLT.Distinction.Probabilistic.FiniteChains
import Mettapedia.GSLT.Distinction.BehaviouralMetric

/-!
# The probabilistic distance dominates the possibilistic distance of the support

The support erasure of a finite chain (`chainSystem`, `ProbabilisticSystem.support`)
is a possibilistic system over the same GSLT, and with the chain's observables
in `[0, 1]` it is a graded system (`supportGraded`) whose behavioural distance
is the Hausdorff fixed point of `GSLT.Distinction.BehaviouralMetric`.  The two
distances compare as follows.

* **The exact inequality** (`behaviouralDistance_le_bisimulationMetric`): if
  every transition of positive probability has probability at least `p`, the
  possibilistic distance of the support at discount `c · p` is at most the
  Kantorovich distance at discount `c`:

  `d_support^(c·p)(s, t) ≤ d_Kantorovich^(c)(s, t)`.

  A step of positive probability `μ x ≥ p` must be matched by an optimal
  coupling, and the coupling sends the mass of `x` to successors at distance at
  least the nearest one, so `p · d(x, y) ≤ cost` for some supported `y`
  (`exists_matching_successor`).  Every finite chain has such a floor
  (`exists_floor`).
* **The factor `p` cannot be dropped, the inequality is attained, and equal
  supports with different weights are at positive distance**: `Controls`.

Observables in `[0, 1]` keep the Kantorovich distance at most one
(`bisimulationMetric_le_one`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S T : Type*} [Fintype S] [Fintype T]

/-! ## A matching successor -/

/-- **A matching successor.**  A coupling sends the mass of a supported point
`x` to points it relates to `x`; one of them is at distance at most the cost
divided by the mass of `x`. -/
theorem exists_matching_successor {μ : S → ℝ} {ν : T → ℝ} (ω : Coupling μ ν) {D : S → T → ℝ}
    (nonneg : ∀ x y, 0 ≤ D x y) {x : S} (positive : μ x ≠ 0) :
    ∃ y, ω.weight x y ≠ 0 ∧ μ x * D x y ≤ ω.cost D := by
  classical
  have row : ∑ y, ω.weight x y ≠ 0 := by rw [ω.sum_right x]; exact positive
  obtain ⟨y₀, _, nonzero₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero row
  set Y := Finset.univ.filter fun y => ω.weight x y ≠ 0
  have nonempty : Y.Nonempty := ⟨y₀, by simp [Y, nonzero₀]⟩
  obtain ⟨y, member, minimal⟩ := Y.exists_min_image (D x) nonempty
  refine ⟨y, (Finset.mem_filter.mp member).2, ?_⟩
  calc μ x * D x y = ∑ y', ω.weight x y' * D x y := by rw [← Finset.sum_mul, ω.sum_right]
    _ ≤ ∑ y', ω.weight x y' * D x y' := Finset.sum_le_sum fun y' _ => by
        by_cases zero : ω.weight x y' = 0
        · rw [zero, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (minimal y' (by simp [Y, zero])) (ω.nonneg x y')
    _ ≤ ω.cost D := by
        unfold Coupling.cost
        exact Finset.single_le_sum (f := fun x' => ∑ y', ω.weight x' y' * D x' y')
          (fun x' _ => Finset.sum_nonneg fun y' _ => mul_nonneg (ω.nonneg x' y') (nonneg x' y'))
          (Finset.mem_univ x)

/-! ## The support as a graded system -/

section Graded

variable (P : LabelledMarkovChain ℝ A Atom S)

/-- Observables of a chain with values in `[0, 1]`. -/
def UnitObservables : Prop := ∀ i s, 0 ≤ P.observe i s ∧ P.observe i s ≤ 1

/-- The observables of a chain, as graded observations of its state GSLT. -/
def unitObservations (bounded : UnitObservables P) : GradedObservations (stateGSLT S) where
  Atom := Atom
  value := P.observe
  value_nonneg i s := (bounded i s).1
  value_le_one i s := (bounded i s).2
  value_resp i left right equivalent := by
    have same : left = right := equivalent
    rw [same]

/-- **The support of a chain as a graded system** at discount `d`: the support
erasure of `chainSystem` with the chain's observables. -/
noncomputable def supportGraded (bounded : UnitObservables P) (d : ℝ) (d_nonneg : 0 ≤ d)
    (d_le : d ≤ 1) : GradedSystem (stateGSLT S) where
  dynamics := (chainSystem P).support
  observations := unitObservations P bounded
  discount := d
  discount_nonneg := d_nonneg
  discount_le_one := d_le

variable {P}

theorem supportGraded_act_iff {bounded : UnitObservables P} {d : ℝ} {d_nonneg : 0 ≤ d}
    {d_le : d ≤ 1} (label : A) (source target : S) :
    (supportGraded P bounded d d_nonneg d_le).dynamics.act label source target ↔
      P.trans label source target ≠ 0 :=
  support_act_iff label source target

/-- **Every finite chain has a floor**: a positive lower bound on its positive
transition probabilities. -/
theorem exists_floor [Fintype A] :
    ∃ p, 0 < p ∧ p ≤ 1 ∧ ∀ a s x, P.trans a s x ≠ 0 → p ≤ P.trans a s x := by
  classical
  let value : A × S × S → ℝ := fun q => if P.trans q.1 q.2.1 q.2.2 ≠ 0 then P.trans q.1 q.2.1 q.2.2
    else 1
  refine ⟨Finset.univ.fold min 1 value, ?_, ?_, fun a s x positive => ?_⟩
  · rw [Finset.lt_fold_min]
    refine ⟨zero_lt_one, fun q _ => ?_⟩
    simp only [value]
    split_ifs with nonzero
    · exact lt_of_le_of_ne ((P.isDistribution q.1 q.2.1).nonneg q.2.2) (Ne.symm nonzero)
    · exact zero_lt_one
  · rw [Finset.fold_min_le]
    exact Or.inl le_rfl
  · rw [Finset.fold_min_le]
    refine Or.inr ⟨(a, s, x), Finset.mem_univ _, ?_⟩
    simp only [value, if_pos positive, le_rfl]

/-- **Observables in `[0, 1]` keep the Kantorovich distance at most one.** -/
theorem bisimulationMetric_le_one [Fintype A] [Fintype Atom] (bounded : UnitObservables P)
    {c : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s t : S) : bisimulationMetric P P c s t ≤ 1 := by
  refine (bisimulationMetric_le (couplingBound_const P P c_le) c_nonneg s t).trans ?_
  unfold observationBound
  rw [Finset.fold_max_le]
  refine ⟨zero_le_one, fun q _ => (observationDistance_le_iff P P).mpr ⟨zero_le_one, fun i => ?_⟩⟩
  rw [abs_le]
  constructor <;> linarith [(bounded i q.1).1, (bounded i q.1).2, (bounded i q.2).1,
    (bounded i q.2).2]

/-! ## The exact inequality -/

variable [Fintype A] [Fintype Atom]

/-- **The Kantorovich distance at discount `c` is a bisimulation metric of the
support at discount `c · p`**, for a floor `p` of the positive transition
probabilities. -/
theorem isBisimMetric_bisimulationMetric (bounded : UnitObservables P) {c p : ℝ}
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1)
    (floor : ∀ a s x, P.trans a s x ≠ 0 → p ≤ P.trans a s x) :
    (supportGraded P bounded (c * p) (mul_nonneg c_nonneg p_nonneg)
      (mul_le_one₀ c_le p_nonneg p_le)).IsBisimMetric (bisimulationMetric P P c) where
  nonneg := bisimulationMetric_nonneg c_nonneg c_le
  observes i s t :=
    (couplingBound_bisimulationMetric (P := P) (Q := P) c_nonneg c_le).observe_le (i : Atom) s t
  forth label left right left' step := by
    refine Or.inr fun ε ε_pos => ?_
    obtain ⟨ω, le⟩ := (couplingBound_bisimulationMetric (P := P) (Q := P) c_nonneg c_le).step_le
      label left right
    have positive : P.trans label left left' ≠ 0 := (supportGraded_act_iff label left left').mp step
    obtain ⟨y, nonzero, matched⟩ := exists_matching_successor ω
      (bisimulationMetric_nonneg (P := P) (Q := P) c_nonneg c_le) positive
    refine ⟨y, (supportGraded_act_iff label right y).mpr fun zero =>
      nonzero (ω.weight_eq_zero_of_right zero left'), ?_⟩
    have lower := floor label left left' positive
    have distance_nonneg := bisimulationMetric_nonneg (P := P) (Q := P) c_nonneg c_le left' y
    change c * p * bisimulationMetric P P c left' y ≤ bisimulationMetric P P c left right + ε
    calc c * p * bisimulationMetric P P c left' y
        ≤ c * (P.trans label left left' * bisimulationMetric P P c left' y) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right lower distance_nonneg) c_nonneg
      _ ≤ c * ω.cost (bisimulationMetric P P c) := mul_le_mul_of_nonneg_left matched c_nonneg
      _ ≤ bisimulationMetric P P c left right := le
      _ ≤ bisimulationMetric P P c left right + ε := by linarith
  back label left right right' step := by
    refine Or.inr fun ε ε_pos => ?_
    obtain ⟨ω, le⟩ := (couplingBound_bisimulationMetric (P := P) (Q := P) c_nonneg c_le).step_le
      label left right
    have positive : P.trans label right right' ≠ 0 :=
      (supportGraded_act_iff label right right').mp step
    obtain ⟨x, nonzero, matched⟩ := exists_matching_successor ω.swap
      (D := fun y x => bisimulationMetric P P c x y)
      (fun y x => bisimulationMetric_nonneg (P := P) (Q := P) c_nonneg c_le x y) positive
    rw [ω.cost_swap] at matched
    refine ⟨x, (supportGraded_act_iff label left x).mpr fun zero =>
      nonzero (ω.weight_eq_zero_of_left zero right'), ?_⟩
    have lower := floor label right right' positive
    have distance_nonneg := bisimulationMetric_nonneg (P := P) (Q := P) c_nonneg c_le x right'
    change c * p * bisimulationMetric P P c x right' ≤ bisimulationMetric P P c left right + ε
    calc c * p * bisimulationMetric P P c x right'
        ≤ c * (P.trans label right right' * bisimulationMetric P P c x right') := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right lower distance_nonneg) c_nonneg
      _ ≤ c * ω.cost (bisimulationMetric P P c) := mul_le_mul_of_nonneg_left matched c_nonneg
      _ ≤ bisimulationMetric P P c left right := le
      _ ≤ bisimulationMetric P P c left right + ε := by linarith

/-- **The exact inequality.**  For a floor `p` of the positive transition
probabilities, the possibilistic behavioural distance of the support at
discount `c · p` is at most the Kantorovich distance at discount `c`. -/
theorem behaviouralDistance_le_bisimulationMetric (bounded : UnitObservables P) {c p : ℝ}
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1)
    (floor : ∀ a s x, P.trans a s x ≠ 0 → p ≤ P.trans a s x) (s t : S) :
    (supportGraded P bounded (c * p) (mul_nonneg c_nonneg p_nonneg)
      (mul_le_one₀ c_le p_nonneg p_le)).behaviouralDistance s t ≤ bisimulationMetric P P c s t :=
  GradedSystem.behaviouralDistance_le _
    (isBisimMetric_bisimulationMetric bounded c_nonneg c_le p_nonneg p_le floor) s t

/-- **The same inequality against the logical distance** of functional
expressions, which is the Kantorovich distance (`LogicalDistance`). -/
theorem behaviouralDistance_le_logicalDistance (bounded : UnitObservables P) {c p : ℝ}
    (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1)
    (floor : ∀ a s x, P.trans a s x ≠ 0 → p ≤ P.trans a s x) (s t : S) :
    (supportGraded P bounded (c * p) (mul_nonneg c_nonneg p_nonneg)
      (mul_le_one₀ c_le p_nonneg p_le)).behaviouralDistance s t ≤ logicalDistance P c s t := by
  rw [← bisimulationMetric_eq_logicalDistance c_nonneg c_le]
  exact behaviouralDistance_le_bisimulationMetric bounded c_nonneg c_le p_nonneg p_le floor s t

end Graded

end Mettapedia.GSLT.Distinction.Probabilistic
