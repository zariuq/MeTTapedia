import Mettapedia.GSLT.Distinction.Probabilistic.Completion
import Mettapedia.GSLT.Distinction.Probabilistic.Domination

/-!
# Domination for probabilistic GSLTs with refusal

`Domination` compares, for a finite chain, the possibilistic distance of the
support with the Kantorovich distance: with a floor `p` on the positive
probabilities, the first at discount `c · p` is at most the second at discount
`c`.  A finite probabilistic GSLT may refuse a step with positive probability;
its metric is that of its stopped completion (`Completion.behaviouralMetric`).

* **Domination through the completion**
  (`supportDistance_le_behaviouralMetric`): with a floor `p` on the positive
  weights, the behavioural distance of the support erasure (atoms read as
  indicators) at discount `c · p` is at most the behavioural metric at discount
  `c`.  A step of one side is matched by an optimal coupling of the completion;
  if the match is the stopped state, the halted observable puts the pair at
  distance at least `c · p`, which is the Hausdorff clause for an unmatched
  step.  Every finite probabilistic GSLT has such a floor (`exists_weight_floor`).
* **The zero kernel is discount-free** (`support_bisimilar_of_behaviouralMetric_eq_zero`,
  `supportDistance_eq_zero_of_behaviouralMetric_eq_zero`): distance zero in the
  behavioural metric at any positive discount makes the two states bisimilar in
  the support, hence at distance zero in the support at every positive
  discount.
* **Refusal is invisible to the support** (`Hesitation.refusal_control`): a state
  that steps surely and one that refuses half the time, to the same successor,
  are bisimilar in the support and at support distance zero at every discount,
  while their behavioural metric is at least `c / 2` and they are not
  Larsen–Skou bisimilar.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction
open Mettapedia.Cybernetics.ApproximateAdequacy

section Domination

variable {S : Type*} [Fintype S] [DecidableEq S] {M : ProbabilisticSystem (stateGSLT S)}

omit [Fintype S] [DecidableEq S] in
/-- The steps of the support erasure are the positively weighted successors. -/
theorem support_act_iff_weight {label : M.Label} {x x' : S} :
    M.support.act label x x' ↔ (M.kernel label x).weight x' ≠ 0 := by
  constructor
  · rintro ⟨z, member, same⟩
    have equal : z = x' := same
    subst equal
    exact Finsupp.mem_support_iff.mp member
  · intro nonzero
    exact ⟨x', Finsupp.mem_support_iff.mpr nonzero, rfl⟩

variable [Fintype M.Label] [Fintype M.Atom]

omit [Fintype M.Atom] in
/-- **Every finite probabilistic GSLT has a floor** on its positive weights. -/
theorem exists_weight_floor :
    ∃ p, 0 < p ∧ p ≤ 1 ∧
      ∀ label s x, (M.kernel label s).weight x ≠ 0 → p ≤ (M.kernel label s).weight x := by
  obtain ⟨p, p_pos, p_le, floor⟩ := exists_floor (P := completion M)
  exact ⟨p, p_pos, p_le, fun label s x nonzero => floor label (some s) (some x) nonzero⟩

/-- The stopped state is at distance at least one from every state. -/
theorem one_le_metric_some_none {c : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (x : S) :
    1 ≤ bisimulationMetric (completion M) (completion M) c (some x) none := by
  have halted := (couplingBound_bisimulationMetric (P := completion M) (Q := completion M)
    c_nonneg c_le).observe_le none (some x) none
  change |(0 : ℝ) - 1| ≤ _ at halted
  norm_num at halted
  exact halted

theorem one_le_metric_none_some {c : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (y : S) :
    1 ≤ bisimulationMetric (completion M) (completion M) c none (some y) := by
  have halted := (couplingBound_bisimulationMetric (P := completion M) (Q := completion M)
    c_nonneg c_le).observe_le none none (some y)
  change |(1 : ℝ) - 0| ≤ _ at halted
  norm_num at halted
  exact halted

/-- **The behavioural metric at discount `c` is a bisimulation metric of the
support at discount `c · p`**, for a floor `p` of the positive weights. -/
theorem isBisimMetric_behaviouralMetric {c p : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (p_nonneg : 0 ≤ p) (p_le : p ≤ 1)
    (floor : ∀ label s x, (M.kernel label s).weight x ≠ 0 → p ≤ (M.kernel label s).weight x) :
    (GradedSystem.ofSystem M.support (c * p) (mul_nonneg c_nonneg p_nonneg)
      (mul_le_one₀ c_le p_nonneg p_le)).IsBisimMetric (behaviouralMetric (M := M) c) where
  nonneg x y := bisimulationMetric_nonneg c_nonneg c_le _ _
  observes atom x y :=
    (couplingBound_bisimulationMetric (P := completion M) (Q := completion M) c_nonneg
      c_le).observe_le (some atom) (some x) (some y)
  forth label x y x' step := by
    have positive : (completion M).trans label (some x) (some x') ≠ 0 :=
      support_act_iff_weight.mp step
    have lower : p ≤ (completion M).trans label (some x) (some x') := floor label x x' positive
    obtain ⟨ω, le⟩ := (couplingBound_bisimulationMetric (P := completion M) (Q := completion M)
      c_nonneg c_le).step_le label (some x) (some y)
    obtain ⟨w, nonzero, matched⟩ := exists_matching_successor ω
      (bisimulationMetric_nonneg (P := completion M) (Q := completion M) c_nonneg c_le) positive
    have weight_nonneg := ((completion M).isDistribution label (some x)).nonneg (some x')
    rcases w with _ | y'
    · left
      have far := one_le_metric_some_none (M := M) c_nonneg c_le x'
      change c * p ≤ bisimulationMetric (completion M) (completion M) c (some x) (some y)
      calc c * p = c * (p * 1) := by ring
        _ ≤ c * ((completion M).trans label (some x) (some x') *
              bisimulationMetric (completion M) (completion M) c (some x') none) :=
            mul_le_mul_of_nonneg_left (mul_le_mul lower far zero_le_one weight_nonneg) c_nonneg
        _ ≤ c * ω.cost (bisimulationMetric (completion M) (completion M) c) :=
            mul_le_mul_of_nonneg_left matched c_nonneg
        _ ≤ _ := le
    · right
      intro ε ε_pos
      refine ⟨y', support_act_iff_weight.mpr fun zero =>
        nonzero (ω.weight_eq_zero_of_right (y := some y') zero (some x')), ?_⟩
      have distance_nonneg := bisimulationMetric_nonneg (P := completion M) (Q := completion M)
        c_nonneg c_le (some x') (some y')
      change c * p * bisimulationMetric (completion M) (completion M) c (some x') (some y') ≤
        bisimulationMetric (completion M) (completion M) c (some x) (some y) + ε
      calc c * p * bisimulationMetric (completion M) (completion M) c (some x') (some y')
          ≤ c * ((completion M).trans label (some x) (some x') *
              bisimulationMetric (completion M) (completion M) c (some x') (some y')) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right lower distance_nonneg) c_nonneg
        _ ≤ c * ω.cost (bisimulationMetric (completion M) (completion M) c) :=
            mul_le_mul_of_nonneg_left matched c_nonneg
        _ ≤ _ := le
        _ ≤ _ := by linarith
  back label x y y' step := by
    have positive : (completion M).trans label (some y) (some y') ≠ 0 :=
      support_act_iff_weight.mp step
    have lower : p ≤ (completion M).trans label (some y) (some y') := floor label y y' positive
    obtain ⟨ω, le⟩ := (couplingBound_bisimulationMetric (P := completion M) (Q := completion M)
      c_nonneg c_le).step_le label (some x) (some y)
    obtain ⟨w, nonzero, matched⟩ := exists_matching_successor ω.swap
      (D := fun w z => bisimulationMetric (completion M) (completion M) c z w)
      (fun w z => bisimulationMetric_nonneg (P := completion M) (Q := completion M) c_nonneg c_le
        z w) positive
    rw [ω.cost_swap] at matched
    have weight_nonneg := ((completion M).isDistribution label (some y)).nonneg (some y')
    rcases w with _ | x'
    · left
      have far := one_le_metric_none_some (M := M) c_nonneg c_le y'
      change c * p ≤ bisimulationMetric (completion M) (completion M) c (some x) (some y)
      calc c * p = c * (p * 1) := by ring
        _ ≤ c * ((completion M).trans label (some y) (some y') *
              bisimulationMetric (completion M) (completion M) c none (some y')) :=
            mul_le_mul_of_nonneg_left (mul_le_mul lower far zero_le_one weight_nonneg) c_nonneg
        _ ≤ c * ω.cost (bisimulationMetric (completion M) (completion M) c) :=
            mul_le_mul_of_nonneg_left matched c_nonneg
        _ ≤ _ := le
    · right
      intro ε ε_pos
      refine ⟨x', support_act_iff_weight.mpr fun zero =>
        nonzero (ω.weight_eq_zero_of_left (x := some x') zero (some y')), ?_⟩
      have distance_nonneg := bisimulationMetric_nonneg (P := completion M) (Q := completion M)
        c_nonneg c_le (some x') (some y')
      change c * p * bisimulationMetric (completion M) (completion M) c (some x') (some y') ≤
        bisimulationMetric (completion M) (completion M) c (some x) (some y) + ε
      calc c * p * bisimulationMetric (completion M) (completion M) c (some x') (some y')
          ≤ c * ((completion M).trans label (some y) (some y') *
              bisimulationMetric (completion M) (completion M) c (some x') (some y')) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right lower distance_nonneg) c_nonneg
        _ ≤ c * ω.cost (bisimulationMetric (completion M) (completion M) c) :=
            mul_le_mul_of_nonneg_left matched c_nonneg
        _ ≤ _ := le
        _ ≤ _ := by linarith

/-- **Domination for probabilistic GSLTs with refusal.**  For a floor `p` of the
positive weights, the behavioural distance of the support erasure at discount
`c · p` is at most the behavioural metric of the completion at discount `c`. -/
theorem supportDistance_le_behaviouralMetric {c p : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (p_nonneg : 0 ≤ p) (p_le : p ≤ 1)
    (floor : ∀ label s x, (M.kernel label s).weight x ≠ 0 → p ≤ (M.kernel label s).weight x)
    (x y : S) :
    (GradedSystem.ofSystem M.support (c * p) (mul_nonneg c_nonneg p_nonneg)
      (mul_le_one₀ c_le p_nonneg p_le)).behaviouralDistance x y ≤
        behaviouralMetric (M := M) c x y :=
  GradedSystem.behaviouralDistance_le _
    (isBisimMetric_behaviouralMetric c_nonneg c_le p_nonneg p_le floor) x y

omit [DecidableEq S] [Fintype M.Label] [Fintype M.Atom] in
/-- The support of a probabilistic GSLT over finitely many states is finitely
branching. -/
theorem support_imageFiniteModulo : M.support.ImageFiniteModulo :=
  fun _ _ => ⟨Set.univ, Set.finite_univ, fun target _ => ⟨target, Set.mem_univ _, rfl⟩⟩

/-- **Distance zero in the behavioural metric gives bisimilarity of the
support**, at any positive discount. -/
theorem support_bisimilar_of_behaviouralMetric_eq_zero {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1)
    {x y : S} (zero : behaviouralMetric (M := M) c x y = 0) : M.support.Bisimilar x y := by
  obtain ⟨p, p_pos, p_le, floor⟩ := exists_weight_floor (M := M)
  have dominated := supportDistance_le_behaviouralMetric c_pos.le c_le p_pos.le p_le floor x y
  refine (GradedSystem.logicalDistance_ofSystem_eq_zero_iff M.support
    (mul_nonneg c_pos.le p_pos.le) (mul_le_one₀ c_le p_pos.le p_le) support_imageFiniteModulo
    (mul_pos c_pos p_pos) x y).mp ?_
  exact le_antisymm (((GradedSystem.ofSystem M.support (c * p) _ _).logicalDistance_le_behaviouralDistance
    x y).trans (dominated.trans zero.le))
    ((GradedSystem.ofSystem M.support (c * p) _ _).logicalDistance_nonneg x y)

/-- **The zero kernel is discount-free**: distance zero in the behavioural metric
at one positive discount gives distance zero in the support at every positive
discount. -/
theorem supportDistance_eq_zero_of_behaviouralMetric_eq_zero {c : ℝ} (c_pos : 0 < c)
    (c_le : c ≤ 1) {x y : S} (zero : behaviouralMetric (M := M) c x y = 0) {d : ℝ}
    (d_pos : 0 < d) (d_le : d ≤ 1) :
    (GradedSystem.ofSystem M.support d d_pos.le d_le).logicalDistance x y = 0 :=
  (GradedSystem.logicalDistance_ofSystem_eq_zero_iff M.support d_pos.le d_le
    support_imageFiniteModulo d_pos x y).mpr (support_bisimilar_of_behaviouralMetric_eq_zero
      c_pos c_le zero)

end Domination

/-! ## Control: refusal is invisible to the support -/

namespace Hesitation

/-- Three states: one steps surely, one refuses half the time, one has stopped. -/
inductive State where
  | sure
  | hesitant
  | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.sure, .hesitant, .done}
  complete state := by cases state <;> decide

theorem sum_state (f : State → ℝ) : ∑ state, f state = f .sure + f .hesitant + f .done := by
  change ∑ state ∈ ({.sure, .hesitant, .done} : Finset State), f state = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The weights: `sure` reaches `done` with probability one, `hesitant` with
probability one half, `done` does not step. -/
noncomputable def weight : State → State → ℝ
  | .sure, .done => 1
  | .hesitant, .done => 1 / 2
  | _, _ => 0

theorem weight_nonneg (source target : State) : 0 ≤ weight source target := by
  cases source <;> cases target <;> norm_num [weight]

theorem weight_total (source : State) : ∑ target, weight source target ≤ 1 := by
  rw [sum_state]
  cases source <;> norm_num [weight]

/-- **The hesitation system.** -/
noncomputable abbrev system : ProbabilisticSystem (stateGSLT State) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  kernel _ source := SubDistribution.ofFunction (weight source) (weight_nonneg source)
    (weight_total source)
  kernel_resp _ left right equivalent _ _ := by
    have same : left = right := equivalent
    rw [same]

theorem act_iff {source target : State} :
    system.support.act () source target ↔ weight source target ≠ 0 := by
  rw [support_act_iff_weight, SubDistribution.ofFunction_weight]

/-- `sure` and `hesitant` step to the same successor, and `done` does not step. -/
def related (left right : State) : Prop :=
  left = right ∨ (left ≠ .done ∧ right ≠ .done)

theorem isBisimulation_related : system.support.IsBisimulation related := by
  have target_done : ∀ {source target : State}, system.support.act () source target →
      target = .done := by
    intro source target step
    have nonzero := act_iff.mp step
    cases source <;> cases target <;> simp_all [weight]
  have source_live : ∀ {source target : State}, system.support.act () source target →
      source ≠ .done := by
    intro source target step
    have nonzero := act_iff.mp step
    cases source <;> cases target <;> simp_all [weight]
  have live_step : ∀ {source : State}, source ≠ .done → system.support.act () source .done := by
    intro source live
    refine act_iff.mpr ?_
    cases source <;> simp_all [weight]
  refine ⟨?_, ?_, ?_⟩
  · rintro left right (rfl | ⟨leftLive, rightLive⟩) label left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases label
      rw [target_done step]
      exact ⟨.done, live_step rightLive, Or.inl rfl⟩
  · rintro left right (rfl | ⟨leftLive, rightLive⟩) label right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases label
      rw [target_done step]
      exact ⟨.done, live_step leftLive, Or.inl rfl⟩
  · intro _ _ _ atom
    exact atom.elim

theorem halted_after (c : ℝ) (source : State) :
    (FunctionalExpression.next () (.observe none)).eval (completion system) c (some source) =
      c * (1 - ∑ target, weight source target) := by
  simp only [FunctionalExpression.eval, expect, Fintype.sum_option]
  change c * ((1 - (system.kernel () source).total) * 1 +
      ∑ target, (system.kernel () source).weight target * 0) = _
  rw [SubDistribution.total_eq_sum]
  simp

/-- **Refusal is invisible to the support.**  `sure` and `hesitant` are bisimilar
in the support and at support distance zero at every positive discount, while
their behavioural metric is at least `c / 2` and they are not Larsen–Skou
bisimilar. -/
theorem refusal_control {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1) :
    system.support.Bisimilar .sure .hesitant ∧
      (∀ (d : ℝ) (d_pos : 0 < d) (d_le : d ≤ 1),
        (GradedSystem.ofSystem system.support d d_pos.le d_le).logicalDistance .sure .hesitant = 0) ∧
      c / 2 ≤ behaviouralMetric (M := system) c .sure .hesitant ∧
      ¬ system.LSBisimilar .sure .hesitant := by
  have bisimilar : system.support.Bisimilar .sure .hesitant :=
    ⟨related, isBisimulation_related, Or.inr ⟨by decide, by decide⟩⟩
  have gap : c / 2 ≤ behaviouralMetric (M := system) c .sure .hesitant := by
    have bound := abs_eval_sub_le_bisimulationMetric (P := completion system)
      (Q := completion system) c_pos.le c_le (.next () (.observe none)) (some .sure)
      (some .hesitant)
    rw [halted_after, halted_after, sum_state, sum_state] at bound
    norm_num [weight] at bound
    rw [abs_of_pos c_pos] at bound
    unfold behaviouralMetric
    linarith
  refine ⟨bisimilar, fun d d_pos d_le => ?_, gap, fun lsBisimilar => ?_⟩
  · exact (GradedSystem.logicalDistance_ofSystem_eq_zero_iff system.support d_pos.le d_le
      support_imageFiniteModulo d_pos _ _).mpr bisimilar
  · have zero := (behaviouralMetric_eq_zero_iff (M := system) c_pos c_le).mpr lsBisimilar
    linarith

end Hesitation

end Mettapedia.GSLT.Distinction.Probabilistic
