import Mettapedia.GSLT.Distinction.Probabilistic.Domination

/-!
# Controls for probabilistic GSLTs and their distances

One chain of five states under a single action.  A fair coin `fair` and a
biased coin `biased` both reach `good` and `bad`, with probabilities `1/2, 1/2`
and `1/4, 3/4`; `doomed` reaches `bad` only; `good` and `bad` stay put.  The
observable is `1` at `good` and `0` elsewhere.  Every positive transition has
probability at least `1/4`.

* **Equal supports, different weights.**  `fair` and `biased` are bisimilar in
  the support erasure (`fair_biased_support_bisimilar`), at support distance
  zero at every discount (`fair_biased_support_distance`), yet not Larsen–Skou
  bisimilar (`fair_biased_not_lsBisimilar`: one reaches `good` with probability
  more than `1/3`, the other does not) and at Kantorovich distance at least
  `c / 4` (`fair_biased_kantorovich_ge`).  So no bound of the Kantorovich
  distance by the support distance exists.
* **The inequality is attained** (`biased_doomed_tight`): for `biased` and
  `doomed` the support distance at discount `c · 1/4` and the Kantorovich
  distance at discount `c` are both `c / 4`.
* **The factor cannot be dropped** (`biased_doomed_factor_needed`): at the same
  discount `c` the support distance of `biased` and `doomed` is at least `c`,
  above their Kantorovich distance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.Cybernetics.ApproximateAdequacy

/-! ## The chain -/

/-- The states. -/
inductive Point
  | fair
  | biased
  | doomed
  | good
  | bad
  deriving DecidableEq

instance : Fintype Point where
  elems := {.fair, .biased, .doomed, .good, .bad}
  complete x := by cases x <;> simp

theorem sum_point {M : Type*} [AddCommMonoid M] (f : Point → M) :
    ∑ x, f x = f .fair + (f .biased + (f .doomed + (f .good + f .bad))) := by
  rw [show (Finset.univ : Finset Point) = {.fair, .biased, .doomed, .good, .bad} from rfl]
  simp

/-- The transition probabilities. -/
noncomputable def step : Point → Point → ℝ
  | .fair, .good => 1 / 2
  | .fair, .bad => 1 / 2
  | .biased, .good => 1 / 4
  | .biased, .bad => 3 / 4
  | .doomed, .bad => 1
  | .good, .good => 1
  | .bad, .bad => 1
  | _, _ => 0

/-- The observable: `1` at `good`. -/
def shown : Point → ℝ
  | .good => 1
  | _ => 0

/-- **The chain.** -/
noncomputable def chain : LabelledMarkovChain ℝ Unit Unit Point where
  trans _ := step
  isDistribution _ source :=
    ⟨fun target => by cases source <;> cases target <;> norm_num [step],
      by rw [sum_point]; cases source <;> norm_num [step]⟩
  observe _ := shown

theorem bounded : UnitObservables chain := fun _ x => by
  cases x <;> norm_num [chain, shown]

theorem floor : ∀ a s x, chain.trans a s x ≠ 0 → 1 / 4 ≤ chain.trans a s x := by
  intro a s x
  cases s <;> cases x <;> norm_num [chain, step]

theorem fair_biased_same_support (x : Point) : step .fair x ≠ 0 ↔ step .biased x ≠ 0 := by
  cases x <;> norm_num [step]

/-! ## Equal supports, different weights -/

/-- The relation pairing the two coins. -/
def coins (x y : Point) : Prop :=
  x = y ∨ (x = .fair ∧ y = .biased) ∨ (x = .biased ∧ y = .fair)

theorem coins_step {x y : Point} (related : coins x y) (x' : Point) (moved : step x x' ≠ 0) :
    step y x' ≠ 0 := by
  rcases related with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact moved
  · exact (fair_biased_same_support x').mp moved
  · exact (fair_biased_same_support x').mpr moved

theorem coins_shown {x y : Point} (related : coins x y) : shown x = shown y := by
  rcases related with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem coins_symm {x y : Point} (related : coins x y) : coins y x := by
  rcases related with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- **The coins are bisimilar in the support erasure.** -/
theorem fair_biased_support_bisimilar :
    (chainSystem chain).support.Bisimilar Point.fair Point.biased := by
  refine ⟨coins, ⟨?_, ?_, ?_⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · intro x y related label x' moved
    have positive : step x x' ≠ 0 := (support_act_iff label x x').mp moved
    exact ⟨x', (support_act_iff label y x').mpr (coins_step related x' positive), Or.inl rfl⟩
  · intro x y related label y' moved
    have positive : step y y' ≠ 0 := (support_act_iff label y y').mp moved
    exact ⟨y', (support_act_iff label x y').mpr (coins_step (coins_symm related) y' positive),
      Or.inl rfl⟩
  · intro x y related atom
    change chain.observe atom.1 x = atom.2 ↔ chain.observe atom.1 y = atom.2
    change shown x = atom.2 ↔ shown y = atom.2
    rw [coins_shown related]

/-- **The coins are at support distance zero**, at every discount. -/
theorem fair_biased_support_distance {d : ℝ} (d_nonneg : 0 ≤ d) (d_le : d ≤ 1) :
    (supportGraded chain bounded d d_nonneg d_le).behaviouralDistance .fair .biased = 0 := by
  refine GradedSystem.behaviouralDistance_eq_zero_of_gradedBisimilar _
    ⟨coins, ⟨?_, ?_, ?_⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · intro x y related label x' moved
    have positive : step x x' ≠ 0 := (supportGraded_act_iff label x x').mp moved
    exact ⟨x', (supportGraded_act_iff label y x').mpr (coins_step related x' positive), Or.inl rfl⟩
  · intro x y related label y' moved
    have positive : step y y' ≠ 0 := (supportGraded_act_iff label y y').mp moved
    exact ⟨y', (supportGraded_act_iff label x y').mpr
      (coins_step (coins_symm related) y' positive), Or.inl rfl⟩
  · intro x y related atom
    exact coins_shown related

/-- The probability that the fair coin shows the observable. -/
theorem fair_prob :
    (chainSystem chain).prob () .fair ((chainSystem chain).sat (.atom ((), 1))) = 1 / 2 := by
  rw [prob_eq_sum, sum_point]
  norm_num [ProbabilisticSystem.sat, chain, shown, step]

/-- The probability that the biased coin shows the observable. -/
theorem biased_prob :
    (chainSystem chain).prob () .biased ((chainSystem chain).sat (.atom ((), 1))) = 1 / 4 := by
  rw [prob_eq_sum, sum_point]
  norm_num [ProbabilisticSystem.sat, chain, shown, step]

/-- **The coins are not Larsen–Skou bisimilar**: the fair one reaches the
observable with probability more than `1/3`, the biased one does not. -/
theorem fair_biased_not_lsBisimilar :
    ¬ (chainSystem chain).LSBisimilar Point.fair Point.biased := by
  intro bisimilar
  have same := bisimilar.logicallyEquivalent (.more () (1 / 3) (.atom ((), 1)))
  have holds : (chainSystem chain).sat (.more () (1 / 3) (.atom ((), 1))) Point.fair := by
    change ((1 / 3 : ℚ) : ℝ) < _
    rw [fair_prob]
    norm_num
  have fails : ¬ (chainSystem chain).sat (.more () (1 / 3) (.atom ((), 1))) Point.biased := by
    change ¬ ((1 / 3 : ℚ) : ℝ) < _
    rw [biased_prob]
    norm_num
  exact fails (same.mp holds)

/-- **The coins are at Kantorovich distance at least `c / 4`.** -/
theorem fair_biased_kantorovich_ge {c : ℝ} (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    c / 4 ≤ bisimulationMetric chain chain c .fair .biased := by
  have bound := abs_eval_sub_le_bisimulationMetric (P := chain) (Q := chain) c_nonneg c_le
    (.next () (.observe ())) Point.fair Point.biased
  have fairValue : (FunctionalExpression.next () (.observe ())).eval chain c Point.fair =
      c * (1 / 2) := by
    simp only [FunctionalExpression.eval, expect]
    rw [sum_point]
    norm_num [chain, shown, step]
  have biasedValue : (FunctionalExpression.next () (.observe ())).eval chain c Point.biased =
      c * (1 / 4) := by
    simp only [FunctionalExpression.eval, expect]
    rw [sum_point]
    norm_num [chain, shown, step]
  rw [fairValue, biasedValue] at bound
  have difference : c * (1 / 2) - c * (1 / 4) = c / 4 := by ring
  rw [difference, abs_of_nonneg (by positivity)] at bound
  exact bound

/-! ## The inequality is attained, and needs its factor -/

theorem doomed_trans : chain.trans () .doomed = dirac .bad := by
  funext x
  cases x <;> simp [chain, step, dirac]

/-- The Kantorovich distance of the biased coin and the doomed state is at most
`c / 4`. -/
theorem biased_doomed_kantorovich_le {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1) :
    bisimulationMetric chain chain c .biased .doomed ≤ c / 4 := by
  have fixed := congrFun (congrFun (bisimulationMetric_eq_step (P := chain) (Q := chain)
    c_pos.le c_le) Point.biased) Point.doomed
  rw [fixed]
  refine kantorovichStep_le_iff.mpr ⟨(observationDistance_le_iff chain chain).mpr
    ⟨by positivity, fun i => ?_⟩, fun a => ?_⟩
  · change |shown .biased - shown .doomed| ≤ c / 4
    norm_num [shown]
    positivity
  · cases a
    rw [kantorovich_of_eq_dirac_right (chain.isDistribution () .biased) doomed_trans]
    have self := bisimulationMetric_self (P := chain) c_pos c_le Point.bad
    have far := bisimulationMetric_le_one bounded c_pos.le c_le Point.good Point.bad
    have value : expect (chain.trans () .biased)
        (fun x => bisimulationMetric chain chain c x .bad) =
          1 / 4 * bisimulationMetric chain chain c .good .bad +
            3 / 4 * bisimulationMetric chain chain c .bad .bad := by
      simp only [expect]
      rw [sum_point]
      norm_num [chain, step]
    rw [value, self]
    nlinarith

/-- The support distance of the biased coin and the doomed state is at least
the discount: one can show the observable after a step, the other cannot. -/
theorem biased_doomed_support_ge {d : ℝ} (d_nonneg : 0 ≤ d) (d_le : d ≤ 1) :
    d ≤ (supportGraded chain bounded d d_nonneg d_le).behaviouralDistance .biased .doomed := by
  set Q := supportGraded chain bounded d d_nonneg d_le
  have formulaBound := Q.abs_eval_sub_le_logicalDistance (.dia () (.atom ())) Point.biased
    Point.doomed
  have upper : Q.eval (.dia () (.atom ())) Point.doomed ≤ 0 := by
    change Q.discount * sSup ((Q.eval (.atom ())) '' Q.successors () Point.doomed) ≤ 0
    refine mul_nonpos_of_nonneg_of_nonpos d_nonneg (Real.sSup_le ?_ le_rfl)
    rintro _ ⟨x, moved, rfl⟩
    have positive : step .doomed x ≠ 0 := (supportGraded_act_iff (bounded := bounded) (d := d)
      (d_nonneg := d_nonneg) (d_le := d_le) () Point.doomed x).mp moved
    cases x
    case bad =>
      change shown Point.bad ≤ 0
      norm_num [shown]
    all_goals exact absurd rfl positive
  have lower : d ≤ Q.eval (.dia () (.atom ())) Point.biased := by
    change d ≤ Q.discount * sSup ((Q.eval (.atom ())) '' Q.successors () Point.biased)
    have reached : Q.eval (.atom ()) Point.good ≤
        sSup ((Q.eval (.atom ())) '' Q.successors () Point.biased) :=
      le_csSup (Q.bddAbove_image _ _) ⟨Point.good,
        (supportGraded_act_iff (bounded := bounded) (d := d) (d_nonneg := d_nonneg) (d_le := d_le)
          () Point.biased Point.good).mpr (by norm_num [chain, step]), rfl⟩
    have one : Q.eval (.atom ()) Point.good = 1 := rfl
    rw [one] at reached
    calc d = d * 1 := (mul_one d).symm
      _ ≤ d * sSup ((Q.eval (.atom ())) '' Q.successors () Point.biased) :=
        mul_le_mul_of_nonneg_left reached d_nonneg
  have := (le_abs_self _).trans formulaBound
  linarith [Q.logicalDistance_le_behaviouralDistance Point.biased Point.doomed]

/-- **The inequality is attained**: the support distance at discount `c · 1/4`
and the Kantorovich distance at discount `c` are both `c / 4`. -/
theorem biased_doomed_tight {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1) :
    (supportGraded chain bounded (c * (1 / 4)) (mul_nonneg c_pos.le (by norm_num))
        (mul_le_one₀ c_le (by norm_num) (by norm_num))).behaviouralDistance .biased .doomed =
      c / 4 ∧ bisimulationMetric chain chain c .biased .doomed = c / 4 := by
  have dominated := behaviouralDistance_le_bisimulationMetric bounded c_pos.le c_le
    (p := 1 / 4) (by norm_num) (by norm_num) floor Point.biased Point.doomed
  have above := biased_doomed_kantorovich_le c_pos c_le
  have below := biased_doomed_support_ge (d := c * (1 / 4)) (mul_nonneg c_pos.le (by norm_num))
    (mul_le_one₀ c_le (by norm_num) (by norm_num))
  constructor <;> linarith

/-- **The factor cannot be dropped**: at the same discount `c > 0`, the support
distance of the biased coin and the doomed state exceeds their Kantorovich
distance. -/
theorem biased_doomed_factor_needed {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1) :
    bisimulationMetric chain chain c .biased .doomed <
      (supportGraded chain bounded c c_pos.le c_le).behaviouralDistance .biased .doomed := by
  have above := biased_doomed_kantorovich_le c_pos c_le
  have below := biased_doomed_support_ge c_pos.le c_le
  linarith

end Mettapedia.GSLT.Distinction.Probabilistic.Controls
