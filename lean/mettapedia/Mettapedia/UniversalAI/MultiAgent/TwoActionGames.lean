import Mettapedia.UniversalAI.ReflectiveOracles.FixedPoints
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Nash equilibria of games with two actions, from reflective oracles

Finitely many players each choose one of two actions. A mixed strategy of a
player is the probability of the action `true`; a profile is a point of the
cube. Player `i` is asked: "is `true` the better action for you, given what
the others do?" Formally, a machine outputs `1` with probability
`1/2 + squash (gain) / 2`, where `gain` is the advantage of `true` over
`false`, and the query has threshold `1/2`.

A profile is a Nash equilibrium exactly when, read as an oracle, it is
reflective for these queries (`reflective_iff_isNash`). This is Theorem 4.1 of
Fallenstein, Taylor and Christiano (2015) for two actions. Since a reflective
oracle exists, so does a Nash equilibrium (`exists_isNash`): Nash's theorem
for such games.

The probabilities of the profile are the oracle's own randomization: a player
who is indifferent may be answered at random.

## Main statements

* `expected_update`: the expected payoff is affine in each player's own
  probability.
* `reflective_iff_isNash`: reflective oracles of the best-response queries are
  the Nash equilibria.
* `exists_isNash`: every game with finitely many players and two actions has
  a Nash equilibrium in mixed strategies.

## References

* Nash (1950). "Equilibrium points in n-person games"
* Fallenstein, Taylor & Christiano (2015). "Reflective Oracles: A Foundation
  for Classical Game Theory", Section 4
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.MultiAgent

open scoped unitInterval
open Finset Mettapedia.UniversalAI.ReflectiveOracles

/-! ## A bounded, sign-preserving rescaling -/

/-- `x / (1 + |x|)`: continuous, of the sign of `x`, of absolute value below one. -/
noncomputable def squash (x : ℝ) : ℝ := x / (1 + |x|)

theorem one_add_abs_pos (x : ℝ) : 0 < 1 + |x| := by positivity

theorem continuous_squash : Continuous squash :=
  continuous_id.div (continuous_const.add continuous_abs) fun x => (one_add_abs_pos x).ne'

theorem squash_pos {x : ℝ} : 0 < squash x ↔ 0 < x := by
  unfold squash
  rw [div_pos_iff_of_pos_right (one_add_abs_pos x)]

theorem squash_neg {x : ℝ} : squash x < 0 ↔ x < 0 := by
  unfold squash
  rw [div_lt_iff₀ (one_add_abs_pos x), zero_mul]

theorem abs_squash_lt_one (x : ℝ) : |squash x| < 1 := by
  unfold squash
  rw [abs_div, abs_of_pos (one_add_abs_pos x), div_lt_one (one_add_abs_pos x)]
  linarith

/-! ## Games -/

/-- A game in which each player chooses one of two actions. -/
structure TwoActionGame (ι : Type*) where
  /-- The payoff of each player for each choice of actions. -/
  payoff : ι → (ι → Bool) → ℝ

namespace TwoActionGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : TwoActionGame ι)

/-- The probability of an action when `true` is played with probability `t`. -/
def weight (t : I) (action : Bool) : ℝ :=
  if action then (t : ℝ) else 1 - (t : ℝ)

theorem weight_affine (t : I) (action : Bool) :
    weight t action = (1 - (t : ℝ)) * weight 0 action + (t : ℝ) * weight 1 action := by
  cases action <;> simp [weight]

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_weight (j : ι) (action : Bool) :
    Continuous fun s : ι → I => weight (s j) action := by
  have coordinate : Continuous fun s : ι → I => (s j : ℝ) :=
    continuous_subtype_val.comp (continuous_apply j)
  cases action
  · show Continuous fun s : ι → I => 1 - (s j : ℝ)
    exact continuous_const.sub coordinate
  · exact coordinate

/-- The expected payoff of player `i` when player `j` plays `true` with
probability `s j`, independently of the others. -/
noncomputable def expected (i : ι) (s : ι → I) : ℝ :=
  ∑ actions : ι → Bool, (∏ j, weight (s j) (actions j)) * G.payoff i actions

theorem continuous_expected (i : ι) : Continuous (G.expected i) :=
  continuous_finsetSum _ fun actions _ =>
    (continuous_finsetProd _ fun j _ => continuous_weight j (actions j)).mul continuous_const

/-- **The expected payoff is affine in the probability of each player.** -/
theorem expected_update (i k : ι) (s : ι → I) (t : I) :
    G.expected i (Function.update s k t) =
      (1 - (t : ℝ)) * G.expected i (Function.update s k 0) +
        (t : ℝ) * G.expected i (Function.update s k 1) := by
  have factor : ∀ (value : I) (actions : ι → Bool),
      ∏ j, weight (Function.update s k value j) (actions j) =
        weight value (actions k) * ∏ j ∈ univ \ {k}, weight (s j) (actions j) := by
    intro value actions
    have rewritten : (fun j => weight (Function.update s k value j) (actions j)) =
        Function.update (fun j => weight (s j) (actions j)) k (weight value (actions k)) := by
      funext j
      by_cases same : j = k
      · rw [same, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne same, Function.update_of_ne same]
    rw [rewritten, prod_update_of_mem (mem_univ k)]
  unfold expected
  simp only [factor]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun actions _ => ?_
  rw [weight_affine t (actions k)]
  ring

/-- No player gains by changing its own probability. -/
def IsNash (s : ι → I) : Prop :=
  ∀ i (t : I), G.expected i (Function.update s i t) ≤ G.expected i s

/-- The advantage of `true` over `false` for player `i`, given the others. -/
noncomputable def gain (i : ι) (s : ι → I) : ℝ :=
  G.expected i (Function.update s i 1) - G.expected i (Function.update s i 0)

theorem continuous_gain (i : ι) : Continuous (G.gain i) :=
  ((G.continuous_expected i).comp (continuous_id.update i continuous_const)).sub
    ((G.continuous_expected i).comp (continuous_id.update i continuous_const))

/-- The expected payoff in terms of the gain. -/
theorem expected_update_eq (i : ι) (s : ι → I) (t : I) :
    G.expected i (Function.update s i t) =
      G.expected i (Function.update s i 0) + (t : ℝ) * G.gain i s := by
  rw [G.expected_update i i s t]
  unfold gain
  ring

theorem expected_eq (i : ι) (s : ι → I) :
    G.expected i s = G.expected i (Function.update s i 0) + (s i : ℝ) * G.gain i s := by
  conv_lhs => rw [← Function.update_eq_self i s]
  exact G.expected_update_eq i s (s i)

/-- The queries "is `true` the better action for player `i`?" -/
noncomputable def bestResponseQueries : QuerySystem ι where
  threshold _ := 1 / 2
  outputOne i s := 1 / 2 + squash (G.gain i s) / 2
  outputZero i s := 1 / 2 - squash (G.gain i s) / 2
  outputOne_nonneg i s := by
    have bound := abs_lt.mp (abs_squash_lt_one (G.gain i s))
    linarith [bound.1]
  outputZero_nonneg i s := by
    have bound := abs_lt.mp (abs_squash_lt_one (G.gain i s))
    linarith [bound.2]
  output_le_one i s := by linarith

theorem bestResponseQueries_semicontinuous : G.bestResponseQueries.OutputsLowerSemicontinuous :=
  fun i =>
    ⟨(continuous_const.add ((continuous_squash.comp (G.continuous_gain i)).div_const 2)).lowerSemicontinuous,
      (continuous_const.sub ((continuous_squash.comp (G.continuous_gain i)).div_const 2)).lowerSemicontinuous⟩

/-- **Reflective oracles of the best-response queries are the Nash
equilibria.** -/
theorem reflective_iff_isNash (s : ι → I) : G.bestResponseQueries.Reflective s ↔ G.IsNash s := by
  constructor
  · intro reflective i t
    obtain ⟨one, zero⟩ := reflective i
    simp only [bestResponseQueries] at one zero
    rw [G.expected_update_eq i s t, G.expected_eq i s]
    have tBounds := t.2
    have sBounds := (s i).2
    rcases lt_trichotomy (G.gain i s) 0 with negative | none | positive
    · have forced : s i = 0 := zero (by linarith [squash_neg.mpr negative])
      rw [forced, Set.Icc.coe_zero, zero_mul]
      nlinarith [tBounds.1]
    · rw [none]
      simp
    · have forced : s i = 1 := one (by linarith [squash_pos.mpr positive])
      rw [forced, Set.Icc.coe_one, one_mul]
      nlinarith [tBounds.2]
  · intro nash i
    simp only [QuerySystem.ReflectiveAt, bestResponseQueries]
    have sBounds := (s i).2
    constructor
    · intro above
      have positive : 0 < G.gain i s := squash_pos.mp (by linarith)
      have best := nash i 1
      rw [G.expected_update_eq i s 1, G.expected_eq i s, Set.Icc.coe_one, one_mul] at best
      apply Subtype.ext
      rw [Set.Icc.coe_one]
      nlinarith [sBounds.2]
    · intro above
      have negative : G.gain i s < 0 := squash_neg.mp (by linarith)
      have best := nash i 0
      rw [G.expected_update_eq i s 0, G.expected_eq i s, Set.Icc.coe_zero, zero_mul] at best
      apply Subtype.ext
      rw [Set.Icc.coe_zero]
      nlinarith [sBounds.1]

/-- **Every game with finitely many players and two actions has a Nash
equilibrium in mixed strategies.** -/
theorem exists_isNash : ∃ s : ι → I, G.IsNash s := by
  obtain ⟨s, reflective⟩ := QuerySystem.exists_reflective G.bestResponseQueries_semicontinuous
  exact ⟨s, (G.reflective_iff_isNash s).mp reflective⟩

end TwoActionGame

/-! ## Two worked games -/

namespace TwoActionGames

/-- One player who is paid for the action `true`. -/
def preferTrue : TwoActionGame Unit where
  payoff _ actions := if actions () then 1 else 0

theorem preferTrue_expected (s : Unit → I) : preferTrue.expected () s = (s () : ℝ) := by
  have profiles : (univ : Finset (Unit → Bool)) = {fun _ => true, fun _ => false} := by
    ext actions
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    cases value : actions ()
    · exact Or.inr (funext fun _ => value)
    · exact Or.inl (funext fun _ => value)
  have different : (fun _ : Unit => true) ≠ fun _ => false := fun same =>
    Bool.noConfusion (congrFun same ())
  unfold TwoActionGame.expected
  rw [profiles, sum_pair different]
  simp [preferTrue, TwoActionGame.weight]

/-- The only equilibrium is to play `true`. -/
theorem preferTrue_isNash_iff (s : Unit → I) : preferTrue.IsNash s ↔ s () = 1 := by
  constructor
  · intro nash
    have best := nash () 1
    rw [preferTrue_expected, preferTrue_expected, Function.update_self, Set.Icc.coe_one] at best
    exact Subtype.ext (le_antisymm (s ()).2.2 best)
  · intro one i t
    rw [preferTrue_expected, preferTrue_expected, Function.update_self, one, Set.Icc.coe_one]
    exact t.2.2

/-- Playing `false` is not an equilibrium. -/
theorem preferTrue_not_isNash_zero : ¬preferTrue.IsNash fun _ => 0 := fun nash =>
  zero_ne_one ((preferTrue_isNash_iff _).mp nash)

end TwoActionGames

end Mettapedia.UniversalAI.MultiAgent
