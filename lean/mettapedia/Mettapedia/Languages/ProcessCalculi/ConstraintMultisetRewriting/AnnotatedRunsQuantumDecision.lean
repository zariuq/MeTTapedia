import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantum

/-!
# The disjunction effect in the Prisoner's Dilemma: total probability and two unrecorded histories

## The data

Shafir and Tversky, "Thinking through uncertainty: nonconsequential reasoning and choice",
Cognitive Psychology 24 (1992) 449–474, as tabulated by Pothos and Busemeyer, "A quantum
probability explanation for violations of 'rational' decision theory", Proc. R. Soc. B 276 (2009)
2171–2178, Table 2. In a one-shot Prisoner's Dilemma, 97% of players defected when told that the
other player had defected, 84% when told that the other had cooperated, and 63% when not told.

## No classical mixture gives the not-told rate

* In any finite family of graded runs that records what the other player did, the law of total
  probability makes the defection rate at least `84%` when the told-condition rates are `97%` and
  `84%` (`total_probability_bound`). So `63%` is not the rate of any classical mixture
  (`disjunction_effect_not_classical`, `mixture_never_63`).

## Two unrecorded histories give it

* The not-told player is in the superposition of the two told preparations, `x + y`: the history
  in which the other defected (`otherDefected`) and the one in which the other cooperated
  (`otherCooperated`), of equal Born weight `900`, as in an equal superposition of the two beliefs.
  Each is an exact Gaussian-rational amplitude over four end states, two in which the player
  defects and two in which the player cooperates.
* Being told the other's move records the history, and each told readout is that history's
  weights: `97/100` and `84/100` (`told_defected`, `told_cooperated`). Not told, the histories add
  at each end state, and the readout is `63/100` (`not_told`).
* **The deviation is the interference term** (`defect_deviation`, `cooperate_deviation`): the
  not-told weight of defection is the recorded weight plus the cross terms of the two histories at
  the end states of defection, here `1629 - 1440 = 189` (`deviation_is_interference`). The two
  histories have equal weight, so the recorded readout of the same preparation is the
  total-probability mixture with weight `1/2` on each, `181/200` (`recorded_is_total_probability`).

## Orthogonal histories cannot give it

* If the two histories are orthogonal (their cross terms over all end states sum to zero, as
  unitary evolution of orthogonal preparations requires), the told-condition rates force the
  not-told rate away from `63%` (`orthogonal_cannot_reproduce`): the cross term of the cooperating
  end states is bounded by Cauchy–Schwarz (`crossC_sq_le`), and it would have to be large. The
  model above is not orthogonal: its cross terms sum to `-1500` (`model_not_orthogonal`), and its
  readout is normalized after interference, as the candidate step's Born readout is.
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

namespace Decision

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_formula born_nonnegative)

/-! ## No classical mixture gives the not-told rate -/

section TotalProbability

variable {R : Type} [Fintype R]

/-- **The law of total probability with the told-condition rates.** In a finite family of runs
with nonnegative grades that records what the other player did, if the rate of defection is `97%`
among the runs in which the other defected and `84%` among those in which the other cooperated,
then the rate of defection is at least `84%`. -/
theorem total_probability_bound (grade : R → ℚ) (nonneg : ∀ r, 0 ≤ grade r)
    (other me : R → Prop) [DecidablePred other] [DecidablePred me]
    (toldDefected : ∑ r ∈ Finset.univ.filter (fun r => me r ∧ other r), grade r =
      97 / 100 * ∑ r ∈ Finset.univ.filter other, grade r)
    (toldCooperated : ∑ r ∈ Finset.univ.filter (fun r => me r ∧ ¬ other r), grade r =
      84 / 100 * ∑ r ∈ Finset.univ.filter (fun r => ¬ other r), grade r) :
    84 / 100 * ∑ r, grade r ≤ ∑ r ∈ Finset.univ.filter me, grade r := by
  have splitMe : ∑ r ∈ Finset.univ.filter me, grade r =
      ∑ r ∈ Finset.univ.filter (fun r => me r ∧ other r), grade r +
        ∑ r ∈ Finset.univ.filter (fun r => me r ∧ ¬ other r), grade r := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter me) other, Finset.filter_filter,
      Finset.filter_filter]
  have splitAll : ∑ r, grade r = ∑ r ∈ Finset.univ.filter other, grade r +
      ∑ r ∈ Finset.univ.filter (fun r => ¬ other r), grade r :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ other grade).symm
  have nonnegOther : 0 ≤ ∑ r ∈ Finset.univ.filter other, grade r :=
    Finset.sum_nonneg fun r _ => nonneg r
  rw [splitMe, toldDefected, toldCooperated, splitAll]
  linarith

/-- **The not-told rate is not the rate of any classical mixture.** -/
theorem disjunction_effect_not_classical (grade : R → ℚ) (nonneg : ∀ r, 0 ≤ grade r)
    (other me : R → Prop) [DecidablePred other] [DecidablePred me]
    (toldDefected : ∑ r ∈ Finset.univ.filter (fun r => me r ∧ other r), grade r =
      97 / 100 * ∑ r ∈ Finset.univ.filter other, grade r)
    (toldCooperated : ∑ r ∈ Finset.univ.filter (fun r => me r ∧ ¬ other r), grade r =
      84 / 100 * ∑ r ∈ Finset.univ.filter (fun r => ¬ other r), grade r)
    (positive : 0 < ∑ r, grade r) :
    (∑ r ∈ Finset.univ.filter me, grade r) / ∑ r, grade r ≠ 63 / 100 := by
  intro same
  have bound := total_probability_bound grade nonneg other me toldDefected toldCooperated
  rw [div_eq_iff positive.ne'] at same
  linarith

end TotalProbability

/-- **No mixture of the told conditions gives `63%`**: every mixture lies between `84%` and
`97%`. -/
theorem mixture_never_63 {p : ℚ} (low : 0 ≤ p) (high : p ≤ 1) :
    84 / 100 ≤ p * (97 / 100) + (1 - p) * (84 / 100) ∧
      p * (97 / 100) + (1 - p) * (84 / 100) ≤ 97 / 100 ∧
      p * (97 / 100) + (1 - p) * (84 / 100) ≠ 63 / 100 := by
  refine ⟨by linarith, by linarith, fun same => ?_⟩
  linarith

/-! ## Two unrecorded histories -/

/-- The end states: two in which the player defects, two in which the player cooperates. -/
inductive Final where
  | d₁
  | d₂
  | c₁
  | c₂

/-- The Born weight of the end states of defection. -/
def defectWeight (amp : Final → Amplitude) : ℚ := born (amp .d₁) + born (amp .d₂)

/-- The Born weight of the end states of cooperation. -/
def cooperateWeight (amp : Final → Amplitude) : ℚ := born (amp .c₁) + born (amp .c₂)

/-- The total Born weight. -/
def totalWeight (amp : Final → Amplitude) : ℚ := defectWeight amp + cooperateWeight amp

/-- **The Born probability of defection**: normalized after the amplitudes have been added. -/
def probDefect (amp : Final → Amplitude) : ℚ := defectWeight amp / totalWeight amp

/-- The cross terms of two histories at the end states of defection. -/
def crossD (x y : Final → Amplitude) : ℚ :=
  interference (x .d₁) (y .d₁) + interference (x .d₂) (y .d₂)

/-- The cross terms of two histories at the end states of cooperation. -/
def crossC (x y : Final → Amplitude) : ℚ :=
  interference (x .c₁) (y .c₁) + interference (x .c₂) (y .c₂)

theorem defectWeight_nonneg (amp : Final → Amplitude) : 0 ≤ defectWeight amp :=
  add_nonneg (born_nonnegative _) (born_nonnegative _)

theorem cooperateWeight_nonneg (amp : Final → Amplitude) : 0 ≤ cooperateWeight amp :=
  add_nonneg (born_nonnegative _) (born_nonnegative _)

/-- **The deviation is the interference term**: unrecorded, the weight of defection is the
recorded weight plus the cross terms at the end states of defection. -/
theorem defect_deviation (x y : Final → Amplitude) :
    defectWeight (x + y) = defectWeight x + defectWeight y + crossD x y := by
  unfold defectWeight crossD
  simp only [Pi.add_apply, born_add]
  ring

theorem cooperate_deviation (x y : Final → Amplitude) :
    cooperateWeight (x + y) = cooperateWeight x + cooperateWeight y + crossC x y := by
  unfold cooperateWeight crossC
  simp only [Pi.add_apply, born_add]
  ring

/-- **The history in which the other defected**, over the end states `d₁ d₂ c₁ c₂`. -/
def otherDefected : Final → Amplitude
  | .d₁ => -1
  | .d₂ => ⟨26, 14⟩
  | .c₁ => ⟨5, 1⟩
  | .c₂ => 1

/-- **The history in which the other cooperated.** -/
def otherCooperated : Final → Amplitude
  | .d₁ => 12
  | .d₂ => ⟨-24, -6⟩
  | .c₁ => ⟨-6, 6⟩
  | .c₂ => ⟨-6, 6⟩

/-- **Told that the other defected: `97%`.** -/
theorem told_defected : probDefect otherDefected = 97 / 100 := by
  norm_num [probDefect, totalWeight, defectWeight, cooperateWeight, otherDefected, born_formula]

/-- **Told that the other cooperated: `84%`.** -/
theorem told_cooperated : probDefect otherCooperated = 84 / 100 := by
  norm_num [probDefect, totalWeight, defectWeight, cooperateWeight, otherCooperated, born_formula]

/-- **Not told: `63%`.** The two histories are unrecorded and add at each end state. -/
theorem not_told : probDefect (otherDefected + otherCooperated) = 63 / 100 := by
  norm_num [probDefect, totalWeight, defectWeight, cooperateWeight, otherDefected,
    otherCooperated, born_formula]

/-- **The deviation is the interference term, in numbers**: the recorded weights of defection and
cooperation are `1629` and `171`; the cross terms are `-1440` and `-60`; the unrecorded weights
are `189` and `111`. -/
theorem deviation_is_interference :
    defectWeight otherDefected + defectWeight otherCooperated = 1629 ∧
      cooperateWeight otherDefected + cooperateWeight otherCooperated = 171 ∧
      crossD otherDefected otherCooperated = -1440 ∧ crossC otherDefected otherCooperated = -60 ∧
      defectWeight (otherDefected + otherCooperated) = 189 ∧
      cooperateWeight (otherDefected + otherCooperated) = 111 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [defectWeight, cooperateWeight, crossD, crossC, interference, otherDefected,
      otherCooperated, born_formula]

/-- **The recorded readout is the total-probability mixture**: the two histories have equal
weight, as an equal superposition of the two beliefs; with both recorded, the rate of defection is
`181/200`, the mixture of the told rates with weight `1/2` on each. -/
theorem recorded_is_total_probability :
    (defectWeight otherDefected + defectWeight otherCooperated) /
        (totalWeight otherDefected + totalWeight otherCooperated) = 181 / 200 ∧
      totalWeight otherDefected / (totalWeight otherDefected + totalWeight otherCooperated) =
        1 / 2 ∧
      (1 / 2 : ℚ) * (97 / 100) + (1 - 1 / 2) * (84 / 100) = 181 / 200 := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
    norm_num [totalWeight, defectWeight, cooperateWeight, otherDefected, otherCooperated,
      born_formula]

/-- **The model is not orthogonal**: its cross terms sum to `-1500`. -/
theorem model_not_orthogonal :
    crossD otherDefected otherCooperated + crossC otherDefected otherCooperated = -1500 := by
  norm_num [crossD, crossC, interference, otherDefected, otherCooperated]

/-! ## Orthogonal histories cannot give it -/

/-- Cauchy–Schwarz in four rational coordinates, as the Lagrange identity. -/
theorem cauchy_schwarz_four (p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ : ℚ) :
    (2 * (p₁ * q₁ + p₂ * q₂) + 2 * (p₃ * q₃ + p₄ * q₄)) ^ 2 ≤
      4 * (p₁ * p₁ + p₂ * p₂ + (p₃ * p₃ + p₄ * p₄)) *
        (q₁ * q₁ + q₂ * q₂ + (q₃ * q₃ + q₄ * q₄)) := by
  nlinarith [sq_nonneg (p₁ * q₂ - p₂ * q₁), sq_nonneg (p₁ * q₃ - p₃ * q₁),
    sq_nonneg (p₁ * q₄ - p₄ * q₁), sq_nonneg (p₂ * q₃ - p₃ * q₂), sq_nonneg (p₂ * q₄ - p₄ * q₂),
    sq_nonneg (p₃ * q₄ - p₄ * q₃)]

/-- **The cross term of the cooperating end states is bounded by their weights.** -/
theorem crossC_sq_le (x y : Final → Amplitude) :
    crossC x y ^ 2 ≤ 4 * cooperateWeight x * cooperateWeight y := by
  unfold crossC cooperateWeight interference
  rw [born_formula, born_formula, born_formula, born_formula]
  exact cauchy_schwarz_four _ _ _ _ _ _ _ _

/-- The arithmetic of the no-go: the told ratios, the not-told ratio and Cauchy–Schwarz are
incompatible. -/
theorem orthogonal_arithmetic {a b c d u : ℚ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (positive : 0 < a + b) (ratioX : 3 * a = 97 * b) (ratioY : 16 * c = 84 * d)
    (cs : u ^ 2 ≤ 4 * b * d) (notTold : 100 * (a + c - u) = 63 * (a + b + c + d)) : False := by
  have hu : u = 34 * a / 97 + c / 4 := by linarith
  have hb : b = 3 * a / 97 := by linarith
  have hd : d = 4 * c / 21 := by linarith
  rw [hu, hb, hd] at cs
  have ac : a * c = 0 := by
    refine le_antisymm ?_ (mul_nonneg ha hc)
    nlinarith [sq_nonneg (34 * a / 97), sq_nonneg (c / 4)]
  have square : (34 * a / 97 + c / 4) ^ 2 = 0 := by
    refine le_antisymm ?_ (sq_nonneg _)
    nlinarith [ac]
  have sum : 34 * a / 97 + c / 4 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp square
  have a0 : a = 0 := by linarith
  rw [hb, a0] at positive
  norm_num at positive

/-- **No orthogonal pair of histories gives the disjunction effect.** If the told-condition rates
are `97%` and `84%` and the two histories are orthogonal, the not-told rate is not `63%`. -/
theorem orthogonal_cannot_reproduce (x y : Final → Amplitude)
    (toldDefect : probDefect x = 97 / 100) (toldCooperate : probDefect y = 84 / 100)
    (orthogonal : crossD x y + crossC x y = 0) : probDefect (x + y) ≠ 63 / 100 := by
  intro notTold
  have totalX : totalWeight x ≠ 0 := by
    intro zero
    rw [probDefect, zero, div_zero] at toldDefect
    norm_num at toldDefect
  have totalY : totalWeight y ≠ 0 := by
    intro zero
    rw [probDefect, zero, div_zero] at toldCooperate
    norm_num at toldCooperate
  have ratioX : 3 * defectWeight x = 97 * cooperateWeight x := by
    rw [probDefect, div_eq_iff totalX, totalWeight] at toldDefect
    linarith
  have ratioY : 16 * defectWeight y = 84 * cooperateWeight y := by
    rw [probDefect, div_eq_iff totalY, totalWeight] at toldCooperate
    linarith
  have positive : 0 < defectWeight x + cooperateWeight x :=
    lt_of_le_of_ne (add_nonneg (defectWeight_nonneg x) (cooperateWeight_nonneg x))
      (Ne.symm totalX)
  have totalXY : totalWeight (x + y) ≠ 0 := by
    unfold totalWeight
    rw [defect_deviation, cooperate_deviation]
    intro zero
    have := add_nonneg (defectWeight_nonneg y) (cooperateWeight_nonneg y)
    linarith
  rw [probDefect, div_eq_iff totalXY, totalWeight, defect_deviation, cooperate_deviation]
    at notTold
  exact orthogonal_arithmetic (defectWeight_nonneg x) (defectWeight_nonneg y) positive ratioX
    ratioY (crossC_sq_le x y) (by linarith)

end Decision

end AmplitudeRuns

open AmplitudeRuns.Decision

#print axioms total_probability_bound
#print axioms disjunction_effect_not_classical
#print axioms mixture_never_63
#print axioms defect_deviation
#print axioms cooperate_deviation
#print axioms told_defected
#print axioms told_cooperated
#print axioms not_told
#print axioms deviation_is_interference
#print axioms recorded_is_total_probability
#print axioms model_not_orthogonal
#print axioms cauchy_schwarz_four
#print axioms crossC_sq_le
#print axioms orthogonal_arithmetic
#print axioms orthogonal_cannot_reproduce

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
