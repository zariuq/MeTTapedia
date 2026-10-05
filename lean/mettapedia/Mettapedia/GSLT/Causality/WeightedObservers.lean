import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.ProbabilityTheory.BayesianInference.Basic
import Mettapedia.ProbabilityTheory.Common.FrechetBounds

/-!
# Weighted observers: finite distributions over the draws of a GSLT

The observers of the causal ladder are possibilistic: a diamond holds when some
step satisfies its body, whatever that step's weight.  A **weighted observer**
reads a finite distribution over draws, each draw a state of the GSLT, and
reports the probability that the drawn state satisfies a formula (`chance`).

* The probability carrier is the library's finite simplex `Prob`, and the
  probability of an event is the expectation of its indicator, the `evidence`
  of `BayesianInference` (`mass`).
* A finite distribution is a modular valuation on the Boolean algebra of
  events (`valuation`), the sum rule of the Knuth–Skilling derivation, so the
  Fréchet bounds of `Common.FrechetBounds` bound the probability of every
  conjunction by those of its conjuncts (`chance_conj_bounds`), and in
  particular the probability that one formula holds while another fails
  (`chance_conj_neg_bounds`): this is the form of the Tian–Pearl bounds.
* The difference of two probabilities is the probability of gaining minus the
  probability of losing (`chance_sub_chance`).

**Erasure** (`Weighting`, `Weighting.erasure`).  A weighting of a labelled
step is a finite distribution over draws whose positively weighted draws are
steps under the label and which reaches every such step up to the equations: a
Markov kernel supported exactly on the steps.  The possibilistic diamond holds
exactly when the weighted observer gives its body positive probability: the
possibilistic observer is the support of the weighted one.  Two weightings of
the same step with the same support are therefore invisible to every
possibilistic observer, whatever their weights.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.WeightedObservers

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.ProbabilityTheory.Common.FrechetBounds

universe uΩ uS uAtom uLabel

/-! ## The probability of an event -/

section Mass

variable {Ω : Type uΩ} [Fintype Ω] (law : Prob Ω)

/-- **The probability of an event**: the expectation of its indicator. -/
noncomputable def mass (event : Set Ω) : ℝ :=
  evidence law (event.indicator 1)

theorem mass_eq_sum (event : Set Ω) : mass law event = ∑ ω, law.1 ω * event.indicator 1 ω :=
  rfl

omit [Fintype Ω] in
theorem indicator_one_nonneg (event : Set Ω) (ω : Ω) : (0 : ℝ) ≤ event.indicator 1 ω :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) ω

theorem mass_nonneg (event : Set Ω) : 0 ≤ mass law event :=
  evidence_nonneg law _ (indicator_one_nonneg event)

theorem mass_univ : mass law Set.univ = 1 := by
  simp only [mass_eq_sum, Set.indicator_univ, Pi.one_apply, mul_one]
  exact law.2.2

theorem mass_empty : mass law ∅ = 0 := by
  simp only [mass_eq_sum, Set.indicator_empty, mul_zero, Finset.sum_const_zero]

theorem mass_mono {event event' : Set Ω} (sub : event ⊆ event') :
    mass law event ≤ mass law event' :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
    (Set.indicator_le_indicator_of_subset sub (fun _ => zero_le_one) ω) (law.2.1 ω)

theorem mass_union_add_inter (event event' : Set Ω) :
    mass law (event ∪ event') + mass law (event ∩ event') = mass law event + mass law event' := by
  simp only [mass_eq_sum, ← Finset.sum_add_distrib, ← mul_add, Set.indicator_union_add_inter_apply]

theorem mass_compl (event : Set Ω) : mass law eventᶜ = 1 - mass law event := by
  have modular := mass_union_add_inter law event eventᶜ
  rw [Set.union_compl_self, Set.inter_compl_self, mass_univ, mass_empty] at modular
  linarith

/-- An event has positive probability exactly when it contains a point of
positive weight. -/
theorem mass_pos_iff (event : Set Ω) : 0 < mass law event ↔ ∃ ω ∈ event, 0 < law.1 ω := by
  rw [mass_eq_sum, Finset.sum_pos_iff_of_nonneg
    (fun ω _ => mul_nonneg (law.2.1 ω) (indicator_one_nonneg event ω))]
  constructor
  · rintro ⟨ω, -, positive⟩
    by_cases member : ω ∈ event
    · rw [Set.indicator_of_mem member, Pi.one_apply, mul_one] at positive
      exact ⟨ω, member, positive⟩
    · rw [Set.indicator_of_notMem member, mul_zero] at positive
      exact absurd positive (lt_irrefl 0)
  · rintro ⟨ω, member, positive⟩
    refine ⟨ω, Finset.mem_univ ω, ?_⟩
    rw [Set.indicator_of_mem member, Pi.one_apply, mul_one]
    exact positive

/-- **A finite distribution is a modular valuation on its events**: the sum
rule, read on the Boolean algebra of events. -/
noncomputable def valuation : ModularValuation (Set Ω) where
  val := mass law
  val_nonneg := mass_nonneg law
  val_modular := mass_union_add_inter law
  val_mono := fun _ _ sub => mass_mono law sub

theorem valuation_top : (valuation law).val ⊤ = 1 :=
  mass_univ law

/-- **The Fréchet bounds for events**, from those of modular valuations. -/
theorem mass_inter_bounds (event event' : Set Ω) :
    max 0 (mass law event + mass law event' - 1) ≤ mass law (event ∩ event') ∧
      mass law (event ∩ event') ≤ min (mass law event) (mass law event') :=
  ⟨(valuation law).frechet_lower event event' (valuation_top law),
    (valuation law).frechet_upper event event'⟩

/-- The difference of two probabilities is the probability of the first event
without the second minus that of the second without the first. -/
theorem mass_sub_mass (event event' : Set Ω) :
    mass law event - mass law event' = mass law (event \ event') - mass law (event' \ event) := by
  simp only [mass_eq_sum, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  by_cases member : ω ∈ event <;> by_cases member' : ω ∈ event' <;>
    simp [member, member']

end Mass

/-! ## The weighted observer -/

section Chance

variable {S : GSLT.{uS}} (M : System.{uAtom, uLabel} S) {Ω : Type uΩ} [Fintype Ω]

/-- **The weighted observer**: the probability that the drawn state satisfies a
formula. -/
noncomputable def chance (law : Prob Ω) (draw : Ω → S.Term)
    (formula : Formula M.Atom M.Label) : ℝ :=
  mass law {ω | M.sat formula (draw ω)}

variable (law : Prob Ω) (draw : Ω → S.Term)

theorem chance_nonneg (formula : Formula M.Atom M.Label) : 0 ≤ chance M law draw formula :=
  mass_nonneg law _

theorem chance_top : chance M law draw .top = 1 :=
  mass_univ law

theorem chance_neg (formula : Formula M.Atom M.Label) :
    chance M law draw (.neg formula) = 1 - chance M law draw formula :=
  mass_compl law _

theorem chance_le_one (formula : Formula M.Atom M.Label) : chance M law draw formula ≤ 1 := by
  have := chance_nonneg M law draw (.neg formula)
  rw [chance_neg] at this
  linarith

/-- **The Fréchet bounds for the weighted observer.** -/
theorem chance_conj_bounds (formula formula' : Formula M.Atom M.Label) :
    max 0 (chance M law draw formula + chance M law draw formula' - 1) ≤
        chance M law draw (.conj formula formula') ∧
      chance M law draw (.conj formula formula') ≤
        min (chance M law draw formula) (chance M law draw formula') :=
  mass_inter_bounds law _ _

/-- **The probability that one formula holds and another fails** is bounded by
their two probabilities alone: the form of the Tian–Pearl bounds. -/
theorem chance_conj_neg_bounds (formula formula' : Formula M.Atom M.Label) :
    max 0 (chance M law draw formula - chance M law draw formula') ≤
        chance M law draw (.conj formula (.neg formula')) ∧
      chance M law draw (.conj formula (.neg formula')) ≤
        min (chance M law draw formula) (1 - chance M law draw formula') := by
  have bounds := chance_conj_bounds M law draw formula (.neg formula')
  rw [chance_neg] at bounds
  have rewrite : chance M law draw formula + (1 - chance M law draw formula') - 1 =
      chance M law draw formula - chance M law draw formula' := by ring
  rw [rewrite] at bounds
  exact bounds

/-- **A difference of probabilities is gain minus loss**: the probability that
the first formula holds and the second fails, minus the probability that the
second holds and the first fails. -/
theorem chance_sub_chance (formula formula' : Formula M.Atom M.Label) :
    chance M law draw formula - chance M law draw formula' =
      chance M law draw (.conj formula (.neg formula')) -
        chance M law draw (.conj formula' (.neg formula)) :=
  mass_sub_mass law _ _

end Chance

/-! ## Erasure: the possibilistic observer is the support of the weighted one -/

section Erasure

variable {S : GSLT.{uS}} (M : System.{uAtom, uLabel} S)

/-- **A weighting of a labelled step**: a finite distribution over draws, each
positively weighted draw a step under the label, and every step under the
label reached, up to the equations, by a positively weighted draw. -/
structure Weighting (label : M.Label) (source : S.Term) (Ω : Type uΩ) [Fintype Ω] where
  /-- The distribution of the draw. -/
  law : Prob Ω
  /-- The state drawn. -/
  draw : Ω → S.Term
  /-- A positively weighted draw is a step. -/
  sound : ∀ ω, 0 < law.1 ω → M.act label source (draw ω)
  /-- Every step is a positively weighted draw, up to the equations. -/
  complete : ∀ target, M.act label source target →
    ∃ ω, 0 < law.1 ω ∧ S.Equiv (draw ω) target

variable {M} {Ω : Type uΩ} [Fintype Ω]

/-- **Erasure.**  The possibilistic diamond holds exactly when the weighted
observer gives its body positive probability. -/
theorem Weighting.erasure {label : M.Label} {source : S.Term}
    (weighting : Weighting M label source Ω) (formula : Formula M.Atom M.Label) :
    M.sat (.dia label formula) source ↔ 0 < chance M weighting.law weighting.draw formula := by
  unfold chance
  rw [mass_pos_iff]
  constructor
  · rintro ⟨target, step, holds⟩
    obtain ⟨ω, positive, equivalent⟩ := weighting.complete target step
    exact ⟨ω, (M.sat_resp formula equivalent).mpr holds, positive⟩
  · rintro ⟨ω, holds, positive⟩
    exact ⟨weighting.draw ω, weighting.sound ω positive, holds⟩

/-- Equal probabilities give equal possibilistic verdicts. -/
theorem Weighting.sat_dia_iff_of_chance_eq {label label' : M.Label} {source source' : S.Term}
    {Ω' : Type uΩ} [Fintype Ω'] (weighting : Weighting M label source Ω)
    (weighting' : Weighting M label' source' Ω') (formula : Formula M.Atom M.Label)
    (same : chance M weighting.law weighting.draw formula =
      chance M weighting'.law weighting'.draw formula) :
    M.sat (.dia label formula) source ↔ M.sat (.dia label' formula) source' := by
  rw [weighting.erasure, weighting'.erasure, same]

end Erasure

end Mettapedia.GSLT.Causality.WeightedObservers
