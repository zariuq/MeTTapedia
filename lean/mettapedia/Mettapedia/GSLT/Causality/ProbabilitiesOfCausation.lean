import Mettapedia.GSLT.Causality.WeightedResponseTypes

/-!
# Probabilities of necessity and sufficiency: abduction and the Tian–Pearl combined bounds

A population of the response-type GSLT is a finite law over individuals, each
with a natural treatment and a response type (`WeightedResponseTypes`).  The
individual is the exogenous state of the model: it fixes the treatment taken
when nobody intervenes and the outcome under each treatment.

**Abduction is conditioning** (`condition`).  Given an observed event, the law
of the individual is replaced by its posterior through
`BayesianInference.posterior`, with the indicator of the event as likelihood.
The posterior probability of an event is the conditional probability
(`mass_condition`), and the weighted observer read after abduction is the
conditional probability of a formula (`chance_condition`).

**PN and PS** follow Pearl's three steps: abduce the individual from an
observational record, act by imposing the other treatment, predict the
outcome.
* `pn`: from the record "treated, effect shown", the effect would not have
  shown untreated, `PN = P(Y_0 = 0 | X = 1, Y = 1)`.
* `ps`: from the record "untreated, no effect", the effect would have shown
  treated, `PS = P(Y_1 = 1 | X = 0, Y = 0)`.
The record is the first slice's passive query `showsRealization`, read with
nobody intervening; the prediction is a counterfactual query of the saturated
system.

**The data** (`Data`, `data`) are the observational joint law of treatment and
outcome and the two experimental marginals.  They are rung-2 quantities:
populations that agree at weighted rung two have the same data
(`data_eq_of_weightedAgree`).

**Tian–Pearl's combined bounds** (J. Tian and J. Pearl, *Probabilities of
causation: bounds and identification*, Ann. Math. AI 28, 2000), from
observational and experimental data together:
* `pn_bounds`: `max 0 ((P(y) − P(y_0)) / P(x, y)) ≤ PN ≤ min 1 ((P(y'_0) − P(x', y')) / P(x, y))`;
* `ps_bounds`: `max 0 ((P(y_1) − P(y)) / P(x', y')) ≤ PS ≤ min 1 ((P(y_1) − P(x, y)) / P(x', y'))`;
* `pns_combined_bounds`: the lower bound is the largest of `0`,
  `P(y_1) − P(y_0)`, `P(y) − P(y_0)` and `P(y_1) − P(y)`; the upper bound is the
  smallest of `P(y_1)`, `P(y'_0)`, `P(x, y) + P(x', y')` and
  `P(y_1) − P(y_0) + P(x, y') + P(x', y)`.

**The swap generates what the data leave open** (`swap`).  Within each group
of natural treatment, move weight from always to helped and the same weight
from never to hurt.  This is the first slice's passage between the fixed and
the mixed populations, made quantitative.  The swap changes no passive query
under any regime (`passiveProbability_swap`), so it preserves weighted rung
two (`weightedAgree_swap`) and the data (`data_swap`).  It moves PN, PS and
PNS by the weight moved (`pn_swap`, `ps_swap`, `pns_swap`).  Conversely the
populations with the data of `μ` are exactly its swaps
(`data_eq_iff_exists_swap`), so on response types weighted rung two is exactly
the observational and experimental data
(`weightedAgree_intervention_iff_data_eq`).

**Tightness with explicit populations.**  For every population, swaps of it
realise every value between the bounds: the sets of values of PN, PS and PNS
compatible with its data are exactly the three intervals (`pn_identifiedSet`,
`ps_identifiedSet`, `pns_identifiedSet`), and both ends are attained
(`pn_bounds_attained`, `ps_bounds_attained`, `pns_bounds_attained`).  The ends
of the PNS interval are `pns μ` plus the least and the greatest admissible
swaps (`pnsLower_eq`, `pnsUpper_eq`).

**Monotonicity identifies** (`pn_eq_of_noHarm`, `ps_eq_of_noHarm`): with no
individual hurt by treatment, `PN = (P(y) − P(y_0)) / P(x, y)` and
`PS = (P(y_1) − P(y)) / P(x', y')`, the lower bounds, so the data identify
both (`pn_identified_of_noHarm`, `ps_identified_of_noHarm`).

**Exogeneity identifies the experiments from observation**
(`experimental_eq_of_exogenous`): when the natural treatment is independent of
the response type, `P(y_x) = P(y | x)`.  With monotonicity as well, PN is the
excess risk ratio `1 − P(y | x') / P(y | x)` (`pn_eq_excessRiskRatio`) and PS is
`(P(y | x) − P(y | x')) / P(y' | x')` (`ps_eq_of_exogenous`): rung-1 data
identify both.

**Controls.**
* `selfSelection_control`: those who take the treatment are helped, those who
  decline it are hurt.  The experiments alone leave PNS on `[0, 1/2]` (a
  population with the same experimental marginals has PNS `0`); the combined
  bounds pin PNS to `1/2` and PN to `1`.
* `confounding_control`: in the self-selected population `P(y | x) = 1` while
  `P(y_x) = 1/2`, so it is not exogenous.
* `rungTwo_does_not_identify`: the uniform population and one of its swaps
  agree at weighted rung two and have PN `1/2` and `1`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ProbabilitiesOfCausation

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes
open Mettapedia.GSLT.Causality.WeightedObservers
open Mettapedia.GSLT.Causality.WeightedResponseTypes
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference

/-! ## Abduction: conditioning a finite law on an observed event -/

section Abduction

variable {Ω : Type*} [Fintype Ω] (law : Prob Ω)

/-- **Abduction**: the posterior of a finite law given that the drawn point lies
in an observed event, by `BayesianInference.posterior` with the indicator of the
event as likelihood. -/
noncomputable def condition (event : Set Ω) (possible : 0 < mass law event) : Prob Ω :=
  posterior law (event.indicator 1) (indicator_one_nonneg event) possible

theorem condition_apply (event : Set Ω) (possible : 0 < mass law event) (ω : Ω) :
    (condition law event possible).1 ω = law.1 ω * event.indicator 1 ω / mass law event :=
  rfl

/-- **The posterior probability of an event is the conditional probability.** -/
theorem mass_condition (event event' : Set Ω) (possible : 0 < mass law event) :
    mass (condition law event possible) event' = mass law (event ∩ event') / mass law event := by
  have product : (fun ω => event.indicator (1 : Ω → ℝ) ω * event'.indicator 1 ω) =
      (event ∩ event').indicator 1 := by
    rw [Set.inter_indicator_one]
    rfl
  have step := evidence_posterior law (event.indicator 1) (event'.indicator 1)
    (indicator_one_nonneg event) possible
  rw [product] at step
  exact step

/-- After abduction the observed event is certain. -/
theorem mass_condition_self (event : Set Ω) (possible : 0 < mass law event) :
    mass (condition law event possible) event = 1 := by
  rw [mass_condition, Set.inter_self, div_self possible.ne']

/-- **The weighted observer after abduction** is the conditional probability of
the formula given the observed event. -/
theorem chance_condition {S : GSLT} (M : System S) (draw : Ω → S.Term) (event : Set Ω)
    (possible : 0 < mass law event) (formula : Formula M.Atom M.Label) :
    chance M (condition law event possible) draw formula =
      mass law (event ∩ {ω | M.sat formula (draw ω)}) / mass law event :=
  mass_condition law event _ possible

end Abduction

/-! ## Records, the data of an experiment, and the eight weights -/

/-- The record observed when nobody intervenes: the treatment taken and the
outcome. -/
def record (treated effect : Bool) : Set Individual :=
  {individual | realization none individual = (treated, effect)}

/-- **The observational probability** `P(X = x, Y = y)`: the passive query "left
to run, the individual shows this treatment and this outcome", nobody
intervening. -/
noncomputable def observational (population : Prob Individual) (treated effect : Bool) : ℝ :=
  passiveProbability population none (showsRealization (treated, effect))

theorem observational_eq_mass (population : Prob Individual) (treated effect : Bool) :
    observational population treated effect = mass population (record treated effect) :=
  congrArg (mass population)
    (Set.ext fun individual => sat_showsRealization (treated, effect) none individual)

/-- **The data of an experiment**: the observational joint law of treatment and
outcome, and the two experimental marginals. -/
structure Data where
  /-- `P(X = x, Y = y)`. -/
  observed : Bool → Bool → ℝ
  /-- `P(Y_x = 1)`. -/
  experimented : Bool → ℝ

/-- The data of a population. -/
noncomputable def data (population : Prob Individual) : Data :=
  ⟨observational population, experimental population⟩

namespace Data

variable (d : Data)

/-- `P(y)`: the effect observed, nobody intervening. -/
noncomputable def effect : ℝ := d.observed true true + d.observed false true

/-- Tian–Pearl's lower bound on PN. -/
noncomputable def pnLower : ℝ :=
  max 0 ((d.effect - d.experimented false) / d.observed true true)

/-- Tian–Pearl's upper bound on PN. -/
noncomputable def pnUpper : ℝ :=
  min 1 ((1 - d.experimented false - d.observed false false) / d.observed true true)

/-- Tian–Pearl's lower bound on PS. -/
noncomputable def psLower : ℝ :=
  max 0 ((d.experimented true - d.effect) / d.observed false false)

/-- Tian–Pearl's upper bound on PS. -/
noncomputable def psUpper : ℝ :=
  min 1 ((d.experimented true - d.observed true true) / d.observed false false)

/-- Tian–Pearl's combined lower bound on PNS. -/
noncomputable def pnsLower : ℝ :=
  max (max 0 (d.experimented true - d.experimented false))
    (max (d.effect - d.experimented false) (d.experimented true - d.effect))

/-- Tian–Pearl's combined upper bound on PNS. -/
noncomputable def pnsUpper : ℝ :=
  min (min (d.experimented true) (1 - d.experimented false))
    (min (d.observed true true + d.observed false false)
      (d.experimented true - d.experimented false + d.observed true false +
        d.observed false true))

end Data

section Weights

variable (μ : Prob Individual)

/-- The probability of an event, over the eight individuals. -/
theorem mass_eq_eight (event : Set Individual) :
    mass μ event =
      (μ.1 (false, .never) * event.indicator 1 (false, .never) +
          μ.1 (false, .helped) * event.indicator 1 (false, .helped) +
          μ.1 (false, .hurt) * event.indicator 1 (false, .hurt) +
          μ.1 (false, .always) * event.indicator 1 (false, .always)) +
        (μ.1 (true, .never) * event.indicator 1 (true, .never) +
          μ.1 (true, .helped) * event.indicator 1 (true, .helped) +
          μ.1 (true, .hurt) * event.indicator 1 (true, .hurt) +
          μ.1 (true, .always) * event.indicator 1 (true, .always)) := by
  rw [mass_eq_sum, sum_individual]

theorem total_eight :
    (μ.1 (false, .never) + μ.1 (false, .helped) + μ.1 (false, .hurt) + μ.1 (false, .always)) +
      (μ.1 (true, .never) + μ.1 (true, .helped) + μ.1 (true, .hurt) + μ.1 (true, .always)) = 1 := by
  rw [← sum_individual]
  exact μ.2.2

theorem mass_singleton (individual : Individual) : mass μ {individual} = μ.1 individual := by
  rw [mass_eq_sum, Finset.sum_eq_single individual]
  · simp
  · intro other _ different
    simp [different]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

theorem observational_true_true :
    observational μ true true = μ.1 (true, .helped) + μ.1 (true, .always) := by
  rw [observational_eq_mass, mass_eq_eight]
  simp [record, realization, Response.outcome]

theorem observational_true_false :
    observational μ true false = μ.1 (true, .never) + μ.1 (true, .hurt) := by
  rw [observational_eq_mass, mass_eq_eight]
  simp [record, realization, Response.outcome]

theorem observational_false_true :
    observational μ false true = μ.1 (false, .hurt) + μ.1 (false, .always) := by
  rw [observational_eq_mass, mass_eq_eight]
  simp [record, realization, Response.outcome]

theorem observational_false_false :
    observational μ false false = μ.1 (false, .never) + μ.1 (false, .helped) := by
  rw [observational_eq_mass, mass_eq_eight]
  simp [record, realization, Response.outcome]

theorem experimental_true_eight :
    experimental μ true = μ.1 (false, .helped) + μ.1 (false, .always) +
      (μ.1 (true, .helped) + μ.1 (true, .always)) := by
  rw [experimental_eq_mass, mass_eq_eight]
  simp [Response.outcome]

theorem experimental_false_eight :
    experimental μ false = μ.1 (false, .hurt) + μ.1 (false, .always) +
      (μ.1 (true, .hurt) + μ.1 (true, .always)) := by
  rw [experimental_eq_mass, mass_eq_eight]
  simp [Response.outcome]

theorem pns_eight : pns μ = μ.1 (false, .helped) + μ.1 (true, .helped) := by
  rw [pns_eq_mass, mass_eq_eight]
  simp

theorem harmProbability_eight : harmProbability μ = μ.1 (false, .hurt) + μ.1 (true, .hurt) := by
  rw [harmProbability_eq_mass, mass_eq_eight]
  simp

/-- The passive probability of the effect is the sum of the two observational
cells with the effect. -/
theorem probability_effectObserved_eq_effect :
    probability μ none effectObserved = (data μ).effect := by
  rw [probability_eq_mass (event := {individual | individual.2.outcome individual.1 = true}) μ none
    fun individual => sat_effectObserved none individual, mass_eq_eight]
  change _ = observational μ true true + observational μ false true
  rw [observational_true_true, observational_false_true]
  simp [Response.outcome]
  ring

end Weights

/-! ## Probabilities of necessity and of sufficiency -/

/-- **Abduction from a record**: the posterior law of the individual given that,
left alone, it showed this treatment and this outcome. -/
noncomputable def abduce (population : Prob Individual) (treated effect : Bool)
    (possible : 0 < observational population treated effect) : Prob Individual :=
  condition population (record treated effect) (by
    rw [← observational_eq_mass]
    exact possible)

/-- **The probability of necessity** `PN = P(Y_0 = 0 | X = 1, Y = 1)`: abduce the
individual from the record "treated, effect shown", withhold treatment, and
predict that the effect does not show. -/
noncomputable def pn (population : Prob Individual)
    (possible : 0 < observational population true true) : ℝ :=
  probability (abduce population true true possible) none (noEffectUnder false)

/-- **The probability of sufficiency** `PS = P(Y_1 = 1 | X = 0, Y = 0)`: abduce
the individual from the record "untreated, no effect", treat, and predict that
the effect shows. -/
noncomputable def ps (population : Prob Individual)
    (possible : 0 < observational population false false) : ℝ :=
  probability (abduce population false false possible) none (effectUnder true)

section Necessity

variable (μ : Prob Individual)

/-- **PN in the weights**: the weight of the treated helped over that of the
treated with the effect. -/
theorem pn_eq (possible : 0 < observational μ true true) :
    pn μ possible = μ.1 (true, .helped) / observational μ true true := by
  have sets : record true true ∩
      {individual | ladder.sat (noEffectUnder false) (drawn none individual)} =
        {(true, .helped)} := by
    ext ⟨natural, response⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, record, realization, sat_noEffectUnder,
      Set.mem_singleton_iff]
    cases natural <;> cases response <;> simp [Response.outcome]
  unfold pn probability abduce
  rw [chance_condition, sets, mass_singleton, observational_eq_mass]

/-- **PS in the weights**: the weight of the untreated helped over that of the
untreated without the effect. -/
theorem ps_eq (possible : 0 < observational μ false false) :
    ps μ possible = μ.1 (false, .helped) / observational μ false false := by
  have sets : record false false ∩
      {individual | ladder.sat (effectUnder true) (drawn none individual)} =
        {(false, .helped)} := by
    ext ⟨natural, response⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, record, realization, sat_effectUnder,
      Set.mem_singleton_iff]
    cases natural <;> cases response <;> simp [Response.outcome]
  unfold ps probability abduce
  rw [chance_condition, sets, mass_singleton, observational_eq_mass]

/-- **Tian–Pearl's bounds on PN** from observational and experimental data. -/
theorem pn_bounds (possible : 0 < observational μ true true) :
    (data μ).pnLower ≤ pn μ possible ∧ pn μ possible ≤ (data μ).pnUpper := by
  rw [pn_eq]
  simp only [Data.pnLower, Data.pnUpper, Data.effect, data]
  have tt := observational_true_true μ
  have ft := observational_false_true μ
  have ff := observational_false_false μ
  have e0 := experimental_false_eight μ
  have total := total_eight μ
  have nonneg := fun individual => μ.2.1 individual
  have h1 := nonneg (true, .hurt)
  have h2 := nonneg (true, .never)
  have h3 := nonneg (true, .helped)
  have h4 := nonneg (true, .always)
  refine ⟨max_le (div_nonneg h3 possible.le) (div_le_div_of_nonneg_right (by linarith) possible.le),
    le_min ((div_le_one₀ possible).mpr (by linarith))
      (div_le_div_of_nonneg_right (by linarith) possible.le)⟩

/-- **Tian–Pearl's bounds on PS** from observational and experimental data. -/
theorem ps_bounds (possible : 0 < observational μ false false) :
    (data μ).psLower ≤ ps μ possible ∧ ps μ possible ≤ (data μ).psUpper := by
  rw [ps_eq]
  simp only [Data.psLower, Data.psUpper, Data.effect, data]
  have tt := observational_true_true μ
  have ft := observational_false_true μ
  have ff := observational_false_false μ
  have e1 := experimental_true_eight μ
  have nonneg := fun individual => μ.2.1 individual
  have h1 := nonneg (false, .hurt)
  have h2 := nonneg (false, .never)
  have h3 := nonneg (false, .helped)
  have h4 := nonneg (false, .always)
  refine ⟨max_le (div_nonneg h3 possible.le) (div_le_div_of_nonneg_right (by linarith) possible.le),
    le_min ((div_le_one₀ possible).mpr (by linarith))
      (div_le_div_of_nonneg_right (by linarith) possible.le)⟩

/-- **Tian–Pearl's combined bounds on PNS** from observational and experimental
data. -/
theorem pns_combined_bounds : (data μ).pnsLower ≤ pns μ ∧ pns μ ≤ (data μ).pnsUpper := by
  simp only [Data.pnsLower, Data.pnsUpper, Data.effect, data]
  have tt := observational_true_true μ
  have tf := observational_true_false μ
  have ft := observational_false_true μ
  have ff := observational_false_false μ
  have e1 := experimental_true_eight μ
  have e0 := experimental_false_eight μ
  have value := pns_eight μ
  have total := total_eight μ
  have nonneg := fun individual => μ.2.1 individual
  have := nonneg (false, .never)
  have := nonneg (false, .helped)
  have := nonneg (false, .hurt)
  have := nonneg (false, .always)
  have := nonneg (true, .never)
  have := nonneg (true, .helped)
  have := nonneg (true, .hurt)
  have := nonneg (true, .always)
  refine ⟨max_le (max_le ?_ ?_) (max_le ?_ ?_), le_min (le_min ?_ ?_) (le_min ?_ ?_)⟩ <;>
    linarith

end Necessity

/-! ## The swap: what the data leave open -/

/-- The sign of a response type in the swap: helped and hurt gain, always and
never lose. -/
def swapSign : Response → ℝ
  | .helped => 1
  | .hurt => 1
  | .always => -1
  | .never => -1

/-- The weight moved in each group of natural treatment. -/
def swapAmount (treated untreated : ℝ) : Bool → ℝ
  | true => treated
  | false => untreated

/-- The weights after the swap. -/
def swapWeight (μ : Prob Individual) (treated untreated : ℝ) (individual : Individual) : ℝ :=
  μ.1 individual + swapAmount treated untreated individual.1 * swapSign individual.2

/-- **The swap**: among the naturally treated, move `treated` from always to
helped and from never to hurt; among the naturally untreated, move `untreated`
likewise.  A negative amount moves the other way. -/
noncomputable def swap (μ : Prob Individual) (treated untreated : ℝ)
    (valid : ∀ individual, 0 ≤ swapWeight μ treated untreated individual) : Prob Individual :=
  ⟨swapWeight μ treated untreated, valid, by
    rw [sum_individual]
    have total := total_eight μ
    simp only [swapWeight, swapAmount, swapSign]
    linarith⟩

section Swap

variable (μ : Prob Individual) (treated untreated : ℝ)
  (valid : ∀ individual, 0 ≤ swapWeight μ treated untreated individual)

theorem swap_apply (individual : Individual) :
    (swap μ treated untreated valid).1 individual = swapWeight μ treated untreated individual :=
  rfl

theorem mass_swap (event : Set Individual) :
    mass (swap μ treated untreated valid) event = mass μ event +
      treated * (event.indicator 1 (true, .helped) + event.indicator 1 (true, .hurt) -
        event.indicator 1 (true, .always) - event.indicator 1 (true, .never)) +
      untreated * (event.indicator 1 (false, .helped) + event.indicator 1 (false, .hurt) -
        event.indicator 1 (false, .always) - event.indicator 1 (false, .never)) := by
  rw [mass_eq_eight, mass_eq_eight]
  simp only [swap_apply, swapWeight, swapAmount, swapSign]
  ring

omit μ treated untreated valid in
/-- Individuals that show the same under a regime satisfy the same passive
queries under it. -/
theorem passive_sat_drawn_iff {imposed : Option Bool} {individual individual' : Individual}
    (same : realization imposed individual = realization imposed individual')
    (query : PassiveQuery) :
    (passive quantities).sat query (drawn imposed individual) ↔
      (passive quantities).sat query (drawn imposed individual') :=
  passive_sat_iff_of_agree everyIntervention quantities
    ⟨realizationMatch imposed [individual] [individual'],
      realizationMatch_isReductionBisimulation
        (fun other member => ⟨individual', List.mem_singleton_self _, by
          rw [List.mem_singleton.mp member]
          exact same.symm⟩)
        (fun other member => ⟨individual, List.mem_singleton_self _, by
          rw [List.mem_singleton.mp member]
          exact same⟩),
      Or.inr (Or.inr ⟨individual, individual', rfl, rfl, same⟩)⟩ query

omit μ treated untreated valid in
theorem indicator_eq_of_iff {event : Set Individual} {first second : Individual}
    (same : first ∈ event ↔ second ∈ event) :
    event.indicator (1 : Individual → ℝ) first = event.indicator 1 second := by
  by_cases member : first ∈ event
  · rw [Set.indicator_of_mem member, Set.indicator_of_mem (same.mp member)]
    rfl
  · rw [Set.indicator_of_notMem member,
      Set.indicator_of_notMem fun member' => member (same.mpr member')]

/-- **The swap changes no passive query under any regime.** -/
theorem passiveProbability_swap (imposed : Option Bool) (query : PassiveQuery) :
    passiveProbability (swap μ treated untreated valid) imposed query =
      passiveProbability μ imposed query := by
  have pair : ∀ first second : Individual,
      realization imposed first = realization imposed second →
        {ω | (passive quantities).sat query (drawn imposed ω)}.indicator (1 : Individual → ℝ)
            first =
          {ω | (passive quantities).sat query (drawn imposed ω)}.indicator 1 second :=
    fun first second same => indicator_eq_of_iff (passive_sat_drawn_iff same query)
  change mass (swap μ treated untreated valid)
      {ω | (passive quantities).sat query (drawn imposed ω)} =
    mass μ {ω | (passive quantities).sat query (drawn imposed ω)}
  rw [mass_swap]
  rcases imposed with _ | _ | _
  · rw [pair (true, .helped) (true, .always) rfl, pair (true, .hurt) (true, .never) rfl,
      pair (false, .helped) (false, .never) rfl, pair (false, .hurt) (false, .always) rfl]
    ring
  · rw [pair (true, .helped) (true, .never) rfl, pair (true, .hurt) (true, .always) rfl,
      pair (false, .helped) (false, .never) rfl, pair (false, .hurt) (false, .always) rfl]
    ring
  · rw [pair (true, .helped) (true, .always) rfl, pair (true, .hurt) (true, .never) rfl,
      pair (false, .helped) (false, .always) rfl, pair (false, .hurt) (false, .never) rfl]
    ring

/-- **The swap preserves weighted rung two.** -/
theorem weightedAgree_swap :
    WeightedAgree .intervention (swap μ treated untreated valid) μ :=
  fun imposed query => passiveProbability_swap μ treated untreated valid imposed query

/-- The experimental marginal is a passive query under the regime. -/
theorem experimental_eq_passiveProbability (population : Prob Individual) (treatment : Bool) :
    experimental population treatment =
      passiveProbability population (some treatment) (.dia () (.atom .effect)) := by
  rw [passiveProbability_eq_probability]
  rfl

omit μ treated untreated valid in
/-- **The data are rung-2 quantities**: populations agreeing at weighted rung two
have the same data. -/
theorem data_eq_of_weightedAgree {population population' : Prob Individual}
    (agree : WeightedAgree .intervention population population') :
    data population = data population' := by
  unfold data
  congr 1
  · funext treated effect
    exact agree none _
  · funext treatment
    rw [experimental_eq_passiveProbability, experimental_eq_passiveProbability]
    exact agree _ _

/-- **The swap preserves the data.** -/
theorem data_swap : data (swap μ treated untreated valid) = data μ :=
  data_eq_of_weightedAgree (weightedAgree_swap μ treated untreated valid)

theorem observational_swap (treatedValue effect : Bool) :
    observational (swap μ treated untreated valid) treatedValue effect =
      observational μ treatedValue effect :=
  passiveProbability_swap μ treated untreated valid none _

/-- **The swap moves PNS by the weight moved.** -/
theorem pns_swap : pns (swap μ treated untreated valid) = pns μ + treated + untreated := by
  rw [pns_eight, pns_eight]
  simp only [swap_apply, swapWeight, swapAmount, swapSign]
  ring

/-- **The swap moves PN by the weight moved among the treated.** -/
theorem pn_swap (possible : 0 < observational (swap μ treated untreated valid) true true) :
    pn (swap μ treated untreated valid) possible =
      (μ.1 (true, .helped) + treated) / observational μ true true := by
  rw [pn_eq, observational_swap, swap_apply]
  simp only [swapWeight, swapAmount, swapSign]
  ring_nf

/-- **The swap moves PS by the weight moved among the untreated.** -/
theorem ps_swap (possible : 0 < observational (swap μ treated untreated valid) false false) :
    ps (swap μ treated untreated valid) possible =
      (μ.1 (false, .helped) + untreated) / observational μ false false := by
  rw [ps_eq, observational_swap, swap_apply]
  simp only [swapWeight, swapAmount, swapSign]
  ring_nf

end Swap

/-! ## The data fiber is exactly the swaps -/

/-- **The populations with the data of `μ` are exactly the swaps of `μ`.** -/
theorem data_eq_iff_exists_swap {μ ν : Prob Individual} :
    data ν = data μ ↔ ∃ (treated untreated : ℝ)
      (valid : ∀ individual, 0 ≤ swapWeight μ treated untreated individual),
      ν = swap μ treated untreated valid := by
  constructor
  · intro same
    have tt : observational ν true true = observational μ true true :=
      congrFun (congrFun (congrArg Data.observed same) true) true
    have tf : observational ν true false = observational μ true false :=
      congrFun (congrFun (congrArg Data.observed same) true) false
    have ft : observational ν false true = observational μ false true :=
      congrFun (congrFun (congrArg Data.observed same) false) true
    have ff : observational ν false false = observational μ false false :=
      congrFun (congrFun (congrArg Data.observed same) false) false
    have e1 : experimental ν true = experimental μ true :=
      congrFun (congrArg Data.experimented same) true
    have e0 : experimental ν false = experimental μ false :=
      congrFun (congrArg Data.experimented same) false
    rw [observational_true_true, observational_true_true] at tt
    rw [observational_true_false, observational_true_false] at tf
    rw [observational_false_true, observational_false_true] at ft
    rw [observational_false_false, observational_false_false] at ff
    rw [experimental_true_eight, experimental_true_eight] at e1
    rw [experimental_false_eight, experimental_false_eight] at e0
    have weights : ∀ individual, ν.1 individual =
        swapWeight μ (ν.1 (true, .helped) - μ.1 (true, .helped))
          (ν.1 (false, .helped) - μ.1 (false, .helped)) individual := by
      rintro ⟨natural, response⟩
      cases natural <;> cases response <;> simp only [swapWeight, swapAmount, swapSign] <;>
        linarith
    exact ⟨_, _, fun individual => by rw [← weights individual]; exact ν.2.1 individual,
      Subtype.ext (funext weights)⟩
  · rintro ⟨treated, untreated, valid, rfl⟩
    exact data_swap μ treated untreated valid

/-- **On response types, weighted rung two is exactly the observational and
experimental data**: two populations agree on every passive query under every
regime exactly when they have the same Tian–Pearl data. -/
theorem weightedAgree_intervention_iff_data_eq {μ ν : Prob Individual} :
    WeightedAgree .intervention ν μ ↔ data ν = data μ := by
  constructor
  · exact data_eq_of_weightedAgree
  · intro same
    obtain ⟨treated, untreated, valid, rfl⟩ := data_eq_iff_exists_swap.mp same
    exact weightedAgree_swap μ treated untreated valid

/-! ## The admissible swaps -/

section Admissible

variable (μ : Prob Individual)

/-- The most the swap can move back from helped among the naturally treated. -/
noncomputable def treatedLow : ℝ := -min (μ.1 (true, .helped)) (μ.1 (true, .hurt))

/-- The most the swap can move to helped among the naturally treated. -/
noncomputable def treatedHigh : ℝ := min (μ.1 (true, .always)) (μ.1 (true, .never))

/-- The most the swap can move back from helped among the naturally untreated. -/
noncomputable def untreatedLow : ℝ := -min (μ.1 (false, .helped)) (μ.1 (false, .hurt))

/-- The most the swap can move to helped among the naturally untreated. -/
noncomputable def untreatedHigh : ℝ := min (μ.1 (false, .always)) (μ.1 (false, .never))

theorem treatedLow_le_zero : treatedLow μ ≤ 0 :=
  neg_nonpos.mpr (le_min (μ.2.1 _) (μ.2.1 _))

theorem zero_le_treatedHigh : 0 ≤ treatedHigh μ := le_min (μ.2.1 _) (μ.2.1 _)

theorem untreatedLow_le_zero : untreatedLow μ ≤ 0 :=
  neg_nonpos.mpr (le_min (μ.2.1 _) (μ.2.1 _))

theorem zero_le_untreatedHigh : 0 ≤ untreatedHigh μ := le_min (μ.2.1 _) (μ.2.1 _)

/-- **A swap within the admissible amounts keeps every weight nonnegative.** -/
theorem swap_valid {treated untreated : ℝ}
    (treatedRange : treatedLow μ ≤ treated ∧ treated ≤ treatedHigh μ)
    (untreatedRange : untreatedLow μ ≤ untreated ∧ untreated ≤ untreatedHigh μ) :
    ∀ individual, 0 ≤ swapWeight μ treated untreated individual := by
  obtain ⟨tl, th⟩ := treatedRange
  obtain ⟨ul, uh⟩ := untreatedRange
  unfold treatedLow treatedHigh untreatedLow untreatedHigh at *
  have a1 := min_le_left (μ.1 (true, .helped)) (μ.1 (true, .hurt))
  have a2 := min_le_right (μ.1 (true, .helped)) (μ.1 (true, .hurt))
  have a3 := min_le_left (μ.1 (true, .always)) (μ.1 (true, .never))
  have a4 := min_le_right (μ.1 (true, .always)) (μ.1 (true, .never))
  have b1 := min_le_left (μ.1 (false, .helped)) (μ.1 (false, .hurt))
  have b2 := min_le_right (μ.1 (false, .helped)) (μ.1 (false, .hurt))
  have b3 := min_le_left (μ.1 (false, .always)) (μ.1 (false, .never))
  have b4 := min_le_right (μ.1 (false, .always)) (μ.1 (false, .never))
  rintro ⟨natural, response⟩
  cases natural <;> cases response <;> simp only [swapWeight, swapAmount, swapSign] <;> linarith

/-- **The lower end of the combined PNS interval** is PNS after the least
admissible swap. -/
theorem pnsLower_eq : (data μ).pnsLower = pns μ + treatedLow μ + untreatedLow μ := by
  simp only [Data.pnsLower, Data.effect, data, treatedLow, untreatedLow]
  have tt := observational_true_true μ
  have ft := observational_false_true μ
  have e1 := experimental_true_eight μ
  have e0 := experimental_false_eight μ
  have value := pns_eight μ
  rcases le_total (μ.1 (true, .helped)) (μ.1 (true, .hurt)) with t | t <;>
    rcases le_total (μ.1 (false, .helped)) (μ.1 (false, .hurt)) with u | u
  · rw [min_eq_left t, min_eq_left u]
    refine le_antisymm (max_le (max_le (by linarith) (by linarith))
      (max_le (by linarith) (by linarith))) (le_max_of_le_left (le_max_of_le_left (by linarith)))
  · rw [min_eq_left t, min_eq_right u]
    refine le_antisymm (max_le (max_le (by linarith) (by linarith))
      (max_le (by linarith) (by linarith))) (le_max_of_le_right (le_max_of_le_right (by linarith)))
  · rw [min_eq_right t, min_eq_left u]
    refine le_antisymm (max_le (max_le (by linarith) (by linarith))
      (max_le (by linarith) (by linarith))) (le_max_of_le_right (le_max_of_le_left (by linarith)))
  · rw [min_eq_right t, min_eq_right u]
    refine le_antisymm (max_le (max_le (by linarith) (by linarith))
      (max_le (by linarith) (by linarith))) (le_max_of_le_left (le_max_of_le_right (by linarith)))

/-- **The upper end of the combined PNS interval** is PNS after the greatest
admissible swap. -/
theorem pnsUpper_eq : (data μ).pnsUpper = pns μ + treatedHigh μ + untreatedHigh μ := by
  simp only [Data.pnsUpper, data, treatedHigh, untreatedHigh]
  have tt := observational_true_true μ
  have tf := observational_true_false μ
  have ft := observational_false_true μ
  have ff := observational_false_false μ
  have e1 := experimental_true_eight μ
  have e0 := experimental_false_eight μ
  have value := pns_eight μ
  have total := total_eight μ
  rcases le_total (μ.1 (true, .always)) (μ.1 (true, .never)) with t | t <;>
    rcases le_total (μ.1 (false, .always)) (μ.1 (false, .never)) with u | u
  · rw [min_eq_left t, min_eq_left u]
    refine le_antisymm (min_le_of_left_le (min_le_of_left_le (by linarith)))
      (le_min (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))
  · rw [min_eq_left t, min_eq_right u]
    refine le_antisymm (min_le_of_right_le (min_le_of_left_le (by linarith)))
      (le_min (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))
  · rw [min_eq_right t, min_eq_left u]
    refine le_antisymm (min_le_of_right_le (min_le_of_right_le (by linarith)))
      (le_min (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))
  · rw [min_eq_right t, min_eq_right u]
    refine le_antisymm (min_le_of_left_le (min_le_of_right_le (by linarith)))
      (le_min (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith)))

end Admissible

/-! ## Tightness: the identified sets -/

section Tightness

variable (μ : Prob Individual)

/-- **The combined PNS bounds are sharp**: the PNS values of the populations with
the data of `μ` are exactly the combined interval, every value realised by a
swap of `μ`. -/
theorem pns_identifiedSet :
    {v | ∃ ν : Prob Individual, data ν = data μ ∧ pns ν = v} =
      Set.Icc (data μ).pnsLower (data μ).pnsUpper := by
  ext v
  constructor
  · rintro ⟨ν, same, rfl⟩
    rw [← same]
    exact pns_combined_bounds ν
  · rintro ⟨lower, upper⟩
    rw [pnsLower_eq] at lower
    rw [pnsUpper_eq] at upper
    have tl := treatedLow_le_zero μ
    have th := zero_le_treatedHigh μ
    have ul := untreatedLow_le_zero μ
    have uh := zero_le_untreatedHigh μ
    set gap := v - pns μ
    set moved := max (treatedLow μ) (gap - untreatedHigh μ)
    have first : treatedLow μ ≤ gap - untreatedLow μ := by linarith
    have second : gap - untreatedHigh μ ≤ gap - untreatedLow μ := by linarith
    have movedLe : moved ≤ gap - untreatedLow μ := max_le first second
    have movedGe : gap - untreatedHigh μ ≤ moved := le_max_right _ _
    have valid := swap_valid μ (treated := moved) (untreated := gap - moved)
      ⟨le_max_left _ _, max_le (by linarith) (by linarith)⟩
      ⟨by linarith, by linarith⟩
    refine ⟨swap μ moved (gap - moved) valid, data_swap μ _ _ valid, ?_⟩
    rw [pns_swap]
    ring

/-- **Both ends of the combined PNS interval are attained.** -/
theorem pns_bounds_attained :
    ∃ low high : Prob Individual,
      (data low = data μ ∧ pns low = (data μ).pnsLower) ∧
        (data high = data μ ∧ pns high = (data μ).pnsUpper) := by
  obtain ⟨lower, upper⟩ := pns_combined_bounds μ
  have lowMember : (data μ).pnsLower ∈
      {v | ∃ ν : Prob Individual, data ν = data μ ∧ pns ν = v} := by
    rw [pns_identifiedSet]
    exact ⟨le_rfl, lower.trans upper⟩
  have highMember : (data μ).pnsUpper ∈
      {v | ∃ ν : Prob Individual, data ν = data μ ∧ pns ν = v} := by
    rw [pns_identifiedSet]
    exact ⟨lower.trans upper, le_rfl⟩
  obtain ⟨low, lowData, lowValue⟩ := lowMember
  obtain ⟨high, highData, highValue⟩ := highMember
  exact ⟨low, high, ⟨lowData, lowValue⟩, ⟨highData, highValue⟩⟩

/-- **The PN bounds are sharp**: the PN values of the populations with the data
of `μ` are exactly Tian–Pearl's interval, every value realised by a swap of
`μ` among the naturally treated. -/
theorem pn_identifiedSet (possible : 0 < observational μ true true) :
    {v | ∃ (ν : Prob Individual) (possible' : 0 < observational ν true true),
        data ν = data μ ∧ pn ν possible' = v} =
      Set.Icc (data μ).pnLower (data μ).pnUpper := by
  ext v
  constructor
  · rintro ⟨ν, possible', same, rfl⟩
    rw [← same]
    exact pn_bounds ν possible'
  · rintro ⟨lower, upper⟩
    simp only [Data.pnLower, Data.pnUpper, Data.effect, data] at lower upper
    have v_nonneg : 0 ≤ v := (le_max_left _ _).trans lower
    have gain := (div_le_iff₀ possible).mp ((le_max_right _ _).trans lower)
    have v_le_one : v ≤ 1 := upper.trans (min_le_left _ _)
    have loss := (le_div_iff₀ possible).mp (upper.trans (min_le_right _ _))
    have scaled : v * observational μ true true ≤ observational μ true true :=
      mul_le_of_le_one_left possible.le v_le_one
    have scaled_nonneg : 0 ≤ v * observational μ true true := mul_nonneg v_nonneg possible.le
    have tt := observational_true_true μ
    have ft := observational_false_true μ
    have ff := observational_false_false μ
    have e0 := experimental_false_eight μ
    have total := total_eight μ
    set moved := v * observational μ true true - μ.1 (true, .helped)
    have valid := swap_valid μ (treated := moved) (untreated := 0)
      ⟨neg_le.mpr (le_min (by linarith) (by linarith)), le_min (by linarith) (by linarith)⟩
      ⟨untreatedLow_le_zero μ, zero_le_untreatedHigh μ⟩
    have possible' : 0 < observational (swap μ moved 0 valid) true true := by
      rw [observational_swap]
      exact possible
    refine ⟨swap μ moved 0 valid, possible', data_swap μ _ _ valid, ?_⟩
    rw [pn_swap]
    field_simp
    ring

/-- **The PS bounds are sharp**, every value realised by a swap of `μ` among
the naturally untreated. -/
theorem ps_identifiedSet (possible : 0 < observational μ false false) :
    {v | ∃ (ν : Prob Individual) (possible' : 0 < observational ν false false),
        data ν = data μ ∧ ps ν possible' = v} =
      Set.Icc (data μ).psLower (data μ).psUpper := by
  ext v
  constructor
  · rintro ⟨ν, possible', same, rfl⟩
    rw [← same]
    exact ps_bounds ν possible'
  · rintro ⟨lower, upper⟩
    simp only [Data.psLower, Data.psUpper, Data.effect, data] at lower upper
    have v_nonneg : 0 ≤ v := (le_max_left _ _).trans lower
    have gain := (div_le_iff₀ possible).mp ((le_max_right _ _).trans lower)
    have v_le_one : v ≤ 1 := upper.trans (min_le_left _ _)
    have loss := (le_div_iff₀ possible).mp (upper.trans (min_le_right _ _))
    have scaled : v * observational μ false false ≤ observational μ false false :=
      mul_le_of_le_one_left possible.le v_le_one
    have scaled_nonneg : 0 ≤ v * observational μ false false := mul_nonneg v_nonneg possible.le
    have tt := observational_true_true μ
    have ft := observational_false_true μ
    have ff := observational_false_false μ
    have e1 := experimental_true_eight μ
    set moved := v * observational μ false false - μ.1 (false, .helped)
    have valid := swap_valid μ (treated := 0) (untreated := moved)
      ⟨treatedLow_le_zero μ, zero_le_treatedHigh μ⟩
      ⟨neg_le.mpr (le_min (by linarith) (by linarith)), le_min (by linarith) (by linarith)⟩
    have possible' : 0 < observational (swap μ 0 moved valid) false false := by
      rw [observational_swap]
      exact possible
    refine ⟨swap μ 0 moved valid, possible', data_swap μ _ _ valid, ?_⟩
    rw [ps_swap]
    field_simp
    ring

/-- **Both ends of the PN interval are attained.** -/
theorem pn_bounds_attained (possible : 0 < observational μ true true) :
    ∃ (low high : Prob Individual) (lowPossible : 0 < observational low true true)
      (highPossible : 0 < observational high true true),
      (data low = data μ ∧ pn low lowPossible = (data μ).pnLower) ∧
        (data high = data μ ∧ pn high highPossible = (data μ).pnUpper) := by
  obtain ⟨lower, upper⟩ := pn_bounds μ possible
  have lowMember : (data μ).pnLower ∈ {v | ∃ (ν : Prob Individual)
      (possible' : 0 < observational ν true true), data ν = data μ ∧ pn ν possible' = v} := by
    rw [pn_identifiedSet μ possible]
    exact ⟨le_rfl, lower.trans upper⟩
  have highMember : (data μ).pnUpper ∈ {v | ∃ (ν : Prob Individual)
      (possible' : 0 < observational ν true true), data ν = data μ ∧ pn ν possible' = v} := by
    rw [pn_identifiedSet μ possible]
    exact ⟨lower.trans upper, le_rfl⟩
  obtain ⟨low, lowPossible, lowData, lowValue⟩ := lowMember
  obtain ⟨high, highPossible, highData, highValue⟩ := highMember
  exact ⟨low, high, lowPossible, highPossible, ⟨lowData, lowValue⟩, ⟨highData, highValue⟩⟩

/-- **Both ends of the PS interval are attained.** -/
theorem ps_bounds_attained (possible : 0 < observational μ false false) :
    ∃ (low high : Prob Individual) (lowPossible : 0 < observational low false false)
      (highPossible : 0 < observational high false false),
      (data low = data μ ∧ ps low lowPossible = (data μ).psLower) ∧
        (data high = data μ ∧ ps high highPossible = (data μ).psUpper) := by
  obtain ⟨lower, upper⟩ := ps_bounds μ possible
  have lowMember : (data μ).psLower ∈ {v | ∃ (ν : Prob Individual)
      (possible' : 0 < observational ν false false), data ν = data μ ∧ ps ν possible' = v} := by
    rw [ps_identifiedSet μ possible]
    exact ⟨le_rfl, lower.trans upper⟩
  have highMember : (data μ).psUpper ∈ {v | ∃ (ν : Prob Individual)
      (possible' : 0 < observational ν false false), data ν = data μ ∧ ps ν possible' = v} := by
    rw [ps_identifiedSet μ possible]
    exact ⟨lower.trans upper, le_rfl⟩
  obtain ⟨low, lowPossible, lowData, lowValue⟩ := lowMember
  obtain ⟨high, highPossible, highData, highValue⟩ := highMember
  exact ⟨low, high, lowPossible, highPossible, ⟨lowData, lowValue⟩, ⟨highData, highValue⟩⟩

end Tightness

/-! ## Monotonicity identifies PN and PS -/

section Monotone

variable (μ : Prob Individual)

theorem hurt_eq_zero_of_noHarm (noHarm : NoHarm μ) :
    μ.1 (true, .hurt) = 0 ∧ μ.1 (false, .hurt) = 0 := by
  have harm := harmProbability_eight μ
  rw [NoHarm] at noHarm
  have first := μ.2.1 (true, .hurt)
  have second := μ.2.1 (false, .hurt)
  constructor <;> linarith

/-- **Under monotonicity PN is identified**:
`PN = (P(y) − P(y_0)) / P(x, y)`, the lower bound. -/
theorem pn_eq_of_noHarm (possible : 0 < observational μ true true) (noHarm : NoHarm μ) :
    pn μ possible = ((data μ).effect - (data μ).experimented false) / (data μ).observed true true := by
  rw [pn_eq]
  simp only [Data.effect, data]
  obtain ⟨treatedHurt, untreatedHurt⟩ := hurt_eq_zero_of_noHarm μ noHarm
  rw [observational_true_true, observational_false_true, experimental_false_eight,
    treatedHurt, untreatedHurt]
  ring_nf

/-- **Under monotonicity PS is identified**:
`PS = (P(y_1) − P(y)) / P(x', y')`, the lower bound. -/
theorem ps_eq_of_noHarm (possible : 0 < observational μ false false) (noHarm : NoHarm μ) :
    ps μ possible = ((data μ).experimented true - (data μ).effect) / (data μ).observed false false := by
  rw [ps_eq]
  simp only [Data.effect, data]
  obtain ⟨treatedHurt, untreatedHurt⟩ := hurt_eq_zero_of_noHarm μ noHarm
  rw [observational_true_true, observational_false_true, experimental_true_eight,
    untreatedHurt]
  ring_nf

theorem pn_identified_of_noHarm {ν : Prob Individual} (possible : 0 < observational μ true true)
    (possible' : 0 < observational ν true true) (noHarm : NoHarm μ) (noHarm' : NoHarm ν)
    (same : data μ = data ν) : pn μ possible = pn ν possible' := by
  rw [pn_eq_of_noHarm μ possible noHarm, pn_eq_of_noHarm ν possible' noHarm', same]

theorem ps_identified_of_noHarm {ν : Prob Individual} (possible : 0 < observational μ false false)
    (possible' : 0 < observational ν false false) (noHarm : NoHarm μ) (noHarm' : NoHarm ν)
    (same : data μ = data ν) : ps μ possible = ps ν possible' := by
  rw [ps_eq_of_noHarm μ possible noHarm, ps_eq_of_noHarm ν possible' noHarm', same]

end Monotone

/-! ## Exogeneity: observational data identify the experiments -/

section Exogeneity

variable (μ : Prob Individual)

/-- `P(X = x)`: the share taking treatment `x` when nobody intervenes. -/
noncomputable def share (treated : Bool) : ℝ :=
  observational μ treated true + observational μ treated false

/-- **Exogeneity**: the natural treatment is independent of the response type;
each weight is the share of its treatment group times the share of its
response type. -/
def Exogenous : Prop :=
  ∀ (natural : Bool) (response : Response), μ.1 (natural, response) =
    (μ.1 (natural, .never) + μ.1 (natural, .helped) + μ.1 (natural, .hurt) +
      μ.1 (natural, .always)) * (μ.1 (false, response) + μ.1 (true, response))

/-- **Under exogeneity the observational cell is the share times the
experimental marginal**: `P(x, y) = P(x) · P(y_x)`. -/
theorem observational_eq_share_mul_of_exogenous (exogenous : Exogenous μ) (treated : Bool) :
    observational μ treated true = share μ treated * experimental μ treated := by
  unfold share
  cases treated
  · rw [observational_false_true, observational_false_false, experimental_false_eight]
    have hurt := exogenous false .hurt
    have always := exogenous false .always
    linear_combination hurt + always
  · rw [observational_true_true, observational_true_false, experimental_true_eight]
    have helped := exogenous true .helped
    have always := exogenous true .always
    linear_combination helped + always

/-- **Under exogeneity the experiments are identified by observation**:
`P(y_x) = P(y | x)`. -/
theorem experimental_eq_of_exogenous (exogenous : Exogenous μ) (treated : Bool)
    (positive : 0 < share μ treated) :
    experimental μ treated = observational μ treated true / share μ treated := by
  rw [observational_eq_share_mul_of_exogenous μ exogenous, mul_div_cancel_left₀ _ positive.ne']

theorem share_add_share : share μ true + share μ false = 1 := by
  unfold share
  rw [observational_true_true, observational_true_false, observational_false_true,
    observational_false_false]
  linarith [total_eight μ]

/-- **Under exogeneity and monotonicity PN is the excess risk ratio**,
`PN = 1 − P(y | x') / P(y | x)`, identified by observational data alone. -/
theorem pn_eq_excessRiskRatio (possible : 0 < observational μ true true) (exogenous : Exogenous μ)
    (noHarm : NoHarm μ) (untreatedShare : 0 < share μ false) :
    pn μ possible = 1 - (observational μ false true / share μ false) /
      (observational μ true true / share μ true) := by
  have treatedShare : 0 < share μ true := by
    unfold share
    rw [observational_true_false]
    linarith [μ.2.1 (true, .never), μ.2.1 (true, .hurt)]
  have total := share_add_share μ
  rw [pn_eq_of_noHarm μ possible noHarm]
  simp only [Data.effect, data]
  rw [experimental_eq_of_exogenous μ exogenous false untreatedShare]
  field_simp
  linear_combination (observational μ false true) * total

/-- **Under exogeneity and monotonicity PS is identified by observation**:
`PS = (P(y | x) − P(y | x')) / P(y' | x')`. -/
theorem ps_eq_of_exogenous (possible : 0 < observational μ false false) (exogenous : Exogenous μ)
    (noHarm : NoHarm μ) (treatedShare : 0 < share μ true) :
    ps μ possible = (observational μ true true / share μ true -
      observational μ false true / share μ false) /
        (observational μ false false / share μ false) := by
  have untreatedShare : 0 < share μ false := by
    unfold share
    rw [observational_false_true]
    linarith [μ.2.1 (false, .hurt), μ.2.1 (false, .always)]
  have total := share_add_share μ
  rw [ps_eq_of_noHarm μ possible noHarm]
  simp only [Data.effect, data]
  rw [experimental_eq_of_exogenous μ exogenous true treatedShare]
  have shareFalse : share μ false = observational μ false true + observational μ false false := rfl
  field_simp
  rw [shareFalse] at total ⊢
  linear_combination (-(observational μ true true)) * total

end Exogeneity

/-! ## Controls -/

/-- The weights of the self-selected population. -/
noncomputable def selfSelectedWeight : Individual → ℝ
  | (true, .helped) => 1 / 2
  | (false, .hurt) => 1 / 2
  | _ => 0

/-- **Self-selection**: half take the treatment and are helped by it, half
decline it and are hurt by it. -/
noncomputable def selfSelected : Prob Individual :=
  ⟨selfSelectedWeight,
    fun individual => by
      obtain ⟨natural, response⟩ := individual
      cases natural <;> cases response <;> simp only [selfSelectedWeight] <;> norm_num, by
      rw [sum_individual]
      simp only [selfSelectedWeight]
      norm_num⟩

theorem selfSelected_apply (individual : Individual) :
    selfSelected.1 individual = selfSelectedWeight individual :=
  rfl

theorem observational_selfSelected_true_true : observational selfSelected true true = 1 / 2 := by
  rw [observational_true_true]
  simp only [selfSelected_apply, selfSelectedWeight]
  norm_num

/-- **Observational data identify what experiments cannot.**  The experiments on
the self-selected population show `P(y_1) = P(y_0) = 1/2`, which leaves PNS
open on `[0, 1/2]`: the population half always and half never showing the
effect has the same experimental marginals and PNS `0`.  Together with the
observational record, the combined bounds pin PNS to `1/2` and PN to `1`. -/
theorem selfSelection_control :
    experimental selfSelected true = 1 / 2 ∧ experimental selfSelected false = 1 / 2 ∧
      experimental weightedFixed true = 1 / 2 ∧ experimental weightedFixed false = 1 / 2 ∧
      pns weightedFixed = 0 ∧
      (data selfSelected).pnsLower = 1 / 2 ∧ (data selfSelected).pnsUpper = 1 / 2 ∧
      pns selfSelected = 1 / 2 ∧
      (data selfSelected).pnLower = 1 ∧
      pn selfSelected (by rw [observational_selfSelected_true_true]; norm_num) = 1 := by
  have e1 : experimental selfSelected true = 1 / 2 := by
    rw [experimental_true_eight]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have e0 : experimental selfSelected false = 1 / 2 := by
    rw [experimental_false_eight]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have tt := observational_selfSelected_true_true
  have tf : observational selfSelected true false = 0 := by
    rw [observational_true_false]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have ft : observational selfSelected false true = 1 / 2 := by
    rw [observational_false_true]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have ff : observational selfSelected false false = 0 := by
    rw [observational_false_false]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have value : pns selfSelected = 1 / 2 := by
    rw [pns_eight]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  refine ⟨e1, e0, ?_, ?_, ?_, ?_, ?_, value, ?_, ?_⟩
  · rw [weightedFixed, experimental_untreated_true]
    norm_num
  · rw [weightedFixed, experimental_untreated_false]
    norm_num
  · rw [weightedFixed, pns_untreated]
  · simp only [Data.pnsLower, Data.effect, data]
    rw [e1, e0, tt, ft]
    norm_num
  · simp only [Data.pnsUpper, data]
    rw [e1, e0, tt, tf, ft, ff]
    norm_num
  · simp only [Data.pnLower, Data.effect, data]
    rw [e0, tt, ft]
    norm_num
  · rw [pn_eq, tt]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num

/-- **Without exogeneity observation does not identify the experiments.**  In
the self-selected population everyone who takes the treatment shows the
effect, `P(y | x) = 1`, while treating everyone shows it half the time,
`P(y_x) = 1/2`; so the population is not exogenous. -/
theorem confounding_control :
    observational selfSelected true true / share selfSelected true = 1 ∧
      experimental selfSelected true = 1 / 2 ∧ ¬ Exogenous selfSelected := by
  have conditional : observational selfSelected true true / share selfSelected true = 1 := by
    unfold share
    rw [observational_true_true, observational_true_false]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have experiment : experimental selfSelected true = 1 / 2 := selfSelection_control.1
  refine ⟨conditional, experiment, fun exogenous => ?_⟩
  have positive : 0 < share selfSelected true := by
    unfold share
    rw [observational_true_true, observational_true_false]
    simp only [selfSelected_apply, selfSelectedWeight]
    norm_num
  have same := experimental_eq_of_exogenous selfSelected exogenous true positive
  rw [conditional, experiment] at same
  norm_num at same

/-- The uniform population over the eight individuals. -/
noncomputable def uniformPopulation : Prob Individual :=
  ⟨fun _ => 1 / 8, fun _ => by norm_num, by
    rw [sum_individual]
    norm_num⟩

theorem uniformPopulation_apply (individual : Individual) :
    uniformPopulation.1 individual = 1 / 8 :=
  rfl

theorem uniform_swap_valid :
    ∀ individual, 0 ≤ swapWeight uniformPopulation (1 / 8) 0 individual := by
  rintro ⟨natural, response⟩
  cases natural <;> cases response <;>
    simp only [swapWeight, swapAmount, swapSign, uniformPopulation_apply] <;> norm_num

/-- **Weighted rung two does not identify PN.**  The uniform population and its
swap moving `1/8` among the treated agree at weighted rung two, and their PN
are `1/2` and `1`. -/
theorem rungTwo_does_not_identify :
    WeightedAgree .intervention (swap uniformPopulation (1 / 8) 0 uniform_swap_valid)
        uniformPopulation ∧
      pn uniformPopulation (by rw [observational_true_true]; norm_num [uniformPopulation_apply]) =
        1 / 2 ∧
      pn (swap uniformPopulation (1 / 8) 0 uniform_swap_valid)
          (by rw [observational_swap, observational_true_true]; norm_num [uniformPopulation_apply]) =
        1 := by
  refine ⟨weightedAgree_swap _ _ _ _, ?_, ?_⟩
  · rw [pn_eq, observational_true_true]
    simp only [uniformPopulation_apply]
    norm_num
  · rw [pn_swap, observational_true_true]
    simp only [uniformPopulation_apply]
    norm_num

end Mettapedia.GSLT.Causality.ProbabilitiesOfCausation
