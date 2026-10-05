import Mettapedia.GSLT.Distinction.Probabilistic.Causal
import Mettapedia.GSLT.Causality.ProbabilitiesOfCausation

/-!
# Abduction over several random steps, and rung-3 identification

A noisy population (`Causal.NoisyPopulation`) takes two random steps: a unit is
drawn, then its response, an individual with a natural treatment and a
response type, is drawn from the unit's law.  This module abducts over both
steps and states which counterfactual quantities are identified from which
data.

**Abduction over the path** (`pathLaw`, `abducePath`).  The law of the path
(unit, individual) is `BayesianInference.joint` of the draw law and the
response laws; abduction conditions it on the record observed at the settled
individual.  PN and PS of the noisy population (`pn`, `ps`) abduce the path,
intervene at the settled individual, and predict; they are PN and PS of the
marginal population (`pn_eq_marginal`, `ps_eq_marginal`), as PNS is
(`Causal.NoisyPopulation.pns_eq_marginal`).  So the Tian–Pearl combined bounds,
their tightness and identification under monotonicity
(`ProbabilitiesOfCausation`) hold for the pooled data of every noisy population
(`pn_bounds`, `ps_bounds`, `pns_combined_bounds`); the pooled data leave PNS
open on exactly the combined interval (`pns_identifiedSet`).  Monotonicity of
the noisy population is monotonicity of every unit that can be drawn
(`noHarm_marginal_iff`), and with it the pooled data identify PN
(`pn_identified_of_noHarm`).  The posterior of the first
step alone (`unitPosterior`) is Bayes over the units, with the probability of
the record under each unit's response as likelihood; it is the unit marginal
of the abduced path (`unitPosterior_eq_sum`).

**What unit-resolved data identify.**  When the unit drawn is recorded, the data
can be resolved by unit: the response law of each unit at weighted rung two.
* *One random step identifies rung three* (`ofTypes_identified`).  If each
  unit responds deterministically, the unit-resolved rung-2 data determine each
  unit's individual, hence the whole law, hence every counterfactual query, PN,
  PS and PNS (`ofTypes_counterfactual`).  A deterministic individual shows its
  natural treatment left alone and each potential outcome under its regime
  (`eq_of_point_weightedAgree`).
* *A second random step breaks it* (`random_step_breaks_identification`).  A
  single unit responding helped or hurt with probability one half each, and one
  responding always or never likewise, have the same unit-resolved rung-2 data
  (one is a swap of the other), and their PNS are `1/2` and `0`, their PS `1`
  and `0`.  Both units pass the experimental check `P(y_0) ≤ P(y_1)`, which
  for a deterministic unit is monotonicity
  (`noHarm_iff_experimental_le_of_point`); with the random step it no longer
  is.
* *The counterfactual that re-draws the response* (`redrawnPN`): abduce only
  the unit and withhold treatment before the response step, which is then
  drawn afresh.  It is identified by the unit-resolved data
  (`redrawnPN_identified`), and it is not PN: on the self-selected population
  as a single unit PN is `1` and the re-drawn quantity `1/2`
  (`redrawn_differs`).  Where the intervention sits relative to the random
  steps decides the query.
* *Recording the unit narrows the bounds* (`unitResolved_pns_bounds`,
  `recording_the_unit_identifies`): PNS lies between the draw-weighted sums of
  the units' combined bounds.  Two units, one helped or always and one hurt or
  never, give PNS `1/4` for every noisy population with their draw and unit
  data, while the pooled data are those of the half helped, half hurt
  population and of the half always, half never one, with PNS `1/2` and `0`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes
open Mettapedia.GSLT.Causality.WeightedObservers
open Mettapedia.GSLT.Causality.WeightedResponseTypes
open Mettapedia.GSLT.Causality.ProbabilitiesOfCausation
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference

namespace Causal.NoisyPopulation

variable {U : Type*} [Fintype U] (N : NoisyPopulation U)

/-! ## The laws of the two random steps -/

/-- The law of the first random step: the unit drawn. -/
def drawLaw : Prob U :=
  ⟨N.drawWeight, N.draw_distribution.nonneg, N.draw_distribution.sum_eq_one⟩

/-- The law of the second random step at a unit: its response. -/
def responseLaw (unit : U) : Prob Individual :=
  ⟨N.respondWeight unit, (N.respond_distribution unit).nonneg,
    (N.respond_distribution unit).sum_eq_one⟩

/-- **The law of the path** through both random steps. -/
noncomputable def pathLaw : Prob (U × Individual) :=
  joint N.drawLaw N.responseLaw

/-- The marginal population is the observation law of the two steps. -/
theorem observationLaw_eq_marginal : observationLaw N.drawLaw N.responseLaw = N.marginal :=
  Subtype.ext rfl

/-- The probability that the settled individual lies in an event is its
probability under the marginal population. -/
theorem mass_pathLaw_snd (event : Set Individual) :
    mass N.pathLaw (Prod.snd ⁻¹' event) = mass N.marginal event := by
  rw [mass_eq_sum, mass_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun individual _ => ?_
  change ∑ unit, N.drawWeight unit * N.respondWeight unit individual *
      (Prod.snd ⁻¹' event).indicator 1 (unit, individual) =
    (∑ unit, N.drawWeight unit * N.respondWeight unit individual) * event.indicator 1 individual
  rw [Finset.sum_mul]
  rfl

/-- The probability of an event under one unit's response, averaged over the
draw, is its probability under the marginal population. -/
theorem evidence_responses (event : Set Individual) :
    evidence N.drawLaw (fun unit => mass (N.responseLaw unit) event) = mass N.marginal event := by
  unfold evidence
  simp only [mass_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun individual _ => ?_
  change ∑ unit, N.drawWeight unit * (N.respondWeight unit individual *
      event.indicator 1 individual) =
    (∑ unit, N.drawWeight unit * N.respondWeight unit individual) * event.indicator 1 individual
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun unit _ => by ring

/-! ## Abduction over both steps -/

/-- **Abduction over the path**: the posterior law of (unit, individual) given
the record observed at the settled individual. -/
noncomputable def abducePath (treated effect : Bool)
    (possible : 0 < observational N.marginal treated effect) : Prob (U × Individual) :=
  condition N.pathLaw (Prod.snd ⁻¹' record treated effect) (by
    rw [mass_pathLaw_snd, ← observational_eq_mass]
    exact possible)

/-- **PN of a noisy population**: abduce the path from "treated, effect shown",
withhold treatment at the settled individual, predict no effect. -/
noncomputable def pn (possible : 0 < observational N.marginal true true) : ℝ :=
  chance ladder (N.abducePath true true possible) (fun path => drawn none path.2)
    (noEffectUnder false)

/-- **PS of a noisy population**: abduce the path from "untreated, no effect",
treat at the settled individual, predict the effect. -/
noncomputable def ps (possible : 0 < observational N.marginal false false) : ℝ :=
  chance ladder (N.abducePath false false possible) (fun path => drawn none path.2)
    (effectUnder true)

/-- **PN of a noisy population is PN of its marginal population.** -/
theorem pn_eq_marginal (possible : 0 < observational N.marginal true true) :
    N.pn possible = Causality.ProbabilitiesOfCausation.pn N.marginal possible := by
  unfold pn Causality.ProbabilitiesOfCausation.pn probability abducePath abduce
  rw [chance_condition, chance_condition]
  have preimage : Prod.snd ⁻¹' record true true ∩
      {path : U × Individual | ladder.sat (noEffectUnder false) (drawn none path.2)} =
        Prod.snd ⁻¹' (record true true ∩
          {individual | ladder.sat (noEffectUnder false) (drawn none individual)}) :=
    rfl
  rw [preimage, mass_pathLaw_snd, mass_pathLaw_snd]

/-- **PS of a noisy population is PS of its marginal population.** -/
theorem ps_eq_marginal (possible : 0 < observational N.marginal false false) :
    N.ps possible = Causality.ProbabilitiesOfCausation.ps N.marginal possible := by
  unfold ps Causality.ProbabilitiesOfCausation.ps probability abducePath abduce
  rw [chance_condition, chance_condition]
  have preimage : Prod.snd ⁻¹' record false false ∩
      {path : U × Individual | ladder.sat (effectUnder true) (drawn none path.2)} =
        Prod.snd ⁻¹' (record false false ∩
          {individual | ladder.sat (effectUnder true) (drawn none individual)}) :=
    rfl
  rw [preimage, mass_pathLaw_snd, mass_pathLaw_snd]

/-- **Tian–Pearl's bounds on PN of a noisy population**, from its pooled
data. -/
theorem pn_bounds (possible : 0 < observational N.marginal true true) :
    (data N.marginal).pnLower ≤ N.pn possible ∧ N.pn possible ≤ (data N.marginal).pnUpper := by
  rw [pn_eq_marginal]
  exact Causality.ProbabilitiesOfCausation.pn_bounds N.marginal possible

/-- **Tian–Pearl's bounds on PS of a noisy population.** -/
theorem ps_bounds (possible : 0 < observational N.marginal false false) :
    (data N.marginal).psLower ≤ N.ps possible ∧ N.ps possible ≤ (data N.marginal).psUpper := by
  rw [ps_eq_marginal]
  exact Causality.ProbabilitiesOfCausation.ps_bounds N.marginal possible

/-- **Tian–Pearl's combined bounds on PNS of a noisy population.** -/
theorem pns_combined_bounds [DecidableEq U] :
    (data N.marginal).pnsLower ≤ N.pns ∧ N.pns ≤ (data N.marginal).pnsUpper := by
  rw [pns_eq_marginal]
  exact Causality.ProbabilitiesOfCausation.pns_combined_bounds N.marginal

/-- **The abduced unit**: Bayes over the first random step, with the probability
of the record under each unit's response as likelihood. -/
noncomputable def unitPosterior (treated effect : Bool)
    (possible : 0 < observational N.marginal treated effect) : Prob U :=
  posterior N.drawLaw (fun unit => mass (N.responseLaw unit) (record treated effect))
    (fun unit => mass_nonneg _ _) (by
      rw [evidence_responses, ← observational_eq_mass]
      exact possible)

/-- **The abduced unit is the unit marginal of the abduced path.** -/
theorem unitPosterior_eq_sum (treated effect : Bool)
    (possible : 0 < observational N.marginal treated effect) (unit : U) :
    (N.unitPosterior treated effect possible).1 unit =
      ∑ individual, (N.abducePath treated effect possible).1 (unit, individual) := by
  unfold unitPosterior abducePath
  rw [posterior_apply, evidence_responses]
  simp only [condition_apply]
  rw [mass_pathLaw_snd, ← Finset.sum_div, mass_eq_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun individual _ => ?_
  change N.drawWeight unit * (N.respondWeight unit individual * _) =
    N.drawWeight unit * N.respondWeight unit individual *
      (Prod.snd ⁻¹' record treated effect).indicator 1 (unit, individual)
  rw [← mul_assoc]
  rfl

/-- The noisy population's PNS is the draw-weighted PNS of its units. -/
theorem pns_eq_sum_units [DecidableEq U] : N.pns = ∑ unit, N.drawWeight unit * Causality.WeightedResponseTypes.pns (N.responseLaw unit) := by
  unfold Causal.NoisyPopulation.pns
  rw [twoStep_eval]
  refine Finset.sum_congr rfl fun unit _ => ?_
  rw [pns_eq_mass, mass_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun individual _ => ?_
  change _ = N.respondWeight unit individual * _
  congr 1
  by_cases helped : individual.2 = .helped
  · simp [settledValue, helped]
  · simp [settledValue, helped]

/-- **Unit-resolved bounds**: PNS lies between the draw-weighted sums of the
combined bounds of the units' data. -/
theorem unitResolved_pns_bounds [DecidableEq U] :
    ∑ unit, N.drawWeight unit * (data (N.responseLaw unit)).pnsLower ≤ N.pns ∧
      N.pns ≤ ∑ unit, N.drawWeight unit * (data (N.responseLaw unit)).pnsUpper := by
  rw [pns_eq_sum_units]
  exact ⟨Finset.sum_le_sum fun unit _ => mul_le_mul_of_nonneg_left
      (Causality.ProbabilitiesOfCausation.pns_combined_bounds _).1 (N.draw_distribution.nonneg unit),
    Finset.sum_le_sum fun unit _ => mul_le_mul_of_nonneg_left
      (Causality.ProbabilitiesOfCausation.pns_combined_bounds _).2 (N.draw_distribution.nonneg unit)⟩

/-! ## Pooled data and unit-level monotonicity -/

/-- The noisy population with the units and draw of `N` whose every unit
responds with the law `ν`. -/
def withResponse (ν : Prob Individual) : NoisyPopulation U where
  drawWeight := N.drawWeight
  draw_distribution := N.draw_distribution
  respondWeight _ := ν.1
  respond_distribution _ := ⟨ν.2.1, ν.2.2⟩

theorem marginal_withResponse (ν : Prob Individual) : (N.withResponse ν).marginal = ν := by
  apply Subtype.ext
  funext individual
  change ∑ unit, N.drawWeight unit * ν.1 individual = ν.1 individual
  rw [← Finset.sum_mul, N.draw_distribution.sum_eq_one, one_mul]

/-- **The pooled data leave PNS open on exactly the combined interval**, over
noisy populations with the same units and draw. -/
theorem pns_identifiedSet [DecidableEq U] :
    {v | ∃ N' : NoisyPopulation U, data N'.marginal = data N.marginal ∧ N'.pns = v} =
      Set.Icc (data N.marginal).pnsLower (data N.marginal).pnsUpper := by
  ext v
  constructor
  · rintro ⟨N', same, rfl⟩
    rw [← same]
    exact N'.pns_combined_bounds
  · intro member
    rw [← Causality.ProbabilitiesOfCausation.pns_identifiedSet] at member
    obtain ⟨ν, same, value⟩ := member
    refine ⟨N.withResponse ν, by rw [marginal_withResponse]; exact same, ?_⟩
    rw [pns_eq_marginal, marginal_withResponse, value]

/-- The probability of an event under the marginal population is the
draw-weighted probability under the units' responses. -/
theorem mass_marginal_eq_sum (event : Set Individual) :
    mass N.marginal event = ∑ unit, N.drawWeight unit * mass (N.responseLaw unit) event :=
  (N.evidence_responses event).symm

/-- **Monotonicity of a noisy population is monotonicity of every unit that can
be drawn.** -/
theorem noHarm_marginal_iff :
    NoHarm N.marginal ↔ ∀ unit, 0 < N.drawWeight unit → NoHarm (N.responseLaw unit) := by
  unfold NoHarm
  rw [harmProbability_eq_mass, mass_marginal_eq_sum, Finset.sum_eq_zero_iff_of_nonneg
    fun unit _ => mul_nonneg (N.draw_distribution.nonneg unit) (mass_nonneg _ _)]
  constructor
  · intro zero unit positive
    rw [harmProbability_eq_mass]
    exact (mul_eq_zero.mp (zero unit (Finset.mem_univ _))).resolve_left positive.ne'
  · intro each unit _
    rcases (N.draw_distribution.nonneg unit).eq_or_lt with drawn | drawn
    · rw [← drawn, zero_mul]
    · rw [← harmProbability_eq_mass, each unit drawn, mul_zero]

/-- **With every unit monotone, the pooled data identify PN**, however many
random steps lead to the settled individual. -/
theorem pn_identified_of_noHarm {N' : NoisyPopulation U}
    (possible : 0 < observational N.marginal true true)
    (possible' : 0 < observational N'.marginal true true)
    (monotone : ∀ unit, NoHarm (N.responseLaw unit))
    (monotone' : ∀ unit, NoHarm (N'.responseLaw unit))
    (same : data N.marginal = data N'.marginal) : N.pn possible = N'.pn possible' := by
  rw [pn_eq_marginal, pn_eq_marginal]
  exact Causality.ProbabilitiesOfCausation.pn_identified_of_noHarm N.marginal possible possible'
    ((N.noHarm_marginal_iff).mpr fun unit _ => monotone unit)
    ((N'.noHarm_marginal_iff).mpr fun unit _ => monotone' unit) same

/-! ## The counterfactual that re-draws the response -/

/-- **The re-drawn counterfactual**: abduce only the unit from "treated, effect
shown", then withhold treatment before the response step, so that the response
is drawn afresh, and predict no effect. -/
noncomputable def redrawnPN (possible : 0 < observational N.marginal true true) : ℝ :=
  evidence (N.unitPosterior true true possible)
    (fun unit => probability (N.responseLaw unit) none (noEffectUnder false))

end Causal.NoisyPopulation

namespace CausalAbduction

open Causal

/-! ## Unit-resolved data -/

/-- The prediction "withheld, no effect" under a law is one minus the
experimental marginal. -/
theorem probability_noEffectUnder (μ : Prob Individual) (treatment : Bool) :
    probability μ none (noEffectUnder treatment) = 1 - experimental μ treatment := by
  rw [probability_eq_mass (event := {individual | individual.2.outcome treatment = true}ᶜ) μ none
    fun individual => by
      rw [sat_noEffectUnder]
      simp,
    mass_compl, experimental_eq_mass]

/-- **The re-drawn counterfactual is identified by the unit-resolved data**: the
draw law and the data of each unit's response. -/
theorem redrawnPN_identified {U : Type*} [Fintype U] [DecidableEq U] (N N' : NoisyPopulation U)
    (sameDraw : ∀ unit, N.drawWeight unit = N'.drawWeight unit)
    (sameData : ∀ unit, data (N.responseLaw unit) = data (N'.responseLaw unit))
    (possible : 0 < observational N.marginal true true)
    (possible' : 0 < observational N'.marginal true true) :
    N.redrawnPN possible = N'.redrawnPN possible' := by
  have record' : ∀ unit, mass (N.responseLaw unit) (record true true) =
      mass (N'.responseLaw unit) (record true true) := fun unit => by
    rw [← observational_eq_mass, ← observational_eq_mass]
    exact congrFun (congrFun (congrArg Data.observed (sameData unit)) true) true
  have predicted : ∀ unit, probability (N.responseLaw unit) none (noEffectUnder false) =
      probability (N'.responseLaw unit) none (noEffectUnder false) := fun unit => by
    rw [probability_noEffectUnder, probability_noEffectUnder]
    exact congrArg (1 - ·) (congrFun (congrArg Data.experimented (sameData unit)) false)
  have draw : ∀ unit, N.drawLaw.1 unit = N'.drawLaw.1 unit := sameDraw
  unfold NoisyPopulation.redrawnPN NoisyPopulation.unitPosterior
  simp only [evidence, posterior_apply, record', predicted, draw]

/-- The weight of a point mass. -/
theorem passiveProbability_point {μ : Prob Individual} {type : Individual}
    (point : ∀ individual, μ.1 individual = if individual = type then 1 else 0)
    (imposed : Option Bool) (query : PassiveQuery) :
    passiveProbability μ imposed query =
      {ω | (passive quantities).sat query (drawn imposed ω)}.indicator 1 type := by
  change mass μ _ = _
  rw [mass_eq_sum, Finset.sum_eq_single type]
  · rw [point, if_pos rfl, one_mul]
  · intro other _ different
    rw [point, if_neg different, zero_mul]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- An individual is determined by what it shows left alone and under each
treatment. -/
theorem eq_of_realizations {individual individual' : Individual}
    (alone : realization none individual = realization none individual')
    (treated : realization (some true) individual = realization (some true) individual')
    (untreated : realization (some false) individual = realization (some false) individual') :
    individual = individual' := by
  obtain ⟨natural, response⟩ := individual
  obtain ⟨natural', response'⟩ := individual'
  revert alone treated untreated
  cases natural <;> cases response <;> cases natural' <;> cases response' <;> decide

/-- **A deterministic individual is identified at weighted rung two.**  Two point
masses that agree on every passive query under every regime are the same
individual. -/
theorem eq_of_point_weightedAgree {μ ν : Prob Individual} {type type' : Individual}
    (point : ∀ individual, μ.1 individual = if individual = type then 1 else 0)
    (point' : ∀ individual, ν.1 individual = if individual = type' then 1 else 0)
    (agree : WeightedAgree .intervention μ ν) : type = type' := by
  have shows : ∀ imposed, realization imposed type = realization imposed type' := by
    intro imposed
    have same := agree imposed (showsRealization (realization imposed type))
    rw [passiveProbability_point point, passiveProbability_point point'] at same
    have member : type ∈ {ω | (passive quantities).sat
        (showsRealization (realization imposed type)) (drawn imposed ω)} :=
      (sat_showsRealization _ _ _).mpr rfl
    rw [Set.indicator_of_mem member] at same
    by_contra different
    have notMember : type' ∉ {ω | (passive quantities).sat
        (showsRealization (realization imposed type)) (drawn imposed ω)} :=
      fun holds => different ((sat_showsRealization _ _ _).mp holds).symm
    rw [Set.indicator_of_notMem notMember] at same
    exact one_ne_zero same
  exact eq_of_realizations (shows none) (shows (some true)) (shows (some false))

/-- **A deterministic noisy population**: a draw law over units, each unit one
individual. -/
noncomputable def ofTypes {U : Type*} [Fintype U] (draw : Prob U) (type : U → Individual) :
    NoisyPopulation U where
  drawWeight := draw.1
  draw_distribution := ⟨draw.2.1, draw.2.2⟩
  respondWeight unit individual := if individual = type unit then 1 else 0
  respond_distribution unit := ⟨fun individual => by split_ifs <;> norm_num, by simp⟩

/-- **One random step: unit-resolved rung-2 data identify the units.**  For
deterministic responses, if every unit's response agrees at weighted rung two,
the units are the same individuals. -/
theorem ofTypes_identified {U : Type*} [Fintype U] [DecidableEq U] (draw : Prob U)
    (type type' : U → Individual)
    (agree : ∀ unit, WeightedAgree .intervention ((ofTypes draw type).responseLaw unit)
      ((ofTypes draw type').responseLaw unit)) : type = type' :=
  funext fun unit => eq_of_point_weightedAgree (fun _ => rfl) (fun _ => rfl) (agree unit)

/-- **Hence every counterfactual query is identified**: the marginal
populations agree at weighted rung three, and PNS, PN and PS agree. -/
theorem ofTypes_counterfactual {U : Type*} [Fintype U] [DecidableEq U] (draw : Prob U)
    (type type' : U → Individual)
    (agree : ∀ unit, WeightedAgree .intervention ((ofTypes draw type).responseLaw unit)
      ((ofTypes draw type').responseLaw unit)) :
    WeightedAgree .counterfactual (ofTypes draw type).marginal (ofTypes draw type').marginal ∧
      (ofTypes draw type).pns = (ofTypes draw type').pns ∧
      ∀ (possible : 0 < observational (ofTypes draw type).marginal true true)
        (possible' : 0 < observational (ofTypes draw type').marginal true true),
        (ofTypes draw type).pn possible = (ofTypes draw type').pn possible' := by
  have same := ofTypes_identified draw type type' agree
  subst same
  exact ⟨weightedAgree_counterfactual_iff.mpr rfl, rfl, fun _ _ => rfl⟩

/-! ## A second random step breaks identification -/

/-- **A population as one unit with a random response.** -/
noncomputable def ofLaw (μ : Prob Individual) : NoisyPopulation Unit where
  drawWeight _ := 1
  draw_distribution := ⟨fun _ => zero_le_one, by simp⟩
  respondWeight _ := μ.1
  respond_distribution _ := ⟨μ.2.1, μ.2.2⟩

theorem marginal_ofLaw (μ : Prob Individual) : (ofLaw μ).marginal = μ := by
  apply Subtype.ext
  funext individual
  change ∑ _unit : Unit, (1 : ℝ) * μ.1 individual = μ.1 individual
  simp

theorem responseLaw_ofLaw (μ : Prob Individual) (only : Unit) : (ofLaw μ).responseLaw only = μ :=
  Subtype.ext rfl

theorem fixed_swap_valid : ∀ individual, 0 ≤ swapWeight weightedMixed 0 (-1 / 2) individual := by
  rintro ⟨natural, response⟩
  cases natural <;> cases response <;>
    simp [swapWeight, swapAmount, swapSign, weightedMixed, untreatedPopulation_apply,
      responseWeight] <;> norm_num

/-- The population half always and half never showing the effect is the swap of
the one half helped and half hurt. -/
theorem weightedFixed_eq_swap : weightedFixed = swap weightedMixed 0 (-1 / 2) fixed_swap_valid := by
  apply Subtype.ext
  funext individual
  obtain ⟨natural, response⟩ := individual
  change (untreatedPopulation _ _ _ _ _ _).1 _ = swapWeight _ _ _ _
  cases natural <;> cases response <;>
    simp [swapWeight, swapAmount, swapSign, weightedMixed, untreatedPopulation_apply,
      responseWeight] <;> norm_num

theorem weightedAgree_mixed_fixed : WeightedAgree .intervention weightedMixed weightedFixed := by
  rw [weightedFixed_eq_swap]
  exact fun imposed query => (weightedAgree_swap _ _ _ _ imposed query).symm

theorem ps_weightedMixed (possible : 0 < observational weightedMixed false false) :
    Causality.ProbabilitiesOfCausation.ps weightedMixed possible = 1 := by
  rw [ps_eq, observational_false_false]
  simp only [weightedMixed, untreatedPopulation_apply, responseWeight]
  norm_num

theorem ps_weightedFixed (possible : 0 < observational weightedFixed false false) :
    Causality.ProbabilitiesOfCausation.ps weightedFixed possible = 0 := by
  rw [ps_eq, observational_false_false]
  simp only [weightedFixed, untreatedPopulation_apply, responseWeight]
  norm_num

theorem observational_mixed_false_false : observational weightedMixed false false = 1 / 2 := by
  rw [observational_false_false]
  simp only [weightedMixed, untreatedPopulation_apply, responseWeight]
  norm_num

theorem observational_fixed_false_false : observational weightedFixed false false = 1 / 2 := by
  rw [observational_false_false]
  simp only [weightedFixed, untreatedPopulation_apply, responseWeight]
  norm_num

/-- The probability of an event under a point mass. -/
theorem mass_point {μ : Prob Individual} {type : Individual}
    (point : ∀ individual, μ.1 individual = if individual = type then 1 else 0)
    (event : Set Individual) : mass μ event = event.indicator 1 type := by
  rw [mass_eq_sum, Finset.sum_eq_single type]
  · rw [point, if_pos rfl, one_mul]
  · intro other _ different
    rw [point, if_neg different, zero_mul]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- **For a deterministic unit, the monotonicity an experiment can check is
monotonicity**: `P(y_0) ≤ P(y_1)` holds exactly when the unit is not hurt. -/
theorem noHarm_iff_experimental_le_of_point {μ : Prob Individual} {type : Individual}
    (point : ∀ individual, μ.1 individual = if individual = type then 1 else 0) :
    NoHarm μ ↔ experimental μ false ≤ experimental μ true := by
  unfold NoHarm
  rw [harmProbability_eq_mass, experimental_eq_mass, experimental_eq_mass, mass_point point,
    mass_point point, mass_point point]
  obtain ⟨natural, response⟩ := type
  cases response <;> norm_num [Set.indicator_apply, Response.outcome] <;> decide

/-- **A second random step breaks identification.**  One unit responding helped
or hurt with probability one half each, and one unit responding always or never
likewise: the unit-resolved rung-2 data agree, both units pass the experimental
monotonicity check `P(y_0) ≤ P(y_1)` (which for a deterministic unit is
monotonicity, `noHarm_iff_experimental_le_of_point`) while the first is not
monotone, and PNS is `1/2` against `0`, PS `1` against `0`. -/
theorem random_step_breaks_identification :
    (∀ only, WeightedAgree .intervention ((ofLaw weightedMixed).responseLaw only)
        ((ofLaw weightedFixed).responseLaw only)) ∧
      experimental weightedMixed false ≤ experimental weightedMixed true ∧
      experimental weightedFixed false ≤ experimental weightedFixed true ∧
      ¬ NoHarm weightedMixed ∧
      (ofLaw weightedMixed).pns = 1 / 2 ∧ (ofLaw weightedFixed).pns = 0 ∧
      (ofLaw weightedMixed).ps
          (by rw [marginal_ofLaw, observational_mixed_false_false]; norm_num) = 1 ∧
      (ofLaw weightedFixed).ps
          (by rw [marginal_ofLaw, observational_fixed_false_false]; norm_num) = 0 := by
  obtain ⟨sameTreated, sameUntreated, -, -, -, notMonotone, -⟩ := pns_not_identified_without_noHarm
  have mixedTreated : experimental weightedMixed true = 1 / 2 := by
    rw [weightedMixed, experimental_untreated_true]
    norm_num
  have mixedUntreated : experimental weightedMixed false = 1 / 2 := by
    rw [weightedMixed, experimental_untreated_false]
    norm_num
  refine ⟨fun only => ?_, by rw [mixedTreated, mixedUntreated],
    by rw [← sameTreated, ← sameUntreated, mixedTreated, mixedUntreated], notMonotone,
    ?_, ?_, ?_, ?_⟩
  · rw [responseLaw_ofLaw, responseLaw_ofLaw]
    exact weightedAgree_mixed_fixed
  · rw [NoisyPopulation.pns_eq_marginal, marginal_ofLaw]
    exact pns_not_identified_without_noHarm.2.2.2.1
  · rw [NoisyPopulation.pns_eq_marginal, marginal_ofLaw]
    exact pns_not_identified_without_noHarm.2.2.2.2.1
  · rw [NoisyPopulation.ps_eq_marginal]
    simp only [marginal_ofLaw]
    exact ps_weightedMixed _
  · rw [NoisyPopulation.ps_eq_marginal]
    simp only [marginal_ofLaw]
    exact ps_weightedFixed _

/-! ## Where the intervention sits: the re-drawn counterfactual is not PN -/

theorem observational_ofLaw_selfSelected :
    0 < observational (ofLaw selfSelected).marginal true true := by
  rw [marginal_ofLaw, observational_selfSelected_true_true]
  norm_num

/-- **Re-drawing the response is a different counterfactual.**  On the
self-selected population as one unit with a random response, PN is `1`: the
treated who showed the effect were helped.  Abducing only the unit and
withholding treatment before the response step gives `1/2`. -/
theorem redrawn_differs :
    (ofLaw selfSelected).pn observational_ofLaw_selfSelected = 1 ∧
      (ofLaw selfSelected).redrawnPN observational_ofLaw_selfSelected = 1 / 2 := by
  obtain ⟨-, e0, -, -, -, -, -, -, -, value⟩ := selfSelection_control
  constructor
  · rw [NoisyPopulation.pn_eq_marginal]
    simp only [marginal_ofLaw]
    exact value
  · unfold NoisyPopulation.redrawnPN
    have constant : (fun only => probability ((ofLaw selfSelected).responseLaw only) none
        (noEffectUnder false)) = fun _ => 1 / 2 := by
      funext only
      rw [responseLaw_ofLaw, probability_noEffectUnder, e0]
      norm_num
    rw [constant]
    unfold evidence
    rw [← Finset.sum_mul, (NoisyPopulation.unitPosterior (ofLaw selfSelected) true true
      observational_ofLaw_selfSelected).2.2, one_mul]

/-! ## Recording the unit narrows the bounds -/

/-- Half helped, half always showing the effect, nobody treated. -/
noncomputable def helpedOrAlways : Prob Individual :=
  untreatedPopulation 0 (1 / 2) 0 (1 / 2) ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩ (by norm_num)

/-- Half hurt, half never showing the effect, nobody treated. -/
noncomputable def hurtOrNever : Prob Individual :=
  untreatedPopulation (1 / 2) 0 (1 / 2) 0 ⟨by norm_num, le_rfl, by norm_num, le_rfl⟩ (by norm_num)

/-- The fair coin over two units. -/
noncomputable def fairUnits : Prob Bool :=
  ⟨fun _ => 1 / 2, fun _ => by norm_num, by rw [Fintype.sum_bool]; norm_num⟩

/-- **Two units**: unit `true` is helped or always shows the effect, unit
`false` is hurt or never shows it, each drawn with probability one half. -/
noncomputable def twoUnits : NoisyPopulation Bool where
  drawWeight := fairUnits.1
  draw_distribution := ⟨fairUnits.2.1, fairUnits.2.2⟩
  respondWeight unit := if unit then helpedOrAlways.1 else hurtOrNever.1
  respond_distribution unit := by
    cases unit
    · exact ⟨hurtOrNever.2.1, hurtOrNever.2.2⟩
    · exact ⟨helpedOrAlways.2.1, helpedOrAlways.2.2⟩

/-- The data of the helped-or-always unit pin its PNS to one half. -/
theorem pns_eq_of_data_helpedOrAlways {ν : Prob Individual} (same : data ν = data helpedOrAlways) :
    pns ν = 1 / 2 := by
  obtain ⟨lower, upper⟩ := Causality.ProbabilitiesOfCausation.pns_combined_bounds ν
  rw [same] at lower upper
  have e1 : experimental helpedOrAlways true = 1 := by
    rw [helpedOrAlways, experimental_untreated_true]
    norm_num
  have e0 : experimental helpedOrAlways false = 1 / 2 := by
    rw [helpedOrAlways, experimental_untreated_false]
    norm_num
  have effect : (data helpedOrAlways).effect = 1 / 2 := by
    rw [← probability_effectObserved_eq_effect, helpedOrAlways,
      probability_effectObserved_untreated]
    norm_num
  have low : 1 / 2 ≤ (data helpedOrAlways).pnsLower := by
    unfold Data.pnsLower
    refine le_max_of_le_right (le_max_of_le_right ?_)
    rw [effect]
    change 1 / 2 ≤ experimental helpedOrAlways true - 1 / 2
    rw [e1]
    norm_num
  have high : (data helpedOrAlways).pnsUpper ≤ 1 / 2 := by
    unfold Data.pnsUpper
    refine min_le_of_left_le (min_le_of_right_le ?_)
    change 1 - experimental helpedOrAlways false ≤ 1 / 2
    rw [e0]
    norm_num
  linarith

/-- The data of the hurt-or-never unit pin its PNS to zero. -/
theorem pns_eq_of_data_hurtOrNever {ν : Prob Individual} (same : data ν = data hurtOrNever) :
    pns ν = 0 := by
  obtain ⟨lower, upper⟩ := Causality.ProbabilitiesOfCausation.pns_combined_bounds ν
  rw [same] at lower upper
  have e1 : experimental hurtOrNever true = 0 := by
    rw [hurtOrNever, experimental_untreated_true]
    norm_num
  have low : 0 ≤ (data hurtOrNever).pnsLower :=
    le_max_of_le_left (le_max_left _ _)
  have high : (data hurtOrNever).pnsUpper ≤ 0 := by
    unfold Data.pnsUpper
    refine min_le_of_left_le (min_le_of_left_le ?_)
    change experimental hurtOrNever true ≤ 0
    rw [e1]
  linarith

theorem pooled_swap_valid :
    ∀ individual, 0 ≤ swapWeight weightedMixed 0 (-1 / 4) individual := by
  rintro ⟨natural, response⟩
  cases natural <;> cases response <;>
    simp [swapWeight, swapAmount, swapSign, weightedMixed, untreatedPopulation_apply,
      responseWeight] <;> norm_num

/-- The pooled population of the two units is a swap of the half helped, half
hurt population. -/
theorem twoUnits_marginal_eq_swap :
    twoUnits.marginal = swap weightedMixed 0 (-1 / 4) pooled_swap_valid := by
  apply Subtype.ext
  funext individual
  obtain ⟨natural, response⟩ := individual
  change ∑ unit, fairUnits.1 unit * (if unit then helpedOrAlways.1 else hurtOrNever.1)
      (natural, response) = swapWeight _ _ _ _
  rw [Fintype.sum_bool]
  cases natural <;> cases response <;>
    simp [fairUnits, helpedOrAlways, hurtOrNever, swapWeight, swapAmount, swapSign, weightedMixed,
      untreatedPopulation_apply, responseWeight] <;> norm_num

/-- **Recording the unit identifies what the pooled data leave open.**  Every
noisy population with the draw and the unit data of `twoUnits` has PNS `1/4`.
The pooled data of `twoUnits` are those of the half helped, half hurt
population and of the half always, half never one, whose PNS are `1/2` and
`0`. -/
theorem recording_the_unit_identifies :
    (∀ N' : NoisyPopulation Bool, (∀ unit, N'.drawWeight unit = twoUnits.drawWeight unit) →
        (∀ unit, data (N'.responseLaw unit) = data (twoUnits.responseLaw unit)) →
        N'.pns = 1 / 4) ∧
      data twoUnits.marginal = data weightedMixed ∧ data twoUnits.marginal = data weightedFixed ∧
      pns weightedMixed = 1 / 2 ∧ pns weightedFixed = 0 := by
  have pooledMixed : data twoUnits.marginal = data weightedMixed := by
    rw [twoUnits_marginal_eq_swap, data_swap]
  refine ⟨fun N' sameDraw sameData => ?_, pooledMixed, ?_,
    pns_not_identified_without_noHarm.2.2.2.1, pns_not_identified_without_noHarm.2.2.2.2.1⟩
  · rw [NoisyPopulation.pns_eq_sum_units, Fintype.sum_bool, sameDraw, sameDraw]
    have helpedUnit : pns (N'.responseLaw true) = 1 / 2 :=
      pns_eq_of_data_helpedOrAlways ((sameData true).trans (congrArg data (Subtype.ext rfl)))
    have hurtUnit : pns (N'.responseLaw false) = 0 :=
      pns_eq_of_data_hurtOrNever ((sameData false).trans (congrArg data (Subtype.ext rfl)))
    rw [helpedUnit, hurtUnit]
    change (1 / 2 : ℝ) * (1 / 2) + 1 / 2 * 0 = 1 / 4
    norm_num
  · rw [pooledMixed, weightedFixed_eq_swap, data_swap]

end CausalAbduction

end Mettapedia.GSLT.Distinction.Probabilistic
