import Mettapedia.GSLT.Causality.Identifiability
import Mettapedia.GSLT.Causality.WeightedObservers

/-!
# Weighted response types: probabilities of causation on the causal ladder

A population of the response-type GSLT (`Hierarchy.ResponseTypes`) draws an
individual, who then responds to the treatment imposed.  The ladder's
observers see which individuals can be drawn, not how often.  Here the draw
carries a finite distribution over individuals (natural treatment and response
type), and a **weighted observer** reports the probability that the drawn
individual satisfies a counterfactual query (`probability`).  Every query is a
formula of the first slice's saturated system, read at the drawn individual.

**Probabilities of causation.**
* The experimental marginals `P(Y_x)` are the probabilities of "treated with
  `x`, the effect shows" (`experimental`).
* The probability of necessity and sufficiency `P(Y_1 ∧ ¬Y_0)` is the
  probability of the body of the first slice's `necessaryAndSufficient`
  (`pns`), and the probability of harm is `P(Y_0 ∧ ¬Y_1)`
  (`harmProbability`).

**Tian–Pearl bounds** (`pns_bounds`):
`max 0 (P(Y_1) - P(Y_0)) ≤ PNS ≤ min P(Y_1) (1 - P(Y_0))`.  They are the
Fréchet bounds of the weighted observer (`chance_conj_neg_bounds`), so they come
from the sum rule on the event algebra.  They are **sharp**: every value
between them is the PNS of a population with the given marginals
(`pns_sharp`), so the set of PNS values the experiments leave open is exactly
the interval (`pns_identifiedSet`), and both ends are attained by populations
with the marginals of any given one (`pns_bounds_attained`).

**Monotonicity** (`NoHarm`, the probability of harm is zero).  The risk
difference is benefit minus harm (`experimental_sub_experimental`), so under
monotonicity `PNS = P(Y_1) - P(Y_0)` (`pns_eq_of_noHarm`) and PNS is
identified by the experiments (`pns_identified_of_noHarm`).  Without it, the
population half helped and half hurt and the one half always and half never
showing the effect have the same experimental marginals and PNS one half and
zero (`pns_not_identified_without_noHarm`).  Weighted monotonicity is the
weighted form of the first slice's `Monotone`: it holds exactly when the
support has no individual hurt by treatment (`noHarm_iff_monotone_support`).

**Erasure** (`erase`, `erasure`).  A weighted population erases to the
possibilistic population of its support.  A possibilistic query "under this
regime, some drawn individual satisfies `φ`" holds at the erasure exactly when
the weighted observer gives `φ` positive probability.  In particular the first
slice's `necessaryAndSufficient` holds at the erasure exactly when PNS is
positive (`necessaryAndSufficient_erase_iff`).

**The weighted ladder** (`WeightedAgree`).  Two populations agree at weighted
rung one when every passive query about the drawn individual left alone has the
same probability, at rung two when this holds under each single regime, and at
rung three when every counterfactual query has the same probability.  Higher
rungs refine lower ones, and on this GSLT weighted rung three is equality of
the population law (`weightedAgree_counterfactual_iff`): each individual is
characterized by its natural treatment and its two potential outcomes.
Erasure maps the weighted ladder to the possibilistic one rung by rung
(`erase_agree_of_weightedAgree`), and loses information at every rung
(`erasure_strict`).

**Kolmogorov's layer.**  The same bounds hold for any probability measure on
the response types, from the real-valued Fréchet bounds of the measure layer
(`pns_bounds_measure`).

**Controls.**
* Equal supports, different weights (`equalSupport_control`): two populations
  with the same support have the same erasure, so they agree at every
  possibilistic rung, counterfactual included; yet they differ already on a
  passive query (the effect observed untreated, one quarter against three
  quarters), on an experimental marginal, and on PNS.
* Weights identify what possibilities could not
  (`monotonicity_identifies_with_weights`): the first slice's monotone and fixed
  populations agree at possibilistic rung two (`monotonicity_not_identifying`);
  weighted uniformly, both are monotone, their experimental marginals differ,
  and their PNS is identified, one third and zero.

**Axioms.**  The probabilities are real numbers on the simplex `Prob`; the
event masses use classical indicators.  Constructivity is not claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.WeightedResponseTypes

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes
open Mettapedia.GSLT.Causality.WeightedObservers
open Mettapedia.InformationTheory

/-! ## Individuals and finite sums -/

instance : Fintype Response where
  elems := {.never, .helped, .hurt, .always}
  complete response := by cases response <;> decide

theorem sum_response (f : Response → ℝ) :
    ∑ response, f response = f .never + f .helped + f .hurt + f .always := by
  change ∑ response ∈ ({.never, .helped, .hurt, .always} : Finset Response), f response = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- An individual: natural treatment and response type. -/
abbrev Individual := Bool × Response

theorem sum_individual (f : Individual → ℝ) :
    ∑ individual, f individual =
      (f (false, .never) + f (false, .helped) + f (false, .hurt) + f (false, .always)) +
        (f (true, .never) + f (true, .helped) + f (true, .hurt) + f (true, .always)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, sum_response, sum_response]
  ring

/-! ## The weighted observer of a population -/

/-- The counterfactual system of the response-type GSLT. -/
abbrev ladder := everyIntervention.saturated quantities

/-- Its queries. -/
abbrev Query := Formula ladder.Atom ladder.Label

/-- The drawn individual, under a regime. -/
def drawn (imposed : Option Bool) (individual : Individual) : Stage :=
  .individual individual.1 individual.2 imposed

/-- **The weighted observer**: the probability that the drawn individual, under
the regime imposed, satisfies a query. -/
noncomputable def probability (population : Prob Individual) (imposed : Option Bool)
    (query : Query) : ℝ :=
  chance ladder population (drawn imposed) query

/-- The treatment received, read with nothing further imposed. -/
def treatmentShown : ladder.Atom :=
  ((Quantity.treatment, ⟨none, AdmissibleClass.top_admissible _⟩) :
    Quantity × {context : Option Bool // everyIntervention.Admissible context})

/-- "Treated with `x`, the effect shows": the potential outcome `Y_x`. -/
def effectUnder (treatment : Bool) : Query :=
  .dia (treat treatment) (.atom effectShown)

/-- "Treated with `x`, the effect does not show." -/
def noEffectUnder (treatment : Bool) : Query :=
  .dia (treat treatment) (.neg (.atom effectShown))

/-- "Left alone, the effect shows": a passive query. -/
def effectObserved : Query :=
  .dia proceed (.atom effectShown)

/-- "Treatment is necessary and sufficient for the effect." -/
def necessityAndSufficiency : Query :=
  .conj (effectUnder true) (noEffectUnder false)

/-- The first slice's query is "some drawn individual satisfies
`necessityAndSufficiency`". -/
theorem necessaryAndSufficient_eq :
    necessaryAndSufficient = .dia proceed necessityAndSufficiency :=
  rfl

/-- "Treatment harms": the effect shows untreated and not treated. -/
def harm : Query :=
  .conj (effectUnder false) (noEffectUnder true)

/-- **The experimental marginal** `P(Y_x)`. -/
noncomputable def experimental (population : Prob Individual) (treatment : Bool) : ℝ :=
  probability population none (effectUnder treatment)

/-- **The probability of necessity and sufficiency** `P(Y_1 ∧ ¬Y_0)`. -/
noncomputable def pns (population : Prob Individual) : ℝ :=
  probability population none necessityAndSufficiency

/-- **The probability of harm** `P(Y_0 ∧ ¬Y_1)`. -/
noncomputable def harmProbability (population : Prob Individual) : ℝ :=
  probability population none harm

/-! ### The queries at a drawn individual -/

theorem sat_effectUnder (treatment : Bool) (imposed : Option Bool) (individual : Individual) :
    ladder.sat (effectUnder treatment) (drawn imposed individual) ↔
      individual.2.outcome treatment = true := by
  obtain ⟨natural, response⟩ := individual
  constructor
  · rintro ⟨target, step, shown⟩
    cases moves_of_step step
    exact shown
  · intro shown
    exact ⟨_, Moves.respond, shown⟩

theorem sat_noEffectUnder (treatment : Bool) (imposed : Option Bool) (individual : Individual) :
    ladder.sat (noEffectUnder treatment) (drawn imposed individual) ↔
      individual.2.outcome treatment = false := by
  obtain ⟨natural, response⟩ := individual
  constructor
  · rintro ⟨target, step, hidden⟩
    cases moves_of_step step
    exact Bool.eq_false_iff.mpr hidden
  · intro hidden
    exact ⟨_, Moves.respond, Bool.eq_false_iff.mp hidden⟩

theorem sat_effectObserved (imposed : Option Bool) (individual : Individual) :
    ladder.sat effectObserved (drawn imposed individual) ↔
      individual.2.outcome (imposed.getD individual.1) = true := by
  obtain ⟨natural, response⟩ := individual
  constructor
  · rintro ⟨target, step, shown⟩
    cases moves_of_step step
    exact shown
  · intro shown
    exact ⟨_, Moves.respond, shown⟩

theorem sat_necessityAndSufficiency (imposed : Option Bool) (individual : Individual) :
    ladder.sat necessityAndSufficiency (drawn imposed individual) ↔ individual.2 = .helped := by
  change ladder.sat (effectUnder true) _ ∧ ladder.sat (noEffectUnder false) _ ↔ _
  rw [sat_effectUnder, sat_noEffectUnder]
  obtain ⟨natural, response⟩ := individual
  cases response <;> simp [Response.outcome]

theorem sat_harm (imposed : Option Bool) (individual : Individual) :
    ladder.sat harm (drawn imposed individual) ↔ individual.2 = .hurt := by
  change ladder.sat (effectUnder false) _ ∧ ladder.sat (noEffectUnder true) _ ↔ _
  rw [sat_effectUnder, sat_noEffectUnder]
  obtain ⟨natural, response⟩ := individual
  cases response <;> simp [Response.outcome]

/-- "Treated, the effect shows, and untreated it does not": at a drawn
individual, the negation of a diamond is the diamond of the negation. -/
theorem sat_gain (imposed : Option Bool) (individual : Individual) :
    ladder.sat (.conj (effectUnder true) (.neg (effectUnder false))) (drawn imposed individual) ↔
      individual.2 = .helped := by
  change ladder.sat (effectUnder true) _ ∧ ¬ ladder.sat (effectUnder false) _ ↔ _
  rw [sat_effectUnder, sat_effectUnder]
  obtain ⟨natural, response⟩ := individual
  cases response <;> simp [Response.outcome]

theorem sat_loss (imposed : Option Bool) (individual : Individual) :
    ladder.sat (.conj (effectUnder false) (.neg (effectUnder true))) (drawn imposed individual) ↔
      individual.2 = .hurt := by
  change ladder.sat (effectUnder false) _ ∧ ¬ ladder.sat (effectUnder true) _ ↔ _
  rw [sat_effectUnder, sat_effectUnder]
  obtain ⟨natural, response⟩ := individual
  cases response <;> simp [Response.outcome]

/-! ### The probabilities as event masses -/

theorem probability_eq_mass {query : Query} {event : Set Individual} (population : Prob Individual)
    (imposed : Option Bool)
    (same : ∀ individual, ladder.sat query (drawn imposed individual) ↔ individual ∈ event) :
    probability population imposed query = mass population event :=
  congrArg (mass population) (Set.ext same)

theorem experimental_eq_mass (population : Prob Individual) (treatment : Bool) :
    experimental population treatment =
      mass population {individual | individual.2.outcome treatment = true} :=
  probability_eq_mass population none fun individual => sat_effectUnder treatment none individual

theorem pns_eq_mass (population : Prob Individual) :
    pns population = mass population {individual | individual.2 = .helped} :=
  probability_eq_mass population none fun individual => sat_necessityAndSufficiency none individual

theorem harmProbability_eq_mass (population : Prob Individual) :
    harmProbability population = mass population {individual | individual.2 = .hurt} :=
  probability_eq_mass population none fun individual => sat_harm none individual

theorem pns_eq_gain (population : Prob Individual) :
    pns population =
      probability population none (.conj (effectUnder true) (.neg (effectUnder false))) :=
  (pns_eq_mass population).trans
    (probability_eq_mass population none fun individual => sat_gain none individual).symm

theorem harmProbability_eq_loss (population : Prob Individual) :
    harmProbability population =
      probability population none (.conj (effectUnder false) (.neg (effectUnder true))) :=
  (harmProbability_eq_mass population).trans
    (probability_eq_mass population none fun individual => sat_loss none individual).symm

/-! ## The Tian–Pearl bounds -/

/-- **The Tian–Pearl bounds on the probability of necessity and sufficiency,
from the experimental marginals.** -/
theorem pns_bounds (population : Prob Individual) :
    max 0 (experimental population true - experimental population false) ≤ pns population ∧
      pns population ≤ min (experimental population true) (1 - experimental population false) := by
  rw [pns_eq_gain]
  exact chance_conj_neg_bounds ladder population (drawn none) (effectUnder true) (effectUnder false)

/-- **Benefit minus harm is the risk difference.** -/
theorem experimental_sub_experimental (population : Prob Individual) :
    experimental population true - experimental population false =
      pns population - harmProbability population := by
  have split := chance_sub_chance ladder population (drawn none) (effectUnder true)
    (effectUnder false)
  have gain := pns_eq_gain population
  have loss := harmProbability_eq_loss population
  unfold experimental
  unfold probability at gain loss ⊢
  linarith

/-! ### Populations of naturally untreated individuals -/

/-- Weights on the four response types. -/
def responseWeight (never helped hurt always : ℝ) : Response → ℝ
  | .never => never
  | .helped => helped
  | .hurt => hurt
  | .always => always

/-- **A population of naturally untreated individuals** with given weights on
the response types. -/
noncomputable def untreatedPopulation (never helped hurt always : ℝ)
    (nonneg : 0 ≤ never ∧ 0 ≤ helped ∧ 0 ≤ hurt ∧ 0 ≤ always)
    (total : never + helped + hurt + always = 1) : Prob Individual :=
  ⟨fun individual =>
      if individual.1 = false then responseWeight never helped hurt always individual.2 else 0,
    fun individual => by
      obtain ⟨natural, response⟩ := individual
      obtain ⟨n, h, u, a⟩ := nonneg
      cases natural <;> cases response <;> simp [responseWeight, n, h, u, a],
    by
      rw [sum_individual]
      simp only [responseWeight, if_true, Bool.true_eq_false, if_false]
      linarith⟩

section Untreated

variable {never helped hurt always : ℝ} {nonneg : 0 ≤ never ∧ 0 ≤ helped ∧ 0 ≤ hurt ∧ 0 ≤ always}
  {total : never + helped + hurt + always = 1}

theorem untreatedPopulation_apply (individual : Individual) :
    (untreatedPopulation never helped hurt always nonneg total).1 individual =
      if individual.1 = false then responseWeight never helped hurt always individual.2 else 0 :=
  rfl

theorem mass_untreatedPopulation (event : Set Individual) :
    mass (untreatedPopulation never helped hurt always nonneg total) event =
      never * event.indicator 1 (false, .never) + helped * event.indicator 1 (false, .helped) +
        hurt * event.indicator 1 (false, .hurt) + always * event.indicator 1 (false, .always) := by
  rw [mass_eq_sum, sum_individual]
  simp only [untreatedPopulation_apply, responseWeight, if_true, Bool.true_eq_false, if_false,
    zero_mul, add_zero]

theorem experimental_untreated_true :
    experimental (untreatedPopulation never helped hurt always nonneg total) true =
      helped + always := by
  rw [experimental_eq_mass, mass_untreatedPopulation]
  simp [Response.outcome]

theorem experimental_untreated_false :
    experimental (untreatedPopulation never helped hurt always nonneg total) false =
      hurt + always := by
  rw [experimental_eq_mass, mass_untreatedPopulation]
  simp [Response.outcome]

theorem pns_untreated :
    pns (untreatedPopulation never helped hurt always nonneg total) = helped := by
  rw [pns_eq_mass, mass_untreatedPopulation]
  simp

theorem harmProbability_untreated :
    harmProbability (untreatedPopulation never helped hurt always nonneg total) = hurt := by
  rw [harmProbability_eq_mass, mass_untreatedPopulation]
  simp

theorem probability_effectObserved_untreated :
    probability (untreatedPopulation never helped hurt always nonneg total) none effectObserved =
      hurt + always := by
  rw [probability_eq_mass (event := {individual | individual.2.outcome individual.1 = true}) _ none
    fun individual => sat_effectObserved none individual, mass_untreatedPopulation]
  simp [Response.outcome]

end Untreated

/-! ### Sharpness -/

/-- **The Tian–Pearl bounds are sharp**: every value between them is the PNS
of a population with the given experimental marginals. -/
theorem pns_sharp {a b v : ℝ} (lower : max 0 (a - b) ≤ v) (upper : v ≤ min a (1 - b)) :
    ∃ population : Prob Individual, experimental population true = a ∧
      experimental population false = b ∧ pns population = v := by
  have v_nonneg : 0 ≤ v := le_trans (le_max_left _ _) lower
  have v_ge : a - b ≤ v := le_trans (le_max_right _ _) lower
  have v_le : v ≤ a := le_trans upper (min_le_left _ _)
  have v_le' : v ≤ 1 - b := le_trans upper (min_le_right _ _)
  refine ⟨untreatedPopulation (1 - b - v) v (b - a + v) (a - v)
    ⟨by linarith, v_nonneg, by linarith, by linarith⟩ (by ring), ?_, ?_, ?_⟩
  · rw [experimental_untreated_true]
    ring
  · rw [experimental_untreated_false]
    ring
  · exact pns_untreated

/-- **The experiments leave PNS open on exactly the Tian–Pearl interval.** -/
theorem pns_identifiedSet (a b : ℝ) :
    {v | ∃ population : Prob Individual, experimental population true = a ∧
        experimental population false = b ∧ pns population = v} =
      Set.Icc (max 0 (a - b)) (min a (1 - b)) := by
  ext v
  constructor
  · rintro ⟨population, rfl, rfl, rfl⟩
    exact pns_bounds population
  · rintro ⟨lower, upper⟩
    exact pns_sharp lower upper

/-- **Both bounds are attained**: for any population there are two with its
experimental marginals, one at each extreme. -/
theorem pns_bounds_attained (population : Prob Individual) :
    ∃ low high : Prob Individual,
      (experimental low true = experimental population true ∧
        experimental low false = experimental population false ∧
        pns low = max 0 (experimental population true - experimental population false)) ∧
      (experimental high true = experimental population true ∧
        experimental high false = experimental population false ∧
        pns high = min (experimental population true) (1 - experimental population false)) := by
  obtain ⟨lower, upper⟩ := pns_bounds population
  obtain ⟨low, lowTrue, lowFalse, lowPns⟩ := pns_sharp le_rfl (lower.trans upper)
  obtain ⟨high, highTrue, highFalse, highPns⟩ := pns_sharp (lower.trans upper) le_rfl
  exact ⟨low, high, ⟨lowTrue, lowFalse, lowPns⟩, ⟨highTrue, highFalse, highPns⟩⟩

/-! ## Monotonicity -/

/-- **Monotonicity**: treatment harms nobody, with probability one. -/
def NoHarm (population : Prob Individual) : Prop :=
  harmProbability population = 0

/-- **Under monotonicity PNS is the risk difference.** -/
theorem pns_eq_of_noHarm {population : Prob Individual} (noHarm : NoHarm population) :
    pns population = experimental population true - experimental population false := by
  rw [experimental_sub_experimental, noHarm, sub_zero]

/-- **Under monotonicity the experiments identify PNS.** -/
theorem pns_identified_of_noHarm {population population' : Prob Individual}
    (noHarm : NoHarm population) (noHarm' : NoHarm population')
    (sameTreated : experimental population true = experimental population' true)
    (sameUntreated : experimental population false = experimental population' false) :
    pns population = pns population' := by
  rw [pns_eq_of_noHarm noHarm, pns_eq_of_noHarm noHarm', sameTreated, sameUntreated]

/-- Half helped and half hurt by treatment, nobody treated. -/
noncomputable def weightedMixed : Prob Individual :=
  untreatedPopulation 0 (1 / 2) (1 / 2) 0 ⟨le_rfl, by norm_num, by norm_num, le_rfl⟩ (by norm_num)

/-- Half always and half never showing the effect, nobody treated. -/
noncomputable def weightedFixed : Prob Individual :=
  untreatedPopulation (1 / 2) 0 0 (1 / 2) ⟨by norm_num, le_rfl, le_rfl, by norm_num⟩ (by norm_num)

/-- **Without monotonicity the experiments do not identify PNS.**  The two
populations have the same experimental marginals and the same passive
probability of the effect; PNS is one half for the first and zero for the
second, and only the second is monotone. -/
theorem pns_not_identified_without_noHarm :
    experimental weightedMixed true = experimental weightedFixed true ∧
      experimental weightedMixed false = experimental weightedFixed false ∧
      probability weightedMixed none effectObserved =
        probability weightedFixed none effectObserved ∧
      pns weightedMixed = 1 / 2 ∧ pns weightedFixed = 0 ∧
      ¬ NoHarm weightedMixed ∧ NoHarm weightedFixed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [weightedMixed, weightedFixed, experimental_untreated_true, experimental_untreated_true]
    norm_num
  · rw [weightedMixed, weightedFixed, experimental_untreated_false, experimental_untreated_false]
    norm_num
  · rw [weightedMixed, weightedFixed, probability_effectObserved_untreated,
      probability_effectObserved_untreated]
    norm_num
  · rw [weightedMixed, pns_untreated]
  · rw [weightedFixed, pns_untreated]
  · rw [NoHarm, weightedMixed, harmProbability_untreated]
    norm_num
  · rw [NoHarm, weightedFixed, harmProbability_untreated]

/-! ## Erasure -/

/-- The individuals of positive weight. -/
noncomputable def support (population : Prob Individual) : List Individual :=
  (Finset.univ.filter fun individual => 0 < population.1 individual).toList

theorem mem_support {population : Prob Individual} {individual : Individual} :
    individual ∈ support population ↔ 0 < population.1 individual := by
  simp [support]

/-- **The erasure of a weighted population**: the possibilistic population of
its support. -/
noncomputable def erase (population : Prob Individual) (imposed : Option Bool) : Stage :=
  .population (support population) imposed

/-- The draw of a weighted population weights the draw step of its erasure,
under any regime. -/
noncomputable def drawWeighting (population : Prob Individual) (label : ladder.Label)
    (imposed : Option Bool) : Weighting ladder label (erase population imposed) Individual where
  law := population
  draw := drawn (label.1.or imposed)
  sound _ positive := Moves.draw (mem_support.mpr positive)
  complete target step := by
    cases moves_of_step step with
    | @draw _ _ natural response member =>
        exact ⟨(natural, response), mem_support.mp member, rfl⟩

/-- **Erasure.**  "Under the regime of this label, some drawn individual
satisfies the query" holds at the erased population exactly when the weighted
observer gives the query positive probability. -/
theorem erasure (population : Prob Individual) (label : ladder.Label) (imposed : Option Bool)
    (query : Query) :
    ladder.sat (.dia label query) (erase population imposed) ↔
      0 < probability population (label.1.or imposed) query :=
  (drawWeighting population label imposed).erasure query

/-- **The first slice's necessity-and-sufficiency query is the support of
PNS.** -/
theorem necessaryAndSufficient_erase_iff (population : Prob Individual) :
    ladder.sat necessaryAndSufficient (erase population none) ↔ 0 < pns population :=
  erasure population proceed none necessityAndSufficiency

/-- **Weighted monotonicity is possibilistic monotonicity of the support.** -/
theorem noHarm_iff_monotone_support (population : Prob Individual) :
    NoHarm population ↔ ResponseTypes.Monotone (support population) := by
  rw [NoHarm, harmProbability_eq_mass]
  constructor
  · intro zero individual member hurt
    have positive : 0 < mass population {individual | individual.2 = .hurt} :=
      (mass_pos_iff population _).mpr ⟨individual, hurt, mem_support.mp member⟩
    rw [zero] at positive
    exact lt_irrefl 0 positive
  · intro monotone
    refine le_antisymm (not_lt.mp fun positive => ?_) (mass_nonneg population _)
    obtain ⟨individual, hurt, weight⟩ := (mass_pos_iff population _).mp positive
    exact monotone individual (mem_support.mpr weight) hurt

/-! ## Controls -/

/-- Populations with the same members agree counterfactually. -/
theorem population_counterfactual_of_mem_iff {individuals individuals' : List Individual}
    (same : ∀ individual, individual ∈ individuals ↔ individual ∈ individuals')
    (imposed : Option Bool) :
    Agree everyIntervention quantities .counterfactual (.population individuals imposed)
      (.population individuals' imposed) := by
  let related : Stage → Stage → Prop := fun left right => left = right ∨
    ∃ setting, left = .population individuals setting ∧ right = .population individuals' setting
  refine everyIntervention.relEquiv_of_isReductionBisimulation quantities (relation := related)
    ⟨⟨?_, ?_⟩, ?_⟩ ?_ (Or.inr ⟨imposed, rfl, rfl⟩)
  · rintro left right (rfl | ⟨setting, rfl, rfl⟩) left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | draw member => exact ⟨_, Moves.draw ((same _).mp member), Or.inl rfl⟩
  · rintro left right (rfl | ⟨setting, rfl, rfl⟩) right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | draw member => exact ⟨_, Moves.draw ((same _).mpr member), Or.inl rfl⟩
  · rintro left right (rfl | ⟨setting, rfl, rfl⟩) atom
    · exact Iff.rfl
    · cases atom <;> exact Iff.rfl
  · rintro context left right - (rfl | ⟨setting, rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨context.or setting, rfl, rfl⟩

/-! ### Equal supports, different weights -/

/-- Three quarters helped by treatment, one quarter always showing the effect. -/
noncomputable def mostlyHelped : Prob Individual :=
  untreatedPopulation 0 (3 / 4) 0 (1 / 4) ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩ (by norm_num)

/-- One quarter helped by treatment, three quarters always showing the effect. -/
noncomputable def mostlyAlways : Prob Individual :=
  untreatedPopulation 0 (1 / 4) 0 (3 / 4) ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩ (by norm_num)

theorem support_mostlyHelped : support mostlyHelped = support mostlyAlways := by
  unfold support
  congr 1
  refine Finset.filter_congr fun individual _ => ?_
  obtain ⟨natural, response⟩ := individual
  cases natural <;> cases response <;>
    simp [mostlyHelped, mostlyAlways, untreatedPopulation_apply, responseWeight]

/-- **Equal supports, different weights.**  The two populations have the same
erasure, so they agree at every possibilistic rung; the weighted observer
separates them on a passive query, on an experimental marginal, and on PNS. -/
theorem equalSupport_control :
    erase mostlyHelped none = erase mostlyAlways none ∧
      (∀ rung, Agree everyIntervention quantities rung (erase mostlyHelped none)
        (erase mostlyAlways none)) ∧
      probability mostlyHelped none effectObserved = 1 / 4 ∧
      probability mostlyAlways none effectObserved = 3 / 4 ∧
      experimental mostlyHelped false = 1 / 4 ∧ experimental mostlyAlways false = 3 / 4 ∧
      pns mostlyHelped = 3 / 4 ∧ pns mostlyAlways = 1 / 4 := by
  have same : erase mostlyHelped none = erase mostlyAlways none := by
    rw [erase, erase, support_mostlyHelped]
  refine ⟨same, fun rung => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [same]
    exact (agree_equivalence everyIntervention quantities rung).refl _
  · rw [mostlyHelped, probability_effectObserved_untreated]
    norm_num
  · rw [mostlyAlways, probability_effectObserved_untreated]
    norm_num
  · rw [mostlyHelped, experimental_untreated_false]
    norm_num
  · rw [mostlyAlways, experimental_untreated_false]
    norm_num
  · rw [mostlyHelped, pns_untreated]
  · rw [mostlyAlways, pns_untreated]

/-! ### Weights identify what possibilities could not -/

/-- Helped, always and never in equal parts, nobody treated. -/
noncomputable def weightedMonotone : Prob Individual :=
  untreatedPopulation (1 / 3) (1 / 3) 0 (1 / 3) ⟨by norm_num, by norm_num, le_rfl, by norm_num⟩
    (by norm_num)

theorem mem_support_weightedMonotone (individual : Individual) :
    individual ∈ support weightedMonotone ↔ individual ∈ monotoneIndividuals := by
  rw [mem_support]
  obtain ⟨natural, response⟩ := individual
  cases natural <;> cases response <;>
    simp [weightedMonotone, untreatedPopulation_apply, responseWeight]

theorem mem_support_weightedFixed (individual : Individual) :
    individual ∈ support weightedFixed ↔ individual ∈ fixedIndividuals := by
  rw [mem_support]
  obtain ⟨natural, response⟩ := individual
  cases natural <;> cases response <;>
    simp [weightedFixed, untreatedPopulation_apply, responseWeight]

/-- **Weights identify what possibilities could not.**  The erasures of the
uniformly weighted monotone and fixed populations are the first slice's
populations of `monotonicity_not_identifying`, and they agree at possibilistic
rung two.  Weighted, both populations are monotone, their risk differences are
one third and zero, and so is their PNS. -/
theorem monotonicity_identifies_with_weights :
    Agree everyIntervention quantities .intervention (erase weightedMonotone none)
        (erase weightedFixed none) ∧
      NoHarm weightedMonotone ∧ NoHarm weightedFixed ∧
      experimental weightedMonotone true - experimental weightedMonotone false = 1 / 3 ∧
      experimental weightedFixed true - experimental weightedFixed false = 0 ∧
      pns weightedMonotone = 1 / 3 ∧ pns weightedFixed = 0 := by
  have monotoneSide := population_counterfactual_of_mem_iff mem_support_weightedMonotone none
  have fixedSide := population_counterfactual_of_mem_iff mem_support_weightedFixed none
  have intervention := agree_equivalence everyIntervention quantities .intervention
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact intervention.trans
      (intervention.trans (agree_intervention_of_counterfactual _ _ monotoneSide)
        intervention_monotone_fixed)
      (intervention.symm (agree_intervention_of_counterfactual _ _ fixedSide))
  · rw [NoHarm, weightedMonotone, harmProbability_untreated]
  · rw [NoHarm, weightedFixed, harmProbability_untreated]
  · rw [weightedMonotone, experimental_untreated_true, experimental_untreated_false]
    norm_num
  · rw [weightedFixed, experimental_untreated_true, experimental_untreated_false]
    norm_num
  · rw [weightedMonotone, pns_untreated]
  · rw [weightedFixed, pns_untreated]

/-! ## The weighted ladder and its erasure -/

/-- The passive queries: formulas of the unintervened system. -/
abbrev PassiveQuery := Formula (passive quantities).Atom (passive quantities).Label

/-- The probability of a passive query about the drawn individual, under a
regime. -/
noncomputable def passiveProbability (population : Prob Individual) (imposed : Option Bool)
    (query : PassiveQuery) : ℝ :=
  chance (passive quantities) population (drawn imposed) query

/-- **Weighted agreement at a rung.**  Association: every passive query about
the drawn individual left alone has the same probability.  Intervention: the
same under each single regime.  Counterfactual: every counterfactual query has
the same probability. -/
def WeightedAgree : Rung → Prob Individual → Prob Individual → Prop
  | .association, population, population' => ∀ query,
      passiveProbability population none query = passiveProbability population' none query
  | .intervention, population, population' => ∀ imposed query,
      passiveProbability population imposed query = passiveProbability population' imposed query
  | .counterfactual, population, population' => ∀ query,
      probability population none query = probability population' none query

theorem weightedAgree_association_of_intervention {population population' : Prob Individual}
    (agree : WeightedAgree .intervention population population') :
    WeightedAgree .association population population' :=
  fun query => agree none query

/-- A passive query read under a regime is a counterfactual query. -/
theorem passiveProbability_eq_probability (population : Prob Individual) (imposed : Option Bool)
    (query : PassiveQuery) :
    passiveProbability population imposed query =
      probability population none (underIntervention everyIntervention quantities
        ⟨imposed, AdmissibleClass.top_admissible _⟩ query) := by
  refine congrArg (mass population) (Set.ext fun individual => ?_)
  change _ ↔ ladder.sat (underIntervention everyIntervention quantities _ query) _
  rw [sat_underIntervention]
  cases imposed <;> exact Iff.rfl

theorem weightedAgree_intervention_of_counterfactual {population population' : Prob Individual}
    (agree : WeightedAgree .counterfactual population population') :
    WeightedAgree .intervention population population' := by
  intro imposed query
  rw [passiveProbability_eq_probability, passiveProbability_eq_probability]
  exact agree _

/-! ### Weighted counterfactual agreement is equality of the law -/

/-- "Left alone, the individual is treated." -/
def treatmentObserved : Query :=
  .dia proceed (.atom treatmentShown)

theorem sat_treatmentObserved (imposed : Option Bool) (individual : Individual) :
    ladder.sat treatmentObserved (drawn imposed individual) ↔
      imposed.getD individual.1 = true := by
  obtain ⟨natural, response⟩ := individual
  constructor
  · rintro ⟨target, step, shown⟩
    cases moves_of_step step
    exact shown
  · intro shown
    exact ⟨_, Moves.respond, shown⟩

/-- A query or its negation. -/
def literal (query : Query) : Bool → Query
  | true => query
  | false => .neg query

theorem sat_literal (query : Query) (value : Bool) (term : Stage) :
    ladder.sat (literal query value) term ↔ (ladder.sat query term ↔ value = true) := by
  cases value
  · exact ⟨fun fails => ⟨fun holds => absurd holds fails, fun impossible => absurd impossible
      Bool.false_ne_true⟩, fun same holds => Bool.false_ne_true (same.mp holds)⟩
  · exact ⟨fun holds => ⟨fun _ => rfl, fun _ => holds⟩, fun same => same.mpr rfl⟩

/-- The query characterizing one individual left alone: its natural treatment
and both of its potential outcomes. -/
def characteristic (individual : Individual) : Query :=
  .conj (literal treatmentObserved individual.1)
    (.conj (literal (effectUnder true) (individual.2.outcome true))
      (literal (effectUnder false) (individual.2.outcome false)))

theorem sat_characteristic (individual individual' : Individual) :
    ladder.sat (characteristic individual) (drawn none individual') ↔ individual' = individual := by
  change ladder.sat (literal _ _) _ ∧ ladder.sat (literal _ _) _ ∧ ladder.sat (literal _ _) _ ↔ _
  rw [sat_literal, sat_literal, sat_literal, sat_treatmentObserved, sat_effectUnder,
    sat_effectUnder]
  obtain ⟨natural, response⟩ := individual
  obtain ⟨natural', response'⟩ := individual'
  cases natural <;> cases response <;> cases natural' <;> cases response' <;> decide

theorem probability_characteristic (population : Prob Individual) (individual : Individual) :
    probability population none (characteristic individual) = population.1 individual := by
  rw [probability_eq_mass (event := {individual}) population none
    fun individual' => sat_characteristic individual individual', mass_eq_sum,
    Finset.sum_eq_single individual]
  · simp
  · intro other _ different
    simp [different]
  · intro absent
    exact absurd (Finset.mem_univ _) absent

/-- **Weighted counterfactual agreement is equality of the population law.** -/
theorem weightedAgree_counterfactual_iff {population population' : Prob Individual} :
    WeightedAgree .counterfactual population population' ↔ population = population' := by
  constructor
  · intro agree
    apply Subtype.ext
    funext individual
    rw [← probability_characteristic population individual,
      ← probability_characteristic population' individual]
    exact agree _
  · rintro rfl _
    rfl

/-! ### Erasure at rungs one and two -/

/-- What a drawn individual shows under a regime: the treatment received and
the outcome. -/
def realization (imposed : Option Bool) (individual : Individual) : Bool × Bool :=
  (imposed.getD individual.1, individual.2.outcome (imposed.getD individual.1))

/-- Stages of two populations under one regime whose drawn individuals are
matched by what they show. -/
def realizationMatch (imposed : Option Bool) (individuals individuals' : List Individual)
    (left right : Stage) : Prop :=
  left = right ∨
    (left = .population individuals imposed ∧ right = .population individuals' imposed) ∨
    ∃ individual individual', left = drawn imposed individual ∧ right = drawn imposed individual' ∧
      realization imposed individual = realization imposed individual'

theorem realizationMatch_isReductionBisimulation {imposed : Option Bool}
    {individuals individuals' : List Individual}
    (forth : ∀ individual ∈ individuals, ∃ individual' ∈ individuals',
      realization imposed individual' = realization imposed individual)
    (back : ∀ individual' ∈ individuals', ∃ individual ∈ individuals,
      realization imposed individual = realization imposed individual') :
    IsReductionBisimulation quantities (realizationMatch imposed individuals individuals') := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨⟨natural, response⟩, ⟨natural', response'⟩, rfl, rfl,
        same⟩) left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural response member =>
          obtain ⟨individual', member', same⟩ := forth (natural, response) member
          exact ⟨_, Moves.draw member', Or.inr (Or.inr ⟨(natural, response), individual', rfl, rfl,
            same.symm⟩)⟩
    · cases moves_of_step step
      exact ⟨_, Moves.respond, Or.inl
        (congrArg (fun shown : Bool × Bool => Stage.record shown.1 shown.2) same)⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨⟨natural, response⟩, ⟨natural', response'⟩, rfl, rfl,
        same⟩) right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · cases moves_of_step step with
      | @draw _ _ natural' response' member' =>
          obtain ⟨individual, member, same⟩ := back (natural', response') member'
          exact ⟨_, Moves.draw member, Or.inr (Or.inr ⟨individual, (natural', response'), rfl, rfl,
            same⟩)⟩
    · cases moves_of_step step
      exact ⟨_, Moves.respond, Or.inl
        (congrArg (fun shown : Bool × Bool => Stage.record shown.1 shown.2) same)⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨⟨natural, response⟩, ⟨natural', response'⟩, rfl, rfl,
        -⟩) atom
    · exact Iff.rfl
    · cases atom <;> exact Iff.rfl
    · cases atom <;> exact Iff.rfl

/-- A passive query or its negation. -/
def passiveLiteral (atom : Quantity) : Bool → PassiveQuery
  | true => .atom atom
  | false => .neg (.atom atom)

theorem sat_passiveLiteral (atom : Quantity) (value : Bool) (term : Stage) :
    (passive quantities).sat (passiveLiteral atom value) term ↔
      (shows atom term ↔ value = true) := by
  cases value
  · exact ⟨fun fails => ⟨fun holds => absurd holds fails, fun impossible => absurd impossible
      Bool.false_ne_true⟩, fun same holds => Bool.false_ne_true (same.mp holds)⟩
  · exact ⟨fun holds => ⟨fun _ => rfl, fun _ => holds⟩, fun same => same.mpr rfl⟩

/-- "Left to run, the individual shows this treatment and this outcome." -/
def showsRealization (shown : Bool × Bool) : PassiveQuery :=
  .dia () (.conj (passiveLiteral .treatment shown.1) (passiveLiteral .effect shown.2))

theorem sat_showsRealization (shown : Bool × Bool) (imposed : Option Bool)
    (individual : Individual) :
    (passive quantities).sat (showsRealization shown) (drawn imposed individual) ↔
      realization imposed individual = shown := by
  obtain ⟨natural, response⟩ := individual
  obtain ⟨treated, effect⟩ := shown
  constructor
  · rintro ⟨target, step, treatedHolds, effectHolds⟩
    cases moves_of_step step
    rw [sat_passiveLiteral] at treatedHolds effectHolds
    exact Prod.ext (Bool.coe_iff_coe.mp treatedHolds) (Bool.coe_iff_coe.mp effectHolds)
  · intro same
    refine ⟨_, Moves.respond, ?_, ?_⟩
    · rw [sat_passiveLiteral]
      exact Bool.coe_iff_coe.mpr (congrArg Prod.fst same)
    · rw [sat_passiveLiteral]
      exact Bool.coe_iff_coe.mpr (congrArg Prod.snd same)

/-- Equal passive probabilities under a regime match the supports by what
their individuals show. -/
theorem forth_of_passive {population population' : Prob Individual} {imposed : Option Bool}
    (agree : ∀ query,
      passiveProbability population imposed query = passiveProbability population' imposed query) :
    ∀ individual ∈ support population, ∃ individual' ∈ support population',
      realization imposed individual' = realization imposed individual := by
  intro individual member
  have positive : 0 < passiveProbability population imposed
      (showsRealization (realization imposed individual)) :=
    (mass_pos_iff population _).mpr
      ⟨individual, (sat_showsRealization _ _ _).mpr rfl, mem_support.mp member⟩
  rw [agree] at positive
  obtain ⟨individual', shown, weight⟩ := (mass_pos_iff population' _).mp positive
  exact ⟨individual', mem_support.mpr weight, (sat_showsRealization _ _ _).mp shown⟩

/-- **Equal passive probabilities under a regime make the erasures reduction
bisimilar under that regime.** -/
theorem reductionBisimilar_erase {population population' : Prob Individual} (imposed : Option Bool)
    (agree : ∀ query,
      passiveProbability population imposed query = passiveProbability population' imposed query) :
    ReductionBisimilar quantities (erase population imposed) (erase population' imposed) :=
  ⟨realizationMatch imposed (support population) (support population'),
    realizationMatch_isReductionBisimulation (forth_of_passive agree)
      (forth_of_passive fun query => (agree query).symm),
    Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- **Erasure maps the weighted ladder to the possibilistic one, rung by
rung.** -/
theorem erase_agree_of_weightedAgree {population population' : Prob Individual} :
    ∀ rung, WeightedAgree rung population population' →
      Agree everyIntervention quantities rung (erase population none) (erase population' none)
  | .association, agree => reductionBisimilar_erase none agree
  | .intervention, agree => fun context _ =>
      reductionBisimilar_erase (context.or none) (agree (context.or none))
  | .counterfactual, agree => by
      rw [weightedAgree_counterfactual_iff.mp agree]
      exact (agree_equivalence everyIntervention quantities .counterfactual).refl _

/-- **Erasure loses information at every rung.**  The two populations with
equal supports agree at every possibilistic rung and at no weighted rung. -/
theorem erasure_strict :
    (∀ rung, Agree everyIntervention quantities rung (erase mostlyHelped none)
        (erase mostlyAlways none)) ∧
      ∀ rung, ¬ WeightedAgree rung mostlyHelped mostlyAlways := by
  obtain ⟨-, possibilistic, helpedObserved, alwaysObserved, -⟩ := equalSupport_control
  refine ⟨possibilistic, fun rung agree => ?_⟩
  have association : WeightedAgree .association mostlyHelped mostlyAlways := by
    cases rung with
    | association => exact agree
    | intervention => exact weightedAgree_association_of_intervention agree
    | counterfactual =>
        exact weightedAgree_association_of_intervention
          (weightedAgree_intervention_of_counterfactual agree)
  have same := association (.dia () (.atom .effect))
  rw [passiveProbability_eq_probability, passiveProbability_eq_probability] at same
  change probability mostlyHelped none effectObserved =
    probability mostlyAlways none effectObserved at same
  rw [helpedObserved, alwaysObserved] at same
  norm_num at same

/-! ## The same bounds for any probability measure on response types -/

section Measure

open MeasureTheory

/-- Response types with every set measurable. -/
instance : MeasurableSpace Response := ⊤

/-- **The Tian–Pearl bounds for any probability measure on response types**,
from the real-valued Fréchet bounds of the measure layer. -/
theorem pns_bounds_measure (μ : Measure Response) [IsProbabilityMeasure μ] :
    max 0 (μ.real {response | response.outcome true = true} -
        μ.real {response | response.outcome false = true}) ≤ μ.real {Response.helped} ∧
      μ.real {Response.helped} ≤ min (μ.real {response | response.outcome true = true})
        (1 - μ.real {response | response.outcome false = true}) := by
  have measurable : ∀ event : Set Response, MeasurableSet event :=
    fun _ => MeasurableSpace.measurableSet_top
  have inter : {response : Response | response.outcome true = true} ∩
      {response | response.outcome false = true}ᶜ = {Response.helped} := by
    ext response
    cases response <;> simp [Response.outcome]
  have complement := probReal_compl_eq_one_sub (μ := μ)
    (measurable {response : Response | response.outcome false = true})
  have lower := Mettapedia.ProbabilityTheory.Common.FrechetBounds.frechet_lower_bound_real μ
    {response : Response | response.outcome true = true}
    {response | response.outcome false = true}ᶜ (measurable _) (measurable _)
  have upper := Mettapedia.ProbabilityTheory.Common.FrechetBounds.frechet_upper_bound_real μ
    {response : Response | response.outcome true = true}
    {response | response.outcome false = true}ᶜ
  rw [inter, complement] at lower upper
  refine ⟨?_, upper⟩
  have rewrite : μ.real {response : Response | response.outcome true = true} +
      (1 - μ.real {response : Response | response.outcome false = true}) - 1 =
    μ.real {response : Response | response.outcome true = true} -
      μ.real {response : Response | response.outcome false = true} := by ring
  rw [rewrite] at lower
  exact lower

end Measure

end Mettapedia.GSLT.Causality.WeightedResponseTypes
