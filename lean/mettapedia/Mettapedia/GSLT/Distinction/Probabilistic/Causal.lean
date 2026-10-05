import Mettapedia.GSLT.Distinction.Probabilistic.Domination
import Mettapedia.GSLT.Causality.WeightedResponseTypes

/-!
# Probabilities of causation over several random steps

`GSLT.Causality.WeightedResponseTypes` puts weights on one step: an individual
is drawn, and responds deterministically.  Here a **noisy population**
(`NoisyPopulation`) takes two random steps: a unit is drawn, then its response
is noisy, a distribution over individuals (natural treatment and response
type).  It is a finite labelled Markov chain (`NoisyPopulation.chain`) with
the moves `draw` and `respond` and, at a settled individual, the readouts of
the potential outcomes `Y_x` and of "treatment is necessary and sufficient".

* **The probabilities of causation are two-step expressions.**  The
  experimental marginal `P(Y_x)` and the probability of necessity and
  sufficiency `PNS = P(Y_1 ∧ ¬Y_0)` are the values at the root of
  `next draw (next respond (observe ·))` at discount one (`experimental`,
  `pns`).  They are the one-step quantities of the marginal population
  (`experimental_eq_marginal`, `pns_eq_marginal`), so the Tian–Pearl bounds hold
  (`pns_bounds`).
* **PNS transports along probabilistic bisimulation** (`pns_eq_of_bisimilar`),
  and along the Kantorovich metric at discount one with constant one
  (`abs_pns_sub_le`).
* **PNS does not transport along support bisimulation.**  Support bisimulation
  (an exact bisimulation of the supports, `SupportBisimilar`) transports only
  whether PNS is positive (`pns_pos_iff_of_supportBisimilar`).  Two populations
  whose single unit responds `helped` or `never` with probabilities `1/2, 1/2`
  and `1/4, 3/4` are support bisimilar at the root, with PNS `1/2` and `1/4`
  (`support_does_not_transport_pns`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.Causal

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Cybernetics.MindWorldApproximation
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes
open Mettapedia.GSLT.Causality.WeightedResponseTypes
open Mettapedia.GSLT.Causality.WeightedObservers
open Mettapedia.InformationTheory
open FunctionalExpression

/-! ## Stages, moves and readouts -/

/-- The stages: before the draw (`none`), a drawn unit, a settled individual. -/
abbrev Stage (U : Type*) := Option (U ⊕ Individual)

/-- The moves: draw a unit, let it respond. -/
inductive Move
  | draw
  | respond
  deriving DecidableEq

instance : Fintype Move where
  elems := {.draw, .respond}
  complete move := by cases move <;> simp

/-- The readouts of a settled individual: the potential outcome `Y_x`, and
"treatment is necessary and sufficient". -/
inductive Readout
  | effect (treatment : Bool)
  | necessity
  deriving DecidableEq

instance : Fintype Readout where
  elems := {.effect false, .effect true, .necessity}
  complete readout := by
    cases readout with
    | effect treatment => cases treatment <;> simp
    | necessity => simp

/-- **A noisy population**: a distribution of units, and for each unit a
distribution of individuals, its noisy response. -/
structure NoisyPopulation (U : Type*) [Fintype U] where
  drawWeight : U → ℝ
  draw_distribution : IsDistribution drawWeight
  respondWeight : U → Individual → ℝ
  respond_distribution : ∀ unit, IsDistribution (respondWeight unit)

/-- The readouts of a settled individual. -/
def settledValue : Readout → Individual → ℝ
  | .effect treatment, individual => if individual.2.outcome treatment = true then 1 else 0
  | .necessity, individual => if individual.2 = .helped then 1 else 0

/-- The readouts of a stage: only a settled individual shows anything. -/
def readoutValue {U : Type*} (readout : Readout) : Stage U → ℝ
  | some (.inr individual) => settledValue readout individual
  | _ => 0

namespace NoisyPopulation

variable {U : Type*} [Fintype U] [DecidableEq U] (N : NoisyPopulation U)

/-- The draw, as a distribution over stages. -/
def drawStep : Stage U → ℝ
  | some (.inl unit) => N.drawWeight unit
  | _ => 0

/-- The response of a unit, as a distribution over stages. -/
def respondStep (unit : U) : Stage U → ℝ
  | some (.inr individual) => N.respondWeight unit individual
  | _ => 0

omit [DecidableEq U] in
theorem isDistribution_drawStep : IsDistribution N.drawStep where
  nonneg stage := by
    rcases stage with _ | unit | individual
    · exact le_rfl
    · exact N.draw_distribution.nonneg unit
    · exact le_rfl
  sum_eq_one := by
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    simp only [drawStep, Finset.sum_const_zero, zero_add, add_zero]
    exact N.draw_distribution.sum_eq_one

omit [DecidableEq U] in
theorem isDistribution_respondStep (unit : U) : IsDistribution (N.respondStep unit) where
  nonneg stage := by
    rcases stage with _ | unit' | individual
    · exact le_rfl
    · exact le_rfl
    · exact (N.respond_distribution unit).nonneg individual
  sum_eq_one := by
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    simp only [respondStep, Finset.sum_const_zero, zero_add]
    exact (N.respond_distribution unit).sum_eq_one

/-- The transitions: drawing at the root, responding at a unit, staying put
otherwise. -/
noncomputable def trans : Move → Stage U → Stage U → ℝ
  | .draw, none => N.drawStep
  | .respond, some (.inl unit) => N.respondStep unit
  | _, stage => dirac stage


/-- **The chain of a noisy population.** -/
noncomputable def chain : LabelledMarkovChain ℝ Move Readout (Stage U) where
  trans := N.trans
  isDistribution move stage := by
    rcases move with _ | _ <;> rcases stage with _ | unit | individual
    · exact N.isDistribution_drawStep
    · exact isDistribution_dirac _
    · exact isDistribution_dirac _
    · exact isDistribution_dirac _
    · exact N.isDistribution_respondStep unit
    · exact isDistribution_dirac _
  observe := readoutValue

theorem observe_nonneg (readout : Readout) (stage : Stage U) : 0 ≤ N.chain.observe readout stage := by
  change 0 ≤ readoutValue readout stage
  rcases stage with _ | unit | individual
  · exact le_rfl
  · exact le_rfl
  · change 0 ≤ settledValue readout individual
    rcases readout with treatment | _ <;> simp only [settledValue] <;> split_ifs <;> norm_num

/-! ## The probabilities of causation -/

/-- The two-step readout: draw, respond, read. -/
def twoStep (readout : Readout) : FunctionalExpression ℝ Move Readout :=
  .next .draw (.next .respond (.observe readout))

/-- **The experimental marginal** `P(Y_x)` of a noisy population. -/
noncomputable def experimental (treatment : Bool) : ℝ :=
  (twoStep (.effect treatment)).eval N.chain 1 none

/-- **The probability of necessity and sufficiency** of a noisy population. -/
noncomputable def pns : ℝ :=
  (twoStep .necessity).eval N.chain 1 none

/-- The two-step readout is the expectation, over units and responses, of the
readout. -/
theorem twoStep_eval (readout : Readout) :
    (twoStep readout).eval N.chain 1 none =
      ∑ unit, N.drawWeight unit *
        ∑ individual, N.respondWeight unit individual *
          settledValue readout individual := by
  simp only [twoStep, eval, one_mul, expect]
  change ∑ x, N.drawStep x * ∑ y, N.trans .respond x y * readoutValue readout y = _
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [drawStep, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  refine Finset.sum_congr rfl fun unit _ => ?_
  congr 1
  change ∑ y, N.respondStep unit y * readoutValue readout y = _
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [respondStep, readoutValue, zero_mul, Finset.sum_const_zero, zero_add]

/-- **The marginal population**: the law of the settled individual. -/
noncomputable def marginal : Prob Individual :=
  ⟨fun individual => ∑ unit, N.drawWeight unit * N.respondWeight unit individual,
    fun individual => Finset.sum_nonneg fun unit _ =>
      mul_nonneg (N.draw_distribution.nonneg unit) ((N.respond_distribution unit).nonneg individual),
    by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, fun unit => (N.respond_distribution unit).sum_eq_one, mul_one]
      exact N.draw_distribution.sum_eq_one⟩

theorem twoStep_eq_marginal (readout : Readout) (event : Set Individual)
    (indicator : ∀ individual, settledValue readout individual =
      event.indicator 1 individual) :
    (twoStep readout).eval N.chain 1 none = mass N.marginal event := by
  rw [twoStep_eval, mass_eq_sum]
  simp_rw [indicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun individual _ => ?_
  change _ = (∑ unit, N.drawWeight unit * N.respondWeight unit individual) *
    event.indicator 1 individual
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun unit _ => by ring

/-- **The experimental marginal is that of the marginal population.** -/
theorem experimental_eq_marginal (treatment : Bool) :
    N.experimental treatment = Mettapedia.GSLT.Causality.WeightedResponseTypes.experimental N.marginal treatment := by
  rw [Mettapedia.GSLT.Causality.WeightedResponseTypes.experimental_eq_mass]
  refine N.twoStep_eq_marginal _ _ fun individual => ?_
  by_cases shown : individual.2.outcome treatment = true
  · simp [settledValue, shown]
  · simp [settledValue, shown]

/-- **PNS is that of the marginal population.** -/
theorem pns_eq_marginal : N.pns = Mettapedia.GSLT.Causality.WeightedResponseTypes.pns N.marginal := by
  rw [Mettapedia.GSLT.Causality.WeightedResponseTypes.pns_eq_mass]
  refine N.twoStep_eq_marginal _ _ fun individual => ?_
  by_cases helped : individual.2 = .helped
  · simp [settledValue, helped]
  · simp [settledValue, helped]

/-- **The Tian–Pearl bounds for a noisy population.** -/
theorem pns_bounds :
    max 0 (N.experimental true - N.experimental false) ≤ N.pns ∧
      N.pns ≤ min (N.experimental true) (1 - N.experimental false) := by
  rw [experimental_eq_marginal, experimental_eq_marginal, pns_eq_marginal]
  exact Mettapedia.GSLT.Causality.WeightedResponseTypes.pns_bounds N.marginal

end NoisyPopulation

/-! ## Transport along probabilistic bisimulation -/

section Transport

variable {U U' : Type*} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U']
  (N : NoisyPopulation U) (N' : NoisyPopulation U')

/-- **PNS transports along probabilistic bisimulation.** -/
theorem pns_eq_of_bisimilar (bisimilar : ProbabilisticallyBisimilar N.chain N'.chain none none) :
    N.pns = N'.pns :=
  bisimilar.eval_eq 1 (NoisyPopulation.twoStep .necessity)

/-- The experimental marginals transport too. -/
theorem experimental_eq_of_bisimilar
    (bisimilar : ProbabilisticallyBisimilar N.chain N'.chain none none) (treatment : Bool) :
    N.experimental treatment = N'.experimental treatment :=
  bisimilar.eval_eq 1 (NoisyPopulation.twoStep (.effect treatment))

/-- **PNS is `1`-Lipschitz in the Kantorovich metric at discount one.** -/
theorem abs_pns_sub_le : |N.pns - N'.pns| ≤ bisimulationMetric N.chain N'.chain 1 none none :=
  abs_eval_sub_le_bisimulationMetric zero_le_one le_rfl (NoisyPopulation.twoStep .necessity) none
    none

end Transport

/-! ## Support bisimulation transports only positivity -/

section Support

variable {A Atom S T : Type*} [Fintype S] [Fintype T] [Fintype Atom]

/-- **Support bisimilarity** of two chains: an exact bisimulation of the
supports of every action, at observation gap zero. -/
def SupportBisimilar (P : LabelledMarkovChain ℝ A Atom S) (Q : LabelledMarkovChain ℝ A Atom T)
    (s : S) (t : T) : Prop :=
  ∃ R : S → T → Prop, (∀ a, IsApproxBisimulation observationGap (P.supportStep a)
    (Q.supportStep a) P.observation Q.observation 0 R) ∧ R s t

/-- **Probabilistic bisimilarity implies support bisimilarity.** -/
theorem ProbabilisticallyBisimilar.supportBisimilar {P : LabelledMarkovChain ℝ A Atom S}
    {Q : LabelledMarkovChain ℝ A Atom T} {s : S} {t : T}
    (bisimilar : ProbabilisticallyBisimilar P Q s t) : SupportBisimilar P Q s t := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  exact ⟨R, fun a => bisimulation.isApproxBisimulation_support a, related⟩

omit [Fintype Atom] in
/-- A two-step readout of a nonnegative observable is positive exactly along a
supported path to a positive reading. -/
theorem twoStep_pos_iff (P : LabelledMarkovChain ℝ A Atom S) (a b : A) (i : Atom)
    (nonneg : ∀ x, 0 ≤ P.observe i x) (s : S) :
    0 < (FunctionalExpression.next a (.next b (.observe i))).eval P 1 s ↔
      ∃ x y, P.supportStep a s x ∧ P.supportStep b x y ∧ 0 < P.observe i y := by
  simp only [eval, one_mul, expect]
  have inner_nonneg : ∀ x, 0 ≤ ∑ y, P.trans b x y * P.observe i y := fun x =>
    Finset.sum_nonneg fun y _ => mul_nonneg ((P.isDistribution b x).nonneg y) (nonneg y)
  rw [Finset.sum_pos_iff_of_nonneg fun x _ =>
    mul_nonneg ((P.isDistribution a s).nonneg x) (inner_nonneg x)]
  constructor
  · rintro ⟨x, _, positive⟩
    have parts := pos_and_pos_or_neg_and_neg_of_mul_pos positive
    rcases parts with ⟨first, second⟩ | ⟨first, _⟩
    · rw [Finset.sum_pos_iff_of_nonneg fun y _ =>
        mul_nonneg ((P.isDistribution b x).nonneg y) (nonneg y)] at second
      obtain ⟨y, _, product⟩ := second
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos product with ⟨third, fourth⟩ | ⟨third, _⟩
      · exact ⟨x, y, first.ne', third.ne', fourth⟩
      · exact absurd third (not_lt.mpr ((P.isDistribution b x).nonneg y))
    · exact absurd first (not_lt.mpr ((P.isDistribution a s).nonneg x))
  · rintro ⟨x, y, first, second, third⟩
    refine ⟨x, Finset.mem_univ x, mul_pos (lt_of_le_of_ne ((P.isDistribution a s).nonneg x)
      (Ne.symm first)) ?_⟩
    exact Finset.sum_pos' (fun y _ => mul_nonneg ((P.isDistribution b x).nonneg y) (nonneg y))
      ⟨y, Finset.mem_univ y, mul_pos (lt_of_le_of_ne ((P.isDistribution b x).nonneg y)
        (Ne.symm second)) third⟩

/-- Exact support bisimulations transfer supported paths to positive readings. -/
theorem path_transfer {P : LabelledMarkovChain ℝ A Atom S} {Q : LabelledMarkovChain ℝ A Atom T}
    {R : S → T → Prop}
    (bisimulation : ∀ a, IsApproxBisimulation observationGap (P.supportStep a) (Q.supportStep a)
      P.observation Q.observation 0 R) {s : S} {t : T} (related : R s t) (a b : A) (i : Atom)
    (path : ∃ x y, P.supportStep a s x ∧ P.supportStep b x y ∧ 0 < P.observe i y) :
    ∃ x y, Q.supportStep a t x ∧ Q.supportStep b x y ∧ 0 < Q.observe i y := by
  obtain ⟨x, y, first, second, positive⟩ := path
  obtain ⟨x', first', related'⟩ := (bisimulation a).1.forth related x first
  obtain ⟨y', second', related''⟩ := (bisimulation b).1.forth related' y second
  have gap := (observationGap_le_iff.mp ((bisimulation b).1.close related'')).2 i
  have same : P.observe i y = Q.observe i y' := by
    have := abs_nonpos_iff.mp gap
    change P.observe i y - Q.observe i y' = 0 at this
    linarith
  exact ⟨x', y', first', second', same ▸ positive⟩

/-- **Support bisimilarity transports whether a two-step readout is
positive.** -/
theorem twoStep_pos_iff_of_supportBisimilar {P : LabelledMarkovChain ℝ A Atom S}
    {Q : LabelledMarkovChain ℝ A Atom T} {s : S} {t : T} (bisimilar : SupportBisimilar P Q s t)
    (a b : A) (i : Atom) (nonneg : ∀ x, 0 ≤ P.observe i x) (nonneg' : ∀ y, 0 ≤ Q.observe i y) :
    0 < (FunctionalExpression.next a (.next b (.observe i))).eval P 1 s ↔
      0 < (FunctionalExpression.next a (.next b (.observe i))).eval Q 1 t := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  rw [twoStep_pos_iff P a b i nonneg, twoStep_pos_iff Q a b i nonneg']
  constructor
  · exact path_transfer bisimulation related a b i
  · intro path
    obtain ⟨x, y, first, second, positive⟩ := path
    obtain ⟨x', first', related'⟩ := (bisimulation a).2.forth related x first
    obtain ⟨y', second', related''⟩ := (bisimulation b).2.forth related' y second
    have gap := (observationGap_le_iff.mp ((bisimulation b).2.close related'')).2 i
    have same : Q.observe i y = P.observe i y' := by
      have := abs_nonpos_iff.mp gap
      change Q.observe i y - P.observe i y' = 0 at this
      linarith
    exact ⟨x', y', first', second', same ▸ positive⟩

/-- **Support bisimilarity transports whether PNS is positive.** -/
theorem pns_pos_iff_of_supportBisimilar {U U' : Type*} [Fintype U] [DecidableEq U] [Fintype U']
    [DecidableEq U'] (N : NoisyPopulation U) (N' : NoisyPopulation U')
    (bisimilar : SupportBisimilar N.chain N'.chain none none) : 0 < N.pns ↔ 0 < N'.pns :=
  twoStep_pos_iff_of_supportBisimilar bisimilar .draw .respond .necessity (N.observe_nonneg _)
    (N'.observe_nonneg _)

end Support

/-! ## The control: equal supports, different PNS -/

section Control

/-- A population of one unit that responds `helped` with probability `p` and
`never` otherwise, naturally untreated. -/
noncomputable def coin (p : ℝ) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1) : NoisyPopulation Unit where
  drawWeight _ := 1
  draw_distribution := ⟨fun _ => zero_le_one, by simp⟩
  respondWeight _ individual :=
    if individual = (false, .helped) then p else if individual = (false, .never) then 1 - p else 0
  respond_distribution _ := ⟨fun individual => by
      split_ifs <;> linarith, by
      rw [sum_individual]
      simp⟩

theorem coin_pns (p : ℝ) (p_nonneg : 0 ≤ p) (p_le : p ≤ 1) : (coin p p_nonneg p_le).pns = p := by
  unfold NoisyPopulation.pns
  rw [NoisyPopulation.twoStep_eval, Fintype.sum_unique, sum_individual]
  simp [coin, settledValue]

/-- Two coins with weights strictly between `0` and `1` have the same supports at
every stage. -/
theorem coin_supportBisimilar {p q : ℝ} (p_pos : 0 < p) (p_lt : p < 1) (q_pos : 0 < q)
    (q_lt : q < 1) :
    SupportBisimilar (coin p p_pos.le p_lt.le).chain (coin q q_pos.le q_lt.le).chain none none := by
  have sameSupport : ∀ (a : Move) (x y : Stage Unit),
      (coin p p_pos.le p_lt.le).chain.supportStep a x y ↔
        (coin q q_pos.le q_lt.le).chain.supportStep a x y := by
    intro a x y
    change (coin p _ _).trans a x y ≠ 0 ↔ (coin q _ _).trans a x y ≠ 0
    rcases a with _ | _ <;> rcases x with _ | u | individual
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases y with _ | u' | individual'
      · rfl
      · rfl
      · change (coin p _ _).respondWeight u individual' ≠ 0 ↔
          (coin q _ _).respondWeight u individual' ≠ 0
        simp only [coin]
        split_ifs <;> constructor <;> intro _ <;> first | assumption | (intro h; linarith)
    · rfl
  have sameObservation : (coin p p_pos.le p_lt.le).chain.observation =
      (coin q q_pos.le q_lt.le).chain.observation := rfl
  refine ⟨Eq, fun a => ⟨⟨fun x y related => ?_, fun x y related x' moved => ?_⟩,
    ⟨fun y x related => ?_, fun y x related y' moved => ?_⟩⟩, rfl⟩
  · subst related
    rw [sameObservation, observationGap_self]
  · subst related
    exact ⟨x', (sameSupport a x x').mp moved, rfl⟩
  · change x = y at related
    subst related
    rw [sameObservation, observationGap_self]
  · change x = y at related
    subst related
    exact ⟨y', (sameSupport a x y').mpr moved, rfl⟩

/-- **PNS does not transport along support bisimulation**: two populations are
support bisimilar at the root, with PNS one half and one quarter. -/
theorem support_does_not_transport_pns :
    SupportBisimilar (coin (1 / 2) (by norm_num) (by norm_num)).chain
        (coin (1 / 4) (by norm_num) (by norm_num)).chain none none ∧
      (coin (1 / 2) (by norm_num) (by norm_num)).pns = 1 / 2 ∧
      (coin (1 / 4) (by norm_num) (by norm_num)).pns = 1 / 4 :=
  ⟨coin_supportBisimilar (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    coin_pns _ _ _, coin_pns _ _ _⟩

/-- Hence the two populations are not probabilistically bisimilar at the root. -/
theorem coins_not_bisimilar :
    ¬ ProbabilisticallyBisimilar (coin (1 / 2) (by norm_num) (by norm_num)).chain
      (coin (1 / 4) (by norm_num) (by norm_num)).chain none none := by
  intro bisimilar
  have same := pns_eq_of_bisimilar _ _ bisimilar
  rw [coin_pns, coin_pns] at same
  norm_num at same

end Control

end Mettapedia.GSLT.Distinction.Probabilistic.Causal
