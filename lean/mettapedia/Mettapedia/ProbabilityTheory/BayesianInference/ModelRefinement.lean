import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveSemantics
import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveTrace
import Mettapedia.Cybernetics.ApproximateAdequacy.Coupling
import Mettapedia.ProbabilityTheory.BayesianInference.InformationLaws
import Mettapedia.ProbabilityTheory.BayesianInference.SufficientFiltering
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Refinement of a finite latent model

The expanded model and the coarse model are supplied independently. An explicit
state map sends the expanded state onto the coarse state, and a section chooses
one expanded state in each fibre. Compatibility is the pushforward equation for
the supplied prior, the controlled transition, and the emission.

Those equations give the same coarse prediction, the same filtering update on
an observation of positive evidence, the same finite execution trace, and the
same value for every finite observation-contingent policy whose reward factors
through the state map.
A coupling cost bounds the one-step reward gap of an arbitrary coarse law.
Observation agreement and successor cost remain separate hypotheses of the
multi-step adaptive bound. Expected information gain under a coarser
observation, and the carrier comparison for a colliding section, are separate
statements with their own hypotheses.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference.ModelRefinement

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.FiniteLumpability
open Mettapedia.Cybernetics.ApproximateAdequacy hiding dirac

/-- Pushing a finite law forward twice is the pushforward along the composite map. -/
theorem coarsen_comp {S C D : Type*} [Fintype S] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] (prior : Prob S) (view : S → C) (next : C → D) :
    coarsen (coarsen prior view) next = coarsen prior (next ∘ view) := by
  apply Subtype.ext
  funext outcome
  rw [coarsen_apply, coarsen_apply]
  have mass :
      (coarsen prior view).1 =
        fun image => Mettapedia.InformationTheory.FiniteRV.pushforward prior.1 view image := by
    funext image
    rw [coarsen_apply]
  rw [mass]
  exact Mettapedia.InformationTheory.FiniteRV.pushforward_pushforward
    prior.1 view next outcome

/-- A kernel that reads the state only through `view` binds after that pushforward. -/
theorem bind_of_coarsen {S C D : Type*} [Fintype S] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] (prior : Prob S) (view : S → C) (kernel : C → Prob D) :
    bind prior (kernel ∘ view) = bind (coarsen prior view) kernel := by
  apply Subtype.ext
  funext outcome
  rw [bind_apply, bind_apply]
  exact (coarsen_expectation prior view (fun image => (kernel image).1 outcome)).symm

section Supplied

variable {Fine Coarse Action : Type*} [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]

/-- A transition that factors through the state map is strongly lumpable. -/
theorem lumpable_of_transition (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state)) :
    StrongLumpability view fineKernel := by
  intro action source target same
  rw [transition action source, transition action target, same]

/-- At each section point the supplied coarse row is the lumped fine row. -/
theorem supplied_matches_lumped (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (representative : Coarse → Fine) (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    (action : Action) (state : Coarse) :
    lumpedKernel view fineKernel representative action state = coarseKernel action state := by
  have push := transition action (representative state)
  rw [sectionLaw state] at push
  exact push

/-- The supplied coarse kernel is the lumped kernel on every action. -/
theorem supplied_kernel_agrees (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (representative : Coarse → Fine) (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state)) :
    lumpedKernel view fineKernel representative = coarseKernel := by
  funext action state
  exact supplied_matches_lumped view fineKernel coarseKernel representative sectionLaw
    transition action state

/-- Coarse prediction agrees with the pushforward of expanded prediction. -/
theorem prediction_preserved (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (representative : Coarse → Fine) (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    (prior : Prob Fine) (action : Action) :
    coarsen (bind prior (fineKernel action)) view =
      bind (coarsen prior view) (coarseKernel action) := by
  rw [coarsen_predict view fineKernel representative sectionLaw
    (lumpable_of_transition view fineKernel coarseKernel transition) prior action]
  exact congrArg (Prob.bind (coarsen prior view))
    (congrFun (supplied_kernel_agrees view fineKernel coarseKernel representative sectionLaw
      transition) action)

/-- The same prediction square holds for a supplied prior with the same pushforward. -/
theorem prediction_of_supplied_prior (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (representative : Coarse → Fine) (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    (finePrior : Prob Fine) (coarsePrior : Prob Coarse)
    (priorPush : coarsen finePrior view = coarsePrior) (action : Action) :
    coarsen (bind finePrior (fineKernel action)) view =
      bind coarsePrior (coarseKernel action) := by
  rw [prediction_preserved view fineKernel coarseKernel representative sectionLaw transition
      finePrior action, priorPush]

/-- Filtering on positive evidence pushes forward to the coarse posterior. -/
theorem filtering_preserved (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (representative : Coarse → Fine) (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    (prior : Prob Fine) (action : Action) (likelihood : Coarse → ℝ)
    (nonneg : ∀ state, 0 ≤ likelihood state)
    (possible : 0 < evidence (bind prior (fineKernel action)) (likelihood ∘ view)) :
    coarsen (posterior (bind prior (fineKernel action)) (likelihood ∘ view)
        (fun state => nonneg (view state)) possible) view =
      posterior (bind (coarsen prior view) (coarseKernel action)) likelihood nonneg
        (by
          rw [← prediction_preserved view fineKernel coarseKernel representative sectionLaw
              transition prior action, evidence_coarsen]
          exact possible) := by
  rw [coarsen_filter_step view fineKernel representative sectionLaw
    (lumpable_of_transition view fineKernel coarseKernel transition)
    prior action likelihood nonneg possible]
  apply Subtype.ext
  funext state
  rw [posterior_apply, posterior_apply,
    supplied_kernel_agrees view fineKernel coarseKernel representative sectionLaw transition]

/-- Joint transitions agree when emissions and state transitions push forward. -/
theorem transition_emission_compatible (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (fineEmit : Action → Fine → Prob Obs) (coarseEmit : Action → Coarse → Prob Obs)
    (emission : ∀ action state, fineEmit action state = coarseEmit action (view state))
    (action : Action) (state : Fine) :
    coarsen (joint (fineKernel action state) (fineEmit action))
        (fun next => (view next.1, next.2)) =
      joint (coarseKernel action (view state)) (coarseEmit action) := by
  rw [show fineEmit action = coarseEmit action ∘ view from funext (emission action),
    coarsen_joint (fineKernel action state) view (coarseEmit action)]
  exact congrArg (fun law => joint law (coarseEmit action)) (transition action state)

/-- Every finite adaptive policy has the same value when the reward factors through the view. -/
theorem policy_preserved (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (fineEmit : Action → Fine → Prob Obs) (coarseEmit : Action → Coarse → Prob Obs)
    (emission : ∀ action state, fineEmit action state = coarseEmit action (view state))
    (reward : Coarse → ℝ) {n : ℕ} (policy : ObservationPolicy Obs Action n) (state : Fine) :
    adaptiveValue (fun action state => joint (fineKernel action state) (fineEmit action))
        (reward ∘ view) policy state =
      adaptiveValue (fun action state => joint (coarseKernel action state) (coarseEmit action))
        reward policy (view state) := by
  refine adaptiveValue_coarsen view
      (fun action state => joint (fineKernel action state) (fineEmit action))
      (fun action state => joint (coarseKernel action state) (coarseEmit action))
      ?_ reward policy state
  intro action state
  exact transition_emission_compatible view fineKernel coarseKernel transition
    fineEmit coarseEmit emission action state

/-- The prior-averaged policy value agrees for a supplied pushforward prior. -/
theorem expected_policy_preserved (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (fineEmit : Action → Fine → Prob Obs) (coarseEmit : Action → Coarse → Prob Obs)
    (emission : ∀ action state, fineEmit action state = coarseEmit action (view state))
    (finePrior : Prob Fine) (coarsePrior : Prob Coarse)
    (priorPush : coarsen finePrior view = coarsePrior) (reward : Coarse → ℝ) {n : ℕ}
    (policy : ObservationPolicy Obs Action n) :
    expect finePrior.1
        (adaptiveValue (fun action state => joint (fineKernel action state) (fineEmit action))
          (reward ∘ view) policy) =
      expect coarsePrior.1
        (adaptiveValue (fun action state => joint (coarseKernel action state) (coarseEmit action))
          reward policy) := by
  have averaged := expected_adaptiveValue_coarsen view
    (fun action state => joint (fineKernel action state) (fineEmit action))
    (fun action state => joint (coarseKernel action state) (coarseEmit action))
    (fun action state => transition_emission_compatible view fineKernel coarseKernel transition
      fineEmit coarseEmit emission action state)
    finePrior reward policy
  rw [priorPush] at averaged
  exact averaged

/-- The finite execution trace pushes forward along the state map. -/
theorem trace_preserved [DecidableEq Fine] (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (fineEmit : Action → Fine → Prob Obs) (coarseEmit : Action → Coarse → Prob Obs)
    (emission : ∀ action state, fineEmit action state = coarseEmit action (view state))
    {n : ℕ} (policy : ObservationPolicy Obs Action n) (state : Fine) :
    coarsen
        (traceLaw (fun action state => joint (fineKernel action state) (fineEmit action))
          policy state)
        (fun trace i => (view (trace i).1, (trace i).2)) =
      traceLaw (fun action state => joint (coarseKernel action state) (coarseEmit action))
        policy (view state) := by
  induction n generalizing state with
  | zero =>
      conv_lhs => rw [traceLaw]
      conv_rhs => rw [traceLaw]
      rw [coarsen_dirac]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      conv_lhs => rw [traceLaw]
      conv_rhs => rw [traceLaw]
      rw [coarsen_bind]
      have kernelRewritten :
          (fun next : Fine × Obs =>
            coarsen
              (coarsen
                (traceLaw (fun action source => joint (fineKernel action source) (fineEmit action))
                  (policy.2 next.2) next.1)
                (fun earlier => Fin.cons next earlier))
              (fun trace : Fin (n + 1) → Fine × Obs =>
                fun i => (view (trace i).1, (trace i).2))) =
            fun next : Fine × Obs =>
              coarsen
                (traceLaw
                  (fun action source => joint (coarseKernel action source) (coarseEmit action))
                  (policy.2 next.2) (view next.1))
                (fun earlier => Fin.cons (view next.1, next.2) earlier) := by
        funext next
        rw [coarsen_comp]
        have mapCons :
            (fun trace : Fin (n + 1) → Fine × Obs => fun i => (view (trace i).1, (trace i).2)) ∘
                (fun earlier : Fin n → Fine × Obs => Fin.cons next earlier) =
              (fun earlier : Fin n → Coarse × Obs => Fin.cons (view next.1, next.2) earlier) ∘
                (fun trace : Fin n → Fine × Obs => fun i => (view (trace i).1, (trace i).2)) := by
          funext earlier i
          cases i using Fin.cases with
          | zero => rfl
          | succ _ => rfl
        rw [mapCons, ← coarsen_comp, ih]
      rw [kernelRewritten]
      have factored :
          (fun next : Fine × Obs =>
            coarsen
              (traceLaw (fun action source => joint (coarseKernel action source) (coarseEmit action))
                (policy.2 next.2) (view next.1))
              (fun earlier => Fin.cons (view next.1, next.2) earlier)) =
            (fun next : Coarse × Obs =>
              coarsen
                (traceLaw
                  (fun action source => joint (coarseKernel action source) (coarseEmit action))
                  (policy.2 next.2) next.1)
                (fun earlier => Fin.cons next earlier)) ∘
              fun next => (view next.1, next.2) := rfl
      rw [factored, bind_of_coarsen,
        transition_emission_compatible view fineKernel coarseKernel transition
          fineEmit coarseEmit emission policy.1 state]

/-- Expected terminal reward of the execution trace agrees with the preserved policy value. -/
theorem trace_reward_preserved [DecidableEq Fine] (view : Fine → Coarse)
    (fineKernel : Action → Fine → Prob Fine) (coarseKernel : Action → Coarse → Prob Coarse)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (fineEmit : Action → Fine → Prob Obs) (coarseEmit : Action → Coarse → Prob Obs)
    (emission : ∀ action state, fineEmit action state = coarseEmit action (view state))
    (reward : Coarse → ℝ) {n : ℕ} (policy : ObservationPolicy Obs Action n) (state : Fine) :
    (∑ trace,
        (traceLaw (fun action state => joint (fineKernel action state) (fineEmit action))
          policy state).1 trace *
          reward (view (traceTerminal state trace))) =
      ∑ trace,
        (traceLaw (fun action state => joint (coarseKernel action state) (coarseEmit action))
          policy (view state)).1 trace *
          reward (traceTerminal (view state) trace) := by
  have fineReward :=
    traceLaw_value (fun action state => joint (fineKernel action state) (fineEmit action))
      (reward ∘ view) policy state
  have coarseReward :=
    traceLaw_value (fun action state => joint (coarseKernel action state) (coarseEmit action))
      reward policy (view state)
  simp only [Function.comp_apply] at fineReward
  rw [fineReward, coarseReward]
  exact policy_preserved view fineKernel coarseKernel transition fineEmit coarseEmit emission
    reward policy state

end Supplied

section CouplingBounds

variable {Fine Coarse : Type*} [Fintype Fine] [Fintype Coarse] [DecidableEq Coarse]

/-- The identity coupling of one finite law, supported on the diagonal. -/
noncomputable def diagonalCoupling {α : Type*} [Fintype α] [DecidableEq α] (law : Prob α) :
    Coupling law.1 law.1 where
  weight x y := if x = y then law.1 x else 0
  nonneg x y := by
    split_ifs
    · exact law.2.1 x
    · exact le_rfl
  sum_right x :=
    Finset.sum_ite_eq_of_mem Finset.univ x (fun _ => law.1 x) (Finset.mem_univ x)
  sum_left y :=
    Finset.sum_ite_eq_of_mem' Finset.univ y (fun x => law.1 x) (Finset.mem_univ y)

/-- A diagonal cost vanishes when the cost itself vanishes on the diagonal. -/
theorem diagonalCoupling_cost_diag {α : Type*} [Fintype α] [DecidableEq α]
    (law : Prob α) (m : α → α → ℝ) (diag : ∀ x, m x x = 0) :
    (diagonalCoupling law).cost m = 0 := by
  unfold Coupling.cost
  change ∑ x, ∑ y, (if x = y then law.1 x else 0) * m x y = 0
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases same : x = y
  · subst same
    rw [if_pos rfl, diag x, mul_zero]
  · rw [if_neg same, zero_mul]

/-- The absolute reward cost of the diagonal coupling is zero. -/
theorem diagonalCoupling_abs_cost {α : Type*} [Fintype α] [DecidableEq α]
    (law : Prob α) (reward : α → ℝ) :
    (diagonalCoupling law).cost (fun x y => |reward x - reward y|) = 0 :=
  diagonalCoupling_cost_diag law _ fun x => by rw [sub_self, abs_zero]

/-- Any coupling of the pushed fine law with a supplied coarse law bounds the reward gap. -/
theorem predictive_coupling_bound (view : Fine → Coarse) (fineLaw : Prob Fine)
    (coarseLaw : Prob Coarse) (reward : Coarse → ℝ)
    (coupling : Coupling (coarsen fineLaw view).1 coarseLaw.1)
    (discrepancy : Coarse → Coarse → ℝ)
    (bound : ∀ x y, |reward x - reward y| ≤ discrepancy x y) :
    |∑ s, fineLaw.1 s * reward (view s) - ∑ c, coarseLaw.1 c * reward c| ≤
      coupling.cost discrepancy := by
  have gap := coupling.abs_expect_sub_le bound
  unfold Mettapedia.Cybernetics.ApproximateAdequacy.expect at gap
  rwa [coarsen_expectation] at gap

/-- Exact transition and prior compatibility make the predictive reward gap zero. -/
theorem compatible_prediction_gap {Action : Type*}
    (view : Fine → Coarse) (fineKernel : Action → Fine → Prob Fine)
    (coarseKernel : Action → Coarse → Prob Coarse) (representative : Coarse → Fine)
    (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    (finePrior : Prob Fine) (coarsePrior : Prob Coarse)
    (priorPush : coarsen finePrior view = coarsePrior) (action : Action) (reward : Coarse → ℝ) :
    (∑ s, (bind finePrior (fineKernel action)).1 s * reward (view s)) =
      ∑ c, (bind coarsePrior (coarseKernel action)).1 c * reward c := by
  rw [← coarsen_expectation (bind finePrior (fineKernel action)) view reward,
    prediction_of_supplied_prior view fineKernel coarseKernel representative sectionLaw
      transition finePrior coarsePrior priorPush action]

/-- Under exact compatibility the diagonal coupling certifies a zero reward gap. -/
theorem compatible_prediction_bound {Action : Type*}
    (view : Fine → Coarse) (fineKernel : Action → Fine → Prob Fine)
    (coarseKernel : Action → Coarse → Prob Coarse) (representative : Coarse → Fine)
    (sectionLaw : Function.RightInverse representative view)
    (transition : ∀ action state,
      coarsen (fineKernel action state) view = coarseKernel action (view state))
    (finePrior : Prob Fine) (coarsePrior : Prob Coarse)
    (priorPush : coarsen finePrior view = coarsePrior) (action : Action) (reward : Coarse → ℝ) :
    |∑ s, (bind finePrior (fineKernel action)).1 s * reward (view s) -
        ∑ c, (bind coarsePrior (coarseKernel action)).1 c * reward c| ≤
      (diagonalCoupling (bind coarsePrior (coarseKernel action))).cost
        (fun x y => |reward x - reward y|) := by
  rw [compatible_prediction_gap view fineKernel coarseKernel representative sectionLaw transition
      finePrior coarsePrior priorPush action reward,
    diagonalCoupling_abs_cost (bind coarsePrior (coarseKernel action)) reward]
  simp

omit [DecidableEq Coarse] in
/-- Observation agreement and successor cost are separate inputs of the adaptive bound. -/
theorem adaptive_coupling_bound {Obs Action : Type*} [Fintype Obs]
    (fineStep : Action → Fine → Prob (Fine × Obs))
    (coarseStep : Action → Coarse → Prob (Coarse × Obs))
    (fineReward : Fine → ℝ) (coarseReward : Coarse → ℝ) (metric : Fine → Coarse → ℝ)
    (rewardBound : ∀ s t, |fineReward s - coarseReward t| ≤ metric s t)
    (step : ∀ action s t, ∃ coupling : Coupling (fineStep action s).1 (coarseStep action t).1,
      (∀ x y, 0 < coupling.weight x y → x.2 = y.2) ∧
        coupling.cost (fun x y => metric x.1 y.1) ≤ metric s t)
    {n : ℕ} (policy : ObservationPolicy Obs Action n) (s : Fine) (t : Coarse) :
    |adaptiveValue fineStep fineReward policy s -
        adaptiveValue coarseStep coarseReward policy t| ≤ metric s t :=
  abs_adaptiveValue_sub_le fineStep coarseStep fineReward coarseReward metric rewardBound step
    policy s t

/-- Coarsening the observation cannot increase expected information gain. -/
theorem observation_coarsening_information {S O C : Type*} [Fintype S] [Fintype O] [Fintype C]
    [DecidableEq S] [DecidableEq O] [DecidableEq C]
    (prior : Prob S) (likelihood : S → Prob O) (observationView : O → C) :
    expectedInformationGain prior (fun s => coarsen (likelihood s) observationView) ≤
      expectedInformationGain prior likelihood :=
  expectedInformationGain_coarsen_le prior likelihood observationView

omit [DecidableEq Coarse] in
/-- A section that misses a collided state has a strictly smaller carrier. -/
theorem carrier_cost_of_collision (view : Fine → Coarse) (representative : Coarse → Fine)
    (sectionLaw : Function.RightInverse representative view)
    (collision : ∃ s t : Fine, s ≠ t ∧ view s = view t) :
    Fintype.card Coarse < Fintype.card Fine := by
  rcases collision with ⟨s, t, distinct, sameView⟩
  have injectiveSection : Function.Injective representative := by
    intro c d equal
    have image := congrArg view equal
    rw [sectionLaw c, sectionLaw d] at image
    exact image
  refine Fintype.card_lt_of_injective_not_surjective representative injectiveSection ?_
  intro surjective
  obtain ⟨c, hc⟩ := surjective s
  obtain ⟨d, hd⟩ := surjective t
  have cView : c = view s := by
    have image := congrArg view hc
    rwa [sectionLaw c] at image
  have dView : d = view t := by
    have image := congrArg view hd
    rwa [sectionLaw d] at image
  apply distinct
  rw [← hc, ← hd, cView, dView, sameView]

/-- A point-mass coupling cannot place its mass on the other point. -/
theorem point_masses_reject_off_support
    (coupling : Coupling (dirac true).1 (dirac false).1) :
    coupling.weight true true ≠ 1 := by
  intro placed
  have bounded := coupling.weight_le_right true true
  simp [dirac_apply] at bounded
  rw [placed] at bounded
  linarith

/-- Two different point masses have reward gap and coupling cost both equal to one. -/
theorem discrepant_point_mass_gap :
    |(∑ b, (dirac true).1 b * (fun bit : Bool => if bit then (1 : ℝ) else 0) b) -
        ∑ b, (dirac false).1 b * (fun bit : Bool => if bit then (1 : ℝ) else 0) b| =
      (Coupling.ofDirac (𝕜 := ℝ) true false).cost
        (fun x y => |(fun bit : Bool => if bit then (1 : ℝ) else 0) x -
          (fun bit : Bool => if bit then (1 : ℝ) else 0) y|) := by
  have leftValue :
      (∑ b, (dirac true).1 b * (fun bit : Bool => if bit then (1 : ℝ) else 0) b) = 1 := by
    rw [expectation_dirac]
    simp
  have rightValue :
      (∑ b, (dirac false).1 b * (fun bit : Bool => if bit then (1 : ℝ) else 0) b) = 0 := by
    rw [expectation_dirac]
    simp
  have costValue :
      (Coupling.ofDirac (𝕜 := ℝ) true false).cost
        (fun x y => |(fun bit : Bool => if bit then (1 : ℝ) else 0) x -
          (fun bit : Bool => if bit then (1 : ℝ) else 0) y|) = 1 := by
    rw [Coupling.cost_dirac]
    simp
  rw [leftValue, rightValue, costValue]
  norm_num

end CouplingBounds

section Helpers

/-- A point mass and a constant observation are a point mass on the pair. -/
theorem joint_dirac {S O : Type*} [Fintype S] [Fintype O] [DecidableEq S] [DecidableEq O]
    (state : S) (observation : O) :
    joint (dirac state) (fun _ => dirac observation) = dirac (state, observation) := by
  apply Subtype.ext
  funext so
  rcases so with ⟨s, o⟩
  by_cases hs : s = state <;> by_cases ho : o = observation <;>
    simp [joint_apply, dirac_apply, hs, ho]

/-- A point-mass prior returns the selected kernel row. -/
theorem bind_dirac {S C : Type*} [Fintype S] [Fintype C] [DecidableEq S]
    (state : S) (kernel : S → Prob C) :
    bind (dirac state) kernel = kernel state := by
  apply Subtype.ext
  funext outcome
  rw [bind_apply]
  exact expectation_dirac state fun source => (kernel source).1 outcome

/-- Evidence under a point mass is the likelihood at that point. -/
theorem evidence_dirac {S : Type*} [Fintype S] [DecidableEq S]
    (state : S) (likelihood : S → ℝ) :
    evidence (dirac state) likelihood = likelihood state :=
  expectation_dirac state likelihood

/-- One action, then a terminal reward. -/
def policyOne {O A : Type*} (action : A) : ObservationPolicy O A 1 :=
  (action, fun _ => PUnit.unit)

/-- One deterministic step records that successor as the whole trace. -/
theorem traceLaw_one_dirac {S O A : Type*} [Fintype S] [Fintype O] [DecidableEq S]
    [DecidableEq O] (kernel : A → S → Prob (S × O)) (action : A) (state next : S)
    (observation : O) (row : kernel action state = dirac (next, observation)) :
    traceLaw kernel (policyOne action) state = dirac (fun _ : Fin 1 => (next, observation)) := by
  rw [traceLaw, policyOne, row, bind_dirac, traceLaw, coarsen_dirac]
  congr 1
  funext i
  fin_cases i
  rfl

/-- Two actions, the second chosen from the first observation. -/
def policyTwo {O A : Type*} (first : A) (nextAction : O → A) : ObservationPolicy O A 2 :=
  (first, fun observation => policyOne (nextAction observation))

/-- Two deterministic steps reduce an adaptive value to the terminal reward. -/
theorem adaptiveValue_two_dirac {S O A : Type*} [Fintype S] [Fintype O] [DecidableEq (S × O)]
    (kernel : A → S → Prob (S × O)) (reward : S → ℝ) (first : A) (nextAction : O → A)
    (state mid final : S) (observed nextObserved : O)
    (firstStep : kernel first state = dirac (mid, observed))
    (secondStep : kernel (nextAction observed) mid = dirac (final, nextObserved)) :
    adaptiveValue kernel reward (policyTwo first nextAction) state = reward final := by
  have firstValue :
      adaptiveValue kernel reward (policyTwo first nextAction) state =
        adaptiveValue kernel reward (policyOne (nextAction observed)) mid := by
    simp only [policyTwo, policyOne, adaptiveValue, firstStep,
      Mettapedia.Cybernetics.ApproximateAdequacy.expect]
    exact expectation_dirac (mid, observed) fun next =>
      adaptiveValue kernel reward (policyOne (nextAction next.2)) next.1
  have secondValue :
      adaptiveValue kernel reward (policyOne (nextAction observed)) mid = reward final := by
    simp only [policyOne, adaptiveValue, secondStep,
      Mettapedia.Cybernetics.ApproximateAdequacy.expect]
    exact expectation_dirac (final, nextObserved) fun next => reward next.1
  exact firstValue.trans secondValue

end Helpers

/-! ## Finer observations -/

/-- A fault record is a location together with whether the repair matches it. -/
abbrev Fault := Bool × Bool

/-- Action `0` inspects. Action `1` matches the false location. Action `2` matches the true one. -/
def repair (action : Fin 3) (state : Fault) : Fault :=
  if action = 0 then state
  else if action = 1 then (state.1, !state.1)
  else (state.1, state.1)

/-- Reward is one exactly when the repair matches the location. -/
def matchedReward (state : Fault) : ℝ :=
  if state.2 then 1 else 0

/-- The coarse observation forgets the location bit. -/
def coarseStep (action : Fin 3) (state : Fault) : Prob (Fault × Unit) :=
  dirac (repair action state, ())

/-- The fine observation emits the location bit and uses the same repair. -/
def fineStep (action : Fin 3) (state : Fault) : Prob (Fault × Bool) :=
  dirac (repair action state, state.1)

/-- Inspect, then choose the repair named by the emitted location. -/
def revealingPolicy : ObservationPolicy Bool (Fin 3) 2 :=
  (0, fun observed => ((if observed then 2 else 1 : Fin 3), fun _ => PUnit.unit))

theorem fine_observation_pushforward (action : Fin 3) (state : Fault) :
    coarsen (fineStep action state) (fun next : Fault × Bool => (next.1, ())) =
      coarseStep action state := by
  rw [fineStep, coarseStep, coarsen_dirac]

theorem blind_value (first second : Fin 3) (state : Fault) :
    adaptiveValue coarseStep matchedReward (policyTwo first fun _ : Unit => second) state =
      matchedReward (repair second (repair first state)) :=
  adaptiveValue_two_dirac coarseStep matchedReward first (fun _ => second) state
    (repair first state) (repair second (repair first state)) () () rfl rfl

theorem revealing_value (location : Bool) :
    adaptiveValue fineStep matchedReward revealingPolicy (location, false) = 1 := by
  have policy :
      revealingPolicy = policyTwo 0 fun observed => if observed then 2 else 1 := by
    rfl
  rw [policy, adaptiveValue_two_dirac fineStep matchedReward 0
      (fun observed => if observed then 2 else 1) (location, false) (location, false)
      (repair (if location then 2 else 1) (location, false)) location location
      (by simp [fineStep, repair]) (by simp [fineStep])]
  fin_cases location <;> simp [repair, matchedReward]

/-- Every constant-observation policy misses at least one of the two fault locations. -/
theorem blind_pair_fails (first second : Fin 3) :
    adaptiveValue coarseStep matchedReward (policyTwo first fun _ : Unit => second) (true, false) = 0 ∨
      adaptiveValue coarseStep matchedReward (policyTwo first fun _ : Unit => second)
        (false, false) = 0 := by
  rw [blind_value, blind_value]
  fin_cases first <;> fin_cases second <;> simp [repair, matchedReward]

theorem every_coarse_policy_misses (policy : ObservationPolicy Unit (Fin 3) 2) :
    adaptiveValue coarseStep matchedReward policy (true, false) = 0 ∨
      adaptiveValue coarseStep matchedReward policy (false, false) = 0 := by
  rcases policy with ⟨first, branch⟩
  have branchAt : branch = fun _ => branch () := by
    funext observation
    cases observation
    rfl
  rcases assignment : branch () with ⟨second, later⟩
  have laterUnit : later = fun _ => PUnit.unit := by
    funext observation
    cases observation
    dsimp [ObservationPolicy] at later
    cases later ()
    rfl
  rw [branchAt, assignment, laterUnit]
  exact blind_pair_fails first second

/-- The location observation supports a repair that every coarse policy misses somewhere. -/
theorem finer_observation_strictly_better :
    adaptiveValue fineStep matchedReward revealingPolicy (true, false) = 1 ∧
      adaptiveValue fineStep matchedReward revealingPolicy (false, false) = 1 ∧
      ∀ policy : ObservationPolicy Unit (Fin 3) 2,
        adaptiveValue coarseStep matchedReward policy (true, false) = 0 ∨
          adaptiveValue coarseStep matchedReward policy (false, false) = 0 :=
  ⟨revealing_value true, revealing_value false, every_coarse_policy_misses⟩

/-! ## Redundant latent flag -/

def bitReward (bit : Bool) : ℝ :=
  if bit then 1 else 0

/-- The declared state is the first component. The second component is redundant for it. -/
def redundantView (state : Bool × Bool) : Bool :=
  state.1

def redundantRep (bit : Bool) : Bool × Bool :=
  (bit, false)

theorem redundant_section : Function.RightInverse redundantRep redundantView :=
  fun _ => rfl

/-- Flip the visible bit and retain the redundant flag. -/
def redundantFine (_ : Unit) (state : Bool × Bool) : Prob (Bool × Bool) :=
  dirac (!state.1, state.2)

/-- The coarse dynamics flip the visible bit. -/
def redundantCoarse (_ : Unit) (bit : Bool) : Prob Bool :=
  dirac (!bit)

theorem redundant_transition (action : Unit) (state : Bool × Bool) :
    coarsen (redundantFine action state) redundantView =
      redundantCoarse action (redundantView state) := by
  unfold redundantFine redundantCoarse redundantView
  rw [coarsen_dirac]

theorem redundant_priors_push (flag : Bool) :
    coarsen (dirac (true, flag)) redundantView = dirac true := by
  unfold redundantView
  rw [coarsen_dirac]

theorem redundant_prediction (flag : Bool) :
    coarsen (bind (dirac (true, flag)) (redundantFine ())) redundantView =
      bind (dirac true) (redundantCoarse ()) :=
  prediction_of_supplied_prior redundantView redundantFine redundantCoarse redundantRep
    redundant_section redundant_transition (dirac (true, flag)) (dirac true)
    (redundant_priors_push flag) ()

theorem redundant_task_preserved (flag : Bool) :
    (∑ s, (bind (dirac (true, flag)) (redundantFine ())).1 s * bitReward (redundantView s)) =
      ∑ bit, (bind (dirac true) (redundantCoarse ())).1 bit * bitReward bit := by
  rw [← coarsen_expectation (bind (dirac (true, flag)) (redundantFine ())) redundantView bitReward,
    redundant_prediction flag]

theorem redundant_task_value (flag : Bool) :
    (∑ s, (bind (dirac (true, flag)) (redundantFine ())).1 s * bitReward (redundantView s)) = 0 := by
  rw [redundant_task_preserved flag, bind_dirac, redundantCoarse, expectation_dirac, bitReward]
  simp

theorem redundant_flags_same_task :
    (∑ s, (bind (dirac (true, false)) (redundantFine ())).1 s * bitReward (redundantView s)) =
      ∑ s, (bind (dirac (true, true)) (redundantFine ())).1 s * bitReward (redundantView s) := by
  rw [redundant_task_preserved false, redundant_task_preserved true]

/-- The flag is visible to a consumer that the declared view discards. -/
def hiddenFlag (state : Bool × Bool) : ℝ :=
  if state.2 then 1 else 0

theorem redundant_hidden (flag : Bool) :
    (∑ s, (bind (dirac (true, flag)) (redundantFine ())).1 s * hiddenFlag s) =
      hiddenFlag (false, flag) := by
  rw [bind_dirac, redundantFine, expectation_dirac]
  rfl

theorem redundant_hidden_splits :
    (∑ s, (bind (dirac (true, false)) (redundantFine ())).1 s * hiddenFlag s) = 0 ∧
      (∑ s, (bind (dirac (true, true)) (redundantFine ())).1 s * hiddenFlag s) = 1 := by
  constructor
  · rw [redundant_hidden, hiddenFlag]
    simp
  · rw [redundant_hidden, hiddenFlag]
    simp

theorem redundant_state_is_larger :
    Fintype.card Bool < Fintype.card (Bool × Bool) :=
  carrier_cost_of_collision redundantView redundantRep redundant_section
    ⟨(true, false), (true, true), by decide, rfl⟩

theorem redundant_policy {n : ℕ} (policy : ObservationPolicy Unit Unit n) (flag : Bool) :
    adaptiveValue
        (fun action state => joint (redundantFine action state) (fun _ => dirac ()))
        (bitReward ∘ redundantView) policy (true, flag) =
      adaptiveValue
        (fun action bit => joint (redundantCoarse action bit) (fun _ => dirac ()))
        bitReward policy true :=
  policy_preserved redundantView redundantFine redundantCoarse redundant_transition
    (fun _ _ => dirac ()) (fun _ _ => dirac ()) (fun _ _ => rfl) bitReward policy (true, flag)

/-- The redundant flag is absent from the execution trace of the declared task. -/
theorem redundant_trace {n : ℕ} (policy : ObservationPolicy Unit Unit n) (flag : Bool) :
    coarsen
        (traceLaw (fun action state => joint (redundantFine action state) (fun _ => dirac ()))
          policy (true, flag))
        (fun trace i => (redundantView (trace i).1, (trace i).2)) =
      traceLaw (fun action bit => joint (redundantCoarse action bit) (fun _ => dirac ()))
        policy true :=
  trace_preserved redundantView redundantFine redundantCoarse redundant_transition
    (fun _ _ => dirac ()) (fun _ _ => dirac ()) (fun _ _ => rfl) policy (true, flag)

/-- The same trace is not the execution that starts on the other visible bit. -/
theorem trace_refuses_other_start (flag : Bool) :
    coarsen
        (traceLaw (fun action state => joint (redundantFine action state) (fun _ => dirac ()))
          (policyOne ()) (true, flag))
        (fun trace i => (redundantView (trace i).1, (trace i).2)) ≠
      traceLaw (fun action bit => joint (redundantCoarse action bit) (fun _ => dirac ()))
        (policyOne ()) false := by
  intro same
  rw [redundant_trace] at same
  have fromTrue :
      traceLaw (fun action bit => joint (redundantCoarse action bit) (fun _ => dirac ()))
          (policyOne ()) true =
        dirac (fun _ : Fin 1 => (false, ())) := by
    refine traceLaw_one_dirac _ () true false () ?_
    rw [redundantCoarse, Bool.not_true, joint_dirac]
  have fromFalse :
      traceLaw (fun action bit => joint (redundantCoarse action bit) (fun _ => dirac ()))
          (policyOne ()) false =
        dirac (fun _ : Fin 1 => (true, ())) := by
    refine traceLaw_one_dirac _ () false true () ?_
    rw [redundantCoarse, Bool.not_false, joint_dirac]
  rw [fromTrue, fromFalse] at same
  have distinct : (fun _ : Fin 1 => ((false, ()) : Bool × Unit)) ≠ fun _ => (true, ()) := by
    intro eq
    exact Bool.false_ne_true (congrArg Prod.fst (congrFun eq 0))
  have mass := congrArg (fun law : Prob (Fin 1 → Bool × Unit) => law.1 (fun _ => (false, ()))) same
  rw [dirac_apply, dirac_apply, if_pos rfl, if_neg distinct] at mass
  exact one_ne_zero mass

/-- A coarse prior outside the pushforward of the expanded prior breaks prediction. -/
theorem unsupported_prior_expansion :
    coarsen (bind (dirac (true, false)) (redundantFine ())) redundantView ≠
      bind (dirac false) (redundantCoarse ()) := by
  intro same
  have leftLaw :
      coarsen (bind (dirac (true, false)) (redundantFine ())) redundantView = dirac false := by
    rw [bind_dirac, redundantFine, coarsen_dirac, redundantView, Bool.not_true]
  have rightLaw : bind (dirac false) (redundantCoarse ()) = dirac true := by
    rw [bind_dirac, redundantCoarse, Bool.not_false]
  rw [leftLaw, rightLaw] at same
  have mass := congrArg (fun law : Prob Bool => law.1 false) same
  simp [dirac_apply] at mass

/-- A likelihood supported on the state the flip has left. -/
def missedFlag (flag : Bool) (state : Bool × Bool) : ℝ :=
  if state = (true, flag) then 1 else 0

theorem missed_flag_impossible (flag : Bool) :
    evidence (bind (dirac (true, flag)) (redundantFine ())) (missedFlag flag) = 0 := by
  rw [bind_dirac, redundantFine, evidence_dirac, missedFlag]
  simp

theorem missed_flag_blocks_filter (flag : Bool) :
    ¬ 0 < evidence (bind (dirac (true, flag)) (redundantFine ())) (missedFlag flag) := by
  rw [missed_flag_impossible]
  exact lt_irrefl 0

end Mettapedia.ProbabilityTheory.BayesianInference.ModelRefinement
