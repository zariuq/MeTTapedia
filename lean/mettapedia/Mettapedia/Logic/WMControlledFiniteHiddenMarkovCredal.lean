import Mettapedia.Logic.ControlledFiniteHiddenMarkovObservedInference
import Mettapedia.Logic.PLNIndefiniteTruth
import Mettapedia.Logic.PLNIndefiniteTruthBridge
import Mettapedia.Logic.PLNWeightTV
import Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
import Mettapedia.UniversalAI.BayesianAgents.Core

/-!
# Credal WM Layer for Observed-Only Controlled Finite HMMs

This file packages the first honest observed-only WM response to controlled-HMM
non-identifiability: a credal interval over filtering posterior strengths.

Positive example:
* a finite family of controlled HMMs induces lower/upper posterior strengths.

Negative example:
* this is not yet a full arbitrary-family credal calculus or a planning layer.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal

open Mettapedia.Logic.ControlledFiniteHiddenMarkovModel
open Mettapedia.Logic.ControlledFiniteHiddenMarkovObservedInference
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
open Mettapedia.UniversalAI.BayesianAgents.Core
open scoped ENNReal BigOperators

universe uA uI

variable {Action : Type uA} {ι : Type uI} {latent obs : ℕ}

/-- Lower/upper truth-value interval for an observed-only credal posterior. -/
structure IndefiniteTruthValue where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  lower_nonneg : 0 ≤ lower
  upper_le_one : upper ≤ 1

/-- Lower observed-only filtering strength across a finite family of controlled
HMMs. -/
noncomputable def lowerFilteringPosteriorStrength
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => (filteringPosteriorMass (Θ i) zs q).toReal)

/-- Upper observed-only filtering strength across a finite family of controlled
HMMs. -/
noncomputable def upperFilteringPosteriorStrength
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => (filteringPosteriorMass (Θ i) zs q).toReal)

theorem lowerFilteringPosteriorStrength_nonneg
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) :
    0 ≤ lowerFilteringPosteriorStrength Θ zs q := by
  unfold lowerFilteringPosteriorStrength
  apply Finset.le_inf'
  intro i _
  exact ENNReal.toReal_nonneg

theorem upperFilteringPosteriorStrength_le_one
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent)
    (hobs : ∀ i, observedCycleProb (Θ i) zs ≠ 0) :
    upperFilteringPosteriorStrength Θ zs q ≤ 1 := by
  unfold upperFilteringPosteriorStrength
  apply Finset.sup'_le
  intro i hi
  have hle : filteringPosteriorMass (Θ i) zs q ≤ 1 :=
    filteringPosteriorMass_le_one (Θ i) zs q (hobs i)
  have htop : filteringPosteriorMass (Θ i) zs q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  exact (ENNReal.toReal_le_toReal htop ENNReal.one_ne_top).2 hle

theorem lowerFilteringPosteriorStrength_le
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) (i : ι) :
    lowerFilteringPosteriorStrength Θ zs q ≤
      (filteringPosteriorMass (Θ i) zs q).toReal := by
  unfold lowerFilteringPosteriorStrength
  exact Finset.inf'_le (fun j => (filteringPosteriorMass (Θ j) zs q).toReal) (Finset.mem_univ i)

theorem le_upperFilteringPosteriorStrength
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) (i : ι) :
    (filteringPosteriorMass (Θ i) zs q).toReal ≤
      upperFilteringPosteriorStrength Θ zs q := by
  unfold upperFilteringPosteriorStrength
  exact Finset.le_sup' (fun j => (filteringPosteriorMass (Θ j) zs q).toReal) (Finset.mem_univ i)

theorem lowerFilteringPosteriorStrength_le_upper
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent) :
    lowerFilteringPosteriorStrength Θ zs q ≤
      upperFilteringPosteriorStrength Θ zs q := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  exact (lowerFilteringPosteriorStrength_le Θ zs q i0).trans
    (le_upperFilteringPosteriorStrength Θ zs q i0)

/-- Credal observed-only WM truth value from a finite family of controlled
HMMs. -/
noncomputable def filteringCredalTruthValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent)
    (hobs : ∀ i, observedCycleProb (Θ i) zs ≠ 0) :
    IndefiniteTruthValue where
  lower := lowerFilteringPosteriorStrength Θ zs q
  upper := upperFilteringPosteriorStrength Θ zs q
  valid := lowerFilteringPosteriorStrength_le_upper Θ zs q
  lower_nonneg := lowerFilteringPosteriorStrength_nonneg Θ zs q
  upper_le_one := upperFilteringPosteriorStrength_le_one Θ zs q hobs

/-- Convert a cycle count to a PLN-style credibility using the weight-primary
`w2c` view with prior scale `κ`. This keeps credibility separate from interval
width. -/
noncomputable def cycleCountCredibility
    (κ : ℝ)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  Mettapedia.Logic.PLNWeightTV.w2c ((zs.length : ℝ) / κ)

theorem cycleCountCredibility_mem_unit
    (κ : ℝ)
    (hκ : 0 < κ)
    (zs : List (CycleObservation Action obs)) :
    cycleCountCredibility (Action := Action) (obs := obs) κ zs ∈ Set.Icc 0 1 := by
  unfold cycleCountCredibility
  have hw_nonneg : 0 ≤ (zs.length : ℝ) / κ := by
    exact div_nonneg (Nat.cast_nonneg zs.length) (le_of_lt hκ)
  exact Mettapedia.Logic.PLNWeightTV.WTV.w2c_bounds _ hw_nonneg

/-- Generic bridge from the local controlled-HMM credal interval into the live
PLN indefinite truth-value surface. -/
noncomputable abbrev IndefiniteTruthValue.toPLNITV
    (tv : IndefiniteTruthValue)
    (credibility : ℝ)
    (hcred : credibility ∈ Set.Icc 0 1) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility
    tv.lower tv.upper credibility tv.valid tv.lower_nonneg tv.upper_le_one hcred

/-- Operational bridge: turn a controlled-HMM credal filtering interval into the
live PLN `ITV` interface, using cycle-count credibility. -/
noncomputable def filteringCredalPLNITV
    [Fintype ι] [Nonempty ι]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (q : Fin latent)
    (hobs : ∀ i, observedCycleProb (Θ i) zs ≠ 0) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  (filteringCredalTruthValue Θ zs q hobs).toPLNITV
    (cycleCountCredibility (Action := Action) (obs := obs) κ zs)
    (cycleCountCredibility_mem_unit (Action := Action) (obs := obs) κ hκ zs)

section OneStepValue

variable [PerceptReward (Fin obs)]

/-- Immediate expected reward from a completed trace and a chosen action, under
the controlled-HMM environment bridge. -/
noncomputable def oneStepQValue
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℝ :=
  ∑ y : Fin obs,
    (observationMassGivenAction θ (filteringMass θ zs) a y).toReal *
      PerceptReward.reward y

omit [PerceptReward (Fin obs)] in
theorem historyOfCycles_wellFormed
    (zs : List (CycleObservation Action obs)) :
    History.wellFormed (Action := Action) (Percept := Fin obs)
      (historyOfCycles zs) = true := by
  induction zs with
  | nil =>
      simp [historyOfCycles, History.wellFormed]
  | cons z zs ih =>
      cases z with
      | mk a y =>
          simp [historyOfCycles, History.wellFormed, ih]

omit [PerceptReward (Fin obs)] in
theorem historyOfCycles_append_act_wellFormed
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    History.wellFormed (Action := Action) (Percept := Fin obs)
      (historyOfCycles zs ++ [HistElem.act a]) = true := by
  induction zs with
  | nil =>
      simp [historyOfCycles, History.wellFormed]
  | cons z zs ih =>
      cases z with
      | mk a' y =>
          simp [historyOfCycles, History.wellFormed, ih]

omit [PerceptReward (Fin obs)] in
@[simp] theorem historyOfCycles_append_singleton
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    historyOfCycles (zs ++ [(a, y)]) =
      historyOfCycles zs ++ [HistElem.act a, HistElem.per y] := by
  induction zs with
  | nil =>
      simp [historyOfCycles]
  | cons z zs ih =>
      cases z with
      | mk a' y' =>
          simp [historyOfCycles, ih]

theorem oneStepQValue_nonneg
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    0 ≤ oneStepQValue θ zs a := by
  unfold oneStepQValue
  refine Finset.sum_nonneg ?_
  intro y _hy
  exact mul_nonneg ENNReal.toReal_nonneg (PerceptReward.nonneg y)

theorem oneStepQValue_le_one
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    oneStepQValue θ zs a ≤ 1 := by
  have hprob_le_one :
      ∑ y : Fin obs,
          observationMassGivenAction θ (filteringMass θ zs) a y ≤ 1 := by
    calc
      ∑ y : Fin obs, observationMassGivenAction θ (filteringMass θ zs) a y
          = ∑ x : Fin latent, filteringMass θ zs x := by
              exact observationMassGivenAction_sum_eq θ (filteringMass θ zs) a
      _ ≤ 1 := filteringMass_sum_le_one θ zs
  have hprob_ne_top :
      ∀ y : Fin obs,
        observationMassGivenAction θ (filteringMass θ zs) a y ≠ (⊤ : ENNReal) := by
    intro y
    have hy_le_sum :
        observationMassGivenAction θ (filteringMass θ zs) a y ≤
          ∑ y' : Fin obs, observationMassGivenAction θ (filteringMass θ zs) a y' := by
      exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ y)
    have hy_le_one :
        observationMassGivenAction θ (filteringMass θ zs) a y ≤ 1 :=
      hy_le_sum.trans hprob_le_one
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hy_le_one
  have htoReal_sum :
      (∑ y : Fin obs, observationMassGivenAction θ (filteringMass θ zs) a y).toReal =
        ∑ y : Fin obs, (observationMassGivenAction θ (filteringMass θ zs) a y).toReal := by
    exact ENNReal.toReal_sum (s := Finset.univ)
      (f := fun y : Fin obs => observationMassGivenAction θ (filteringMass θ zs) a y)
      (by
        intro y _hy
        exact hprob_ne_top y)
  have hsum_toReal_le :
      ∑ y : Fin obs, (observationMassGivenAction θ (filteringMass θ zs) a y).toReal ≤ 1 := by
    have hle :
        (∑ y : Fin obs, observationMassGivenAction θ (filteringMass θ zs) a y).toReal ≤
          (1 : ENNReal).toReal :=
      (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top ENNReal.one_ne_top hprob_le_one)
        ENNReal.one_ne_top).2 hprob_le_one
    simpa [htoReal_sum] using hle
  have hsum_le :
      ∑ y : Fin obs,
          (observationMassGivenAction θ (filteringMass θ zs) a y).toReal *
            PerceptReward.reward y
        ≤ ∑ y : Fin obs, (observationMassGivenAction θ (filteringMass θ zs) a y).toReal := by
    refine Finset.sum_le_sum ?_
    intro y _hy
    have hprob_nonneg :
        0 ≤ (observationMassGivenAction θ (filteringMass θ zs) a y).toReal :=
      ENNReal.toReal_nonneg
    have hrew_le_one : PerceptReward.reward y ≤ 1 := PerceptReward.le_one y
    nlinarith
  exact hsum_le.trans hsum_toReal_le

theorem qValue_historyOfCycles_one_eq_oneStepQValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    qValue (toEnvironment θ) π γ (historyOfCycles zs) a 1 =
      oneStepQValue θ zs a := by
  rw [qValue_succ]
  have hwf :
      History.wellFormed (Action := Action) (Percept := Fin obs)
        (historyOfCycles zs ++ [HistElem.act a]) = true :=
    historyOfCycles_append_act_wellFormed (Action := Action) (obs := obs) zs a
  have hprob :
      (fun y : Fin obs =>
        (toEnvironment θ).prob (historyOfCycles zs ++ [HistElem.act a]) y) =
      (fun y : Fin obs =>
        observationMassGivenAction θ (filteringMass θ zs) a y) := by
    funext y
    simpa [toEnvironment] using
      environmentProb_historyOfCycles_append_act (θ := θ) (zs := zs) (a := a) (y := y)
  simp [hwf, value_zero]
  simp [oneStepQValue, hprob]

theorem optimalQValue_historyOfCycles_one_eq_oneStepQValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    optimalQValue (toEnvironment θ) γ (historyOfCycles zs) a 1 =
      oneStepQValue θ zs a := by
  rw [optimalQValue_succ]
  have hwf :
      History.wellFormed (Action := Action) (Percept := Fin obs)
        (historyOfCycles zs ++ [HistElem.act a]) = true :=
    historyOfCycles_append_act_wellFormed (Action := Action) (obs := obs) zs a
  have hprob :
      (fun y : Fin obs =>
        (toEnvironment θ).prob (historyOfCycles zs ++ [HistElem.act a]) y) =
      (fun y : Fin obs =>
        observationMassGivenAction θ (filteringMass θ zs) a y) := by
    funext y
    simpa [toEnvironment] using
      environmentProb_historyOfCycles_append_act (θ := θ) (zs := zs) (a := a) (y := y)
  simp [hwf, optimalValue_zero]
  simp [oneStepQValue, hprob]

/-- The one-step optimal decision value from a completed trace: maximum over the
available one-step `qValue`s. In the BayesianAgents horizon convention, this
matches `optimalValue ... 2`. -/
noncomputable def oneStepOptimalValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  (Finset.univ : Finset Action).fold max 0 (fun a => oneStepQValue θ zs a)

theorem oneStepOptimalValue_nonneg
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    0 ≤ oneStepOptimalValue θ zs := by
  unfold oneStepOptimalValue
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

theorem oneStepOptimalValue_le_one
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    oneStepOptimalValue θ zs ≤ 1 := by
  unfold oneStepOptimalValue
  rw [Finset.fold_max_le]
  constructor
  · norm_num
  · intro a _ha
    exact oneStepQValue_le_one θ zs a

theorem optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
    [Fintype Action]
    (θ : ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) :
    optimalValue (toEnvironment θ) γ (historyOfCycles zs) 2 =
      oneStepOptimalValue θ zs := by
  rw [optimalValue_succ]
  have hwf :
      History.wellFormed (Action := Action) (Percept := Fin obs)
        (historyOfCycles zs) = true :=
    historyOfCycles_wellFormed (Action := Action) (obs := obs) zs
  simp [hwf, oneStepOptimalValue, optimalQValue_historyOfCycles_one_eq_oneStepQValue]

/-- Lower one-step `qValue` envelope across a finite family of controlled HMMs. -/
noncomputable def lowerOneStepQValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => oneStepQValue (Θ i) zs a)

/-- Upper one-step `qValue` envelope across a finite family of controlled HMMs. -/
noncomputable def upperOneStepQValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => oneStepQValue (Θ i) zs a)

theorem lowerOneStepQValue_le
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    lowerOneStepQValue Θ zs a ≤ oneStepQValue (Θ i) zs a := by
  unfold lowerOneStepQValue
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_upperOneStepQValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    oneStepQValue (Θ i) zs a ≤ upperOneStepQValue Θ zs a := by
  unfold upperOneStepQValue
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun j : ι => oneStepQValue (Θ j) zs a)
    (Finset.mem_univ i)

theorem lowerOneStepQValue_le_upper
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    lowerOneStepQValue Θ zs a ≤ upperOneStepQValue Θ zs a := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  exact (lowerOneStepQValue_le Θ zs a i0).trans
    (le_upperOneStepQValue Θ zs a i0)

theorem lowerOneStepQValue_nonneg
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    0 ≤ lowerOneStepQValue Θ zs a := by
  unfold lowerOneStepQValue
  exact Finset.le_inf' (s := Finset.univ)
    (H := Finset.univ_nonempty)
    (f := fun i : ι => oneStepQValue (Θ i) zs a)
    (by
      intro i _hi
      exact oneStepQValue_nonneg (Θ i) zs a)

theorem upperOneStepQValue_le_one
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    upperOneStepQValue Θ zs a ≤ 1 := by
  unfold upperOneStepQValue
  exact Finset.sup'_le (s := Finset.univ)
    (H := Finset.univ_nonempty)
    (f := fun i : ι => oneStepQValue (Θ i) zs a)
    (by
      intro i _hi
      exact oneStepQValue_le_one (Θ i) zs a)

/-- Credal one-step value envelope across a finite family of controlled HMMs. -/
noncomputable def oneStepQValueCredalTruthValue
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    IndefiniteTruthValue where
  lower := lowerOneStepQValue Θ zs a
  upper := upperOneStepQValue Θ zs a
  valid := lowerOneStepQValue_le_upper Θ zs a
  lower_nonneg := lowerOneStepQValue_nonneg Θ zs a
  upper_le_one := upperOneStepQValue_le_one Θ zs a

/-- One-step `qValue` envelope rendered as the live PLN indefinite truth-value
surface. -/
noncomputable abbrev oneStepQValuePLNITV
    [Fintype ι] [Nonempty ι]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  IndefiniteTruthValue.toPLNITV
    (oneStepQValueCredalTruthValue Θ zs a)
    (cycleCountCredibility (Action := Action) (obs := obs) κ zs)
    (cycleCountCredibility_mem_unit (Action := Action) (obs := obs) κ hκ zs)

/-- Any family member's one-step `qValue` lies inside the credal envelope. -/
theorem qValue_historyOfCycles_one_mem_envelope
    [Fintype ι] [Nonempty ι]
    [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    lowerOneStepQValue Θ zs a ≤
        qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ∧
      qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ≤
        upperOneStepQValue Θ zs a := by
  have hq :=
    qValue_historyOfCycles_one_eq_oneStepQValue
      (θ := Θ i) (π := π) (γ := γ) (zs := zs) (a := a)
  constructor
  · simpa [hq] using lowerOneStepQValue_le Θ zs a i
  · simpa [hq] using le_upperOneStepQValue Θ zs a i

theorem qValue_historyOfCycles_one_mem_PLNITV_interval
    [Fintype ι] [Nonempty ι]
    [Fintype Action]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    let itv := oneStepQValuePLNITV (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ zs a
    itv.lower ≤ qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ∧
      qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ≤ itv.upper := by
  simpa [oneStepQValuePLNITV, IndefiniteTruthValue.toPLNITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    oneStepQValueCredalTruthValue]
    using qValue_historyOfCycles_one_mem_envelope Θ π γ zs a i

/-- Lower one-step optimal decision value across a finite family of controlled
HMMs. This corresponds to the BayesianAgents quantity `optimalValue ... 2`. -/
noncomputable def lowerOneStepOptimalValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => oneStepOptimalValue (Θ i) zs)

/-- Upper one-step optimal decision value across a finite family of controlled
HMMs. -/
noncomputable def upperOneStepOptimalValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => oneStepOptimalValue (Θ i) zs)

theorem lowerOneStepOptimalValue_le
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    lowerOneStepOptimalValue Θ zs ≤ oneStepOptimalValue (Θ i) zs := by
  unfold lowerOneStepOptimalValue
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_upperOneStepOptimalValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    oneStepOptimalValue (Θ i) zs ≤ upperOneStepOptimalValue Θ zs := by
  unfold upperOneStepOptimalValue
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun j : ι => oneStepOptimalValue (Θ j) zs)
    (Finset.mem_univ i)

theorem lowerOneStepOptimalValue_le_upper
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    lowerOneStepOptimalValue Θ zs ≤ upperOneStepOptimalValue Θ zs := by
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  exact (lowerOneStepOptimalValue_le Θ zs i0).trans
    (le_upperOneStepOptimalValue Θ zs i0)

theorem lowerOneStepOptimalValue_nonneg
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    0 ≤ lowerOneStepOptimalValue Θ zs := by
  unfold lowerOneStepOptimalValue
  exact Finset.le_inf' (s := Finset.univ)
    (H := Finset.univ_nonempty)
    (f := fun i : ι => oneStepOptimalValue (Θ i) zs)
    (by
      intro i _hi
      exact oneStepOptimalValue_nonneg (Θ i) zs)

theorem upperOneStepOptimalValue_le_one
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    upperOneStepOptimalValue Θ zs ≤ 1 := by
  unfold upperOneStepOptimalValue
  exact Finset.sup'_le (s := Finset.univ)
    (H := Finset.univ_nonempty)
    (f := fun i : ι => oneStepOptimalValue (Θ i) zs)
    (by
      intro i _hi
      exact oneStepOptimalValue_le_one (Θ i) zs)

/-- Credal one-step optimal decision value envelope rendered as the local
bounded interval type. -/
noncomputable def oneStepOptimalValueCredalTruthValue
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    IndefiniteTruthValue where
  lower := lowerOneStepOptimalValue Θ zs
  upper := upperOneStepOptimalValue Θ zs
  valid := lowerOneStepOptimalValue_le_upper Θ zs
  lower_nonneg := lowerOneStepOptimalValue_nonneg Θ zs
  upper_le_one := upperOneStepOptimalValue_le_one Θ zs

/-- One-step optimal decision envelope as the live PLN indefinite truth-value
surface. -/
noncomputable abbrev oneStepOptimalValuePLNITV
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs)) :
    Mettapedia.Logic.PLNIndefiniteTruth.ITV :=
  IndefiniteTruthValue.toPLNITV
    (oneStepOptimalValueCredalTruthValue Θ zs)
    (cycleCountCredibility (Action := Action) (obs := obs) κ zs)
    (cycleCountCredibility_mem_unit (Action := Action) (obs := obs) κ hκ zs)

theorem optimalValue_historyOfCycles_two_mem_envelope
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    lowerOneStepOptimalValue Θ zs ≤
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ∧
      optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ≤
        upperOneStepOptimalValue Θ zs := by
  have hopt :=
    optimalValue_historyOfCycles_two_eq_oneStepOptimalValue
      (θ := Θ i) (γ := γ) (zs := zs)
  constructor
  · simpa [hopt] using lowerOneStepOptimalValue_le Θ zs i
  · simpa [hopt] using le_upperOneStepOptimalValue Θ zs i

theorem optimalValue_historyOfCycles_two_mem_PLNITV_interval
    [Fintype ι] [Nonempty ι] [Fintype Action]
    (κ : ℝ)
    (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) (i : ι) :
    let itv := oneStepOptimalValuePLNITV (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ zs
    itv.lower ≤ optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ∧
      optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ≤ itv.upper := by
  simpa [oneStepOptimalValuePLNITV, IndefiniteTruthValue.toPLNITV,
    Mettapedia.Logic.PLNIndefiniteTruthBridge.ofBoundsAndCredibility,
    oneStepOptimalValueCredalTruthValue]
    using optimalValue_historyOfCycles_two_mem_envelope Θ γ zs i

end OneStepValue

section RecursiveValueEnvelope

variable [PerceptReward (Fin obs)] [Fintype Action]

mutual

/-- Lower recursive fixed-policy value envelope across a finite family of
controlled HMMs. -/
noncomputable def lowerRecursiveValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      ∑ a : Action,
        (π.policy (historyOfCycles zs) a).toReal *
          lowerRecursiveQValueEnvelope Θ π γ zs a n

/-- Lower recursive fixed-policy Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def lowerRecursiveQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.inf' Finset.univ_nonempty
        (fun i =>
          ∑ y : Fin obs,
            (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val * lowerRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n))

end

mutual

/-- Upper recursive fixed-policy value envelope across a finite family of
controlled HMMs. -/
noncomputable def upperRecursiveValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      ∑ a : Action,
        (π.policy (historyOfCycles zs) a).toReal *
          upperRecursiveQValueEnvelope Θ π γ zs a n

/-- Upper recursive fixed-policy Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def upperRecursiveQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.sup' Finset.univ_nonempty
        (fun i =>
          ∑ y : Fin obs,
            (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val * upperRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n))

end

mutual

/-- Lower recursive optimal value envelope across a finite family of controlled
HMMs. -/
noncomputable def lowerRecursiveOptimalValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      (Finset.univ : Finset Action).fold max 0
        (fun a => lowerRecursiveOptimalQValueEnvelope Θ γ zs a n)

/-- Lower recursive optimal Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def lowerRecursiveOptimalQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.inf' Finset.univ_nonempty
        (fun i =>
          ∑ y : Fin obs,
            (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))

end

mutual

/-- Upper recursive optimal value envelope across a finite family of controlled
HMMs. -/
noncomputable def upperRecursiveOptimalValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs)) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      (Finset.univ : Finset Action).fold max 0
        (fun a => upperRecursiveOptimalQValueEnvelope Θ γ zs a n)

/-- Upper recursive optimal Q-value envelope across a finite family of
controlled HMMs. -/
noncomputable def upperRecursiveOptimalQValueEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      Finset.univ.sup' Finset.univ_nonempty
        (fun i =>
          ∑ y : Fin obs,
            (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))

end

mutual

theorem qValue_historyOfCycles_mem_recursiveEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action) (i : ι),
      lowerRecursiveQValueEnvelope Θ π γ zs a n ≤
          qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n ∧
        qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n ≤
          upperRecursiveQValueEnvelope Θ π γ zs a n
  | 0, zs, a, i => by
      simp [lowerRecursiveQValueEnvelope, upperRecursiveQValueEnvelope, qValue_zero]
  | n + 1, zs, a, i => by
      have hwf :
          History.wellFormed (Action := Action) (Percept := Fin obs)
            (historyOfCycles zs ++ [HistElem.act a]) = true :=
        historyOfCycles_append_act_wellFormed (Action := Action) (obs := obs) zs a
      have hprob :
          (fun y : Fin obs =>
            (toEnvironment (Θ i)).prob (historyOfCycles zs ++ [HistElem.act a]) y) =
            (fun y : Fin obs =>
              observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y) := by
        funext y
        simpa [toEnvironment] using
          environmentProb_historyOfCycles_append_act
            (θ := Θ i) (zs := zs) (a := a) (y := y)
      have hq :
          qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a (n + 1) =
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val *
                    value (toEnvironment (Θ i)) π γ
                      (historyOfCycles (zs ++ [(a, y)])) n) := by
        rw [qValue_succ]
        simp [hwf, hprob, historyOfCycles_append_singleton]
      constructor
      · calc
          lowerRecursiveQValueEnvelope Θ π γ zs a (n + 1)
              = Finset.univ.inf' Finset.univ_nonempty
                  (fun j =>
                    ∑ y : Fin obs,
                      (observationMassGivenAction (Θ j) (filteringMass (Θ j) zs) a y).toReal *
                        (PerceptReward.reward y +
                          γ.val * lowerRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n)) := rfl
          _ ≤ ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val * lowerRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n) := by
                exact Finset.inf'_le
                  (fun j =>
                    ∑ y : Fin obs,
                      (observationMassGivenAction (Θ j) (filteringMass (Θ j) zs) a y).toReal *
                        (PerceptReward.reward y +
                          γ.val * lowerRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n))
                  (Finset.mem_univ i)
          _ ≤ ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val *
                      value (toEnvironment (Θ i)) π γ
                        (historyOfCycles (zs ++ [(a, y)])) n) := by
                refine Finset.sum_le_sum ?_
                intro y _hy
                have hy :=
                  (value_historyOfCycles_mem_recursiveEnvelope
                    (Θ := Θ) (π := π) (γ := γ) n (zs ++ [(a, y)]) i).1
                have hγhy :
                    γ.val * lowerRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n ≤
                      γ.val *
                        value (toEnvironment (Θ i)) π γ
                          (historyOfCycles (zs ++ [(a, y)])) n :=
                  mul_le_mul_of_nonneg_left hy γ.nonneg
                have hterm :
                    PerceptReward.reward y +
                        γ.val * lowerRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n ≤
                      PerceptReward.reward y +
                        γ.val *
                          value (toEnvironment (Θ i)) π γ
                            (historyOfCycles (zs ++ [(a, y)])) n :=
                  by
                    have htmp := add_le_add_right hγhy (PerceptReward.reward y)
                    simpa [add_comm, add_left_comm, add_assoc] using htmp
                exact mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg
          _ = qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a (n + 1) := by
                exact hq.symm
      · calc
          qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a (n + 1)
              = ∑ y : Fin obs,
                  (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                    (PerceptReward.reward y +
                      γ.val *
                        value (toEnvironment (Θ i)) π γ
                          (historyOfCycles (zs ++ [(a, y)])) n) := hq
          _ ≤ ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val *
                      upperRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n) := by
                refine Finset.sum_le_sum ?_
                intro y _hy
                have hy :=
                  (value_historyOfCycles_mem_recursiveEnvelope
                    (Θ := Θ) (π := π) (γ := γ) n (zs ++ [(a, y)]) i).2
                have hγhy :
                    γ.val *
                        value (toEnvironment (Θ i)) π γ
                          (historyOfCycles (zs ++ [(a, y)])) n ≤
                      γ.val * upperRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n :=
                  mul_le_mul_of_nonneg_left hy γ.nonneg
                have hterm :
                    PerceptReward.reward y +
                        γ.val *
                          value (toEnvironment (Θ i)) π γ
                            (historyOfCycles (zs ++ [(a, y)])) n ≤
                      PerceptReward.reward y +
                        γ.val * upperRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n :=
                  by
                    have htmp := add_le_add_right hγhy (PerceptReward.reward y)
                    simpa [add_comm, add_left_comm, add_assoc] using htmp
                exact mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg
          _ ≤ upperRecursiveQValueEnvelope Θ π γ zs a (n + 1) := by
                exact Finset.le_sup'
                  (s := Finset.univ)
                  (f := fun j =>
                    ∑ y : Fin obs,
                      (observationMassGivenAction (Θ j) (filteringMass (Θ j) zs) a y).toReal *
                        (PerceptReward.reward y +
                          γ.val * upperRecursiveValueEnvelope Θ π γ (zs ++ [(a, y)]) n))
                  (Finset.mem_univ i)

theorem value_historyOfCycles_mem_recursiveEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (i : ι),
      lowerRecursiveValueEnvelope Θ π γ zs n ≤
          value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n ∧
        value (toEnvironment (Θ i)) π γ (historyOfCycles zs) n ≤
          upperRecursiveValueEnvelope Θ π γ zs n
  | 0, zs, i => by
      simp [lowerRecursiveValueEnvelope, upperRecursiveValueEnvelope, value_zero]
  | n + 1, zs, i => by
      have hwf :
          History.wellFormed (Action := Action) (Percept := Fin obs)
            (historyOfCycles zs) = true :=
        historyOfCycles_wellFormed (Action := Action) (obs := obs) zs
      have hv :
          value (toEnvironment (Θ i)) π γ (historyOfCycles zs) (n + 1) =
            ∑ a : Action,
              (π.policy (historyOfCycles zs) a).toReal *
                qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n := by
        rw [value_succ]
        simp [hwf]
      constructor
      · calc
          lowerRecursiveValueEnvelope Θ π γ zs (n + 1)
              = ∑ a : Action,
                  (π.policy (historyOfCycles zs) a).toReal *
                    lowerRecursiveQValueEnvelope Θ π γ zs a n := rfl
          _ ≤ ∑ a : Action,
                (π.policy (historyOfCycles zs) a).toReal *
                  qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n := by
                refine Finset.sum_le_sum ?_
                intro a _ha
                have ha :=
                  (qValue_historyOfCycles_mem_recursiveEnvelope
                    (Θ := Θ) (π := π) (γ := γ) n zs a i).1
                exact mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
          _ = value (toEnvironment (Θ i)) π γ (historyOfCycles zs) (n + 1) := by
                exact hv.symm
      · calc
          value (toEnvironment (Θ i)) π γ (historyOfCycles zs) (n + 1)
              = ∑ a : Action,
                  (π.policy (historyOfCycles zs) a).toReal *
                    qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a n := hv
          _ ≤ ∑ a : Action,
                (π.policy (historyOfCycles zs) a).toReal *
                  upperRecursiveQValueEnvelope Θ π γ zs a n := by
                refine Finset.sum_le_sum ?_
                intro a _ha
                have ha :=
                  (qValue_historyOfCycles_mem_recursiveEnvelope
                    (Θ := Θ) (π := π) (γ := γ) n zs a i).2
                exact mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
          _ = upperRecursiveValueEnvelope Θ π γ zs (n + 1) := by
                rfl

end

mutual

theorem optimalQValue_historyOfCycles_mem_recursiveEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action) (i : ι),
      lowerRecursiveOptimalQValueEnvelope Θ γ zs a n ≤
          optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a n ∧
        optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a n ≤
          upperRecursiveOptimalQValueEnvelope Θ γ zs a n
  | 0, zs, a, i => by
      simp [lowerRecursiveOptimalQValueEnvelope, upperRecursiveOptimalQValueEnvelope,
        optimalQValue_zero]
  | n + 1, zs, a, i => by
      have hwf :
          History.wellFormed (Action := Action) (Percept := Fin obs)
            (historyOfCycles zs ++ [HistElem.act a]) = true :=
        historyOfCycles_append_act_wellFormed (Action := Action) (obs := obs) zs a
      have hprob :
          (fun y : Fin obs =>
            (toEnvironment (Θ i)).prob (historyOfCycles zs ++ [HistElem.act a]) y) =
            (fun y : Fin obs =>
              observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y) := by
        funext y
        simpa [toEnvironment] using
          environmentProb_historyOfCycles_append_act
            (θ := Θ i) (zs := zs) (a := a) (y := y)
      have hq :
          optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a (n + 1) =
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val *
                    optimalValue (toEnvironment (Θ i)) γ
                      (historyOfCycles (zs ++ [(a, y)])) n) := by
        rw [optimalQValue_succ]
        simp [hwf, hprob, historyOfCycles_append_singleton]
      constructor
      · calc
          lowerRecursiveOptimalQValueEnvelope Θ γ zs a (n + 1)
              = Finset.univ.inf' Finset.univ_nonempty
                  (fun j =>
                    ∑ y : Fin obs,
                      (observationMassGivenAction (Θ j) (filteringMass (Θ j) zs) a y).toReal *
                        (PerceptReward.reward y +
                          γ.val *
                            lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n)) := rfl
          _ ≤ ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val *
                      lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n) := by
                exact Finset.inf'_le
                  (fun j =>
                    ∑ y : Fin obs,
                      (observationMassGivenAction (Θ j) (filteringMass (Θ j) zs) a y).toReal *
                        (PerceptReward.reward y +
                          γ.val *
                            lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
                  (Finset.mem_univ i)
          _ ≤ ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val *
                      optimalValue (toEnvironment (Θ i)) γ
                        (historyOfCycles (zs ++ [(a, y)])) n) := by
                refine Finset.sum_le_sum ?_
                intro y _hy
                have hy :=
                  (optimalValue_historyOfCycles_mem_recursiveEnvelope
                    (Θ := Θ) (γ := γ) n (zs ++ [(a, y)]) i).1
                have hγhy :
                    γ.val *
                        lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n ≤
                      γ.val *
                        optimalValue (toEnvironment (Θ i)) γ
                          (historyOfCycles (zs ++ [(a, y)])) n :=
                  mul_le_mul_of_nonneg_left hy γ.nonneg
                have hterm :
                    PerceptReward.reward y +
                        γ.val *
                          lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n ≤
                      PerceptReward.reward y +
                        γ.val *
                          optimalValue (toEnvironment (Θ i)) γ
                            (historyOfCycles (zs ++ [(a, y)])) n :=
                  by
                    have htmp := add_le_add_right hγhy (PerceptReward.reward y)
                    simpa [add_comm, add_left_comm, add_assoc] using htmp
                exact mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg
          _ = optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a (n + 1) := by
                exact hq.symm
      · calc
          optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a (n + 1)
              = ∑ y : Fin obs,
                  (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                    (PerceptReward.reward y +
                      γ.val *
                        optimalValue (toEnvironment (Θ i)) γ
                          (historyOfCycles (zs ++ [(a, y)])) n) := hq
          _ ≤ ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val *
                      upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n) := by
                refine Finset.sum_le_sum ?_
                intro y _hy
                have hy :=
                  (optimalValue_historyOfCycles_mem_recursiveEnvelope
                    (Θ := Θ) (γ := γ) n (zs ++ [(a, y)]) i).2
                have hγhy :
                    γ.val *
                        optimalValue (toEnvironment (Θ i)) γ
                          (historyOfCycles (zs ++ [(a, y)])) n ≤
                      γ.val *
                        upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n :=
                  mul_le_mul_of_nonneg_left hy γ.nonneg
                have hterm :
                    PerceptReward.reward y +
                        γ.val *
                          optimalValue (toEnvironment (Θ i)) γ
                            (historyOfCycles (zs ++ [(a, y)])) n ≤
                      PerceptReward.reward y +
                        γ.val *
                          upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n :=
                  by
                    have htmp := add_le_add_right hγhy (PerceptReward.reward y)
                    simpa [add_comm, add_left_comm, add_assoc] using htmp
                exact mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg
          _ ≤ upperRecursiveOptimalQValueEnvelope Θ γ zs a (n + 1) := by
                exact Finset.le_sup'
                  (s := Finset.univ)
                  (f := fun j =>
                    ∑ y : Fin obs,
                      (observationMassGivenAction (Θ j) (filteringMass (Θ j) zs) a y).toReal *
                        (PerceptReward.reward y +
                          γ.val *
                            upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
                  (Finset.mem_univ i)

theorem optimalValue_historyOfCycles_mem_recursiveEnvelope
    [Fintype ι] [Nonempty ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (i : ι),
      lowerRecursiveOptimalValueEnvelope Θ γ zs n ≤
          optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ∧
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ≤
          upperRecursiveOptimalValueEnvelope Θ γ zs n
  | 0, zs, i => by
      simp [lowerRecursiveOptimalValueEnvelope, upperRecursiveOptimalValueEnvelope,
        optimalValue_zero]
  | n + 1, zs, i => by
      have hwf :
          History.wellFormed (Action := Action) (Percept := Fin obs)
            (historyOfCycles zs) = true :=
        historyOfCycles_wellFormed (Action := Action) (obs := obs) zs
      rw [optimalValue_succ]
      simp [hwf]
      constructor
      · have hlower :
            (Finset.univ : Finset Action).fold max 0
                (fun a => lowerRecursiveOptimalQValueEnvelope Θ γ zs a n) ≤
              (Finset.univ : Finset Action).fold max 0
                (fun a => optimalQValue (toEnvironment (Θ i)) γ (historyOfCycles zs) a n) := by
            rw [Finset.fold_max_le]
            constructor
            · rw [Finset.le_fold_max]
              exact Or.inl le_rfl
            · intro a _ha
              have ha :=
                (optimalQValue_historyOfCycles_mem_recursiveEnvelope
                  (Θ := Θ) (γ := γ) n zs a i).1
              exact ha.trans (by
                rw [Finset.le_fold_max]
                exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩)
        simpa [lowerRecursiveOptimalValueEnvelope] using hlower
      · have hupper_nonneg :
            0 ≤ upperRecursiveOptimalValueEnvelope Θ γ zs (n + 1) := by
              rw [show upperRecursiveOptimalValueEnvelope Θ γ zs (n + 1) =
                  (Finset.univ : Finset Action).fold max 0
                    (fun a => upperRecursiveOptimalQValueEnvelope Θ γ zs a n) by rfl]
              rw [Finset.le_fold_max]
              exact Or.inl le_rfl
        rw [show upperRecursiveOptimalValueEnvelope Θ γ zs (n + 1) =
            (Finset.univ : Finset Action).fold max 0
              (fun a => upperRecursiveOptimalQValueEnvelope Θ γ zs a n) by rfl]
        rw [Finset.fold_max_le]
        constructor
        · exact hupper_nonneg
        · intro a _ha
          have ha :=
            (optimalQValue_historyOfCycles_mem_recursiveEnvelope
              (Θ := Θ) (γ := γ) n zs a i).2
          exact ha.trans (by
            rw [Finset.le_fold_max]
            exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩)

end

end RecursiveValueEnvelope

section RecursiveEnvelopeRestriction

variable [PerceptReward (Fin obs)] [Fintype Action]
variable {κ : Type*}

mutual

/-- Restricting to a reindexed subfamily can only raise the lower recursive
optimal `Q` envelope. This is the credal monotonicity theorem corresponding to
learning by narrowing the admissible model family. -/
theorem lowerRecursiveOptimalQValueEnvelope_le_reindex
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action),
      lowerRecursiveOptimalQValueEnvelope Θ γ zs a n ≤
        lowerRecursiveOptimalQValueEnvelope (fun k => Θ (f k)) γ zs a n
  | 0, zs, a => by
      simp [lowerRecursiveOptimalQValueEnvelope]
  | n + 1, zs, a => by
      unfold lowerRecursiveOptimalQValueEnvelope
      refine Finset.le_inf' (s := Finset.univ)
        (H := Finset.univ_nonempty)
        (f := fun k : κ =>
          ∑ y : Fin obs,
            (observationMassGivenAction (Θ (f k)) (filteringMass (Θ (f k)) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val *
                  lowerRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                    (zs ++ [(a, y)]) n)) ?_
      intro k _hk
      calc
        Finset.univ.inf' Finset.univ_nonempty
            (fun i =>
              ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
          ≤
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ (f k)) (filteringMass (Θ (f k)) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n) := by
              exact Finset.inf'_le
                (fun i =>
                  ∑ y : Fin obs,
                    (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                      (PerceptReward.reward y +
                        γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
                (Finset.mem_univ (f k))
        _ ≤
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ (f k)) (filteringMass (Θ (f k)) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val *
                    lowerRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                      (zs ++ [(a, y)]) n) := by
              refine Finset.sum_le_sum ?_
              intro y _hy
              have hy :=
                lowerRecursiveOptimalValueEnvelope_le_reindex
                  (Θ := Θ) (f := f) (γ := γ) n (zs ++ [(a, y)])
              have hγhy :
                  γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n ≤
                    γ.val *
                      lowerRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                        (zs ++ [(a, y)]) n :=
                mul_le_mul_of_nonneg_left hy γ.nonneg
              have hterm :
                  PerceptReward.reward y +
                      γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n ≤
                    PerceptReward.reward y +
                      γ.val *
                        lowerRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                          (zs ++ [(a, y)]) n := by
                  have htmp := add_le_add_right hγhy (PerceptReward.reward y)
                  simpa [add_comm, add_left_comm, add_assoc] using htmp
              exact mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg

/-- Restricting to a reindexed subfamily can only lower the upper recursive
optimal `Q` envelope. -/
theorem upperRecursiveOptimalQValueEnvelope_reindex_le
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action),
      upperRecursiveOptimalQValueEnvelope (fun k => Θ (f k)) γ zs a n ≤
        upperRecursiveOptimalQValueEnvelope Θ γ zs a n
  | 0, zs, a => by
      simp [upperRecursiveOptimalQValueEnvelope]
  | n + 1, zs, a => by
      unfold upperRecursiveOptimalQValueEnvelope
      refine Finset.sup'_le (s := Finset.univ)
        (H := Finset.univ_nonempty)
        (f := fun k : κ =>
          ∑ y : Fin obs,
            (observationMassGivenAction (Θ (f k)) (filteringMass (Θ (f k)) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val *
                  upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                    (zs ++ [(a, y)]) n)) ?_
      intro k _hk
      calc
        ∑ y : Fin obs,
            (observationMassGivenAction (Θ (f k)) (filteringMass (Θ (f k)) zs) a y).toReal *
              (PerceptReward.reward y +
                γ.val *
                  upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                    (zs ++ [(a, y)]) n)
          ≤
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ (f k)) (filteringMass (Θ (f k)) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n) := by
              refine Finset.sum_le_sum ?_
              intro y _hy
              have hy :=
                upperRecursiveOptimalValueEnvelope_reindex_le
                  (Θ := Θ) (f := f) (γ := γ) n (zs ++ [(a, y)])
              have hγhy :
                  γ.val *
                      upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                        (zs ++ [(a, y)]) n ≤
                    γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n :=
                mul_le_mul_of_nonneg_left hy γ.nonneg
              have hterm :
                  PerceptReward.reward y +
                      γ.val *
                        upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ
                          (zs ++ [(a, y)]) n ≤
                    PerceptReward.reward y +
                      γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n := by
                  have htmp := add_le_add_right hγhy (PerceptReward.reward y)
                  simpa [add_comm, add_left_comm, add_assoc] using htmp
              exact mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg
        _ ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun i =>
                ∑ y : Fin obs,
                  (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                    (PerceptReward.reward y +
                      γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n)) := by
              exact Finset.le_sup'
                (s := Finset.univ)
                (f := fun i =>
                  ∑ y : Fin obs,
                    (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                      (PerceptReward.reward y +
                        γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
                (Finset.mem_univ (f k))

/-- Restricting to a reindexed subfamily can only raise the lower recursive
optimal value envelope. -/
theorem lowerRecursiveOptimalValueEnvelope_le_reindex
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)),
      lowerRecursiveOptimalValueEnvelope Θ γ zs n ≤
        lowerRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ zs n
  | 0, zs => by
      simp [lowerRecursiveOptimalValueEnvelope]
  | n + 1, zs => by
      have hfold :
          (Finset.univ : Finset Action).fold max 0
              (fun a => lowerRecursiveOptimalQValueEnvelope Θ γ zs a n)
            ≤
          (Finset.univ : Finset Action).fold max 0
              (fun a => lowerRecursiveOptimalQValueEnvelope (fun k => Θ (f k)) γ zs a n) := by
        rw [Finset.fold_max_le]
        constructor
        · rw [Finset.le_fold_max]
          exact Or.inl le_rfl
        · intro a _ha
          exact (lowerRecursiveOptimalQValueEnvelope_le_reindex
            (Θ := Θ) (f := f) (γ := γ) n zs a).trans
            (by
              rw [Finset.le_fold_max]
              exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩)
      simpa [lowerRecursiveOptimalValueEnvelope] using hfold

/-- Restricting to a reindexed subfamily can only lower the upper recursive
optimal value envelope. -/
theorem upperRecursiveOptimalValueEnvelope_reindex_le
    [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)),
      upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ zs n ≤
        upperRecursiveOptimalValueEnvelope Θ γ zs n
  | 0, zs => by
      simp [upperRecursiveOptimalValueEnvelope]
  | n + 1, zs => by
      have hupper_nonneg :
          0 ≤ upperRecursiveOptimalValueEnvelope Θ γ zs (n + 1) := by
        rw [show upperRecursiveOptimalValueEnvelope Θ γ zs (n + 1) =
            (Finset.univ : Finset Action).fold max 0
              (fun a => upperRecursiveOptimalQValueEnvelope Θ γ zs a n) by rfl]
        rw [Finset.le_fold_max]
        exact Or.inl le_rfl
      rw [show upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ zs (n + 1) =
          (Finset.univ : Finset Action).fold max 0
            (fun a => upperRecursiveOptimalQValueEnvelope (fun k => Θ (f k)) γ zs a n) by rfl]
      rw [show upperRecursiveOptimalValueEnvelope Θ γ zs (n + 1) =
          (Finset.univ : Finset Action).fold max 0
            (fun a => upperRecursiveOptimalQValueEnvelope Θ γ zs a n) by rfl]
      rw [Finset.fold_max_le]
      constructor
      · exact hupper_nonneg
      · intro a _ha
        exact (upperRecursiveOptimalQValueEnvelope_reindex_le
          (Θ := Θ) (f := f) (γ := γ) n zs a).trans
          (by
            rw [Finset.le_fold_max]
            exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩)

end

/- Credal learning monotonicity: narrowing the controlled-HMM family via a
reindexing map shrinks the recursive optimal decision interval. -/
set_option linter.unusedSectionVars false
theorem recursiveOptimalValueEnvelope_mono_reindex
    [PerceptReward (Fin obs)] [Fintype Action]
    [Fintype ι] [Nonempty ι]
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (f : κ → ι)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (n : ℕ) :
    lowerRecursiveOptimalValueEnvelope Θ γ zs n ≤
        lowerRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ zs n ∧
      upperRecursiveOptimalValueEnvelope (fun k => Θ (f k)) γ zs n ≤
        upperRecursiveOptimalValueEnvelope Θ γ zs n := by
  exact ⟨
    lowerRecursiveOptimalValueEnvelope_le_reindex (Θ := Θ) (f := f) (γ := γ) n zs,
    upperRecursiveOptimalValueEnvelope_reindex_le (Θ := Θ) (f := f) (γ := γ) n zs
  ⟩
set_option linter.unusedSectionVars true

end RecursiveEnvelopeRestriction

section RecursiveEnvelopeSingletonCollapse

variable [PerceptReward (Fin obs)] [Fintype Action]

mutual

/-- In a singleton controlled-HMM family, the lower and upper recursive optimal
`Q` envelopes coincide. -/
theorem recursiveOptimalQValueEnvelope_eq_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)) (a : Action),
      lowerRecursiveOptimalQValueEnvelope Θ γ zs a n =
        upperRecursiveOptimalQValueEnvelope Θ γ zs a n
  | 0, zs, a => by
      simp [lowerRecursiveOptimalQValueEnvelope, upperRecursiveOptimalQValueEnvelope]
  | n + 1, zs, a => by
      obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
      have hlower :
          lowerRecursiveOptimalQValueEnvelope Θ γ zs a (n + 1) =
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ i0) (filteringMass (Θ i0) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n) := by
        unfold lowerRecursiveOptimalQValueEnvelope
        apply le_antisymm
        · exact Finset.inf'_le
            (fun i =>
              ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
            (Finset.mem_univ i0)
        · refine Finset.le_inf' (s := Finset.univ)
            (H := Finset.univ_nonempty)
            (f := fun i : ι =>
              ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val * lowerRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n)) ?_
          intro i _hi
          have hi : i = i0 := Subsingleton.elim i i0
          subst hi
          exact le_rfl
      have hupper :
          upperRecursiveOptimalQValueEnvelope Θ γ zs a (n + 1) =
            ∑ y : Fin obs,
              (observationMassGivenAction (Θ i0) (filteringMass (Θ i0) zs) a y).toReal *
                (PerceptReward.reward y +
                  γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n) := by
        unfold upperRecursiveOptimalQValueEnvelope
        apply le_antisymm
        · refine Finset.sup'_le (s := Finset.univ)
            (H := Finset.univ_nonempty)
            (f := fun i : ι =>
              ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n)) ?_
          intro i _hi
          have hi : i = i0 := Subsingleton.elim i i0
          subst hi
          exact le_rfl
        · exact Finset.le_sup'
            (s := Finset.univ)
            (f := fun i =>
              ∑ y : Fin obs,
                (observationMassGivenAction (Θ i) (filteringMass (Θ i) zs) a y).toReal *
                  (PerceptReward.reward y +
                    γ.val * upperRecursiveOptimalValueEnvelope Θ γ (zs ++ [(a, y)]) n))
            (Finset.mem_univ i0)
      rw [hlower, hupper]
      refine Finset.sum_congr rfl ?_
      intro y _hy
      have hy :=
        recursiveOptimalValueEnvelope_eq_of_subsingleton
          (Θ := Θ) (γ := γ) n (zs ++ [(a, y)])
      simp [hy]

/-- In a singleton controlled-HMM family, the lower and upper recursive optimal
value envelopes coincide. -/
theorem recursiveOptimalValueEnvelope_eq_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor) :
    ∀ (n : ℕ) (zs : List (CycleObservation Action obs)),
      lowerRecursiveOptimalValueEnvelope Θ γ zs n =
        upperRecursiveOptimalValueEnvelope Θ γ zs n
  | 0, zs => by
      simp [lowerRecursiveOptimalValueEnvelope, upperRecursiveOptimalValueEnvelope]
  | n + 1, zs => by
      unfold lowerRecursiveOptimalValueEnvelope upperRecursiveOptimalValueEnvelope
      have hlower_nonneg :
          0 ≤ (Finset.univ : Finset Action).fold max 0
            (fun a => lowerRecursiveOptimalQValueEnvelope Θ γ zs a n) := by
        rw [Finset.le_fold_max]
        exact Or.inl le_rfl
      apply le_antisymm
      · rw [Finset.fold_max_le]
        constructor
        · rw [Finset.le_fold_max]
          exact Or.inl le_rfl
        · intro a _ha
          rw [recursiveOptimalQValueEnvelope_eq_of_subsingleton
            (Θ := Θ) (γ := γ) n zs a]
          rw [Finset.le_fold_max]
          exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩
      · rw [Finset.fold_max_le]
        constructor
        · exact hlower_nonneg
        · intro a _ha
          rw [show upperRecursiveOptimalQValueEnvelope Θ γ zs a n =
              lowerRecursiveOptimalQValueEnvelope Θ γ zs a n by
                exact (recursiveOptimalQValueEnvelope_eq_of_subsingleton
                  (Θ := Θ) (γ := γ) n zs a).symm]
          rw [Finset.le_fold_max]
          exact Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩

end

/- In a singleton controlled-HMM family, the recursive credal optimal-value
envelope collapses exactly to the model's optimal value. -/
set_option linter.unusedSectionVars false
theorem recursiveOptimalValueEnvelope_eq_model_of_subsingleton
    [PerceptReward (Fin obs)] [Fintype Action]
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (n : ℕ)
    (zs : List (CycleObservation Action obs))
    (i : ι) :
    lowerRecursiveOptimalValueEnvelope Θ γ zs n =
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ∧
      upperRecursiveOptimalValueEnvelope Θ γ zs n =
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n := by
  have hmem :=
    optimalValue_historyOfCycles_mem_recursiveEnvelope
      (Θ := Θ) (γ := γ) n zs i
  have hcollapse :=
    recursiveOptimalValueEnvelope_eq_of_subsingleton
      (Θ := Θ) (γ := γ) n zs
  constructor
  · apply le_antisymm
    · exact hmem.1
    · simpa [hcollapse] using hmem.2
  · apply le_antisymm
    · simpa [hcollapse] using hmem.1
    · exact hmem.2
set_option linter.unusedSectionVars true

end RecursiveEnvelopeSingletonCollapse

section LabelSwapWitness

/-- Tiny local Dirac helper for the credal witness models. -/
private def diracPM {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : MeasureTheory.ProbabilityMeasure α :=
  ⟨MeasureTheory.Measure.dirac a, MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

@[simp] private theorem diracPM_apply_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α]
    (a b : α) :
    diracPM a ({b} : Set α) = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h
    simp [diracPM]
  · simp [diracPM, h]

@[simp] private theorem singleton_indicator_one_toNNReal
    {α : Type*} [DecidableEq α] (a b : α) :
    (((Set.singleton a).indicator (1 : α → ENNReal)) b).toNNReal = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h
    have hb : b ∈ Set.singleton b := Set.mem_singleton b
    have hind : (((Set.singleton b).indicator (1 : α → ENNReal)) b) = 1 := by
      rw [Set.indicator_of_mem hb]
      simp
    simp [hind]
  · have hb : b ∉ Set.singleton a := by
      intro hb
      exact h (Set.mem_singleton_iff.mp hb)
    have hind : (((Set.singleton a).indicator (1 : α → ENNReal)) b) = 0 := by
      rw [Set.indicator_of_notMem hb]
    simp [h, hind]

/-- Unit-action version of the first label-swap witness. -/
noncomputable def hiddenLabelSwapControlledHMM₀ : ControlledFiniteHMMParam Unit 2 2 where
  init := diracPM 0
  trans := fun _ i => diracPM i
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1

/-- Same observed process, swapped hidden labels. -/
noncomputable def hiddenLabelSwapControlledHMM₁ : ControlledFiniteHMMParam Unit 2 2 where
  init := diracPM 1
  trans := fun _ i => diracPM i
  emission := fun
    | 0 => diracPM 1
    | 1 => diracPM 0

noncomputable def hiddenLabelSwapFamily : Fin 2 → ControlledFiniteHMMParam Unit 2 2
  | 0 => hiddenLabelSwapControlledHMM₀
  | 1 => hiddenLabelSwapControlledHMM₁

@[simp] theorem hiddenLabelSwapControlled_observedCycleProb_singleton_model0 :
    observedCycleProb hiddenLabelSwapControlledHMM₀ [((), 0)] = 1 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    observedCycleProb_append_singleton]
  unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₀, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_observedCycleProb_singleton_model1 :
    observedCycleProb hiddenLabelSwapControlledHMM₁ [((), 0)] = 1 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    observedCycleProb_append_singleton]
  unfold observationMassGivenAction filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₁, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_filteringMass_model0 :
    filteringMass hiddenLabelSwapControlledHMM₀ [((), 0)] 0 = 1 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    filteringMass_append_singleton]
  unfold filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₀, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_filteringMass_model1 :
    filteringMass hiddenLabelSwapControlledHMM₁ [((), 0)] 0 = 0 := by
  rw [show ([((), 0)] : List (CycleObservation Unit 2)) = [] ++ [((), 0)] by simp,
    filteringMass_append_singleton]
  unfold filteringMass filteringMassAux initialLatentMass
    filteringStepMass predictiveLatentMass
  rw [Fin.sum_univ_two]
  simp [hiddenLabelSwapControlledHMM₁, initProb, stepProb, emissionProb, diracPM]

@[simp] theorem hiddenLabelSwapControlled_filteringPosteriorMass_model0 :
    filteringPosteriorMass hiddenLabelSwapControlledHMM₀ [((), 0)] 0 = 1 := by
  unfold filteringPosteriorMass
  rw [hiddenLabelSwapControlled_observedCycleProb_singleton_model0,
    hiddenLabelSwapControlled_filteringMass_model0]
  simp

@[simp] theorem hiddenLabelSwapControlled_filteringPosteriorMass_model1 :
    filteringPosteriorMass hiddenLabelSwapControlledHMM₁ [((), 0)] 0 = 0 := by
  unfold filteringPosteriorMass
  rw [hiddenLabelSwapControlled_observedCycleProb_singleton_model1,
    hiddenLabelSwapControlled_filteringMass_model1]
  simp

theorem hiddenLabelSwapFamily_observed_nonzero (i : Fin 2) :
    observedCycleProb (hiddenLabelSwapFamily i) [((), 0)] ≠ 0 := by
  fin_cases i <;> simp [hiddenLabelSwapFamily]

theorem hiddenLabelSwapFamily_lower_eq_zero :
    lowerFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 = 0 := by
  apply le_antisymm
  · calc
      lowerFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0
        ≤ (filteringPosteriorMass (hiddenLabelSwapFamily 1) [((), 0)] 0).toReal :=
            lowerFilteringPosteriorStrength_le hiddenLabelSwapFamily [((), 0)] 0 1
      _ = 0 := by
          have hzero :
              (filteringPosteriorMass (hiddenLabelSwapFamily 1) [((), 0)] 0).toReal = 0 := by
            exact congrArg ENNReal.toReal hiddenLabelSwapControlled_filteringPosteriorMass_model1
          exact hzero
  · exact lowerFilteringPosteriorStrength_nonneg hiddenLabelSwapFamily [((), 0)] 0

theorem hiddenLabelSwapFamily_upper_eq_one :
    upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 = 1 := by
  apply le_antisymm
  · exact upperFilteringPosteriorStrength_le_one hiddenLabelSwapFamily [((), 0)] 0
      hiddenLabelSwapFamily_observed_nonzero
  · have hmem :
        (1 : ℝ) ≤ upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 := by
        calc
          (1 : ℝ) = (filteringPosteriorMass (hiddenLabelSwapFamily 0) [((), 0)] 0).toReal := by
            simp [hiddenLabelSwapFamily]
          _ ≤ upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 := by
            exact le_upperFilteringPosteriorStrength hiddenLabelSwapFamily [((), 0)] 0 0
    exact hmem

/-- Positive example: the credal truth value for the unit-action label-swap
family spans the full interval `[0,1]`. -/
example :
    (filteringCredalTruthValue hiddenLabelSwapFamily [((), 0)] 0
      hiddenLabelSwapFamily_observed_nonzero).lower = 0 := by
  exact hiddenLabelSwapFamily_lower_eq_zero

/-- Negative example: the observed-only credal interval need not collapse to a
point, even for a singleton observed cycle. -/
example :
    (filteringCredalTruthValue hiddenLabelSwapFamily [((), 0)] 0
      hiddenLabelSwapFamily_observed_nonzero).upper = 1 := by
  exact hiddenLabelSwapFamily_upper_eq_one

end LabelSwapWitness

end Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal
