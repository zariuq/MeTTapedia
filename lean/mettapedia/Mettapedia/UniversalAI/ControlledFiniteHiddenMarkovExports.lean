import Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal
import Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge
import Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovPlanningExamples

/-!
# Controlled Finite HMM Exports (Recommended Import Surface)

This is the single recommended import path for the current controlled finite
HMM seam connecting:

- action-conditioned latent-state models,
- observed-only inference,
- credal WM / PLN-ITV packaging,
- BayesianAgents environment and planning examples.

Positive example:
* downstream users can import one file and access the controlled-HMM
  environment bridge, history filtering surface, credal ITV bridge, and a small
  verified planning example.

Negative example:
* this export surface does not yet provide a full recursive credal planning
  theory or HMM Xi consumer semantics.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI

open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovModel
open Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge
open Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge
open Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovPlanningExamples
open Mettapedia.UniversalAI.BayesianAgents.Core

universe uA uI

variable {Action : Type uA} {ι : Type uI} {latent obs : ℕ}

/-- Recommended export: controlled finite HMM parameters as the structured
POMDP-facing latent model surface. -/
abbrev controlledHMMParam (Action : Type uA) (latent obs : ℕ) :=
  ControlledFiniteHMMParam Action latent obs

/-- Recommended export: controlled finite HMM parameters equipped with the
lower-semicomputability witnesses needed for the fixed-action-stream
Solomonoff regret theorem. -/
abbrev lscControlledHMMParam (Action : Type uA) (latent obs : ℕ) :=
  Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge.LSCControlledFiniteHMMParam
    Action latent obs

/-- Recommended export: convert a completed action-observation trace into a
BayesianAgents history. -/
abbrev controlledHMM_historyOfCycles {Action : Type uA} {obs : ℕ} :=
  @Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge.historyOfCycles Action obs

/-- Recommended export: package a controlled finite HMM as a BayesianAgents
environment. -/
noncomputable abbrev controlledHMM_toEnvironment {Action : Type uA} {latent obs : ℕ} :=
  @Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovBridge.toEnvironment Action latent obs

/-- Recommended export: package a controlled finite HMM as a controlled prefix
law for the action-conditioned universal-prediction interface. -/
noncomputable abbrev controlledHMM_toControlledPrefixMeasure {Action : Type uA} {latent obs : ℕ} :=
  @Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge.toControlledPrefixMeasure
    Action latent obs

/-- Recommended export: concrete controlled Solomonoff-style semimeasure used
for fixed-action-stream universal prediction bounds. -/
noncomputable abbrev controlledSolomonoffM₂ {Action : Type uA} {obs : ℕ} :=
  @Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledSolomonoffBridge.M₂ Action (Fin obs)

/-- Recommended export: next-percept law after a completed trace and pending
action is exactly the controlled-HMM observation mass. -/
theorem controlledHMM_environmentProb_historyOfCycles_append_act
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    environmentProb θ (historyOfCycles zs ++ [HistElem.act a]) y =
      observationMassGivenAction θ (filteringMass θ zs) a y :=
  environmentProb_historyOfCycles_append_act θ zs a y

/-- Recommended export: history-level filtering mass for the completed cycles
contained in a BayesianAgents history. -/
noncomputable abbrev controlledHMM_historyFilteringMass {Action : Type uA} {latent obs : ℕ} :=
  @Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference.historyFilteringMass Action latent obs

/-- Recommended export: history-level observed probability for completed cycles
contained in a BayesianAgents history. -/
noncomputable abbrev controlledHMM_observedHistoryProb {Action : Type uA} {latent obs : ℕ} :=
  @Mettapedia.ProbabilityTheory.HiddenMarkovModels.ControlledFiniteHiddenMarkovObservedInference.observedHistoryProb Action latent obs

/-- Recommended export: appending a completed action-observation cycle to a
history updates the history-level filtering mass exactly by the controlled
filtering step. -/
theorem controlledHMM_historyFilteringMass_historyOfCycles_append_act_per
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    historyFilteringMass θ
        (historyOfCycles zs ++ [HistElem.act a, HistElem.per y]) =
      filteringStepMass θ (filteringMass θ zs) a y :=
  historyFilteringMass_historyOfCycles_append_act_per θ zs a y

/-- Recommended export: append-one-cycle history probability is the pending
action's next-percept law. -/
theorem controlledHMM_observedHistoryProb_historyOfCycles_append_act_per
    (θ : ControlledFiniteHMMParam Action latent obs)
    (zs : List (CycleObservation Action obs))
    (a : Action) (y : Fin obs) :
    observedHistoryProb θ (historyOfCycles zs ++ [HistElem.act a, HistElem.per y]) =
      environmentProb θ (historyOfCycles zs ++ [HistElem.act a]) y :=
  observedHistoryProb_historyOfCycles_append_act_per θ zs a y

/-- Recommended export: credal observed-only filtering interval packaged as a
live PLN indefinite truth value. -/
noncomputable abbrev controlledHMM_filteringCredalPLNITV {Action : Type uA} {ι : Type uI} {latent obs : ℕ} :=
  @Mettapedia.Logic.WMControlledFiniteHiddenMarkovCredal.filteringCredalPLNITV Action ι latent obs

/-- Recommended export: a family member's one-step `qValue` from a completed
history lies inside the credal PLN-ITV interval. -/
theorem controlledHMM_qValue_historyOfCycles_one_mem_PLNITV_interval
    [Fintype ι] [Nonempty ι] [Fintype Action] [PerceptReward (Fin obs)]
    (κ : ℝ) (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (π : Agent Action (Fin obs))
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (a : Action) (i : ι) :
    let itv := oneStepQValuePLNITV (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ zs a
    itv.lower ≤ qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ∧
      qValue (toEnvironment (Θ i)) π γ (historyOfCycles zs) a 1 ≤ itv.upper := by
  simpa using
    qValue_historyOfCycles_one_mem_PLNITV_interval
      (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ π γ zs a i

/-- Recommended export: a family member's two-step optimal value from a
completed history lies inside the one-step optimal credal PLN-ITV interval. -/
theorem controlledHMM_optimalValue_historyOfCycles_two_mem_PLNITV_interval
    [Fintype ι] [Nonempty ι] [Fintype Action] [PerceptReward (Fin obs)]
    (κ : ℝ) (hκ : 0 < κ)
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (i : ι) :
    let itv := oneStepOptimalValuePLNITV (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ zs
    itv.lower ≤ optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ∧
      optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) 2 ≤ itv.upper := by
  simpa using
    optimalValue_historyOfCycles_two_mem_PLNITV_interval
      (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      κ hκ Θ γ zs i

/-- Recommended export: a family member's finite-horizon optimal value from a
completed history lies inside the recursive credal decision envelope. -/
theorem controlledHMM_optimalValue_historyOfCycles_mem_recursiveEnvelope
    [Fintype ι] [Nonempty ι] [Fintype Action] [PerceptReward (Fin obs)]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (n : ℕ) (i : ι) :
    lowerRecursiveOptimalValueEnvelope Θ γ zs n ≤
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ∧
      optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ≤
        upperRecursiveOptimalValueEnvelope Θ γ zs n := by
  simpa using
    optimalValue_historyOfCycles_mem_recursiveEnvelope
      (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      (Θ := Θ) (γ := γ) n zs i

/- Recommended export: narrowing a controlled-HMM family via reindexing shrinks
the recursive credal decision interval. -/
theorem controlledHMM_recursiveOptimalValueEnvelope_mono_reindex
    [Fintype ι] [Nonempty ι] [Fintype Action] [PerceptReward (Fin obs)]
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
  simpa using
    recursiveOptimalValueEnvelope_mono_reindex
      (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      (Θ := Θ) (f := f) (γ := γ) (zs := zs) (n := n)

/- Recommended export: singleton controlled-HMM families have no credal slack;
the recursive optimal-value envelope collapses to the model's actual
`optimalValue`. -/
theorem controlledHMM_recursiveOptimalValueEnvelope_eq_model_of_subsingleton
    [Fintype ι] [Nonempty ι] [Subsingleton ι]
    [Fintype Action] [PerceptReward (Fin obs)]
    (Θ : ι → ControlledFiniteHMMParam Action latent obs)
    (γ : DiscountFactor)
    (zs : List (CycleObservation Action obs))
    (n : ℕ)
    (i : ι) :
    lowerRecursiveOptimalValueEnvelope Θ γ zs n =
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n ∧
      upperRecursiveOptimalValueEnvelope Θ γ zs n =
        optimalValue (toEnvironment (Θ i)) γ (historyOfCycles zs) n := by
  simpa using
    recursiveOptimalValueEnvelope_eq_model_of_subsingleton
      (Action := Action) (ι := ι) (latent := latent) (obs := obs)
      (Θ := Θ) (γ := γ) (n := n) (zs := zs) (i := i)

/-- Recommended export: any controlled predictor dominating the observed
controlled-HMM law inherits the standard finite-horizon controlled log-loss
regret bound along every fixed action stream. -/
theorem controlledHMM_relEntropy_le_log_inv_of_dominates
    (θ : ControlledFiniteHMMParam Action latent obs)
    (ξ :
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledSemimeasure
        Action (Fin obs))
    {c : ENNReal}
    (hdom :
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledDominates
        ξ (toControlledPrefixMeasure θ) c)
    (hc0 : c ≠ 0)
    (u : ℕ → Action)
    (n : ℕ) :
    Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledFiniteHorizon.relEntropy
        (toControlledPrefixMeasure θ) ξ u n ≤
      Real.log (1 / c.toReal) := by
  simpa using
    Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge.relEntropy_le_log_inv_of_dominates
      (θ := θ) (ξ := ξ) (hdom := hdom) (hc0 := hc0) (u := u) (n := n)

/-- Recommended export: the concrete controlled Solomonoff-style predictor
inherits the finite-horizon regret bound against any controlled finite HMM
whose fixed-stream observation law is lower semicomputable. -/
theorem controlledHMM_relEntropy_le_log_inv_controlledSolomonoffM₂
    (θ : ControlledFiniteHMMParam Action latent obs)
    (u : ℕ → Action)
    (hμ :
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.LowerSemicomputablePrefixMeasure
        (α := Fin obs)
        ((toControlledPrefixMeasure θ).conditionOnActionStream u))
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.Dominates
          ((controlledSolomonoffM₂ (Action := Action) (obs := obs)).conditionOnActionStream u)
          ((toControlledPrefixMeasure θ).conditionOnActionStream u) c ∧
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledFiniteHorizon.relEntropy
          (toControlledPrefixMeasure θ)
          (controlledSolomonoffM₂ (Action := Action) (obs := obs))
          u n ≤
        Real.log (1 / c.toReal) := by
  simpa [controlledSolomonoffM₂] using
    Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge.relEntropy_le_log_inv_controlledM₂
      (θ := θ) (u := u) (hμ := hμ) (n := n)

/-- Recommended export: packaged version of the fixed-action-stream Solomonoff
regret bound when lower semicomputability is part of the controlled-HMM
parameter package itself. -/
theorem controlledHMM_relEntropy_le_log_inv_controlledSolomonoffM₂_of_lscParam
    (θ : lscControlledHMMParam Action latent obs)
    (u : ℕ → Action)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.Dominates
          ((controlledSolomonoffM₂ (Action := Action) (obs := obs)).conditionOnActionStream u)
          ((toControlledPrefixMeasure (θ : ControlledFiniteHMMParam Action latent obs)).conditionOnActionStream u) c ∧
      Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledFiniteHorizon.relEntropy
          (toControlledPrefixMeasure (θ : ControlledFiniteHMMParam Action latent obs))
          (controlledSolomonoffM₂ (Action := Action) (obs := obs))
          u n ≤
        Real.log (1 / c.toReal) := by
  simpa [controlledSolomonoffM₂] using
    Mettapedia.UniversalAI.ControlledFiniteHiddenMarkovUniversalPredictionBridge.relEntropy_le_log_inv_controlledM₂_of_lscParam
      (θ := θ) (u := u) (n := n)

/-- Recommended export: the tiny deterministic controlled switch example has
optimal action `1` at horizon `1`. -/
theorem controlledHMM_example_optimalAction_one :
    optimalAction controlledSwitchEnv gammaOne [] 1 = 1 :=
  controlledSwitch_optimalAction_one

/-- Recommended export: the tiny deterministic controlled switch example has
optimal value `2` at horizon `4`. -/
theorem controlledHMM_example_optimalValue_four :
    optimalValue controlledSwitchEnv gammaOne [] 4 = 2 :=
  controlledSwitch_optimalValue_four

/-- Recommended export: the deterministic policy choosing action `1` attains
that horizon-`4` optimum. -/
theorem controlledHMM_example_value_four_eq_optimalValue :
    value controlledSwitchEnv chooseOneAgent gammaOne [] 4 =
      optimalValue controlledSwitchEnv gammaOne [] 4 :=
  controlledSwitch_value_four_eq_optimalValue

/-- Recommended export: the ambiguity-sensitive controlled family has a
nontrivial recursive decision interval and no unique observation-history-based
optimal action at the empty history. -/
theorem controlledHMM_example_ambiguous_optimalValue_mem_interval_and_no_uniqueAction :
    (∀ i : Fin 2,
        lowerRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 ≤
            optimalValue (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 4 ∧
          optimalValue (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 4 ≤
            upperRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4) ∧
      lowerRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 <
        upperRecursiveOptimalValueEnvelope ambiguousControlledFamily gammaOne [] 4 ∧
      ¬ ∃ a : Fin 2, ∀ i : Fin 2,
        optimalAction (toEnvironment (ambiguousControlledFamily i)) gammaOne [] 3 = a :=
  ambiguousControlledFamily_optimalValue_mem_interval_and_no_uniqueAction

end Mettapedia.UniversalAI
