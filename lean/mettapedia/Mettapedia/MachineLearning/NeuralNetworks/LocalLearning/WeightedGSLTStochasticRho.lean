import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCostImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StochasticValuation
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Stochastic rho realization of conserved-credit efficacy

The conserved-credit image already reconstructs a quantized efficacy

`base + quantum * ownedCreditCount`.

This file realizes that observable as a stochastic rho transition intensity.
One output races against one base receiver and one receiver for each owned
credit quantum.  The executable rho engine therefore exposes exactly
`1 + ownedCreditCount` indexed `COMM` occurrences.  A
Knuth--Skilling-style additive event valuation assigns the base occurrence
rate `base` and every credit occurrence rate `quantum`; their total hazard is
exactly the derived efficacy.

This is a rate-realization construction.  It does not claim that arbitrary
pure-rho contexts preserve a weighted source's rate semantics automatically.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTStochasticRho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StochasticValuation
open WeightedGSLTConservedCredit
open WeightedGSLTCausalCredit
open WeightedGSLTRhoInternalization
open Finset BigOperators
open scoped ENNReal

/-! ## Abstract credit-event valuation -/

/-- One base event plus one event for every credit quantum owned by a synapse.
The finite indices enumerate the owned quanta; slot identity is irrelevant to
the aggregate rate but multiplicity is retained. -/
abbrev CreditRateEvent
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :=
  Option (Fin (accountCredits state.core (.synapse synapse)))

/-- The base alternative carries `base`; every owned-credit alternative
carries `quantum`. -/
def creditEventRate {Event : Type*}
    (base quantum : ℝ≥0∞) : Option Event → ℝ≥0∞
  | none => base
  | some _ => quantum

/-- Additive valuation of all base and owned-credit alternatives. -/
noncomputable def creditRateHazard
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) : ℝ≥0∞ :=
  eventHazard (creditEventRate base quantum :
    CreditRateEvent state synapse → ℝ≥0∞) Finset.univ

/-- **Knuth--Skilling rate realization.**  Disjoint base and credit
alternatives add to `base + count • quantum`. -/
theorem creditRateHazard_eq_base_add_credits
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    creditRateHazard base quantum state synapse =
      base + accountCredits state.core (.synapse synapse) • quantum := by
  unfold creditRateHazard eventHazard
  rw [Fintype.sum_option]
  simp [creditEventRate]

/-- Negative boundary: zero quantum rate makes every credit allocation
observationally identical at the transition-intensity surface. -/
theorem creditRateHazard_zeroQuantum
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    creditRateHazard base 0 state synapse = base := by
  rw [creditRateHazard_eq_base_add_credits]
  simp

/-! ## Executable rho race -/

/-- The pure-rho race induced by one state/synapse observation.  It uses the
generic closed communication canary with one base receiver and one receiver
per owned credit. -/
def creditRaceElements
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) : List Pattern :=
  repeatedCommunicationCanary
    (accountCredits state.core (.synapse synapse) + 1)

/-- Exact operational frontier cardinality of the state-induced rho race. -/
theorem creditRace_frontier_length
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    (Engine.findAllComm (creditRaceElements state synapse)).length =
      accountCredits state.core (.synapse synapse) + 1 := by
  exact repeatedCommunicationCanary_frontier_length _

/-- The executable engine's indexed occurrences are equivalent to the
abstract base-or-credit event family. -/
noncomputable def creditRaceOccurrenceEquiv
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    CommOccurrence (creditRaceElements state synapse) ≃
      CreditRateEvent state synapse :=
  (finCongr (creditRace_frontier_length state synapse)).trans
    (finSuccEquiv (accountCredits state.core (.synapse synapse)))

/-- Pull the abstract base/quantum valuation back to actual engine occurrence
indices. -/
noncomputable def creditRaceOccurrenceRate
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    CommOccurrence (creditRaceElements state synapse) → ℝ≥0∞ :=
  fun occurrence =>
    creditEventRate base quantum
      (creditRaceOccurrenceEquiv state synapse occurrence)

/-- Total exit hazard of the executable state-induced rho race. -/
noncomputable def rhoCreditHazard
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) : ℝ≥0∞ :=
  commExitHazard (creditRaceElements state synapse)
    (creditRaceOccurrenceRate base quantum state synapse)

/-- **Generator correspondence.**  Summing the rates of the actual indexed
`COMM` frontier agrees exactly with the abstract credit-event valuation. -/
theorem rhoCreditHazard_eq_creditRateHazard
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    rhoCreditHazard base quantum state synapse =
      creditRateHazard base quantum state synapse := by
  unfold rhoCreditHazard commExitHazard eventHazard
  unfold creditRaceOccurrenceRate creditRateHazard eventHazard
  exact (creditRaceOccurrenceEquiv state synapse).sum_comp
    (creditEventRate base quantum)

/-- **Stochastic rho realizes the derived efficacy.** -/
theorem rhoCreditHazard_eq_base_add_credits
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    rhoCreditHazard base quantum state synapse =
      base + accountCredits state.core (.synapse synapse) • quantum := by
  rw [rhoCreditHazard_eq_creditRateHazard,
    creditRateHazard_eq_base_add_credits]

/-- For finite nonnegative parameters, the real-valued view of the rho hazard
is exactly the previously defined image-derived weight. -/
theorem rhoCreditHazard_toReal_eq_imageDerivedWeight
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : NNReal)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    (rhoCreditHazard (base : ℝ≥0∞) (quantum : ℝ≥0∞)
      state synapse).toReal =
      imageDerivedWeight (base : Real) (quantum : Real) state synapse := by
  rw [rhoCreditHazard_eq_base_add_credits]
  simp only [nsmul_eq_mul]
  rw [ENNReal.toReal_add ENNReal.coe_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top),
    ENNReal.toReal_mul]
  simp [imageDerivedWeight, imageAccountCredits_eq_accountCredits, mul_comm]

/-! ## Rate observation from the concrete target term -/

/-- Build the stochastic observation race from a pure-rho term alone.  The
syntax-level decoder determines how many credit occurrences belong to the
selected synapse; no source state is an argument. -/
noncomputable def decodedCreditRaceElements
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (image : Pattern) (synapse : Synapse) : List Pattern :=
  repeatedCommunicationCanary
    (decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots) (signalSlots := signalSlots)
      (creditBudget := creditBudget) image (.synapse synapse) + 1)

/-- The target-only observation race has one base occurrence plus one
occurrence for every decoded credit quantum. -/
theorem decodedCreditRace_frontier_length
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (image : Pattern) (synapse : Synapse) :
    (Engine.findAllComm
      (decodedCreditRaceElements (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (signalSlots := signalSlots) (creditBudget := creditBudget)
        image synapse)).length =
      decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) image (.synapse synapse) + 1 := by
  exact repeatedCommunicationCanary_frontier_length _

/-- Actual target-observation occurrences are equivalent to one base event
or one event for each decoded credit quantum. -/
noncomputable def decodedCreditRaceOccurrenceEquiv
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (image : Pattern) (synapse : Synapse) :
    CommOccurrence
        (decodedCreditRaceElements (Synapse := Synapse) (Neuron := Neuron)
          (receiptSlots := receiptSlots)
          (signalSlots := signalSlots) (creditBudget := creditBudget)
          image synapse) ≃
      Option (Fin
        (decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
          (receiptSlots := receiptSlots) (signalSlots := signalSlots)
          (creditBudget := creditBudget) image (.synapse synapse))) :=
  (finCongr (decodedCreditRace_frontier_length
      (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots) (signalSlots := signalSlots)
      (creditBudget := creditBudget) image synapse)).trans
    (finSuccEquiv
      (decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) image (.synapse synapse)))

/-- Pull the base/quantum rates back to the engine occurrences constructed
from the target term. -/
noncomputable def decodedCreditRaceOccurrenceRate
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞) (image : Pattern) (synapse : Synapse) :
    CommOccurrence
        (decodedCreditRaceElements (Synapse := Synapse) (Neuron := Neuron)
          (receiptSlots := receiptSlots)
          (signalSlots := signalSlots) (creditBudget := creditBudget)
          image synapse) → ℝ≥0∞ :=
  fun occurrence =>
    creditEventRate base quantum
      (decodedCreditRaceOccurrenceEquiv
        (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) image synapse occurrence)

/-- Exit hazard of the stochastic observation compiled from a target term. -/
noncomputable def decodedRhoCreditHazard
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞) (image : Pattern) (synapse : Synapse) : ℝ≥0∞ :=
  commExitHazard
    (decodedCreditRaceElements (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      image synapse)
    (decodedCreditRaceOccurrenceRate
      (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots) (signalSlots := signalSlots)
      (creditBudget := creditBudget) base quantum image synapse)

/-- The target-only operational hazard is base rate plus one quantum rate for
each credit decoded from the concrete pure-rho term. -/
theorem decodedRhoCreditHazard_eq_base_add_credits
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞) (image : Pattern) (synapse : Synapse) :
    decodedRhoCreditHazard (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (signalSlots := signalSlots) (creditBudget := creditBudget)
        base quantum image synapse =
      base + decodedAccountCredits (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) image (.synapse synapse) • quantum := by
  unfold decodedRhoCreditHazard commExitHazard eventHazard
  unfold decodedCreditRaceOccurrenceRate
  rw [(decodedCreditRaceOccurrenceEquiv
    (Synapse := Synapse) (Neuron := Neuron)
    (receiptSlots := receiptSlots) (signalSlots := signalSlots)
    (creditBudget := creditBudget) image synapse).sum_comp]
  rw [Fintype.sum_option]
  simp [creditEventRate]

/-- For finite nonnegative parameters, the target-only stochastic observer
recovers the target-decoded efficacy exactly. -/
theorem decodedRhoCreditHazard_toReal_eq_decodedDerivedWeight
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : NNReal) (image : Pattern) (synapse : Synapse) :
    (decodedRhoCreditHazard (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      (base : ℝ≥0∞) (quantum : ℝ≥0∞) image synapse).toReal =
      decodedDerivedWeight (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) (base : Real) (quantum : Real)
        image synapse := by
  rw [decodedRhoCreditHazard_eq_base_add_credits]
  simp only [nsmul_eq_mul]
  rw [ENNReal.toReal_add ENNReal.coe_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top),
    ENNReal.toReal_mul]
  simp [decodedDerivedWeight, mul_comm]

/-- On a complete compiler image, the target-only observer agrees with the
state-induced operational hazard. -/
theorem decodedRhoCreditHazard_stateResourceImage
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : ℝ≥0∞)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    decodedRhoCreditHazard (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots)
        (signalSlots := signalSlots) (creditBudget := creditBudget)
        base quantum (stateResourceImage state) synapse =
      rhoCreditHazard base quantum state synapse := by
  rw [decodedRhoCreditHazard_eq_base_add_credits,
    rhoCreditHazard_eq_base_add_credits,
    decodedAccountCredits_stateResourceImage]

/-- Crown target-image statement: mapping a complete credit state into pure
rho and then applying the stochastic observer recovers the original derived
efficacy exactly. -/
theorem decodedRhoCreditHazard_stateResourceImage_toReal_eq_derivedWeight
    {Synapse Neuron : Type*} {receiptSlots signalSlots creditBudget : Nat}
    [Fintype Synapse] [Fintype Neuron]
    [DecidableEq Synapse] [DecidableEq Neuron]
    (base quantum : NNReal)
    (state : CausalCreditState Synapse Neuron
      receiptSlots signalSlots creditBudget)
    (synapse : Synapse) :
    (decodedRhoCreditHazard (Synapse := Synapse) (Neuron := Neuron)
      (receiptSlots := receiptSlots)
      (signalSlots := signalSlots) (creditBudget := creditBudget)
      (base : ℝ≥0∞) (quantum : ℝ≥0∞)
      (stateResourceImage state) synapse).toReal =
      derivedWeight (base : Real) (quantum : Real) state.core synapse := by
  calc
    _ = decodedDerivedWeight (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) (base : Real) (quantum : Real)
        (stateResourceImage state) synapse :=
      decodedRhoCreditHazard_toReal_eq_decodedDerivedWeight
        (Synapse := Synapse) (Neuron := Neuron)
        (receiptSlots := receiptSlots) (signalSlots := signalSlots)
        (creditBudget := creditBudget) base quantum
        (stateResourceImage state) synapse
    _ = _ := decodedDerivedWeight_stateResourceImage
      (base : Real) (quantum : Real) state synapse

/-! ## Choice-task canaries -/

/-- Initially, the target synapse owns one credit, so unit base and quantum
give exit hazard two. -/
theorem initialTarget_rhoCreditHazard :
    rhoCreditHazard 1 1 causalInitialChoiceState .target = 2 := by
  rw [rhoCreditHazard_eq_base_add_credits]
  change 1 + accountCredits initialChoiceState (.synapse .target) • 1 = 2
  rw [initial_target_credits]
  norm_num

/-- After target crediting, the target synapse owns three credits and its
unit-parameter exit hazard is four. -/
theorem learnedTarget_rhoCreditHazard :
    rhoCreditHazard 1 1 causalTargetLearnedState .target = 4 := by
  rw [rhoCreditHazard_eq_base_add_credits]
  change 1 + accountCredits targetLearnedState (.synapse .target) • 1 = 4
  rw [targetLearned_target_credits]
  norm_num

/-- The same learned state leaves the distractor at one credit, hence hazard
two.  The stochastic surface therefore distinguishes the rewarded choice. -/
theorem learnedDistractor_rhoCreditHazard :
    rhoCreditHazard 1 1 causalTargetLearnedState .distractor = 2 := by
  rw [rhoCreditHazard_eq_base_add_credits]
  change 1 + accountCredits targetLearnedState (.synapse .distractor) • 1 = 2
  rw [targetLearned_distractor_credits]
  norm_num

/-- Positive discrimination canary for the stochastic realization. -/
theorem learnedChoice_rhoCreditHazard_separates :
    rhoCreditHazard 1 1 causalTargetLearnedState .target >
      rhoCreditHazard 1 1 causalTargetLearnedState .distractor := by
  rw [learnedTarget_rhoCreditHazard, learnedDistractor_rhoCreditHazard]
  norm_num

/-- Negative control: setting quantum rate to zero removes the learned
distinction even though the underlying resource allocation still differs. -/
theorem learnedChoice_zeroQuantum_collapses (base : ℝ≥0∞) :
    rhoCreditHazard base 0 causalTargetLearnedState .target =
      rhoCreditHazard base 0 causalTargetLearnedState .distractor := by
  rw [rhoCreditHazard_eq_base_add_credits,
    rhoCreditHazard_eq_base_add_credits]
  simp

end WeightedGSLTStochasticRho
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
