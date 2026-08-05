import Mathlib.Tactic

/-!
# Loss-free expert-load feedback and its causal boundary

Loss-free mixture-of-experts balancing modifies the scores used to select
experts while retaining the original, unbiased scores as the output weights.
After a batch, each expert bias moves toward underloaded experts and away from
overloaded experts.  Using the preceding load observation makes this a causal
state machine; selecting a fixed expert capacity from an entire batch need not
be prefix causal.

This file isolates the reusable deterministic content of that construction:

* the exact light, heavy, and balanced bias updates;
* contraction of the bias gap for two unequally loaded experts;
* the corresponding wrong-sign instability;
* prefix causality of historical-load routing;
* an explicit future-token counterexample for batch-wide expert choice; and
* separation of selection bias from the selected expert's output weight.

No claim is made here that the closed-loop router always converges.  Such a
claim additionally needs a response model relating a changed bias to future
expert loads.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

namespace LossFreeExpertBalancing

noncomputable section

variable {Expert Bias Input Load Choice : Type*}

/-! ## Expert-wise feedback -/

/-- Bang-bang feedback for one expert.  An underloaded expert receives `+1`,
an overloaded expert receives `-1`, and an exactly balanced expert receives
zero. -/
def loadFeedback (target observed : ℝ) : ℝ :=
  if observed < target then 1
  else if target < observed then -1
  else 0

/-- One loss-free expert-bias update.  The target and observed loads are kept
separate so that nonuniform capacity targets can use the same construction. -/
def biasStep
    (rate : ℝ)
    (bias target observed : Expert → ℝ) : Expert → ℝ :=
  fun expert =>
    bias expert + rate * loadFeedback (target expert) (observed expert)

theorem biasStep_underloaded
    (rate : ℝ) (bias target observed : Expert → ℝ) (expert : Expert)
    (underloaded : observed expert < target expert) :
    biasStep rate bias target observed expert = bias expert + rate := by
  simp [biasStep, loadFeedback, underloaded]

theorem biasStep_overloaded
    (rate : ℝ) (bias target observed : Expert → ℝ) (expert : Expert)
    (overloaded : target expert < observed expert) :
    biasStep rate bias target observed expert = bias expert - rate := by
  have notUnderloaded : ¬ observed expert < target expert :=
    not_lt_of_ge (le_of_lt overloaded)
  simp [biasStep, loadFeedback, overloaded, notUnderloaded]
  ring

theorem biasStep_balanced
    (rate : ℝ) (bias target observed : Expert → ℝ) (expert : Expert)
    (balanced : observed expert = target expert) :
    biasStep rate bias target observed expert = bias expert := by
  simp [biasStep, loadFeedback, balanced]

/-! ## Exact two-expert correction law -/

/-- The arithmetic mean load for a pair of experts. -/
def meanLoad2 (observed : Fin 2 → ℝ) : ℝ :=
  (observed 0 + observed 1) / 2

/-- The uniform mean-load target, specialized to two experts. -/
def meanTarget2 (observed : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun _expert => meanLoad2 observed

/-- One two-expert loss-free balancing step. -/
def meanBiasStep2
    (rate : ℝ) (bias observed : Fin 2 → ℝ) : Fin 2 → ℝ :=
  biasStep rate bias (meanTarget2 observed) observed

/-- If expert zero is heavier than expert one, the heavy expert's bias
decreases and the light expert's bias increases. -/
theorem meanBiasStep2_of_right_lt_left
    (rate : ℝ) (bias observed : Fin 2 → ℝ)
    (unequal : observed 1 < observed 0) :
    meanBiasStep2 rate bias observed 0 = bias 0 - rate ∧
      meanBiasStep2 rate bias observed 1 = bias 1 + rate := by
  have mean_lt_left : meanLoad2 observed < observed 0 := by
    simp only [meanLoad2]
    linarith
  have right_lt_mean : observed 1 < meanLoad2 observed := by
    simp only [meanLoad2]
    linarith
  constructor
  · exact biasStep_overloaded rate bias (meanTarget2 observed) observed 0 mean_lt_left
  · exact biasStep_underloaded rate bias (meanTarget2 observed) observed 1 right_lt_mean

/-- The bias difference moves by exactly twice the update rate toward the
lighter expert. -/
theorem meanBiasStep2_gap_of_right_lt_left
    (rate : ℝ) (bias observed : Fin 2 → ℝ)
    (unequal : observed 1 < observed 0) :
    meanBiasStep2 rate bias observed 0 -
        meanBiasStep2 rate bias observed 1 =
      (bias 0 - bias 1) - 2 * rate := by
  obtain ⟨leftStep, rightStep⟩ :=
    meanBiasStep2_of_right_lt_left rate bias observed unequal
  rw [leftStep, rightStep]
  ring

/-- Equal loads leave both expert biases unchanged. -/
theorem meanBiasStep2_eq_bias_of_balanced
    (rate : ℝ) (bias observed : Fin 2 → ℝ)
    (balanced : observed 0 = observed 1) :
    meanBiasStep2 rate bias observed = bias := by
  funext expert
  fin_cases expert <;>
    simp [meanBiasStep2, biasStep, meanTarget2, meanLoad2, loadFeedback, balanced]

/-- Reversing the violation error is not an innocuous convention: for a
heavier left expert it increases the bias gap by exactly twice the rate. -/
def reversedMeanBiasStep2
    (rate : ℝ) (bias observed : Fin 2 → ℝ) : Fin 2 → ℝ :=
  biasStep rate bias observed (meanTarget2 observed)

theorem reversedMeanBiasStep2_gap_of_right_lt_left
    (rate : ℝ) (bias observed : Fin 2 → ℝ)
    (unequal : observed 1 < observed 0) :
    reversedMeanBiasStep2 rate bias observed 0 -
        reversedMeanBiasStep2 rate bias observed 1 =
      (bias 0 - bias 1) + 2 * rate := by
  have mean_lt_left : meanLoad2 observed < observed 0 := by
    simp only [meanLoad2]
    linarith
  have right_lt_mean : observed 1 < meanLoad2 observed := by
    simp only [meanLoad2]
    linarith
  have leftStep :=
    biasStep_underloaded rate bias observed (meanTarget2 observed) 0 mean_lt_left
  have rightStep :=
    biasStep_overloaded rate bias observed (meanTarget2 observed) 1 right_lt_mean
  change
    biasStep rate bias observed (meanTarget2 observed) 0 -
        biasStep rate bias observed (meanTarget2 observed) 1 =
      (bias 0 - bias 1) + 2 * rate
  rw [leftStep, rightStep]
  ring

/-! ## Historical routing is prefix causal -/

/-- Route a stream with the current bias, then update the bias from that
event's load observation for the next event. -/
def runHistorical
    (select : Bias → Input → Choice)
    (update : Bias → Load → Bias) :
    Bias → List (Input × Load) → List Choice
  | _bias, [] => []
  | bias, (input, load) :: rest =>
      select bias input :: runHistorical select update (update bias load) rest

/-- The first `n` decisions depend only on the first `n` input/load events. -/
theorem runHistorical_take
    (select : Bias → Input → Choice)
    (update : Bias → Load → Bias)
    (initial : Bias) (events : List (Input × Load)) (n : ℕ) :
    (runHistorical select update initial events).take n =
      runHistorical select update initial (events.take n) := by
  induction n generalizing initial events with
  | zero =>
      simp [runHistorical]
  | succ n inductionHypothesis =>
      cases events with
      | nil =>
          simp [runHistorical]
      | cons event rest =>
          rcases event with ⟨input, load⟩
          simp [runHistorical, inductionHypothesis]

/-- Equal input/load prefixes imply equal routed-decision prefixes. -/
theorem runHistorical_prefix_causal
    (select : Bias → Input → Choice)
    (update : Bias → Load → Bias)
    (initial : Bias)
    (left right : List (Input × Load)) (n : ℕ)
    (samePrefix : left.take n = right.take n) :
    (runHistorical select update initial left).take n =
      (runHistorical select update initial right).take n := by
  rw [runHistorical_take, runHistorical_take, samePrefix]

/-! ## Batch-wide expert choice can inspect the future -/

/-- A single expert with capacity one selects the first token exactly when no
later token has a larger score. -/
def capacityOneSelectsFirst : List ℝ → Prop
  | [] => False
  | first :: rest => ∀ score ∈ rest, score ≤ first

/-- A first-token decision is prefix causal when changing only the later
tokens cannot change that decision. -/
def FirstTokenPrefixCausal (route : List ℝ → Prop) : Prop :=
  ∀ first leftTail rightTail,
    route (first :: leftTail) ↔ route (first :: rightTail)

/-- Batch-wide expert choice with capacity one is not prefix causal: adding a
later, higher-scoring token evicts the unchanged first token. -/
theorem capacityOneSelectsFirst_not_prefix_causal :
    ¬ FirstTokenPrefixCausal capacityOneSelectsFirst := by
  intro causal
  have contradiction := causal 1 [] [2]
  norm_num [capacityOneSelectsFirst] at contradiction

/-! ## Selection bias is not an output-weight bias -/

/-- Top-one routing for two experts, with deterministic preference for expert
zero on ties. -/
def biasedWinner2
    (score bias : Fin 2 → ℝ) : Fin 2 :=
  if score 1 + bias 1 ≤ score 0 + bias 0 then 0 else 1

/-- The loss-free gate uses biased scores only to select the expert.  The
selected output weight is the original score. -/
def lossFreeGate2
    (score bias : Fin 2 → ℝ) (expert : Fin 2) : ℝ :=
  if expert = biasedWinner2 score bias then score expert else 0

/-- A deliberately incorrect comparator that also adds the selection bias to
the selected output weight. -/
def contaminatedGate2
    (score bias : Fin 2 → ℝ) (expert : Fin 2) : ℝ :=
  if expert = biasedWinner2 score bias then score expert + bias expert else 0

theorem lossFreeGate2_selected_weight
    (score bias : Fin 2 → ℝ) :
    lossFreeGate2 score bias (biasedWinner2 score bias) =
      score (biasedWinner2 score bias) := by
  simp [lossFreeGate2]

theorem lossFreeGate2_unselected_zero
    (score bias : Fin 2 → ℝ) (expert : Fin 2)
    (unselected : expert ≠ biasedWinner2 score bias) :
    lossFreeGate2 score bias expert = 0 := by
  simp [lossFreeGate2, unselected]

def fixtureScore : Fin 2 → ℝ := ![1, (1 : ℝ) / 2]
def zeroBias : Fin 2 → ℝ := ![0, 0]
def rightSelectionBias : Fin 2 → ℝ := ![0, 1]

theorem fixture_bias_changes_selected_expert :
    biasedWinner2 fixtureScore zeroBias = 0 ∧
      biasedWinner2 fixtureScore rightSelectionBias = 1 := by
  norm_num [biasedWinner2, fixtureScore, zeroBias, rightSelectionBias]

theorem fixture_loss_free_weight_remains_unbiased :
    lossFreeGate2 fixtureScore rightSelectionBias 1 = (1 : ℝ) / 2 := by
  norm_num [lossFreeGate2, biasedWinner2, fixtureScore, rightSelectionBias]

theorem fixture_contaminated_weight_differs :
    contaminatedGate2 fixtureScore rightSelectionBias 1 = (3 : ℝ) / 2 ∧
      contaminatedGate2 fixtureScore rightSelectionBias 1 ≠
        lossFreeGate2 fixtureScore rightSelectionBias 1 := by
  norm_num [
    contaminatedGate2, lossFreeGate2, biasedWinner2,
    fixtureScore, rightSelectionBias
  ]

#print axioms biasStep_underloaded
#print axioms biasStep_overloaded
#print axioms meanBiasStep2_gap_of_right_lt_left
#print axioms reversedMeanBiasStep2_gap_of_right_lt_left
#print axioms runHistorical_prefix_causal
#print axioms capacityOneSelectsFirst_not_prefix_causal
#print axioms fixture_loss_free_weight_remains_unbiased
#print axioms fixture_contaminated_weight_differs

end

end LossFreeExpertBalancing

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
