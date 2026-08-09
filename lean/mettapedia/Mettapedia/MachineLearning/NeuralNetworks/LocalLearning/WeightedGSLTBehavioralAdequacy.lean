import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLT

/-!
# Behavioral adequacy of weighted-GSLT local learning

This module separates three questions that are easy to conflate:

* whether a behavior is representable by an admissible weight map;
* what information a local update rule retains from an event history; and
* whether every history admitted by a training protocol ends in a solving map.

The shipped saturating-add rule depends only on per-key firing counts.  A
two-choice task with equal exposure but asymmetric local reward is therefore a
negative example: the task is representable, but the shipped rule leaves the
choice probabilities equal.  A reward-sensitive local update is a positive
control.  Its activity and weight changes are projections of one integrated
transition, so the control does not introduce a separate training relation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTBehavioralAdequacy

open WeightedGSLT

abbrev WeightMap (Key : Type*) := Key → ℝ

/-- A behavioral task evaluates a weight map through an observable output.
Admissibility is kept separate from success so representability cannot be
witnessed by an illegal map. -/
structure BehavioralTask (Key Output : Type*) where
  admissible : WeightMap Key → Prop
  evaluate : WeightMap Key → Output
  accepts : Output → Prop

def BehavioralTask.Solves {Key Output : Type*}
    (task : BehavioralTask Key Output) (weights : WeightMap Key) : Prop :=
  task.accepts (task.evaluate weights)

/-- The architecture represents a task when an admissible weight map realizes
an accepted behavior. -/
def Representable {Key Output : Type*} (task : BehavioralTask Key Output) : Prop :=
  ∃ weights : WeightMap Key, task.admissible weights ∧ task.Solves weights

/-- Reliability on an explicit training protocol means that every admitted
event history yields accepted behavior.  For a stochastic protocol this is a
support-wise certificate, hence stronger than probability-one success. -/
def ReliablyLearnsOn {Key Event Output : Type*}
    (task : BehavioralTask Key Output)
    (protocol : List Event → Prop)
    (learner : List Event → WeightMap Key) : Prop :=
  ∀ episode, protocol episode → task.Solves (learner episode)

/-- One local communication event.  `rewarded` is a local third factor carried
by the same event; it is not an outer optimization step. -/
structure LocalEvent (Key : Type*) where
  key : Key
  rewarded : Bool
deriving DecidableEq

def fireCount {Key : Type*} [DecidableEq Key]
    (episode : List (LocalEvent Key)) (key : Key) : ℕ :=
  (episode.map LocalEvent.key).count key

def rewardedKeys {Key : Type*} : List (LocalEvent Key) → List Key
  | [] => []
  | event :: rest =>
      if event.rewarded = true then event.key :: rewardedKeys rest
      else rewardedKeys rest

def rewardedCount {Key : Type*} [DecidableEq Key]
    (episode : List (LocalEvent Key)) (key : Key) : ℕ :=
  (rewardedKeys episode).count key

/-! ## Integrated local transitions -/

/-- The activity marginal records which local communications occurred; the
weight marginal records plasticity. -/
structure IntegratedState (Key : Type*) where
  activity : Key → ℕ
  weights : WeightMap Key

def initialState {Key : Type*} (weights : WeightMap Key) : IntegratedState Key where
  activity := fun _ => 0
  weights := weights

/-- The shipped rule: every communication increments activity and potentiates
the weight of exactly the fired key. -/
noncomputable def shippedStep {Key : Type*} [DecidableEq Key]
    (eta ceiling : ℝ) (state : IntegratedState Key) (event : LocalEvent Key) :
    IntegratedState Key where
  activity := fun key =>
    if event.key = key then state.activity key + 1 else state.activity key
  weights := fun key =>
    if event.key = key then min ceiling (state.weights key + eta)
    else state.weights key

/-- Local reward-sensitive potentiation.  Communication always changes the
activity marginal, while the same integrated step changes the weight marginal
only when its local reward bit is present. -/
noncomputable def rewardSensitiveStep {Key : Type*} [DecidableEq Key]
    (eta ceiling : ℝ) (state : IntegratedState Key) (event : LocalEvent Key) :
    IntegratedState Key where
  activity := fun key =>
    if event.key = key then state.activity key + 1 else state.activity key
  weights := fun key =>
    if event.rewarded = true ∧ event.key = key then
      min ceiling (state.weights key + eta)
    else state.weights key

/-- Event histories are stored newest first.  Folding the tail before the head
therefore executes them chronologically. -/
noncomputable def runShipped {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ) :
    List (LocalEvent Key) → IntegratedState Key
  | [] => initialState initial
  | event :: rest => shippedStep eta ceiling (runShipped initial eta ceiling rest) event

/-- Integrated execution of reward-sensitive local events. -/
noncomputable def runRewardSensitive {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ) :
    List (LocalEvent Key) → IntegratedState Key
  | [] => initialState initial
  | event :: rest =>
      rewardSensitiveStep eta ceiling (runRewardSensitive initial eta ceiling rest) event

/-! ## Exact count semantics -/

noncomputable def shippedAfter {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (episode : List (LocalEvent Key)) : WeightMap Key :=
  fun key => saturatingWeight (initial key) eta ceiling (fireCount episode key)

noncomputable def rewardSensitiveAfter {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (episode : List (LocalEvent Key)) : WeightMap Key :=
  fun key => saturatingWeight (initial key) eta ceiling (rewardedCount episode key)

theorem runShipped_activity {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (episode : List (LocalEvent Key)) (key : Key) :
    (runShipped initial eta ceiling episode).activity key = fireCount episode key := by
  induction episode with
  | nil => simp [runShipped, initialState, fireCount]
  | cons event rest ih =>
      by_cases hkey : event.key = key
      · simp [runShipped, shippedStep, fireCount, hkey, ih]
      · simp [runShipped, shippedStep, fireCount, hkey, ih]

theorem runRewardSensitive_activity {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (episode : List (LocalEvent Key)) (key : Key) :
    (runRewardSensitive initial eta ceiling episode).activity key = fireCount episode key := by
  induction episode with
  | nil => simp [runRewardSensitive, initialState, fireCount]
  | cons event rest ih =>
      by_cases hkey : event.key = key
      · simp [runRewardSensitive, rewardSensitiveStep, fireCount, hkey, ih]
      · simp [runRewardSensitive, rewardSensitiveStep, fireCount, hkey, ih]

theorem runShipped_weights {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (hη : 0 ≤ eta) (hinitial : ∀ key, initial key ≤ ceiling)
    (episode : List (LocalEvent Key)) (key : Key) :
    (runShipped initial eta ceiling episode).weights key =
      shippedAfter initial eta ceiling episode key := by
  induction episode with
  | nil =>
      simp [runShipped, initialState, shippedAfter, fireCount,
        saturatingWeight_zero, hinitial key]
  | cons event rest ih =>
      by_cases hkey : event.key = key
      · simp [runShipped, shippedStep, shippedAfter, fireCount, hkey, ih,
          saturatingWeight_succ, hη]
      · simp [runShipped, shippedStep, shippedAfter, fireCount, hkey, ih]

theorem runRewardSensitive_weights {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (hη : 0 ≤ eta) (hinitial : ∀ key, initial key ≤ ceiling)
    (episode : List (LocalEvent Key)) (key : Key) :
    (runRewardSensitive initial eta ceiling episode).weights key =
      rewardSensitiveAfter initial eta ceiling episode key := by
  induction episode with
  | nil =>
      simp [runRewardSensitive, initialState, rewardSensitiveAfter, rewardedCount,
        rewardedKeys, saturatingWeight_zero, hinitial key]
  | cons event rest ih =>
      cases hre : event.rewarded with
      | false =>
          simp [runRewardSensitive, rewardSensitiveStep, rewardSensitiveAfter,
            rewardedCount, rewardedKeys, hre, ih]
      | true =>
          by_cases hkey : event.key = key
          · simp [runRewardSensitive, rewardSensitiveStep, rewardSensitiveAfter,
              rewardedCount, rewardedKeys, hre, hkey, ih,
              saturatingWeight_succ, hη]
          · simp [runRewardSensitive, rewardSensitiveStep, rewardSensitiveAfter,
              rewardedCount, rewardedKeys, hre, hkey, ih]

/-- The shipped learner retains exactly the per-key firing counts needed by
its closed form. -/
theorem shippedAfter_eq_of_fireCount_eq {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (first second : List (LocalEvent Key))
    (hcounts : ∀ key, fireCount first key = fireCount second key) :
    shippedAfter initial eta ceiling first = shippedAfter initial eta ceiling second := by
  funext key
  simp only [shippedAfter]
  rw [hcounts key]

/-- Reward annotations are invisible to the shipped rule whenever the event
keys, and hence their firing counts, agree. -/
theorem shippedAfter_ignores_reward_annotations {Key : Type*} [DecidableEq Key]
    (initial : WeightMap Key) (eta ceiling : ℝ)
    (first second : List (LocalEvent Key))
    (hkeys : first.map LocalEvent.key = second.map LocalEvent.key) :
    shippedAfter initial eta ceiling first = shippedAfter initial eta ceiling second := by
  apply shippedAfter_eq_of_fireCount_eq initial eta ceiling first second
  intro key
  simp only [fireCount]
  rw [hkeys]

/-! ## Rewarded two-choice canary -/

inductive ChoiceSynapse where
  | target
  | distractor
deriving DecidableEq, Fintype

@[simp]
theorem ChoiceSynapse.target_ne_distractor :
    ChoiceSynapse.target ≠ ChoiceSynapse.distractor := by
  intro h
  cases h

@[simp]
theorem ChoiceSynapse.distractor_ne_target :
    ChoiceSynapse.distractor ≠ ChoiceSynapse.target := by
  intro h
  cases h

def uniformChoiceWeights : WeightMap ChoiceSynapse := fun _ => 1

def choiceWitness : WeightMap ChoiceSynapse
  | .target => 3
  | .distractor => 1

noncomputable def targetChoiceProbability (weights : WeightMap ChoiceSynapse) : ℝ :=
  weights .target / (weights .target + weights .distractor)

def choiceAdmissible (weights : WeightMap ChoiceSynapse) : Prop :=
  ∀ key, 0 ≤ weights key ∧ weights key ≤ 4

noncomputable def rewardedChoiceTask : BehavioralTask ChoiceSynapse ℝ where
  admissible := choiceAdmissible
  evaluate := targetChoiceProbability
  accepts := fun probability => (3 / 4 : ℝ) ≤ probability

theorem rewardedChoice_representable : Representable rewardedChoiceTask := by
  refine ⟨choiceWitness, ?_, ?_⟩
  · intro key
    cases key <;> norm_num [choiceWitness]
  · norm_num [BehavioralTask.Solves, rewardedChoiceTask,
      targetChoiceProbability, choiceWitness]

/-- Both synapses carry equal traffic, while only the target traffic carries
the local reward bit. -/
def rewardedChoiceProtocol (episode : List (LocalEvent ChoiceSynapse)) : Prop :=
  fireCount episode .target = 2 ∧
  fireCount episode .distractor = 2 ∧
  rewardedCount episode .target = 2 ∧
  rewardedCount episode .distractor = 0

def rewardedChoiceEpisode : List (LocalEvent ChoiceSynapse) :=
  [ { key := .distractor, rewarded := false }
  , { key := .target, rewarded := true }
  , { key := .distractor, rewarded := false }
  , { key := .target, rewarded := true } ]

theorem rewardedChoiceEpisode_satisfies_protocol :
    rewardedChoiceProtocol rewardedChoiceEpisode := by
  norm_num [rewardedChoiceProtocol, rewardedChoiceEpisode, fireCount,
    rewardedCount, rewardedKeys, List.count_cons]

noncomputable def shippedChoiceLearner
    (episode : List (LocalEvent ChoiceSynapse)) : WeightMap ChoiceSynapse :=
  shippedAfter uniformChoiceWeights 1 4 episode

noncomputable def rewardSensitiveChoiceLearner
    (episode : List (LocalEvent ChoiceSynapse)) : WeightMap ChoiceSynapse :=
  rewardSensitiveAfter uniformChoiceWeights 1 4 episode

theorem shippedChoiceLearner_is_integrated_run
    (episode : List (LocalEvent ChoiceSynapse)) :
    shippedChoiceLearner episode = (runShipped uniformChoiceWeights 1 4 episode).weights := by
  funext key
  exact (runShipped_weights uniformChoiceWeights 1 4 (by norm_num)
    (by intro choice; norm_num [uniformChoiceWeights]) episode key).symm

theorem rewardSensitiveChoiceLearner_is_integrated_run
    (episode : List (LocalEvent ChoiceSynapse)) :
    rewardSensitiveChoiceLearner episode =
      (runRewardSensitive uniformChoiceWeights 1 4 episode).weights := by
  funext key
  exact (runRewardSensitive_weights uniformChoiceWeights 1 4 (by norm_num)
    (by intro choice; norm_num [uniformChoiceWeights]) episode key).symm

theorem shippedChoiceLearner_equal_weights_of_protocol
    (episode : List (LocalEvent ChoiceSynapse))
    (hprotocol : rewardedChoiceProtocol episode) :
    shippedChoiceLearner episode .target = 3 ∧
      shippedChoiceLearner episode .distractor = 3 := by
  constructor
  · norm_num [shippedChoiceLearner, shippedAfter, uniformChoiceWeights,
      hprotocol.1, saturatingWeight, min_def]
  · norm_num [shippedChoiceLearner, shippedAfter, uniformChoiceWeights,
      hprotocol.2.1, saturatingWeight, min_def]

theorem shippedChoiceLearner_fails_of_protocol
    (episode : List (LocalEvent ChoiceSynapse))
    (hprotocol : rewardedChoiceProtocol episode) :
    ¬ rewardedChoiceTask.Solves (shippedChoiceLearner episode) := by
  rcases shippedChoiceLearner_equal_weights_of_protocol episode hprotocol with
    ⟨htarget, hdistractor⟩
  norm_num [BehavioralTask.Solves, rewardedChoiceTask, targetChoiceProbability,
    htarget, hdistractor]

/-- The task is representable, yet the shipped count-only rule is not reliable
on the equal-exposure rewarded protocol. -/
theorem shippedRule_not_reliably_learns_rewardedChoice :
    ¬ ReliablyLearnsOn rewardedChoiceTask rewardedChoiceProtocol shippedChoiceLearner := by
  intro hreliable
  exact shippedChoiceLearner_fails_of_protocol rewardedChoiceEpisode
    rewardedChoiceEpisode_satisfies_protocol
    (hreliable rewardedChoiceEpisode rewardedChoiceEpisode_satisfies_protocol)

theorem rewardSensitiveChoiceLearner_weights_of_protocol
    (episode : List (LocalEvent ChoiceSynapse))
    (hprotocol : rewardedChoiceProtocol episode) :
    rewardSensitiveChoiceLearner episode .target = 3 ∧
      rewardSensitiveChoiceLearner episode .distractor = 1 := by
  constructor
  · norm_num [rewardSensitiveChoiceLearner, rewardSensitiveAfter, uniformChoiceWeights,
      hprotocol.2.2.1, saturatingWeight, min_def]
  · norm_num [rewardSensitiveChoiceLearner, rewardSensitiveAfter, uniformChoiceWeights,
      hprotocol.2.2.2, saturatingWeight]

theorem rewardSensitiveChoiceLearner_succeeds_of_protocol
    (episode : List (LocalEvent ChoiceSynapse))
    (hprotocol : rewardedChoiceProtocol episode) :
    rewardedChoiceTask.Solves (rewardSensitiveChoiceLearner episode) := by
  rcases rewardSensitiveChoiceLearner_weights_of_protocol episode hprotocol with
    ⟨htarget, hdistractor⟩
  norm_num [BehavioralTask.Solves, rewardedChoiceTask, targetChoiceProbability,
    htarget, hdistractor]

/-- Positive control: local reward modulation reaches accepted behavior for
every ordering admitted by the same equal-exposure protocol. -/
theorem rewardSensitiveRule_reliably_learns_rewardedChoice :
    ReliablyLearnsOn rewardedChoiceTask rewardedChoiceProtocol
      rewardSensitiveChoiceLearner := by
  intro episode hprotocol
  exact rewardSensitiveChoiceLearner_succeeds_of_protocol episode hprotocol

/-! ## Positive support-learning example for the shipped rule -/

def supportProtocol (episode : List (LocalEvent ChoiceSynapse)) : Prop :=
  fireCount episode .target = 2 ∧ fireCount episode .distractor = 0

def supportEpisode : List (LocalEvent ChoiceSynapse) :=
  [ { key := .target, rewarded := false }
  , { key := .target, rewarded := false } ]

theorem supportEpisode_satisfies_protocol : supportProtocol supportEpisode := by
  norm_num [supportProtocol, supportEpisode, fireCount, List.count_cons]

theorem shippedChoiceLearner_succeeds_on_support
    (episode : List (LocalEvent ChoiceSynapse)) (hprotocol : supportProtocol episode) :
    rewardedChoiceTask.Solves (shippedChoiceLearner episode) := by
  have htarget : shippedChoiceLearner episode .target = 3 := by
    norm_num [shippedChoiceLearner, shippedAfter, uniformChoiceWeights,
      hprotocol.1, saturatingWeight, min_def]
  have hdistractor : shippedChoiceLearner episode .distractor = 1 := by
    simp [shippedChoiceLearner, shippedAfter, uniformChoiceWeights,
      hprotocol.2, saturatingWeight]
  norm_num [BehavioralTask.Solves, rewardedChoiceTask, targetChoiceProbability,
    htarget, hdistractor]

/-- Positive boundary: count-only potentiation does learn a task whose desired
behavior is aligned with firing support. -/
theorem shippedRule_reliably_learns_supportTask :
    ReliablyLearnsOn rewardedChoiceTask supportProtocol shippedChoiceLearner := by
  intro episode hprotocol
  exact shippedChoiceLearner_succeeds_on_support episode hprotocol

#print axioms rewardedChoice_representable
#print axioms runShipped_weights
#print axioms runRewardSensitive_weights
#print axioms shippedAfter_eq_of_fireCount_eq
#print axioms shippedAfter_ignores_reward_annotations
#print axioms shippedRule_not_reliably_learns_rewardedChoice
#print axioms rewardSensitiveRule_reliably_learns_rewardedChoice
#print axioms shippedRule_reliably_learns_supportTask

end WeightedGSLTBehavioralAdequacy
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
