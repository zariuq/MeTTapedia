import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ModernHopfieldRetrieval
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RouterPerturbation
import Mettapedia.MachineLearning.ContinualLearning.PathNet
import Mettapedia.MachineLearning.ContinualLearning.OnlineLowRankConsolidation
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.Accounting
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.CommonAncestorIndependence

/-!
# Virtually addressed parameter memory

This file isolates the mathematical boundary between immutable parameter
storage and mutable content addressing.  It is tailored to VAMP's deployed
semantics while reusing the existing MeTTapedia theories of finite softmax
retrieval, router perturbation, frozen paths, low-rank consolidation, lineage
DAGs, and projection-aware evidence accounting.

The central distinctions are:

* a positive inverse temperature changes softmax probabilities but cannot
  change a hard score winner;
* appending an immutable candidate preserves old scores and paths but can
  change both normalized soft weights and the hard winner;
* availability of a stored address is weaker than resource-bounded
  findability; and
* functional routing is a relation between inputs and competent memories,
  not merely equality with a designated task node.

Every positive guarantee is paired with an executable boundary.  No theorem
identifies router entropy with a calibrated correctness probability.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace VirtuallyAddressedParameterMemory

open Mettapedia.MachineLearning.NeuralNetworks.Architecture
open Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
open Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.RouterPerturbation
open Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.ModernHopfieldRetrieval
open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
open Mettapedia.MachineLearning.ContinualLearning.OnlineLowRankConsolidation

noncomputable section

/-! ## Storage invariance is not addressing invariance -/

/-- A state transition retains stored competence for an evaluator when every
input receives exactly the same stored output before and after the transition.
This definition deliberately says nothing about which state a router selects. -/
def StorageInvariant
    {State Input Output : Type*}
    (evaluate : State → Input → Output) (before after : State) : Prop :=
  ∀ input, evaluate after input = evaluate before input

/-- Existing frozen-path retention instantiates the generic storage boundary
for arbitrary, possibly nonlinear path evaluators. -/
theorem pathNet_frozen_path_storageInvariant
    {Layer ModuleIndex Input Output : Type*}
    [DecidableEq ModuleIndex]
    (evaluator : (Layer → ModuleIndex → ℝ) → Input → Output)
    (state : PathNet.State Layer ModuleIndex)
    (source frozen : PathNet.Path Layer ModuleIndex)
    (updates : List (PathNet.LaterUpdate Layer ModuleIndex))
    (sourceFrozen : ∀ layer, source layer ⊆ frozen layer) :
    StorageInvariant
      (fun current input ↦
        PathNet.evaluatePath evaluator current source input)
      state (PathNet.runLaterUpdates frozen state updates) := by
  intro input
  exact PathNet.evaluatePath_runLaterUpdates_of_subset_frozen
    evaluator state source frozen updates sourceFrozen input

/-- Existing low-rank merge-and-reset retention supplies a second,
architecturally different instance of the same storage boundary. -/
theorem lowRank_consolidation_storageInvariant
    {Output Input : Type*} {rankBudget : ℕ}
    [Fintype Input]
    (state : OnlineLowRankState Output Input rankBudget)
    (newScale : ℝ)
    (newDown : Matrix (Fin rankBudget) Input ℝ) :
    StorageInvariant
      (fun current input ↦ current.effectiveWeight.mulVec input)
      state (state.consolidateAndReset newScale newDown) := by
  intro input
  exact state.mulVec_consolidateAndReset newScale newDown input

/-! ## Hard and soft addressing are distinct semantics -/

variable {Key : Type*}

/-- Positive score scaling preserves the complete winner relation, including
ties.  This is the exact-real core of hard-router temperature invariance. -/
theorem isWinner_mul_pos_iff
    (score : Key → ℝ) (winner : Key) {β : ℝ} (β_pos : 0 < β) :
    IsWinner score winner ↔
      IsWinner (fun key ↦ β * score key) winner := by
  constructor
  · intro wins key
    exact mul_le_mul_of_nonneg_left (wins key) β_pos.le
  · intro scaledWins key
    have scaled := scaledWins key
    nlinarith

/-- Any two positive inverse temperatures induce the same hard-winner
relation.  Temperature can still change the corresponding soft read. -/
theorem hardWinner_positive_temperature_independent
    (score : Key → ℝ) (winner : Key)
    {β γ : ℝ} (β_pos : 0 < β) (γ_pos : 0 < γ) :
    IsWinner (fun key ↦ β * score key) winner ↔
      IsWinner (fun key ↦ γ * score key) winner := by
  rw [← isWinner_mul_pos_iff score winner β_pos,
    ← isWinner_mul_pos_iff score winner γ_pos]

/-- Pairwise score order, and hence every order-defined top-k set, is
unchanged by positive inverse-temperature scaling. -/
theorem pairwise_order_positive_temperature_independent
    (score : Key → ℝ) (left right : Key)
    {β : ℝ} (β_pos : 0 < β) :
    β * score left ≤ β * score right ↔ score left ≤ score right := by
  constructor <;> intro comparison <;> nlinarith

/-- A score family extended by one fresh candidate. -/
def extendScore (score : Key → ℝ) (freshScore : ℝ) : Key ⊕ Unit → ℝ
  | .inl key => score key
  | .inr _ => freshScore

/-- An old hard winner survives candidate insertion exactly when the fresh
candidate does not beat it. -/
theorem oldWinner_survives_extension_iff
    (score : Key → ℝ) (freshScore : ℝ) (winner : Key) :
    IsWinner (extendScore score freshScore) (.inl winner) ↔
      IsWinner score winner ∧ freshScore ≤ score winner := by
  constructor
  · intro wins
    constructor
    · intro key
      simpa [extendScore] using wins (.inl key)
    · simpa [extendScore] using wins (.inr ())
  · rintro ⟨oldWins, freshBound⟩ candidate
    cases candidate with
    | inl key => simpa [extendScore] using oldWins key
    | inr _unit => simpa [extendScore] using freshBound

/-- The old candidate's normalized weight after appending one fresh score,
written using the canonical attention mass. -/
def appendedOldWeight [Fintype Key]
    (score : Key → ℝ) (freshScore : ℝ) (key : Key) : ℝ :=
  Real.exp (score key) /
    (attentionMass score + Real.exp freshScore)

theorem attentionMass_extendScore [Fintype Key]
    (score : Key → ℝ) (freshScore : ℝ) :
    attentionMass (extendScore score freshScore) =
      attentionMass score + Real.exp freshScore := by
  classical
  simp [attentionMass, extendScore]

theorem attentionWeight_extendScore_inl [Fintype Key]
    (score : Key → ℝ) (freshScore : ℝ) (key : Key) :
    attentionWeight (extendScore score freshScore) (.inl key) =
      appendedOldWeight score freshScore key := by
  simp [attentionWeight, appendedOldWeight, attentionMass_extendScore,
    extendScore]

/-- Appending any finite-score candidate strictly dilutes every old softmax
weight, even when the old hard winner survives. -/
theorem appendedOldWeight_strictly_decreases
    [Fintype Key] [Nonempty Key]
    (score : Key → ℝ) (freshScore : ℝ) (key : Key) :
    appendedOldWeight score freshScore key < attentionWeight score key := by
  have oldMass_pos : 0 < attentionMass score := attentionMass_pos score
  have freshMass_pos : 0 < Real.exp freshScore := Real.exp_pos freshScore
  rw [appendedOldWeight, attentionWeight,
    div_lt_div_iff₀ (add_pos oldMass_pos freshMass_pos) oldMass_pos]
  have product_pos :
      0 < Real.exp (score key) * Real.exp freshScore :=
    mul_pos (Real.exp_pos _) freshMass_pos
  nlinarith

/-- The strict dilution theorem expressed directly on the extended softmax
row. -/
theorem oldAttentionWeight_strictly_decreases_after_extension
    [Fintype Key] [Nonempty Key]
    (score : Key → ℝ) (freshScore : ℝ) (key : Key) :
    attentionWeight (extendScore score freshScore) (.inl key) <
      attentionWeight score key := by
  rw [attentionWeight_extendScore_inl]
  exact appendedOldWeight_strictly_decreases score freshScore key

/-! ### Executable hard/soft boundaries -/

def singletonScore (_ : Unit) : ℝ := 0

/-- A newly appended higher score reroutes the hard decision even though the
old score is definitionally unchanged. -/
theorem fresh_candidate_can_displace_immutable_old_winner :
    IsWinner singletonScore () ∧
      ¬ IsWinner (extendScore singletonScore 1) (.inl ()) ∧
      IsWinner (extendScore singletonScore 1) (.inr ()) := by
  constructor
  · intro key
    cases key
    rfl
  constructor
  · intro oldWins
    have := oldWins (.inr ())
    norm_num [extendScore, singletonScore] at this
  · intro candidate
    cases candidate <;> norm_num [extendScore, singletonScore]

/-- Equal scores witness a second boundary: a hard winner exists while the
soft Hopfield read is not that winner's stored value. -/
theorem hard_winner_and_soft_read_can_disagree :
    IsWinner collisionScores 0 ∧
      modernHopfieldRead 1 collisionScores collisionValues ≠
        collisionValues 0 := by
  constructor
  · intro key
    fin_cases key <;> norm_num [collisionScores]
  · exact equal_score_collision_returns_average.2.1

/-- A soft address can be rounded to a hard target with controlled scalar
readout error when its off-target mass and value diameter are controlled.
This is the reusable soft-to-hard license needed by relaxed EBT routing. -/
theorem abs_softRead_sub_hardValue_le
    [Fintype Key] [Nonempty Key] [DecidableEq Key]
    (β δ diameter : ℝ) (score value : Key → ℝ) (target : Key)
    (diameter_nonneg : 0 ≤ diameter)
    (massBound : offTargetMass β score target ≤ δ)
    (valueDiameter :
      ∀ key, |value key - value target| ≤ diameter) :
    |modernHopfieldRead β score value - value target| ≤
      diameter * δ := by
  rw [modernHopfieldRead_sub_target]
  calc
    |∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item ↦ β * score item) key *
          (value key - value target)| ≤
        ∑ key ∈ Finset.univ.erase target,
          |attentionWeight (fun item ↦ β * score item) key *
            (value key - value target)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ key ∈ Finset.univ.erase target,
        attentionWeight (fun item ↦ β * score item) key * diameter := by
      apply Finset.sum_le_sum
      intro key _
      rw [abs_mul, abs_of_pos (attentionWeight_pos _ key)]
      exact mul_le_mul_of_nonneg_left
        (valueDiameter key) (attentionWeight_pos _ key).le
    _ = diameter * offTargetMass β score target := by
      unfold offTargetMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key _
      ring
    _ ≤ diameter * δ :=
      mul_le_mul_of_nonneg_left massBound diameter_nonneg

/-- Without a concentration premise, rounding the equal-score soft read to
the hard target incurs unit error in the canonical collision fixture. -/
theorem soft_to_hard_rounding_without_concentration_has_unit_error :
    |modernHopfieldRead 1 collisionScores collisionValues -
        collisionValues 0| = 1 := by
  simp [modernHopfieldRead, collisionScores, collisionValues,
    attentionWeight, attentionMass, Fin.sum_univ_succ]
  norm_num

/-! ## Routing drift from winner disagreement -/

section RoutingLoss

variable {Sample Expert : Type*}

/-- Total routed loss over a finite sample.  Division by sample cardinality
is deliberately left to consumers so the empty-sample case stays explicit. -/
def routedLossSum [Fintype Sample]
    (loss : Sample → Expert → ℝ) (route : Sample → Expert) : ℝ :=
  ∑ sample, loss sample (route sample)

/-- The total routed-loss change is supported exactly on route disagreements. -/
theorem routedLossSum_sub_eq_sum_disagreement
    [Fintype Sample] [DecidableEq Expert]
    (loss : Sample → Expert → ℝ)
    (oldRoute newRoute : Sample → Expert) :
    routedLossSum loss newRoute - routedLossSum loss oldRoute =
      ∑ sample ∈ disagreementSet oldRoute newRoute,
        (loss sample (newRoute sample) - loss sample (oldRoute sample)) := by
  classical
  rw [routedLossSum, routedLossSum, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro sample _ sample_not_disagreement
  have sameRoute : oldRoute sample = newRoute sample := by
    simpa [disagreementSet] using sample_not_disagreement
  simp [sameRoute]

/-- If every per-sample pairwise loss gap is at most `diameter`, total routed
loss drift is at most route-disagreement count times that diameter. -/
theorem abs_routedLossSum_sub_le_disagreement
    [Fintype Sample] [DecidableEq Expert]
    (loss : Sample → Expert → ℝ)
    (oldRoute newRoute : Sample → Expert)
    (diameter : ℝ)
    (lossDiameter :
      ∀ sample left right,
        |loss sample left - loss sample right| ≤ diameter) :
    |routedLossSum loss newRoute - routedLossSum loss oldRoute| ≤
      ((disagreementSet oldRoute newRoute).card : ℝ) * diameter := by
  rw [routedLossSum_sub_eq_sum_disagreement]
  calc
    |∑ sample ∈ disagreementSet oldRoute newRoute,
        (loss sample (newRoute sample) - loss sample (oldRoute sample))| ≤
        ∑ sample ∈ disagreementSet oldRoute newRoute,
          |loss sample (newRoute sample) - loss sample (oldRoute sample)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _sample ∈ disagreementSet oldRoute newRoute, diameter := by
      apply Finset.sum_le_sum
      intro sample _
      exact lossDiameter sample (newRoute sample) (oldRoute sample)
    _ = ((disagreementSet oldRoute newRoute).card : ℝ) * diameter := by
      simp

/-- Existing near-tie control composes directly with the loss-diameter
bound.  This turns a score-margin certificate into a routed-loss certificate. -/
theorem abs_routedLossSum_sub_le_nearTie
    [Fintype Sample] [DecidableEq Expert]
    (loss : Sample → Expert → ℝ)
    {oldLogit newLogit : Expert → ℝ}
    {noise : Sample → Expert → ℝ}
    {oldRoute newRoute : Sample → Expert}
    {budget diameter : ℝ}
    (diameter_nonneg : 0 ≤ diameter)
    (lossDiameter :
      ∀ sample left right,
        |loss sample left - loss sample right| ≤ diameter)
    (close : UniformlyClose oldLogit newLogit budget)
    (oldWins :
      ∀ sample,
        IsWinner (noisyScore oldLogit (noise sample)) (oldRoute sample))
    (newWins :
      ∀ sample,
        IsWinner (noisyScore newLogit (noise sample)) (newRoute sample)) :
    |routedLossSum loss newRoute - routedLossSum loss oldRoute| ≤
      ((nearTieSet oldLogit noise oldRoute newRoute budget).card : ℝ) *
        diameter := by
  calc
    |routedLossSum loss newRoute - routedLossSum loss oldRoute| ≤
        ((disagreementSet oldRoute newRoute).card : ℝ) * diameter :=
      abs_routedLossSum_sub_le_disagreement
        loss oldRoute newRoute diameter lossDiameter
    _ ≤ ((nearTieSet oldLogit noise oldRoute newRoute budget).card : ℝ) *
        diameter := by
      apply mul_le_mul_of_nonneg_right _ diameter_nonneg
      exact_mod_cast disagreement_card_le_nearTie_card
        close oldWins newWins

end RoutingLoss

/-! ## Availability versus resource-bounded findability -/

section ResourceBoundedRecall

variable {Address : Type*}

/-- Approximate minimization on an explicitly declared candidate set. -/
def EpsilonOptimalOn
    (candidates : Set Address) (objective : Address → ℝ)
    (returned : Address) (ε : ℝ) : Prop :=
  returned ∈ candidates ∧
    ∀ candidate ∈ candidates,
      objective returned ≤ objective candidate + ε

/-- Task energy plus a charged addressing resource. -/
def penalizedEnergy
    (energy resource : Address → ℝ) (penalty : ℝ) (address : Address) : ℝ :=
  energy address + penalty * resource address

/-- Correct finite-resource recall debit.  A stored address being present in
the candidate set supplies a comparator, not a promise that raw task energy
is preserved exactly. -/
theorem epsilonOptimal_rawEnergy_le_stored_add_debit
    (candidates : Set Address)
    (energy resource : Address → ℝ)
    (penalty ε : ℝ) (returned stored : Address)
    (optimal :
      EpsilonOptimalOn candidates
        (penalizedEnergy energy resource penalty) returned ε)
    (stored_available : stored ∈ candidates) :
    energy returned ≤
      energy stored +
        penalty * (resource stored - resource returned) + ε := by
  have comparison := optimal.2 stored stored_available
  unfold penalizedEnergy at comparison
  linarith

/-- With nonnegative resource and multiplier, dropping the returned
address's nonnegative credit gives a simpler one-sided debit. -/
theorem epsilonOptimal_rawEnergy_le_stored_add_cost
    (candidates : Set Address)
    (energy resource : Address → ℝ)
    (penalty ε : ℝ) (returned stored : Address)
    (penalty_nonneg : 0 ≤ penalty)
    (resource_nonneg : ∀ address, 0 ≤ resource address)
    (optimal :
      EpsilonOptimalOn candidates
        (penalizedEnergy energy resource penalty) returned ε)
    (stored_available : stored ∈ candidates) :
    energy returned ≤
      energy stored + penalty * resource stored + ε := by
  have refined := epsilonOptimal_rawEnergy_le_stored_add_debit
    candidates energy resource penalty ε returned stored optimal
      stored_available
  have returned_cost_nonneg : 0 ≤ penalty * resource returned :=
    mul_nonneg penalty_nonneg (resource_nonneg returned)
  nlinarith

/-- Exact unpenalized global search recovers the familiar availability
guarantee as a special case. -/
theorem exact_unpenalized_recall_no_worse_than_stored
    (candidates : Set Address)
    (energy resource : Address → ℝ)
    (returned stored : Address)
    (optimal :
      EpsilonOptimalOn candidates
        (penalizedEnergy energy resource 0) returned 0)
    (stored_available : stored ∈ candidates) :
    energy returned ≤ energy stored := by
  simpa using epsilonOptimal_rawEnergy_le_stored_add_debit
    candidates energy resource 0 0 returned stored optimal stored_available

/-- As the exact penalty multiplier increases, the selected resource cost
cannot increase; raw task energy cannot improve. -/
theorem exact_regularization_path_monotone
    (candidates : Set Address)
    (energy resource : Address → ℝ)
    {penalty₁ penalty₂ : ℝ} {first second : Address}
    (penalty₁_nonneg : 0 ≤ penalty₁)
    (multiplier_strict : penalty₁ < penalty₂)
    (firstOptimal :
      EpsilonOptimalOn candidates
        (penalizedEnergy energy resource penalty₁) first 0)
    (secondOptimal :
      EpsilonOptimalOn candidates
        (penalizedEnergy energy resource penalty₂) second 0) :
    resource second ≤ resource first ∧
      energy first ≤ energy second := by
  have firstComparison := firstOptimal.2 second secondOptimal.1
  have secondComparison := secondOptimal.2 first firstOptimal.1
  unfold penalizedEnergy at firstComparison secondComparison
  have resource_antitone : resource second ≤ resource first := by
    nlinarith
  have charged_difference_nonneg :
      0 ≤ penalty₁ * (resource first - resource second) :=
    mul_nonneg penalty₁_nonneg (sub_nonneg.mpr resource_antitone)
  constructor
  · exact resource_antitone
  · nlinarith

/-! ### Executable findability boundaries -/

def omittedEnergy : Bool → ℝ
  | false => 10
  | true => 0

def zeroResource (_ : Bool) : ℝ := 0

/-- If the good stored address is absent from the candidate set, exact search
within that set gives no comparison to it. -/
theorem omitted_stored_address_has_no_recall_guarantee :
    EpsilonOptimalOn ({false} : Set Bool)
        (penalizedEnergy omittedEnergy zeroResource 0) false 0 ∧
      omittedEnergy true < omittedEnergy false := by
  constructor
  · constructor
    · simp
    · intro candidate candidate_mem
      simp at candidate_mem
      subst candidate
      norm_num [penalizedEnergy]
  · norm_num [omittedEnergy]

def penalizedFixtureEnergy : Bool → ℝ
  | false => 1
  | true => 0

def penalizedFixtureResource : Bool → ℝ
  | false => 0
  | true => 2

/-- A positive resource charge can correctly select a cheaper address whose
raw task energy is worse than the stored address's. -/
theorem addressing_cost_can_select_higher_raw_energy :
    EpsilonOptimalOn (Set.univ : Set Bool)
        (penalizedEnergy penalizedFixtureEnergy penalizedFixtureResource 1)
        false 0 ∧
      penalizedFixtureEnergy true < penalizedFixtureEnergy false := by
  constructor
  · constructor
    · simp
    · intro candidate _
      cases candidate <;>
        norm_num [penalizedEnergy, penalizedFixtureEnergy,
          penalizedFixtureResource]
  · norm_num [penalizedFixtureEnergy]

end ResourceBoundedRecall

/-! ## Relation-valued routing correctness -/

section RelationalRouting

variable {Input Node : Type*}

/-- A memory is functionally competent on an input when it lies within
`ε` of every candidate's loss.  This avoids choosing an arbitrary designated
node when several memories solve the same input. -/
def EpsilonGood
    (loss : Input → Node → ℝ) (ε : ℝ) (input : Input) (node : Node) : Prop :=
  ∀ candidate, loss input node ≤ loss input candidate + ε

/-- Equality with a designated task node implies functional success only
when that designated node is itself known to be competent. -/
theorem taskIdentity_implies_epsilonGood
    (loss : Input → Node → ℝ) (ε : ℝ)
    (taskNode route : Input → Node) (input : Input)
    (task_good : EpsilonGood loss ε input (taskNode input))
    (identity_correct : route input = taskNode input) :
    EpsilonGood loss ε input (route input) := by
  simpa [identity_correct] using task_good

/-- Best candidate inside an explicitly bounded address set. -/
def IsBestAmong [DecidableEq Node]
    (loss : Input → Node → ℝ) (input : Input)
    (candidates : Finset Node) (node : Node) : Prop :=
  node ∈ candidates ∧
    ∀ candidate ∈ candidates,
      loss input node ≤ loss input candidate

/-- Enlarging the candidate set cannot worsen the best attainable loss,
provided an exact best candidate is supplied on each finite set. -/
theorem bestLoss_antitone_under_candidate_expansion
    [DecidableEq Node]
    (loss : Input → Node → ℝ) (input : Input)
    {small large : Finset Node} {smallBest largeBest : Node}
    (subset : small ⊆ large)
    (smallOptimal : IsBestAmong loss input small smallBest)
    (largeOptimal : IsBestAmong loss input large largeBest) :
    loss input largeBest ≤ loss input smallBest :=
  largeOptimal.2 smallBest (subset smallOptimal.1)

/-- Finite competence relation used as the atomic routing-evidence space. -/
noncomputable def competenceRelation
    [DecidableEq Input] [DecidableEq Node]
    (inputs : Finset Input) (nodes : Finset Node)
    (loss : Input → Node → ℝ) (ε : ℝ) : Finset (Input × Node) :=
  by
    classical
    exact (inputs.product nodes).filter fun edge ↦
      EpsilonGood loss ε edge.1 edge.2

theorem mem_competenceRelation_iff
    [DecidableEq Input] [DecidableEq Node]
    (inputs : Finset Input) (nodes : Finset Node)
    (loss : Input → Node → ℝ) (ε : ℝ)
    (input : Input) (node : Node) :
    (input, node) ∈ competenceRelation inputs nodes loss ε ↔
      input ∈ inputs ∧ node ∈ nodes ∧ EpsilonGood loss ε input node := by
  classical
  simp [competenceRelation, and_assoc]

/-- The one-address-per-input relation selected by a deterministic router. -/
def selectedRelation
    [DecidableEq Input] [DecidableEq Node]
    (inputs : Finset Input) (route : Input → Node) :
    Finset (Input × Node) :=
  inputs.image fun input ↦ (input, route input)

/-- Competent facts that are both available and actually selected. -/
def accessibleCompetence
    [DecidableEq Input] [DecidableEq Node]
    (inputs : Finset Input) (route : Input → Node)
    (available : Finset (Input × Node)) : Finset (Input × Node) :=
  selectedRelation inputs route ∩ available

/-- Inputs with at least one competent memory somewhere in storage. -/
def availableInputs
    [DecidableEq Input] [DecidableEq Node]
    (available : Finset (Input × Node)) : Finset Input :=
  projectedSet Prod.fst available

/-- Inputs whose selected memory is competent. -/
def accessibleInputs
    [DecidableEq Input] [DecidableEq Node]
    (inputs : Finset Input) (route : Input → Node)
    (available : Finset (Input × Node)) : Finset Input :=
  projectedSet Prod.fst (accessibleCompetence inputs route available)

/-- Accessibility is bounded by availability.  This is the common theorem
behind VAMP routing failures and collateral program discovery. -/
theorem accessibleInputs_subset_availableInputs
    [DecidableEq Input] [DecidableEq Node]
    (inputs : Finset Input) (route : Input → Node)
    (available : Finset (Input × Node)) :
    accessibleInputs inputs route available ⊆ availableInputs available := by
  apply projectedSet_mono
  exact Finset.inter_subset_right

/-- Transpose input-memory competence into the canonical witness-target
orientation used by the existing program-discovery accounting theory. -/
def transposeCompetence
    [DecidableEq Input] [DecidableEq Node]
    (available : Finset (Input × Node)) : SolveRelation Node Input :=
  available.image Prod.swap

/-- The available-input projection is exactly target coverage after
transposing memories into witnesses and inputs into targets. -/
theorem targetSet_transposeCompetence_eq_availableInputs
    [DecidableEq Input] [DecidableEq Node]
    (available : Finset (Input × Node)) :
    targetSet (transposeCompetence available) = availableInputs available := by
  ext input
  simp only [targetSet, transposeCompetence, availableInputs, projectedSet,
    Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨original, original_mem, swapped⟩, edge_target⟩
    subst edge
    exact ⟨original, original_mem, by simpa using edge_target⟩
  · rintro ⟨edge, edge_mem, edge_input⟩
    refine ⟨edge.swap, ?_, ?_⟩
    · exact ⟨edge, edge_mem, rfl⟩
    · simpa using edge_input

/-- Leave-one-memory coverage has the exact decomposition already proved for
program-target relations: retained input coverage plus the memory's exclusive
input contribution equals original available coverage. -/
theorem leaveOneMemory_exact_coverage_decomposition
    [DecidableEq Input] [DecidableEq Node]
    (available : Finset (Input × Node)) (memory : Node) :
    targetCoverage
        (withoutProgram (transposeCompetence available) memory) +
      exclusiveTargetContribution (transposeCompetence available) memory =
        targetCoverage (transposeCompetence available) :=
  targetCoverage_withoutProgram_add_exclusive
    (transposeCompetence available) memory

/-- A memory's exclusive coverage contribution is no greater than the number
of inputs it can solve.  Equality means all of those facts lack a redundant
memory witness; strict inequality records robustness through alternatives. -/
theorem exclusiveMemoryContribution_le_competenceDegree
    [DecidableEq Input] [DecidableEq Node]
    (available : Finset (Input × Node)) (memory : Node) :
    exclusiveTargetContribution (transposeCompetence available) memory ≤
      programTargetDegree (transposeCompetence available) memory :=
  exclusiveTargetContribution_le_programTargetDegree
    (transposeCompetence available) memory

/-- Two distinct input-node facts that share a node collide after projection
to node identity.  Existing WM-PLN projected accounting therefore requires
overlap correction at the projected identity. -/
theorem nodeProjection_not_disjoint_of_shared_node
    [DecidableEq Input] [DecidableEq Node]
    {left right : Finset (Input × Node)}
    {leftInput rightInput : Input} {node : Node}
    (left_mem : (leftInput, node) ∈ left)
    (right_mem : (rightInput, node) ∈ right) :
    ¬ Disjoint
        (projectedSet Prod.snd left)
        (projectedSet Prod.snd right) := by
  exact projected_not_disjoint_of_collision
    Prod.snd left_mem right_mem rfl

/-- Samples on which routing returns the designated task node. -/
def taskIdentitySuccessSet
    {Sample : Type*} [DecidableEq Sample] [DecidableEq Node]
    (samples : Finset Sample)
    (taskNode route : Sample → Node) : Finset Sample :=
  samples.filter fun sample ↦ route sample = taskNode sample

/-- Samples on which routing returns any functionally competent node. -/
noncomputable def functionalSuccessSet
    {Sample : Type*} [DecidableEq Sample]
    (samples : Finset Sample)
    (loss : Sample → Node → ℝ) (ε : ℝ)
    (route : Sample → Node) : Finset Sample := by
  classical
  exact samples.filter fun sample ↦
    EpsilonGood loss ε sample (route sample)

/-- If every designated task node is competent, exact task identity is a
subset of relational functional success. -/
theorem taskIdentitySuccessSet_subset_functionalSuccessSet
    {Sample : Type*} [DecidableEq Sample] [DecidableEq Node]
    (samples : Finset Sample)
    (loss : Sample → Node → ℝ) (ε : ℝ)
    (taskNode route : Sample → Node)
    (task_good :
      ∀ sample ∈ samples,
        EpsilonGood loss ε sample (taskNode sample)) :
    taskIdentitySuccessSet samples taskNode route ⊆
      functionalSuccessSet samples loss ε route := by
  classical
  intro sample sample_mem
  rcases Finset.mem_filter.mp sample_mem with
    ⟨in_samples, identity_correct⟩
  exact Finset.mem_filter.mpr
    ⟨in_samples,
      taskIdentity_implies_epsilonGood
        loss ε taskNode route sample
        (task_good sample in_samples) identity_correct⟩

/-- Cardinal form of the task-identity lower bound on functional success. -/
theorem taskIdentitySuccessCount_le_functionalSuccessCount
    {Sample : Type*} [DecidableEq Sample] [DecidableEq Node]
    (samples : Finset Sample)
    (loss : Sample → Node → ℝ) (ε : ℝ)
    (taskNode route : Sample → Node)
    (task_good :
      ∀ sample ∈ samples,
        EpsilonGood loss ε sample (taskNode sample)) :
    (taskIdentitySuccessSet samples taskNode route).card ≤
      (functionalSuccessSet samples loss ε route).card :=
  Finset.card_le_card
    (taskIdentitySuccessSet_subset_functionalSuccessSet
      samples loss ε taskNode route task_good)

/-- A fixed router score vector observed without the competence relation. -/
def fixedRouterObservation (_world : Bool) : Fin 2 → ℝ := ![1, 0]

/-- Router scores, and therefore every deterministic entropy or margin
summary of those scores, do not identify which node is functionally correct.
Calibration needs outcome-labelled evidence in addition to router telemetry. -/
theorem routerScores_alone_do_not_identify_correctness :
    ¬ ∃ recover : (Fin 2 → ℝ) → Bool,
      ∀ world : Bool, recover (fixedRouterObservation world) = world := by
  apply no_uniform_recovery_of_observation_collision
    fixedRouterObservation id (left := false) (right := true)
  · rfl
  · decide

/-! ### Executable relational boundaries -/

def tiedNodeLoss (_ : Unit) (_ : Bool) : ℝ := 0

/-- Functional routing can succeed through a node different from the
designated task node when competence is many-to-many. -/
theorem functional_success_can_strictly_exceed_task_identity :
    EpsilonGood tiedNodeLoss 0 () true ∧
      true ≠ (false : Bool) := by
  constructor
  · intro candidate
    cases candidate <;> norm_num [tiedNodeLoss]
  · decide

def misleadingTaskLoss (_ : Unit) : Bool → ℝ
  | false => 1
  | true => 0

/-- Conversely, exact agreement with a designated node says nothing about
functional optimality unless that node has a competence certificate. -/
theorem task_identity_without_competence_can_mislead :
    (fun _ : Unit ↦ false) () = (fun _ : Unit ↦ false) () ∧
      ¬ EpsilonGood misleadingTaskLoss 0 () false := by
  constructor
  · rfl
  · intro good
    have := good true
    norm_num [misleadingTaskLoss] at this

def twoByTwoAvailable : Finset (Bool × Bool) :=
  {(false, false), (true, true)}

def misaddressedRoute (_ : Bool) : Bool := false

/-- Strict availability/findability boundary: both inputs have a competent
memory, but the router exposes competence for only one of them. -/
theorem accessibility_can_be_strictly_less_than_availability :
    (availableInputs twoByTwoAvailable).card = 2 ∧
      (accessibleInputs {false, true} misaddressedRoute
        twoByTwoAvailable).card = 1 := by
  decide +kernel

end RelationalRouting

/-! ## The implemented graph is a single-parent lineage DAG -/

section GraphSemantics

universe uN uW uL

/-- A rooted arborescence is the single-parent restriction of MeTTapedia's
existing provenance-aware lineage DAG.  The current VAMP node schema has
exactly this shape. -/
structure RootedMemoryArborescence
    (Node : Type uN) (World : Type uW) (Lineage : Type uL)
    [DecidableEq Node] where
  graph : LineageDAG Node World Lineage
  root : Node
  root_parentless : (graph.node root).parents = ∅
  parent_exists :
    ∀ node, node ≠ root → (graph.node node).parents.Nonempty
  parent_unique :
    ∀ node left right,
      left ∈ (graph.node node).parents →
      right ∈ (graph.node node).parents →
      left = right

namespace RootedMemoryArborescence

variable {Node : Type uN} {World : Type uW} {Lineage : Type uL}
variable [DecidableEq Node]

/-- The single-parent schema cannot directly represent a genuine
multi-parent node. -/
theorem distinct_parents_impossible
    (tree : RootedMemoryArborescence Node World Lineage)
    {node left right : Node} (distinct : left ≠ right) :
    ¬ (tree.graph.ParentOf left node ∧
      tree.graph.ParentOf right node) := by
  rintro ⟨leftParent, rightParent⟩
  exact distinct (tree.parent_unique node left right leftParent rightParent)

/-- Acyclicity is inherited from the existing generation-ranked lineage DAG,
not stored as a fresh axiom. -/
theorem not_ancestor_self
    (tree : RootedMemoryArborescence Node World Lineage)
    (node : Node) : ¬ tree.graph.AncestorOf node node :=
  tree.graph.not_ancestor_self node

end RootedMemoryArborescence

end GraphSemantics

#print axioms isWinner_mul_pos_iff
#print axioms hardWinner_positive_temperature_independent
#print axioms pathNet_frozen_path_storageInvariant
#print axioms lowRank_consolidation_storageInvariant
#print axioms oldWinner_survives_extension_iff
#print axioms oldAttentionWeight_strictly_decreases_after_extension
#print axioms fresh_candidate_can_displace_immutable_old_winner
#print axioms hard_winner_and_soft_read_can_disagree
#print axioms abs_softRead_sub_hardValue_le
#print axioms soft_to_hard_rounding_without_concentration_has_unit_error
#print axioms abs_routedLossSum_sub_le_nearTie
#print axioms epsilonOptimal_rawEnergy_le_stored_add_debit
#print axioms exact_regularization_path_monotone
#print axioms omitted_stored_address_has_no_recall_guarantee
#print axioms addressing_cost_can_select_higher_raw_energy
#print axioms taskIdentity_implies_epsilonGood
#print axioms bestLoss_antitone_under_candidate_expansion
#print axioms accessibleInputs_subset_availableInputs
#print axioms targetSet_transposeCompetence_eq_availableInputs
#print axioms leaveOneMemory_exact_coverage_decomposition
#print axioms exclusiveMemoryContribution_le_competenceDegree
#print axioms nodeProjection_not_disjoint_of_shared_node
#print axioms taskIdentitySuccessCount_le_functionalSuccessCount
#print axioms routerScores_alone_do_not_identify_correctness
#print axioms functional_success_can_strictly_exceed_task_identity
#print axioms task_identity_without_competence_can_mislead
#print axioms accessibility_can_be_strictly_less_than_availability
#print axioms RootedMemoryArborescence.distinct_parents_impossible
#print axioms RootedMemoryArborescence.not_ancestor_self

end

end VirtuallyAddressedParameterMemory

end Mettapedia.MachineLearning.ContinualLearning
