import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.PairedDesignEstimands
import Mettapedia.MachineLearning.ContinualLearning.EvidenceLedger
import Mettapedia.PLN.Evidence.EvidentialLedger
import Mettapedia.PLN.Evidence.Convergence.IIDBernoulli
import Mettapedia.PLN.WorldModel.WorldModelOverlap
import Mathlib.Probability.Moments.Variance

/-!
# Provenance- and dependence-aware WM-PLN bridge

Discovery packets contribute count evidence in `(n⁺,n⁻)` coordinates.  A
source lineage is represented explicitly, including ancestors used for later
training.  Arithmetic aggregation and epistemic licensing are separated:
lists always have a mechanical fold, while an additive revision license also
contains a proof of source separation.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Evidence.EvidentialLedger
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WorldModelOverlap
open Mettapedia.PLN.WorldModel.Experiment.PLNWorldModelExperiment

universe uP uT uL

/-- One checker-backed positive solve packet with its transitive declared
training/source dependencies. -/
structure SourcePacket
    (Program : Type uP) (Target : Type uT) (Lineage : Type uL) where
  program : Program
  target : Target
  source : Lineage
  ancestors : Finset Lineage

namespace SourcePacket

variable {Program : Type uP} {Target : Type uT} {Lineage : Type uL}

def claim (packet : SourcePacket Program Target Lineage) : Program × Target :=
  (packet.program, packet.target)

/-- Two packets are source-disjoint only if neither source is equal to, nor a
declared ancestor of, the other. -/
def SourceDisjoint [DecidableEq Lineage]
    (left right : SourcePacket Program Target Lineage) : Prop :=
  left.source ≠ right.source ∧
    left.source ∉ right.ancestors ∧
    right.source ∉ left.ancestors

def DependsOn [DecidableEq Lineage]
    (later earlier : SourcePacket Program Target Lineage) : Prop :=
  earlier.source ∈ later.ancestors

end SourcePacket

section PacketEvidence

variable {Program : Type uP} {Target : Type uT} {Lineage : Type uL}
variable [BEq Program] [BEq Target]

/-- One accepted packet is one positive count for its exact program-target
claim and zero evidence for every other claim. -/
def packetSupport (packet : SourcePacket Program Target Lineage)
    (query : Program × Target) : BinEvNat :=
  if packet.program == query.1 && packet.target == query.2 then ⟨1, 0⟩ else 0

def packetSourceItem (packet : SourcePacket Program Target Lineage) :
    SourceItem Lineage (Program × Target) where
  source := packet.source
  kind := .empirical
  support := packetSupport packet
  note := "checker-backed program discovery"

/-- Counts-native PLN aggregation of discovery packets. -/
def aggregatePacketEvidence
    (packets : List (SourcePacket Program Target Lineage))
    (query : Program × Target) : BinEvNat :=
  aggregate (packets.map packetSourceItem) query

theorem aggregatePacketEvidence_append
    (left right : List (SourcePacket Program Target Lineage))
    (query : Program × Target) :
    aggregatePacketEvidence (left ++ right) query =
      aggregatePacketEvidence left query + aggregatePacketEvidence right query := by
  simp only [aggregatePacketEvidence, List.map_append]
  exact aggregate_append _ _ query

/-- An epistemic additive-revision license contains both the operational
source-separation reason and the counts-addition equation. -/
structure AdditiveRevisionLicense [DecidableEq Lineage]
    (left right : SourcePacket Program Target Lineage) : Prop where
  sourceDisjoint : left.SourceDisjoint right
  evidenceAdds : ∀ query,
    aggregatePacketEvidence [left, right] query =
      aggregatePacketEvidence [left] query + aggregatePacketEvidence [right] query

theorem sourceDisjoint_licenses_additiveRevision
    [DecidableEq Lineage]
    (left right : SourcePacket Program Target Lineage)
    (h : left.SourceDisjoint right) :
    AdditiveRevisionLicense left right := by
  refine ⟨h, ?_⟩
  intro query
  simpa only [List.singleton_append] using
    aggregatePacketEvidence_append [left] [right] query

noncomputable def distinctPacketSources
    (packets : List (SourcePacket Program Target Lineage))
    (query : Program × Target) : Finset Lineage := by
  classical
  exact ((packets.filter (fun packet ↦ packet.claim = query)).map
    (fun packet ↦ packet.source)).toFinset

noncomputable def distinctPacketPrograms
    (packets : List (SourcePacket Program Target Lineage))
    (target : Target) : Finset Program := by
  classical
  exact ((packets.filter (fun packet ↦ packet.target = target)).map
    (fun packet ↦ packet.program)).toFinset

end PacketEvidence

/-! ## Deterministic WM experiment view -/

section ExperimentView

variable {Program : Type uP} {Target : Type uT} {Lineage : Type uL}
variable [DecidableEq Program] [DecidableEq Target]

abbrev PLNBinaryEvidence :=
  Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence

def packetExperimentChannel :
    ExperimentChannel (SourcePacket Program Target Lineage) (Program × Target) :=
  ⟨SourcePacket.claim⟩

def packetExperimentQuery (query : Program × Target) :
    ExperimentQuery (SourcePacket Program Target Lineage) (Program × Target) :=
  queryOf packetExperimentChannel (fun observed ↦ observed = query)

noncomputable def packetExperimentEvidence
    (packets : Multiset (SourcePacket Program Target Lineage))
    (query : Program × Target) : PLNBinaryEvidence :=
  experimentEvidence packets (packetExperimentQuery query)

theorem packetExperimentEvidence_pos_eq_countP
    (packets : Multiset (SourcePacket Program Target Lineage))
    (query : Program × Target) :
    (packetExperimentEvidence packets query).pos =
      packets.countP (fun packet ↦ packet.claim = query) := by
  classical
  simp [packetExperimentEvidence, experimentEvidence, packetExperimentQuery,
    packetExperimentChannel, queryOf, queryHolds]

end ExperimentView

/-! ## Registered binary samples

`BernoulliObservations` is a valid count pair only when successes and trials
share one atomic unit.  The registered sample below makes that obligation
structural: successes are literally a subset of the declared trial set.  This
does not by itself assert IID sampling; it only makes the finite count
arithmetic well typed.
-/

structure FiniteBinarySample (Trial : Type*) where
  trials : Finset Trial
  successes : Finset Trial
  successes_subset : successes ⊆ trials

namespace FiniteBinarySample

variable {Trial : Type*}

def observations (sample : FiniteBinarySample Trial) :
    Mettapedia.PLN.Evidence.Convergence.BernoulliObservations where
  successes := sample.successes.card
  total := sample.trials.card
  successes_le := Finset.card_le_card sample.successes_subset

def evidence (sample : FiniteBinarySample Trial) : PLNBinaryEvidence :=
  Mettapedia.PLN.Evidence.Convergence.observationsToEvidence sample.observations

def merge [DecidableEq Trial]
    (left right : FiniteBinarySample Trial) : FiniteBinarySample Trial where
  trials := left.trials ∪ right.trials
  successes := left.successes ∪ right.successes
  successes_subset := Finset.union_subset_union
    left.successes_subset right.successes_subset

/-- Total-trial additivity is licensed exactly by disjoint atomic trial sets. -/
theorem merge_total_additive_iff [DecidableEq Trial]
    (left right : FiniteBinarySample Trial) :
    (merge left right).observations.total =
        left.observations.total + right.observations.total ↔
      Disjoint left.trials right.trials := by
  simpa [observations, merge] using
    (Finset.card_union_eq_card_add_card (s := left.trials) (t := right.trials))

/-- When trial identities are disjoint, merging registered samples agrees
exactly with the pre-existing Bernoulli combination operation. -/
theorem observations_merge_of_disjoint [DecidableEq Trial]
    (left right : FiniteBinarySample Trial)
    (hdisjoint : Disjoint left.trials right.trials) :
    (merge left right).observations =
      Mettapedia.PLN.Evidence.Convergence.BernoulliObservations.combine
        left.observations right.observations := by
  have hsuccess : Disjoint left.successes right.successes := by
    refine Finset.disjoint_left.mpr ?_
    intro trial hleft hright
    exact (Finset.disjoint_left.mp hdisjoint)
      (left.successes_subset hleft) (right.successes_subset hright)
  cases left with
  | mk leftTrials leftSuccesses leftSubset =>
    cases right with
    | mk rightTrials rightSuccesses rightSubset =>
      simp only [observations, merge,
        Mettapedia.PLN.Evidence.Convergence.BernoulliObservations.combine,
        Mettapedia.PLN.Evidence.Convergence.BernoulliObservations.mk.injEq]
      exact ⟨Finset.card_union_of_disjoint hsuccess,
        Finset.card_union_of_disjoint hdisjoint⟩

theorem evidence_merge_of_disjoint [DecidableEq Trial]
    (left right : FiniteBinarySample Trial)
    (hdisjoint : Disjoint left.trials right.trials) :
    (merge left right).evidence = left.evidence + right.evidence := by
  rw [evidence, evidence, evidence, observations_merge_of_disjoint left right hdisjoint]
  exact Mettapedia.PLN.Evidence.Convergence.observationsToEvidence_combine
    left.observations right.observations

end FiniteBinarySample

/-! ## Projected Gaussian evidence

The same event-space rule applies to continuous sufficient statistics.  We
reuse the Gaussian natural-parameter ledger and aggregate only once per
distinct projected identity.
-/

open Mettapedia.MachineLearning.ContinualLearning

noncomputable def aggregateProjectedGaussian
    {Atom Feature Index : Type*} [DecidableEq Feature]
    (projection : Atom → Feature) (events : Finset Atom)
    (contribution : Feature → GaussianEvidence Index) : GaussianEvidence Index :=
  aggregateDistinctGaussian (projectedSet projection events) contribution

/-- Projection overlap, rather than raw-event overlap, is the correction term
for Gaussian evidence accumulation. -/
theorem aggregateProjectedGaussian_inclusion_exclusion
    {Atom Feature Index : Type*} [DecidableEq Atom] [DecidableEq Feature]
    (projection : Atom → Feature) (left right : Finset Atom)
    (contribution : Feature → GaussianEvidence Index) :
    (aggregateProjectedGaussian projection (left ∪ right) contribution).add
        (aggregateDistinctGaussian
          (projectedSet projection left ∩ projectedSet projection right)
          contribution) =
      (aggregateProjectedGaussian projection left contribution).add
        (aggregateProjectedGaussian projection right contribution) := by
  unfold aggregateProjectedGaussian
  rw [projectedSet_union]
  exact aggregateDistinctGaussian_inclusion_exclusion
    (projectedSet projection left) (projectedSet projection right) contribution

/-! ## Capture--recapture identifiability boundary

Two capture sets reveal their sizes and overlap.  They do not reveal how many
population members were missed by both sets.  An estimator therefore needs a
sampling model (homogeneous catchability, a stratified alternative, or an
explicit lower-bound target); the overlap table alone cannot identify the
population size.
-/

namespace CaptureRecapture

structure Summary where
  first : ℕ
  second : ℕ
  overlap : ℕ
  deriving DecidableEq, Repr

structure World (Unit : Type*) where
  population : Finset Unit
  first : Finset Unit
  second : Finset Unit
  first_subset : first ⊆ population
  second_subset : second ⊆ population

variable {Unit : Type*} [DecidableEq Unit]

def summary (world : World Unit) : Summary where
  first := world.first.card
  second := world.second.card
  overlap := (world.first ∩ world.second).card

def populationSize (world : World Unit) : ℕ := world.population.card

def observedUnion (world : World Unit) : Finset Unit :=
  world.first ∪ world.second

def CompleteCapture (world : World Unit) : Prop :=
  observedUnion world = world.population

/-- Positive boundary: a complete two-list census identifies population size
without a probabilistic model. -/
theorem populationSize_eq_observedUnion_of_complete
    (world : World Unit) (hcomplete : CompleteCapture world) :
    populationSize world = (observedUnion world).card := by
  simpa [populationSize, CompleteCapture] using congrArg Finset.card hcomplete.symm

namespace Fixtures

def smallWorld : World (Fin 4) where
  population := {0, 1}
  first := {0}
  second := {0}
  first_subset := by decide
  second_subset := by decide

def hiddenWorld : World (Fin 4) where
  population := {0, 1, 2, 3}
  first := {0}
  second := {0}
  first_subset := by decide
  second_subset := by decide

/-- Negative boundary: identical capture counts and overlap are compatible
with different finite population sizes. -/
theorem summary_does_not_identify_populationSize :
    ¬ ∃ estimate : Summary → ℕ,
      ∀ world : World (Fin 4), estimate (summary world) = populationSize world := by
  apply no_uniform_recovery_of_observation_collision summary populationSize
    (left := smallWorld) (right := hiddenWorld)
  · decide +kernel
  · decide +kernel

end Fixtures
end CaptureRecapture

/-! ## Cluster-aware uncertainty

Mathlib's covariance expansion supplies the exact uncertainty law.  The IID
shortcut is a corollary requiring pairwise independence, not a default attached
to a count table.
-/

open MeasureTheory

theorem registered_sum_variance_eq_covariance_sum
    {Ω Trial : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] [DecidableEq Trial]
    (trials : Finset Trial) (X : Trial → Ω → ℝ)
    (hX : ∀ trial ∈ trials, MemLp (X trial) 2 μ) :
    _root_.ProbabilityTheory.variance (∑ trial ∈ trials, X trial) μ =
      ∑ left ∈ trials, ∑ right ∈ trials,
        _root_.ProbabilityTheory.covariance (X left) (X right) μ :=
  _root_.ProbabilityTheory.variance_sum' hX

theorem registered_sum_variance_of_pairwise_independent
    {Ω Trial : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] [DecidableEq Trial]
    (trials : Finset Trial) (X : Trial → Ω → ℝ)
    (hX : ∀ trial ∈ trials, MemLp (X trial) 2 μ)
    (hindependent : (↑trials : Set Trial).Pairwise
      (fun left right ↦ _root_.ProbabilityTheory.IndepFun (X left) (X right) μ)) :
    _root_.ProbabilityTheory.variance (∑ trial ∈ trials, X trial) μ =
      ∑ trial ∈ trials, _root_.ProbabilityTheory.variance (X trial) μ :=
  _root_.ProbabilityTheory.IndepFun.variance_sum hX hindependent

/-- Exchangeable within-cluster variance summary: `n` marginal variances plus
`n(n-1)` ordered off-diagonal covariance contributions. -/
noncomputable def exchangeableClusterVariance
    (n : ℕ) (marginalVariance pairCovariance : ℝ) : ℝ :=
  (n : ℝ) * marginalVariance +
    (n : ℝ) * ((n - 1 : ℕ) : ℝ) * pairCovariance

theorem exchangeableClusterVariance_of_zero_covariance
    (n : ℕ) (marginalVariance : ℝ) :
    exchangeableClusterVariance n marginalVariance 0 = n * marginalVariance := by
  simp [exchangeableClusterVariance]

/-- Positive within-cluster covariance makes the independent-trial variance
strictly too small as soon as the cluster contains at least two trials. -/
theorem independent_variance_understates_positive_cluster
    (n : ℕ) (marginalVariance pairCovariance : ℝ)
    (hn : 2 ≤ n) (hcovariance : 0 < pairCovariance) :
    (n : ℝ) * marginalVariance <
      exchangeableClusterVariance n marginalVariance pairCovariance := by
  unfold exchangeableClusterVariance
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hnsubpos : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  have hpositive : 0 < (n : ℝ) * (n - 1 : ℕ) * pairCovariance := by positivity
  linarith

/-! ## Exact-packet overlap correction in the existing WM layer -/

namespace ExactPacketOverlap

structure PacketKey where
  programId : ℕ
  targetId : ℕ
  sourceId : ℕ
  deriving DecidableEq, Repr

abbrev State := Multiset PacketKey
abbrev Query := PacketKey

noncomputable instance : EvidenceType State :=
  Mettapedia.PLN.WorldModel.PLNWorldModelAdditive.multisetEvidenceType PacketKey

noncomputable instance : AdditiveWorldModel State Query ℕ where
  extract state query := state.count query
  extract_add left right query := by
    exact Multiset.count_add query left right

/-- Multiset union retains the maximum multiplicity of an exact packet; the
intersection is precisely the reused overlap. -/
noncomputable def layer : SubtractiveOverlapLayer State Query ℕ where
  merge := fun left right ↦ left ∪ right
  overlap := fun left right query ↦ (left ∩ right).count query
  combine := fun left right overlap ↦ left + right - overlap
  independent := fun left right query ↦ (left ∩ right).count query = 0
  evidence_merge := by
    intro left right query
    simp only [AdditiveWorldModel.extract, Multiset.count_union,
      Multiset.count_inter]
    omega
  additive_of_independent := by
    intro left right query hindependent
    simp only [AdditiveWorldModel.extract, Multiset.count_union,
      Multiset.count_inter] at hindependent ⊢
    omega
  combine_eq_sub := by
    intro left right overlap
    rfl
  independent_iff_zero_overlap := by
    intro left right query
    rfl

theorem inclusionExclusion
    (left right : State) (query : Query) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := ℕ)
        (layer.merge left right) query =
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := ℕ)
          left query +
        AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := ℕ)
          right query -
        layer.overlap left right query :=
  SubtractiveOverlapLayer.inclusionExclusion layer left right query

def key : PacketKey := ⟨1, 7, 11⟩

/-- Reusing one exact packet makes naive addition two, overlap one, and the
corrected merged evidence one. -/
theorem exact_repeat_overlap :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := ℕ)
        ({key} + {key}) key = 2 ∧
      layer.overlap {key} {key} key = 1 ∧
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := ℕ)
        (layer.merge {key} {key}) key = 1 := by
  decide +kernel

end ExactPacketOverlap

/-! ## Dependence-class fixtures -/

namespace EvidenceFixtures

inductive Program where
  | p0 | p1
  deriving DecidableEq, BEq, Repr

inductive Target where
  | t0 | t1
  deriving DecidableEq, BEq, Repr

inductive Lineage where
  | source0 | source1 | descendant
  deriving DecidableEq, BEq, Repr

abbrev Packet := SourcePacket Program Target Lineage

def first : Packet := ⟨.p0, .t0, .source0, ∅⟩
def sameSourceDifferentProgram : Packet := ⟨.p1, .t0, .source0, ∅⟩
def sameProgramDifferentTarget : Packet := ⟨.p0, .t1, .source0, ∅⟩
def independentRefind : Packet := ⟨.p0, .t0, .source1, ∅⟩
def trainedDescendant : Packet := ⟨.p0, .t0, .descendant, {.source0}⟩

theorem exact_repeat_increases_counts_not_diversity :
    (aggregatePacketEvidence [first, first] (.p0, .t0)).pos = 2 ∧
      (distinctPacketPrograms [first, first] .t0).card = 1 ∧
      (distinctPacketSources [first, first] (.p0, .t0)).card = 1 := by
  classical
  constructor
  · change (packetSupport first (.p0, .t0) + packetSupport first (.p0, .t0)).pos = 2
    rw [show packetSupport first (.p0, .t0) = ⟨1, 0⟩ by rfl]
    rfl
  · simp [distinctPacketPrograms, distinctPacketSources, SourcePacket.claim, first]

/-- Two different programs from one model/search lineage are two witnesses but
only one source of confirmation. -/
theorem witness_multiplicity_not_independent_confidence :
    (distinctPacketPrograms [first, sameSourceDifferentProgram] .t0).card = 2 ∧
      (distinctPacketSources [first, sameSourceDifferentProgram] (.p0, .t0)).card = 1 := by
  classical
  simp [distinctPacketPrograms, distinctPacketSources, SourcePacket.claim,
    first, sameSourceDifferentProgram]

/-- One program covering two targets does not create source independence. -/
theorem one_program_many_targets_not_independent :
    first.program = sameProgramDifferentTarget.program ∧
      ¬ first.SourceDisjoint sameProgramDifferentTarget := by
  simp [first, sameProgramDifferentTarget, SourcePacket.SourceDisjoint]

/-- A later lineage trained on the earlier source is explicitly dependent and
cannot receive an additive-revision license from source inequality alone. -/
theorem trained_descendant_not_source_disjoint :
    trainedDescendant.DependsOn first ∧
      ¬ first.SourceDisjoint trainedDescendant := by
  simp [trainedDescendant, first, SourcePacket.DependsOn,
    SourcePacket.SourceDisjoint]

/-- Source-disjoint refinds add two positive counts while preserving one exact
program witness and recording two genuinely distinct sources. -/
theorem source_disjoint_refind :
    first.SourceDisjoint independentRefind ∧
      (aggregatePacketEvidence [first, independentRefind] (.p0, .t0)).pos = 2 ∧
      (distinctPacketPrograms [first, independentRefind] .t0).card = 1 ∧
      (distinctPacketSources [first, independentRefind] (.p0, .t0)).card = 2 := by
  classical
  constructor
  · simp [SourcePacket.SourceDisjoint, first, independentRefind]
  · constructor
    · change (packetSupport first (.p0, .t0) +
          packetSupport independentRefind (.p0, .t0)).pos = 2
      rw [show packetSupport first (.p0, .t0) = ⟨1, 0⟩ by rfl]
      rw [show packetSupport independentRefind (.p0, .t0) = ⟨1, 0⟩ by rfl]
      rfl
    · simp [distinctPacketPrograms, distinctPacketSources, SourcePacket.claim,
        first, independentRefind]

theorem source_disjoint_refind_has_additive_license :
    AdditiveRevisionLicense first independentRefind :=
  sourceDisjoint_licenses_additiveRevision first independentRefind
    source_disjoint_refind.1

theorem packet_experiment_repeat_counts_twice :
    (packetExperimentEvidence ({first, first} : Multiset Packet) (.p0, .t0)).pos = 2 := by
  rw [packetExperimentEvidence_pos_eq_countP]
  have hcount :
      Multiset.countP (fun packet : Packet ↦ packet.claim = (.p0, .t0))
          {first, first} = 2 := by
    change Multiset.countP (fun packet : Packet ↦ packet.claim = (.p0, .t0))
      (first ::ₘ first ::ₘ 0) = 2
    rw [Multiset.countP_cons_of_pos _ (by rfl)]
    rw [Multiset.countP_cons_of_pos _ (by rfl)]
    simp
  exact_mod_cast hcount

def oneRegisteredTrial : FiniteBinarySample Bool where
  trials := {true}
  successes := {true}
  successes_subset := by simp

/-- Negative fixture: merging the same trial identity deduplicates it, whereas
blind Bernoulli combination counts it twice. -/
theorem repeated_trial_is_not_fresh_evidence :
    (FiniteBinarySample.merge oneRegisteredTrial oneRegisteredTrial).observations.total = 1 ∧
      (Mettapedia.PLN.Evidence.Convergence.BernoulliObservations.combine
        oneRegisteredTrial.observations oneRegisteredTrial.observations).total = 2 := by
  decide +kernel

end EvidenceFixtures

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
