import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.CausalInnovationLedger

/-!
# Source-faithful evidence-memory dynamics

The executable Unified carrier stores a nonnegative table indexed by a hole
signature, a positive/negative plane, and a chart coordinate.  At an episode
boundary it multiplies the whole table by one retention factor and adds only
the episode innovation.  This file states that update directly, derives its
finite-round age weighting, and separates it from the cumulative prior rebuilt
outside the model at registered round boundaries.

The table is an evidence accumulator.  No probabilistic-posterior
interpretation is assumed here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

noncomputable section

/-- The exact logical shape of the persistent tensor: signature, polarity,
then chart coordinate.  `true` is the positive plane and `false` the negative
plane. -/
abbrev SignatureEvidenceTable (Signature Chart : Type*) :=
  Signature → Bool → Chart → ℝ

/-- Pointwise zero table. -/
def zeroEvidenceTable {Signature Chart : Type*} :
    SignatureEvidenceTable Signature Chart :=
  fun _ _ _ ↦ 0

/-- One source-faithful boundary update: decay every old cell once and add the
fresh innovation in the matching signature/polarity/chart cell. -/
def evidenceMemoryUpdate {Signature Chart : Type*}
    (retention : ℝ)
    (prior innovation : SignatureEvidenceTable Signature Chart) :
    SignatureEvidenceTable Signature Chart :=
  fun signature polarity chart ↦
    retention * prior signature polarity chart +
      innovation signature polarity chart

/-- Apply the registered update to innovations numbered from zero. -/
def evidenceMemoryRun {Signature Chart : Type*}
    (retention : ℝ)
    (initial : SignatureEvidenceTable Signature Chart)
    (innovation : ℕ → SignatureEvidenceTable Signature Chart) :
    ℕ → SignatureEvidenceTable Signature Chart
  | 0 => initial
  | n + 1 => evidenceMemoryUpdate retention
      (evidenceMemoryRun retention initial innovation n) (innovation n)

/-- Nonnegativity of every table cell. -/
def EvidenceTableNonnegative {Signature Chart : Type*}
    (table : SignatureEvidenceTable Signature Chart) : Prop :=
  ∀ signature polarity chart, 0 ≤ table signature polarity chart

theorem evidenceMemoryUpdate_nonnegative
    {Signature Chart : Type*} {retention : ℝ}
    {prior innovation : SignatureEvidenceTable Signature Chart}
    (retentionNonnegative : 0 ≤ retention)
    (priorNonnegative : EvidenceTableNonnegative prior)
    (innovationNonnegative : EvidenceTableNonnegative innovation) :
    EvidenceTableNonnegative
      (evidenceMemoryUpdate retention prior innovation) := by
  intro signature polarity chart
  exact add_nonneg
    (mul_nonneg retentionNonnegative
      (priorNonnegative signature polarity chart))
    (innovationNonnegative signature polarity chart)

theorem evidenceMemoryRun_nonnegative
    {Signature Chart : Type*} {retention : ℝ}
    {initial : SignatureEvidenceTable Signature Chart}
    {innovation : ℕ → SignatureEvidenceTable Signature Chart}
    (retentionNonnegative : 0 ≤ retention)
    (initialNonnegative : EvidenceTableNonnegative initial)
    (innovationNonnegative : ∀ n, EvidenceTableNonnegative (innovation n)) :
    ∀ n, EvidenceTableNonnegative
      (evidenceMemoryRun retention initial innovation n) := by
  intro n
  induction n with
  | zero => exact initialNonnegative
  | succ n ih =>
      exact evidenceMemoryUpdate_nonnegative retentionNonnegative ih
        (innovationNonnegative n)

/-- The age of innovation `birth` at the boundary after `rounds` updates. -/
def innovationAge (rounds birth : ℕ) : ℕ :=
  rounds - 1 - birth

/-- Exact finite-round expansion.  Each innovation is weighted by retention
raised to its age; the initial table has age `rounds`. -/
theorem evidenceMemoryRun_closedForm
    {Signature Chart : Type*}
    (retention : ℝ)
    (initial : SignatureEvidenceTable Signature Chart)
    (innovation : ℕ → SignatureEvidenceTable Signature Chart)
    (rounds : ℕ) (signature : Signature) (polarity : Bool) (chart : Chart) :
    evidenceMemoryRun retention initial innovation rounds
        signature polarity chart =
      retention ^ rounds * initial signature polarity chart +
        ∑ birth ∈ Finset.range rounds,
          retention ^ innovationAge rounds birth *
            innovation birth signature polarity chart := by
  induction rounds with
  | zero => simp [evidenceMemoryRun]
  | succ rounds ih =>
      rw [evidenceMemoryRun]
      simp only [evidenceMemoryUpdate, ih]
      rw [Finset.sum_range_succ]
      have weightedShift :
          retention *
              (∑ birth ∈ Finset.range rounds,
                retention ^ innovationAge rounds birth *
                  innovation birth signature polarity chart) =
            ∑ birth ∈ Finset.range rounds,
              retention ^ innovationAge (rounds + 1) birth *
                innovation birth signature polarity chart := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro birth birthInRange
        have birthLt : birth < rounds := Finset.mem_range.mp birthInRange
        have ageStep :
            innovationAge (rounds + 1) birth =
              innovationAge rounds birth + 1 := by
          unfold innovationAge
          omega
        rw [ageStep, pow_succ]
        ring
      rw [mul_add, weightedShift]
      have newestAge : innovationAge (rounds + 1) rounds = 0 := by
        simp [innovationAge]
      rw [newestAge, pow_zero]
      rw [pow_succ]
      ring

/-- In the absence of innovations, retention is the exact effective decay. -/
theorem evidenceMemoryRun_zeroInnovation
    {Signature Chart : Type*}
    (retention : ℝ)
    (initial : SignatureEvidenceTable Signature Chart)
    (rounds : ℕ) (signature : Signature) (polarity : Bool) (chart : Chart) :
    evidenceMemoryRun retention initial
        (fun _ ↦ zeroEvidenceTable) rounds signature polarity chart =
      retention ^ rounds * initial signature polarity chart := by
  rw [evidenceMemoryRun_closedForm]
  simp [zeroEvidenceTable]

/-- External round-boundary reconstruction uses cumulative innovations and a
single declared normalization factor; it does not implement chronological
decay. -/
def externallyReconstructedPrior {Signature Chart : Type*}
    (normalization : ℝ)
    (innovation : ℕ → SignatureEvidenceTable Signature Chart)
    (rounds : ℕ) : SignatureEvidenceTable Signature Chart :=
  fun signature polarity chart ↦
    normalization *
      ∑ birth ∈ Finset.range rounds,
        innovation birth signature polarity chart

/-- Exact agreement boundary used by the no-decay, unit-normalization case. -/
theorem online_eq_external_of_noDecay_unitNormalization
    {Signature Chart : Type*}
    (innovation : ℕ → SignatureEvidenceTable Signature Chart)
    (rounds : ℕ) :
    evidenceMemoryRun 1 zeroEvidenceTable innovation rounds =
      externallyReconstructedPrior 1 innovation rounds := by
  funext signature polarity chart
  rw [evidenceMemoryRun_closedForm]
  simp [zeroEvidenceTable, externallyReconstructedPrior, innovationAge]

/-- Scalar tables provide executable positive and negative fixtures without
hiding the full signature/polarity/chart shape. -/
def constantEvidenceTable {Signature Chart : Type*} (value : ℝ) :
    SignatureEvidenceTable Signature Chart :=
  fun _ _ _ ↦ value

/-- With retention one, two unit innovations are both retained. -/
theorem two_distinct_innovations_accumulate :
    evidenceMemoryRun (Signature := Unit) (Chart := Unit) 1
        zeroEvidenceTable (fun _ ↦ constantEvidenceTable 1) 2
        () true () = 2 := by
  norm_num [evidenceMemoryRun, evidenceMemoryUpdate, zeroEvidenceTable,
    constantEvidenceTable]

/-- Chronological decay separates the online update from cumulative external
reconstruction even when both receive the same two innovations. -/
theorem decay_separates_online_from_external :
    evidenceMemoryRun (Signature := Unit) (Chart := Unit) (1 / 2)
        zeroEvidenceTable (fun _ ↦ constantEvidenceTable 1) 2
        () true () ≠
      externallyReconstructedPrior 1 (fun _ ↦ constantEvidenceTable 1) 2
        () true () := by
  norm_num [evidenceMemoryRun, evidenceMemoryUpdate, zeroEvidenceTable,
    constantEvidenceTable, externallyReconstructedPrior]

/-- Replaying one identity twice is not the same operation as an exactly-once
causal ledger.  Exactly-once behavior therefore comes from
`CausalInnovationLedger`, not from numeric addition alone. -/
theorem replay_without_identity_dedup_doubleCounts :
    evidenceMemoryRun (Signature := Unit) (Chart := Unit) 1
        zeroEvidenceTable (fun _ ↦ constantEvidenceTable 1) 2
        () false () ≠
      constantEvidenceTable (Signature := Unit) (Chart := Unit) 1
        () false () := by
  norm_num [evidenceMemoryRun, evidenceMemoryUpdate, zeroEvidenceTable,
    constantEvidenceTable]

/-- Under decay, reversing two unequal innovations changes the endpoint. -/
theorem decay_makes_innovation_order_observable :
    evidenceMemoryRun (Signature := Unit) (Chart := Unit) (1 / 2)
        zeroEvidenceTable
        (fun n ↦ if n = 0 then constantEvidenceTable 1
          else constantEvidenceTable 2) 2 () true () ≠
      evidenceMemoryRun (Signature := Unit) (Chart := Unit) (1 / 2)
        zeroEvidenceTable
        (fun n ↦ if n = 0 then constantEvidenceTable 2
          else constantEvidenceTable 1) 2 () true () := by
  norm_num [evidenceMemoryRun, evidenceMemoryUpdate, zeroEvidenceTable,
    constantEvidenceTable]

/-- The source-faithful scalar boundary from the executable test: decay old
mass `(2,4)` by one half, then add innovation `(4,12)`. -/
theorem executable_episode_boundary_fixture :
    evidenceMemoryUpdate (Signature := Unit) (Chart := Unit) (1 / 2)
        (fun _ polarity _ ↦ if polarity then 2 else 4)
        (fun _ polarity _ ↦ if polarity then 4 else 12)
        () true () = 5 ∧
      evidenceMemoryUpdate (Signature := Unit) (Chart := Unit) (1 / 2)
        (fun _ polarity _ ↦ if polarity then 2 else 4)
        (fun _ polarity _ ↦ if polarity then 4 else 12)
        () false () = 14 := by
  norm_num [evidenceMemoryUpdate]

end

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
