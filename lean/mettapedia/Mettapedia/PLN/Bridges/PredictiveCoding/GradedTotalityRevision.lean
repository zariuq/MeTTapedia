import Mettapedia.PLN.Bridges.PredictiveCoding.EvidenceRegisterBridge

/-!
# Graded totality evidence with an absolute partiality guard

The external OEIS property checker remains an opaque producer of typed
verdicts.  This module only specifies how such a verdict combines with
behavioral evidence in the existing `BinaryCounts` ledger.  An undetermined
verdict can accumulate evidence; a proved-partial verdict can never be
accepted, regardless of the accumulated counts.
-/

namespace Mettapedia.PLN.Bridges.PredictiveCoding

open Mettapedia.PLN.TruthValues.PLNTruthTower

/-- Typed totality verdict supplied by a sound but budget-bounded certifier. -/
inductive TotalityVerdict where
  | provablyTotal
  | undeterminedAtBudget
  | provablyPartial
  deriving DecidableEq, Repr

/-- The additive identity represented explicitly in the existing counts
type, whose zero-total state is intentionally allowed. -/
def noTotalityEvidence : BinaryCounts where
  nPlus := 0
  nMinus := 0
  nPlus_nonneg := by norm_num
  nMinus_nonneg := by norm_num

/-- One negative count records the static evidence attached to a proved
partial verdict.  This value is diagnostic only: the hard guard below, not a
threshold comparison, makes partiality irrevocable. -/
def singlePartialityEvidence : BinaryCounts := BinaryCounts.ofNatCounts 0 1

/-- Static evidence attached to a typed certifier verdict.  Undetermined is
not treated as negative evidence; it contributes the additive identity. -/
def totalityVerdictEvidence : TotalityVerdict → BinaryCounts
  | .provablyTotal => BinaryCounts.singlePositive
  | .undeterminedAtBudget => noTotalityEvidence
  | .provablyPartial => singlePartialityEvidence

/-- Pool static certifier evidence and accumulated behavioral evidence using
the existing counts-addition operation. -/
def pooledTotalityEvidence
    (verdict : TotalityVerdict) (behavioral : BinaryCounts) : BinaryCounts :=
  (totalityVerdictEvidence verdict).add behavioral

/-- Graded readout of the pooled count register. -/
noncomputable def gradedTotalityValue
    (verdict : TotalityVerdict) (behavioral : BinaryCounts) : ℝ :=
  (pooledTotalityEvidence verdict behavioral).strength

/-- The hard-mask comparison surface: only a statically proved-total verdict
exposes a score.  In particular, undetermined evidence is discarded. -/
noncomputable def hardMaskTotalityValue
    (verdict : TotalityVerdict) (behavioral : BinaryCounts) : ℝ :=
  match verdict with
  | .provablyTotal => gradedTotalityValue verdict behavioral
  | .undeterminedAtBudget => 0
  | .provablyPartial => 0

/-- Acceptance combines a graded threshold with an independent inviolable
partiality guard.  Nonzero total evidence is explicit because strength is a
division chart of the counts. -/
def gradedTotalityAccepted
    (threshold : ℝ) (verdict : TotalityVerdict)
    (behavioral : BinaryCounts) : Prop :=
  verdict ≠ .provablyPartial ∧
    (pooledTotalityEvidence verdict behavioral).total ≠ 0 ∧
      threshold ≤ gradedTotalityValue verdict behavioral

/-- T2 safety invariant: no behavioral evidence and no threshold can revise a
proved-partial program to accepted. -/
theorem provablyPartial_never_accepted
    (threshold : ℝ) (behavioral : BinaryCounts) :
    ¬ gradedTotalityAccepted threshold .provablyPartial behavioral := by
  intro haccepted
  exact haccepted.1 rfl

/-- A nonnegative increment of positive behavioral evidence. -/
def positiveBehavioralEvidence (amount : ℝ) (hamount : 0 ≤ amount) :
    BinaryCounts where
  nPlus := amount
  nMinus := 0
  nPlus_nonneg := hamount
  nMinus_nonneg := by norm_num

/-- Adding positive behavioral evidence cannot decrease the displayed
strength of any nonzero count register. -/
theorem BinaryCounts.strength_le_add_positiveBehavioralEvidence
    (evidence : BinaryCounts) (amount : ℝ) (hamount : 0 ≤ amount)
    (htotal : evidence.total ≠ 0) :
    evidence.strength ≤
      (evidence.add (positiveBehavioralEvidence amount hamount)).strength := by
  have htotalPos : 0 < evidence.total :=
    evidence.total_pos_of_ne_zero htotal
  have hnewTotalPos :
      0 < evidence.total + (positiveBehavioralEvidence amount hamount).total := by
    have hincrement :
        0 ≤ (positiveBehavioralEvidence amount hamount).total :=
      (positiveBehavioralEvidence amount hamount).total_nonneg
    linarith
  unfold BinaryCounts.strength
  rw [BinaryCounts.add_total]
  rw [div_le_div_iff₀ htotalPos hnewTotalPos]
  simp [positiveBehavioralEvidence, BinaryCounts.total, BinaryCounts.add]
  nlinarith [mul_nonneg hamount evidence.nMinus_nonneg]

/-- Accumulate one further positive behavioral contribution in the pooled
register. -/
def accumulatePositiveTotalityEvidence
    (verdict : TotalityVerdict) (behavioral : BinaryCounts)
    (amount : ℝ) (hamount : 0 ≤ amount) : BinaryCounts :=
  (pooledTotalityEvidence verdict behavioral).add
    (positiveBehavioralEvidence amount hamount)

/-- T2 monotonicity obligation: the pooled value is monotone under additional
positive behavioral evidence whenever its current total is nonzero. -/
theorem gradedTotalityValue_monotone_in_positiveEvidence
    (verdict : TotalityVerdict) (behavioral : BinaryCounts)
    (amount : ℝ) (hamount : 0 ≤ amount)
    (htotal : (pooledTotalityEvidence verdict behavioral).total ≠ 0) :
    gradedTotalityValue verdict behavioral ≤
      (accumulatePositiveTotalityEvidence
        verdict behavioral amount hamount).strength := by
  exact BinaryCounts.strength_le_add_positiveBehavioralEvidence
    (pooledTotalityEvidence verdict behavioral) amount hamount htotal

/-- Quantified separation from hard masking: on every undetermined input with
positive support and nonzero total evidence, graded revision retains a
strictly positive value while the hard mask returns zero. -/
theorem undetermined_graded_strictly_recovers_behavioralEvidence
    (behavioral : BinaryCounts)
    (hplus : 0 < behavioral.nPlus) (htotal : behavioral.total ≠ 0) :
    hardMaskTotalityValue .undeterminedAtBudget behavioral = 0 ∧
      0 < gradedTotalityValue .undeterminedAtBudget behavioral := by
  constructor
  · rfl
  · have htotalPos : 0 < behavioral.total :=
      behavioral.total_pos_of_ne_zero htotal
    simpa [gradedTotalityValue, pooledTotalityEvidence,
      totalityVerdictEvidence, noTotalityEvidence, BinaryCounts.add,
      BinaryCounts.strength, BinaryCounts.total] using
        (div_pos hplus htotalPos)

/-- Concrete undetermined evidence with strength `3/4`. -/
def totalityBehavioralPositiveFixture : BinaryCounts where
  nPlus := 3
  nMinus := 1
  nPlus_nonneg := by norm_num
  nMinus_nonneg := by norm_num

/-- Positive real-number fixture: graded revision accepts strong behavioral
evidence at threshold `2/3`, while the hard mask still exposes zero. -/
theorem undetermined_graded_revision_positive_fixture :
    hardMaskTotalityValue .undeterminedAtBudget
        totalityBehavioralPositiveFixture = 0 ∧
      gradedTotalityValue .undeterminedAtBudget
          totalityBehavioralPositiveFixture = (3 / 4 : ℝ) ∧
      gradedTotalityAccepted (2 / 3 : ℝ) .undeterminedAtBudget
        totalityBehavioralPositiveFixture := by
  norm_num [hardMaskTotalityValue, gradedTotalityValue,
    gradedTotalityAccepted, pooledTotalityEvidence, totalityVerdictEvidence,
    noTotalityEvidence, totalityBehavioralPositiveFixture, BinaryCounts.add,
    BinaryCounts.strength, BinaryCounts.total]
  decide

/-- Negative fixture: purely negative behavioral evidence does not make an
undetermined program pass a positive threshold. -/
theorem undetermined_negativeEvidence_not_accepted_fixture :
    ¬ gradedTotalityAccepted (1 / 2 : ℝ) .undeterminedAtBudget
      (BinaryCounts.ofNatCounts 0 3) := by
  norm_num [gradedTotalityAccepted, gradedTotalityValue,
    pooledTotalityEvidence, totalityVerdictEvidence, noTotalityEvidence,
    BinaryCounts.ofNatCounts, BinaryCounts.add, BinaryCounts.strength,
    BinaryCounts.total]

/-- T2 crown packages the absolute safety invariant, strict separation from
hard masking, and monotonicity of the pooled count readout. -/
theorem gradedTotalityRevision :
    (∀ threshold behavioral,
      ¬ gradedTotalityAccepted threshold .provablyPartial behavioral) ∧
      (hardMaskTotalityValue .undeterminedAtBudget
          totalityBehavioralPositiveFixture = 0 ∧
        gradedTotalityValue .undeterminedAtBudget
            totalityBehavioralPositiveFixture = (3 / 4 : ℝ) ∧
        gradedTotalityAccepted (2 / 3 : ℝ) .undeterminedAtBudget
          totalityBehavioralPositiveFixture) ∧
      (∀ verdict behavioral amount hamount,
        (pooledTotalityEvidence verdict behavioral).total ≠ 0 →
          gradedTotalityValue verdict behavioral ≤
            (accumulatePositiveTotalityEvidence
              verdict behavioral amount hamount).strength) := by
  exact ⟨provablyPartial_never_accepted,
    undetermined_graded_revision_positive_fixture,
    fun verdict behavioral amount hamount =>
      gradedTotalityValue_monotone_in_positiveEvidence
        verdict behavioral amount hamount⟩

#print axioms gradedTotalityRevision

end Mettapedia.PLN.Bridges.PredictiveCoding
