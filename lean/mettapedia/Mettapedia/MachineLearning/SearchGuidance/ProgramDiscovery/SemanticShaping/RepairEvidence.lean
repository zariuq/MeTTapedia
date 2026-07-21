import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.CounterexampleRepair
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.OverlapCalibration
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.WeightedEvidenceDynamics
import Mettapedia.OSLF.Framework.WMCalculusLanguageDef

/-!
# Counts-native, provenance-aware repair evidence

Evidence is recorded per completed repair attempt, never per correlated term
of one recurrent trace.  Independent outcomes add in primal `(n⁺,n⁻)`
coordinates.  Declared lineage overlap is removed componentwise before
fusion.  Temporal forgetting then lifts exact counts into PLN's canonical
weighted-count carrier and applies the drift-derived retention.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping

open Mettapedia.PLN.Evidence
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
open scoped ENNReal

universe uP uT uL

/-- One completed repair attempt with explicit source lineage. -/
structure RepairOutcome
    (Program : Type uP) (Target : Type uT) (Lineage : Type uL) where
  program : Program
  target : Target
  source : Lineage
  ancestors : Finset Lineage
  beforeDepth : ℕ
  afterDepth : ℕ

namespace RepairOutcome

variable {Program : Type uP} {Target : Type uT} {Lineage : Type uL}

def Improved (outcome : RepairOutcome Program Target Lineage) : Prop :=
  outcome.beforeDepth < outcome.afterDepth

/-- One completed improvement contributes a positive repair count; every
completed non-improvement contributes a negative repair count. -/
def evidence (outcome : RepairOutcome Program Target Lineage) : BinEvNat :=
  if outcome.beforeDepth < outcome.afterDepth then ⟨1, 0⟩ else ⟨0, 1⟩

def asSourcePacket (outcome : RepairOutcome Program Target Lineage) :
    SourcePacket Program Target Lineage where
  program := outcome.program
  target := outcome.target
  source := outcome.source
  ancestors := outcome.ancestors

end RepairOutcome

/-- Mechanical counts fold.  Its epistemic use is licensed separately. -/
def aggregateRepairEvidence
    {Program : Type uP} {Target : Type uT} {Lineage : Type uL}
    (outcomes : List (RepairOutcome Program Target Lineage)) : BinEvNat :=
  (outcomes.map RepairOutcome.evidence).sum

theorem aggregateRepairEvidence_append
    {Program : Type uP} {Target : Type uT} {Lineage : Type uL}
    (left right : List (RepairOutcome Program Target Lineage)) :
    aggregateRepairEvidence (left ++ right) =
      aggregateRepairEvidence left + aggregateRepairEvidence right := by
  simp [aggregateRepairEvidence, List.map_append]

/-- Additive counts are epistemically licensed only for source-disjoint
repair outcomes. -/
structure IndependentRepairRevisionLicense
    {Program : Type uP} {Target : Type uT} {Lineage : Type uL}
    [DecidableEq Lineage]
    (left right : RepairOutcome Program Target Lineage) : Prop where
  sourceDisjoint : left.asSourcePacket.SourceDisjoint right.asSourcePacket
  evidenceAdds : aggregateRepairEvidence [left, right] =
    aggregateRepairEvidence [left] + aggregateRepairEvidence [right]

theorem sourceDisjoint_licenses_repairAddition
    {Program : Type uP} {Target : Type uT} {Lineage : Type uL}
    [DecidableEq Lineage]
    (left right : RepairOutcome Program Target Lineage)
    (hdisjoint : left.asSourcePacket.SourceDisjoint right.asSourcePacket) :
    IndependentRepairRevisionLicense left right := by
  exact ⟨hdisjoint, by
    simpa only [List.singleton_append] using
      aggregateRepairEvidence_append [left] [right]⟩

/-! ## Counts-native overlap correction -/

/-- Remove a declared shared lineage packet before adding the incoming repair
evidence. -/
def overlapCorrectedRepairRevision
    (old first second overlap : BinEvNat) : BinEvNat :=
  overlapCalibratedBinEvNatRevision old first second overlap

theorem overlapCorrectedRepairRevision_components
    (old first second overlap : BinEvNat) :
    (overlapCorrectedRepairRevision old first second overlap).pos =
        old.pos + first.pos + (second.pos - overlap.pos) ∧
      (overlapCorrectedRepairRevision old first second overlap).neg =
        old.neg + first.neg + (second.neg - overlap.neg) :=
  overlapCalibratedBinEvNatRevision_components old first second overlap

theorem duplicatedRepairOutcome_contributes_once :
    overlapCorrectedRepairRevision ⟨0, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ =
      ⟨1, 0⟩ :=
  duplicatePositiveCount_discounted_negativeExample

/-! ## Temporal decay in the canonical weighted-count extension -/

/-- Fade old repair evidence, then add only the non-overlapping part of the
fresh packet at full weight. -/
noncomputable def temporalRepairRevision
    (retention : ℝ≥0∞) (old fresh overlap : BinEvNat) : WeightedEvidence :=
  WeightedEvidence.fadeThenFuse retention
    (WeightedEvidence.ofBinEvNat old)
    (WeightedEvidence.ofBinEvNat (discountBinEvNat fresh overlap))

/-- Unit retention recovers exact counts-native overlap-corrected addition. -/
theorem temporalRepairRevision_one
    (old fresh overlap : BinEvNat) :
    temporalRepairRevision 1 old fresh overlap =
      WeightedEvidence.ofBinEvNat (old + discountBinEvNat fresh overlap) := by
  unfold temporalRepairRevision
  rw [WeightedEvidence.fadeThenFuse_one]
  exact (WeightedEvidence.ofBinEvNat.map_add old
    (discountBinEvNat fresh overlap)).symm

/-- Drift statistics supply an honest retention factor, rather than an
unconstrained evidence amplifier. -/
theorem derivedRepairRetention_le_one
    (oldVariance jumpVariance : ℝ)
    (hold : 0 < oldVariance) (hjump : 0 ≤ jumpVariance) :
    derivedJumpEvidenceRetention oldVariance jumpVariance ≤ 1 :=
  derivedJumpEvidenceRetention_le_one oldVariance jumpVariance hold hjump

noncomputable def driftAwareRepairRevision
    (oldVariance jumpVariance : ℝ)
    (old fresh overlap : BinEvNat) : WeightedEvidence :=
  temporalRepairRevision
    (derivedJumpEvidenceRetention oldVariance jumpVariance) old fresh overlap

theorem zeroDrift_recovers_exactOverlapCorrectedAddition
    (oldVariance : ℝ) (hold : 0 < oldVariance)
    (old fresh overlap : BinEvNat) :
    driftAwareRepairRevision oldVariance 0 old fresh overlap =
      WeightedEvidence.ofBinEvNat (old + discountBinEvNat fresh overlap) := by
  rw [driftAwareRepairRevision,
    derivedJumpEvidenceRetention_zeroJump oldVariance hold]
  exact temporalRepairRevision_one old fresh overlap

/-! ## Operational WM-calculus alignment -/

namespace WMAlignment

open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The maximal WM calculus exposes both overlap correction and forgetting as
actual reduction steps, so the repair ledger's two non-additive operations
use the same operational vocabulary as WM-PLN. -/
theorem overlap_and_forgetting_are_wmSteps
    (first second query scope state : Pattern) :
    wmFullLangReduces wmFullVertexMaximal
        (pExtract (pOverlapMerge first second) query)
        (pOverlapCorrect (pExtract first query) (pExtract second query)
          (pOverlapFactor first second query)) ∧
      wmFullLangReduces wmFullVertexMaximal
        (pExtract (pForget scope state) query)
        (pExtract state query) := by
  constructor
  · exact wmFullLangReduces_overlapExtract wmFullVertexMaximal rfl
      first second query
  · exact wmFullLangReduces_forgetOutside wmFullVertexMaximal
      (Or.inr rfl) scope state query

end WMAlignment

/-! ## Positive and negative fixtures -/

def improvedFixture : RepairOutcome Unit Unit ℕ where
  program := ()
  target := ()
  source := 1
  ancestors := ∅
  beforeDepth := 2
  afterDepth := 3

def failedFixture : RepairOutcome Unit Unit ℕ where
  program := ()
  target := ()
  source := 2
  ancestors := ∅
  beforeDepth := 2
  afterDepth := 1

theorem oneImprovement_oneFailure_counts_fixture :
    aggregateRepairEvidence [improvedFixture, failedFixture] = ⟨1, 1⟩ := by
  decide

theorem sameLineage_repairOutcomes_not_independent :
    let repeated := { failedFixture with source := improvedFixture.source }
    ¬ improvedFixture.asSourcePacket.SourceDisjoint repeated.asSourcePacket := by
  dsimp
  intro h
  exact h.1 rfl

#print axioms aggregateRepairEvidence_append
#print axioms sourceDisjoint_licenses_repairAddition
#print axioms duplicatedRepairOutcome_contributes_once
#print axioms temporalRepairRevision_one
#print axioms zeroDrift_recovers_exactOverlapCorrectedAddition
#print axioms WMAlignment.overlap_and_forgetting_are_wmSteps
#print axioms sameLineage_repairOutcomes_not_independent

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping
