/-
# PLN evidence as a typed weighted scheduler policy

This module is an adapter, not a second evidence algebra.  It uses the
existing `BinaryEvidence`, its order-dual parallel-aggregation quantale
`EvidenceHplus`, the existing strength-times-confidence fusion theorem, and
the generic weighted scheduler.

Two uses of evidence remain deliberately distinct:

* full `BinaryEvidence` inhabits the quantale-valued policy type, retaining
  positive and negative support for stateful aggregation;
* a declared propensity projection inhabits the commutative-semiring
  `where` fragment when an authored graded clause requires one scalar.

Neither representation authorizes an inference edge.
-/

import Mettapedia.GSLT.Core.WeightedMuScheduler
import Mettapedia.Languages.MeTTa.Prime.TypedScheduler
import Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization
import Mettapedia.PLN.Evidence.EvidenceHplusQuantale

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler

open scoped ENNReal

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Mettapedia.Languages.MeTTa.Prime.TypedScheduler
open Mettapedia.PLN.Bridges.GSLT.GuidanceOptimization
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.InferenceControl.PremiseSelection

universe uGoal uNode uAnswer uMemory

noncomputable section

/-! ## The existing evidence quantale as a policy carrier -/

/-- The empty path carries zero accumulated evidence.  The path unit is an
explicit field of `QuantalePolicy`, avoiding a conflicting global `One`
instance on a carrier that also supports the distinct tensor product. -/
def evidencePathUnit : EvidenceHplus :=
  OrderDual.toDual BinaryEvidence.zero

theorem evidencePathUnit_mul (grade : EvidenceHplus) :
    evidencePathUnit * grade = grade := by
  change OrderDual.toDual
      (BinaryEvidence.zero + OrderDual.ofDual grade) = grade
  simpa using congrArg OrderDual.toDual
    (BinaryEvidence.zero_hplus (OrderDual.ofDual grade))

theorem mul_evidencePathUnit (grade : EvidenceHplus) :
    grade * evidencePathUnit = grade := by
  change OrderDual.toDual
      (OrderDual.ofDual grade + BinaryEvidence.zero) = grade
  simpa using congrArg OrderDual.toDual
    (BinaryEvidence.hplus_zero (OrderDual.ofDual grade))

/-- Lift an existing PLN scorer directly into quantale-valued scheduling.
The caller states preference explicitly because the evidence information order
does not itself choose an attention policy. -/
def ofScorer
    (scorer : Scorer Memory Node)
    (prefer : EvidenceHplus → EvidenceHplus → Bool)
    (base : Memory → Scheduler Node)
    (initialMemory : Memory)
    (advance : Memory → Node → Option Answer → List Node → Memory) :
    QuantalePolicy EvidenceHplus Node Answer Memory where
  pathUnit := evidencePathUnit
  pathUnit_mul := evidencePathUnit_mul
  mul_pathUnit := mul_evidencePathUnit
  initialMemory := initialMemory
  grade memory node := OrderDual.toDual (scorer.score memory node)
  prefer := prefer
  base := base
  advance := advance

@[simp] theorem ofScorer_grade
    (scorer : Scorer Memory Node)
    (prefer : EvidenceHplus → EvidenceHplus → Bool)
    (base : Memory → Scheduler Node)
    (initialMemory : Memory)
    (advance : Memory → Node → Option Answer → List Node → Memory)
    (memory : Memory) (node : Node) :
    OrderDual.ofDual
      ((ofScorer scorer prefer base initialMemory advance).grade memory node) =
        scorer.score memory node :=
  rfl

/-- PLN revision is exactly quantale path multiplication after lifting.  This
is the bridge law connecting the established evidence algebra to the generic
policy carrier. -/
theorem fusedScorer_grade_mul
    (first second : Scorer Memory Node)
    (prefer : EvidenceHplus → EvidenceHplus → Bool)
    (base : Memory → Scheduler Node)
    (initialMemory : Memory)
    (advance : Memory → Node → Option Answer → List Node → Memory)
    (memory : Memory) (node : Node) :
    (ofScorer (fuse first second) prefer base initialMemory advance).grade
        memory node =
      (ofScorer first prefer base initialMemory advance).grade memory node *
        (ofScorer second prefer base initialMemory advance).grade memory node :=
  rfl

/-! ## The explicit scalar projection used by graded `where` -/

/-- The scalar propensity is the already-proved fused form of
strength-times-confidence.  It is a projection from evidence, not a
replacement for the evidence quantale. -/
abbrev propensity (prior : ℝ≥0∞) (evidence : BinaryEvidence) : ℝ≥0∞ :=
  ScoreFusion.binaryEvidenceFusedQuality prior evidence

/-- On finite evidence, the scalar projection agrees with the reference
strength-times-confidence definition. -/
theorem propensity_eq_strength_mul_confidence
    (prior : ℝ≥0∞) (evidence : BinaryEvidence)
    (total_finite : evidence.total ≠ ⊤) :
    propensity prior evidence =
      BinaryEvidence.toStrength evidence *
        BinaryEvidence.toConfidence prior evidence := by
  exact (ScoreFusion.binaryEvidenceReferenceQuality_eq_fused
    prior evidence total_finite).symm

/-- A PLN scorer becomes a one-state graded clause only through the declared
propensity projection. -/
def whereClause (prior : ℝ≥0∞) (scorer : Scorer Goal Node) (goal : Goal) :
    WeighClause ℝ≥0∞ Node :=
  .observe fun node => propensity prior (scorer.score goal node)

@[simp] theorem whereClause_eval
    (prior : ℝ≥0∞) (scorer : Scorer Goal Node) (goal : Goal) (node : Node) :
    WeighClause.eval node (whereClause prior scorer goal) =
      propensity prior (scorer.score goal node) :=
  rfl

namespace Examples

def noEvidence : BinaryEvidence := ⟨0, 0⟩
def onePositive : BinaryEvidence := ⟨1, 0⟩
def manyPositive : BinaryEvidence := ⟨100, 0⟩

/-- Positive control: absent evidence has zero scalar propensity. -/
theorem noEvidence_propensity : propensity 1 noEvidence = 0 := by
  norm_num [propensity, ScoreFusion.binaryEvidenceFusedQuality,
    noEvidence, BinaryEvidence.total]

/-- Negative control: equal strength does not justify erasing confidence.
The two all-positive packets have equal strength but distinct propensities. -/
theorem strength_does_not_determine_propensity :
    BinaryEvidence.toStrength onePositive =
        BinaryEvidence.toStrength manyPositive ∧
      propensity 1 onePositive ≠ propensity 1 manyPositive := by
  constructor
  · simp [BinaryEvidence.toStrength, BinaryEvidence.total, onePositive,
      manyPositive, ENNReal.div_self]
  · simp only [propensity, ScoreFusion.binaryEvidenceFusedQuality,
      BinaryEvidence.total, onePositive, manyPositive]
    intro claimed
    have real_claimed := congrArg ENNReal.toReal claimed
    norm_num [ENNReal.toReal_div] at real_claimed

end Examples

/-! ## Prime semantic internalization -/

section PrimeNeed

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

/-- Evidence-guided control for the actual Prime Need occurrence machine.
The policy remains occurrence-preserving and all evidence stays available in
its native carrier. -/
def needEvidencePolicy
    (score : NeedOccurrence Origin Local Resume Rule Value StableFault
      RetryableFault Effect → BinaryEvidence)
    (prefer : EvidenceHplus → EvidenceHplus → Bool) :
    QuantalePolicy EvidenceHplus
      (NeedOccurrence Origin Local Resume Rule Value StableFault RetryableFault Effect)
      (NeedAnswer Value StableFault RetryableFault) Unit :=
  ofScorer ⟨fun _ node => score node⟩ prefer (fun _ => Scheduler.breadthFirst)
    () (fun _ _ _ _ => ())

/-- The evidence policy is an ordinary closed Prime semantic term.  Interface
syntax and its independent elaboration theorem remain a separate obligation. -/
def internalNeedEvidencePolicy
    (score : NeedOccurrence Origin Local Resume Rule Value StableFault
      RetryableFault Effect → BinaryEvidence)
    (prefer : EvidenceHplus → EvidenceHplus → Bool) :
    Mettapedia.Languages.MeTTa.StagedReflective.familiesCwF.Tm PrimeContext
      (policyTyFor (Origin := Origin) (Local := Local) (Resume := Resume)
        (Rule := Rule) (Value := Value) (StableFault := StableFault)
        (RetryableFault := RetryableFault) (Effect := Effect) EvidenceHplus) :=
  fun _ => needEvidencePolicy score prefer

@[simp] theorem internalNeedEvidencePolicy_apply
    (score : NeedOccurrence Origin Local Resume Rule Value StableFault
      RetryableFault Effect → BinaryEvidence)
    (prefer : EvidenceHplus → EvidenceHplus → Bool) :
    internalNeedEvidencePolicy score prefer PUnit.unit =
      needEvidencePolicy score prefer :=
  rfl

end PrimeNeed

end

end Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
