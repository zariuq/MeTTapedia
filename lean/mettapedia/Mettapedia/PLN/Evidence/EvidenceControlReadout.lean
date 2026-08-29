import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# Evidence readouts for control policies

A control policy may consult evidence without treating evidence as control
authority.  The sufficient readout depends on the policy family being asked
for:

* current-strength policies factor through the scalar strength readout;
* positive-revision policies do not factor through strength alone; and
* retaining the full evidence state supports both.

Thus no universal numeric weight is required.  A readout is admitted for a
declared family exactly when it retains enough information to reproduce every
decision in that family.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Evidence.EvidenceControlReadout

open Mettapedia.GSLT.Core
open Mettapedia.PLN.Evidence.EvidenceQuantale

noncomputable section

/-- One additional positive observation. -/
def positiveObservation : BinaryEvidence := ⟨1, 0⟩

/-- Revision by one positive observation. -/
def revisePositive (evidence : BinaryEvidence) : BinaryEvidence :=
  evidence + positiveObservation

/-- Two evidence occurrences with strength one half. -/
def light : BinaryEvidence := ⟨1, 1⟩

/-- Four evidence occurrences with the same strength. -/
def heavy : BinaryEvidence := ⟨2, 2⟩

theorem light_strength : BinaryEvidence.toStrength light = 1 / 2 := by
  norm_num [light, BinaryEvidence.toStrength, BinaryEvidence.total]

theorem heavy_strength : BinaryEvidence.toStrength heavy = 1 / 2 := by
  unfold BinaryEvidence.toStrength BinaryEvidence.total
  have total_ne : (2 : ENNReal) + 2 ≠ 0 := by norm_num
  simp only [heavy, total_ne, ↓reduceIte]
  have two_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have two_ne_top : (2 : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top 2
  have four_eq : (4 : ENNReal) = 2 * 2 := by norm_num
  have two_eq : (2 : ENNReal) = 1 * 2 := by ring
  rw [show (2 : ENNReal) + 2 = 4 by norm_num, two_eq, four_eq]
  rw [ENNReal.mul_div_mul_right 1 2 two_ne_zero two_ne_top]
  simp only [one_mul]

theorem light_revised_strength :
    BinaryEvidence.toStrength (revisePositive light) = 2 / 3 := by
  norm_num [revisePositive, light, positiveObservation,
    BinaryEvidence.toStrength, BinaryEvidence.total,
    BinaryEvidence.hplus_def]

theorem heavy_revised_strength :
    BinaryEvidence.toStrength (revisePositive heavy) = 3 / 5 := by
  norm_num [revisePositive, heavy, positiveObservation,
    BinaryEvidence.toStrength, BinaryEvidence.total,
    BinaryEvidence.hplus_def]

/-- Equal current strengths may demand different decisions after revision. -/
theorem revision_separates_equal_strengths :
    BinaryEvidence.toStrength light = BinaryEvidence.toStrength heavy ∧
      BinaryEvidence.toStrength (revisePositive light) ≠
        BinaryEvidence.toStrength (revisePositive heavy) := by
  constructor
  · exact light_strength.trans heavy_strength.symm
  · rw [light_revised_strength, heavy_revised_strength]
    intro equality
    have realEquality := congrArg ENNReal.toReal equality
    norm_num at realEquality

/-- A policy family that asks only for current strength. -/
def currentStrengthPolicy : PolicyFamily BinaryEvidence where
  Policy := Unit
  Result := fun _ => ENNReal
  decide := fun _ evidence => BinaryEvidence.toStrength evidence

/-- Strength is sufficient for the policy which asks only for strength. -/
theorem strength_supports_currentStrengthPolicy :
    currentStrengthPolicy.SupportsReadout BinaryEvidence.toStrength := by
  refine ⟨{
    run := fun _ strength => strength
    agrees := ?_ }⟩
  intro policy evidence
  rfl

/-- A policy family whose decision observes the result of positive revision. -/
def positiveRevisionPolicy : PolicyFamily BinaryEvidence where
  Policy := Unit
  Result := fun _ => ENNReal
  decide := fun _ evidence =>
    BinaryEvidence.toStrength (revisePositive evidence)

/-- Full evidence is sufficient for the revision-sensitive policy. -/
theorem fullEvidence_supports_positiveRevisionPolicy :
    positiveRevisionPolicy.SupportsReadout id := by
  refine ⟨{
    run := fun _ evidence =>
      BinaryEvidence.toStrength (revisePositive evidence)
    agrees := ?_ }⟩
  intro policy evidence
  rfl

/-- Strength alone cannot implement the revision-sensitive policy family. -/
theorem strength_does_not_support_positiveRevisionPolicy :
    Not (positiveRevisionPolicy.SupportsReadout BinaryEvidence.toStrength) := by
  apply positiveRevisionPolicy.not_supportsReadout_of_policy_collision
    BinaryEvidence.toStrength
    revision_separates_equal_strengths.1
    ()
  change BinaryEvidence.toStrength (revisePositive light) ≠
    BinaryEvidence.toStrength (revisePositive heavy)
  exact revision_separates_equal_strengths.2

#print axioms light_strength
#print axioms heavy_strength
#print axioms light_revised_strength
#print axioms heavy_revised_strength
#print axioms revision_separates_equal_strengths
#print axioms strength_supports_currentStrengthPolicy
#print axioms fullEvidence_supports_positiveRevisionPolicy
#print axioms strength_does_not_support_positiveRevisionPolicy

end

end Mettapedia.PLN.Evidence.EvidenceControlReadout
