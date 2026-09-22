import Mettapedia.PLN.WorldModel.WMCalculusJointEvidenceNative
import Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL

/-!
# A partial PLN mass space in the WM capability category

Joint-evidence mass is the additive WM evidence. Positive finite mass is
the separate eligibility condition for a normalized readout. The resulting
specialized backend is a lawful capability object and its GSLT-IL relation
is genuinely partial: zero-mass requests have no receipt, whereas a
normalized ProbLog full event has one with mass one.
-/


set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMJointEvidenceCapabilitySpace

open scoped ENNReal
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusJointEvidenceNative
open Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact

variable {n : ℕ}

/-- A concrete PLN backend in the generic category of lawful supported
WM readings. Its evidence carrier remains unnormalized mass. -/
noncomputable def jointEvidenceBackend
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool) : LawfulCapability where
  model := {
    State := JointEvidence n
    Query := Fin (2 ^ n) → Bool
    Evidence := ℝ≥0∞
    reading := additiveReading (Ev := ℝ≥0∞) world queryName
    laws := additiveReading_coreLaws world queryName }
  capability := normalizableMassCapability world queryName

/-- A normalized ProbLog source has a supported full-world event of mass
one. The support law checks both positivity and finiteness. -/
theorem probLog_fullEvent_supported
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (compiled : world "facts" = probLogToJointEvidence p) :
    (normalizableMassCapability world queryName).supports
      (world "facts") (fun _ => true) := by
  change 0 < countWorld (world "facts") (fun _ => true) ∧
    countWorld (world "facts") (fun _ => true) < ⊤
  rw [compiled]
  have mass : countWorld (probLogToJointEvidence p) (fun _ => true) =
      totalMass p := by
    simp [totalMass, total, countWorld]
  rw [mass, totalMass_eq_one p normalized]
  norm_num

/-- The actual GSLT-IL capability relation contains a checked full-event
answer for a compiled normalized ProbLog state. -/
theorem probLog_fullEvent_receipt
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (compiled : world "facts" = probLogToJointEvidence p) :
    Nonempty ((capabilityAnswerRelation
      (normalizableMassCapability world queryName)).evidence
        (world "facts", fun _ => true) 1) := by
  refine ⟨⟨probLog_fullEvent_supported p normalized world queryName compiled,
    ?_⟩⟩
  change countWorld (world "facts") (fun _ => true) = 1
  rw [compiled]
  have mass : countWorld (probLogToJointEvidence p) (fun _ => true) =
      totalMass p := by
    simp [totalMass, total, countWorld]
  rw [mass, totalMass_eq_one p normalized]

/-- Despite its positive supported requests, this backend does not earn a
total GSLT-IL compiler on all semantic state-query pairs: the zero state
has no finite positive normalization mass. -/
theorem jointEvidenceBackend_not_representable
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool) :
    ¬ Nonempty (Mettapedia.GSLT.RelationPresentation.Rel.Representation
      (capabilityAnswerRelation
        (normalizableMassCapability world queryName))) := by
  intro represented
  have allSupported :=
    (representable_iff_all_supported
      (normalizableMassCapability world queryName)).1 represented
  exact (normalizableMassCapability_zero_unsupported world queryName
    (fun _ => true)) (allSupported (0, fun _ => true))

end Mettapedia.PLN.WorldModel.WMJointEvidenceCapabilitySpace
