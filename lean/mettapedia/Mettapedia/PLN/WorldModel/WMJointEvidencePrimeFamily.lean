import Mettapedia.PLN.WorldModel.WMJointEvidenceCapabilitySpace
import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability

/-!
# ProbLog joint evidence in Prime's observable receipt family

The compiled ProbLog state has a checked, supported full-event mass receipt.
That receipt inhabits the same dependent family used by Prime's semantic
families CwF and the OSLF native supported graph. The backend remains partial:
the zero-mass state prevents a global dependent receipt section and hence a
total semantic GSLT-IL representation. This comparison does not claim an
executable query provider or an authored Prime term for every semantic state.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMJointEvidencePrimeFamily

open scoped ENNReal
open _root_.CategoryTheory
open Mettapedia.PLN.Evidence.PLNJointEvidence
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusJointEvidenceNative
open Mettapedia.PLN.WorldModel.WMJointEvidenceCapabilitySpace
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityPiRepresentability
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics

variable {n : ℕ}

/-- A normalized ProbLog compilation supplies a checked inhabitant of the
observable dependent receipt family at its full-world event. -/
theorem probLog_fullEvent_observableReceipt
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (compiled : world "facts" = probLogToJointEvidence p) :
    Nonempty (observableReceiptFamily
      (normalizableMassCapability world queryName) 1
      (classOf (additiveReading (Ev := ℝ≥0∞) world queryName)
        (world "facts"), fun _ => true)) := by
  obtain ⟨receipt⟩ :=
    probLog_fullEvent_receipt p normalized world queryName compiled
  exact ⟨(rawReceiptEquiv
    (normalizableMassCapability world queryName)
    (world "facts", fun _ => true) 1) receipt⟩

/-- The same checked receipt belongs to the native supported graph at every
constructor stage; this is not only a matching informal reading. -/
theorem probLog_fullEvent_nativeSupported
    (p : ProbAssignment n) (normalized : ∀ i, p i ≤ 1)
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool)
    (compiled : world "facts" = probLogToJointEvidence p)
    (X : Opposite (ConstructorObj
      (wmExtVertexLanguageDefWithCong wmExtVertexMinimal))) :
    ((world "facts", fun _ => true), (1 : ℝ≥0∞)) ∈
      (supportedGraph (normalizableMassCapability world queryName)).obj X :=
  (observableReceipt_iff_nativeSupportedGraph
    (normalizableMassCapability world queryName)
    X (world "facts") (fun _ => true) 1).mp
      (probLog_fullEvent_observableReceipt
        p normalized world queryName compiled)

/-- A supported compiled request does not make the backend globally total.
The zero-mass semantic state has no normalizable request, so Prime's
dependent product over all observable requests has no section. -/
theorem jointEvidenceBackend_no_globalReceiptPi
    (world : String → JointEvidence n)
    (queryName : String → Fin (2 ^ n) → Bool) :
    ¬ Nonempty (allObservableReceiptPi
      (normalizableMassCapability world queryName)
      PUnit.unit) := by
  intro receiptSection
  exact jointEvidenceBackend_not_representable world queryName
    ((receiptPi_iff_semanticRepresentation _).mp receiptSection)

end Mettapedia.PLN.WorldModel.WMJointEvidencePrimeFamily
