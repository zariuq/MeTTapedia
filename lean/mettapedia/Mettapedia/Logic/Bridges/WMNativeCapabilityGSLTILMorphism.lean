import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL
import Mettapedia.Logic.Bridges.WMNativeGSLTILMorphism
import Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory

/-!
# Capability-preserving maps of proof-relevant WM answer routes

An arrow of capability backends maps supported answer receipts and the
syntax-to-answer route, preserving its actual semantic middle request.
The map is forward only: widening support can add answers without making
the previously unsupported requests valid in the source backend.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism

open _root_.CategoryTheory
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeCapability
open Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
open Mettapedia.OSLF.Framework.WMCalculusNativeContextExample
open Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample
open Mettapedia.Logic.Bridges.WMNativeGSLTILMorphism
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL

variable {source target : LawfulCapability} (hom : source ⟶ target)

/-- A backend arrow preserves both parts of a partial answer receipt:
admissibility and the checked extracted value. -/
def mapCapabilityReceipt (request : source.model.State × source.model.Query)
    (answer : source.model.Evidence) :
    CapabilityAnswerReceipt source.capability request answer →
      CapabilityAnswerReceipt target.capability
        (mapRequest hom.readingMap request)
        (hom.readingMap.mapEvidence answer)
  | receipt =>
      ⟨hom.support_forward request.1 request.2 receipt.supported,
        by
          change target.model.reading.extract
            (hom.readingMap.mapState request.1)
            (hom.readingMap.mapQuery request.2) =
              hom.readingMap.mapEvidence answer
          rw [← hom.readingMap.extract_comm, receipt.checked]⟩

/-- The chained witness map retains the middle request and denotation
receipt while transporting capability support and answer evidence. -/
def mapTermCapabilityEvidence
    (terms : WMTerm .state × WMTerm .query)
    (answer : source.model.Evidence) :
    (termCapabilityChain source.capability).evidence terms answer →
      (termCapabilityChain target.capability).evidence terms
        (hom.readingMap.mapEvidence answer)
  | ⟨request, pairReceipt, answerReceipt⟩ =>
      ⟨mapRequest hom.readingMap request,
        mapTermPairReceipt hom.readingMap terms request pairReceipt,
        mapCapabilityReceipt hom request answer answerReceipt⟩

/-- Hence supported syntax-to-answer routes survive a backend map, with
no unsupported converse inferred. -/
theorem termCapability_support_forward
    (terms : WMTerm .state × WMTerm .query)
    (answer : source.model.Evidence) :
    Nonempty ((termCapabilityChain source.capability).evidence terms answer) →
      Nonempty ((termCapabilityChain target.capability).evidence terms
        (hom.readingMap.mapEvidence answer)) := by
  rintro ⟨witness⟩
  exact ⟨mapTermCapabilityEvidence hom terms answer witness⟩

/-! ## Strict one-way support control -/

private def booleanModel :
    Mettapedia.OSLF.Framework.WMCalculusReadingCategory.LawfulReading where
  State := Bool
  Query := Unit
  Evidence := Bool
  reading := booleanReading
  laws := booleanReading_coreLaws

/-- A second capability accepts every Boolean request. -/
def allBooleanCapability : WMCapability booleanReading where
  supports := fun _ _ => True
  respectsAgree := by
    intro first second query agree
    exact Iff.rfl

def truthBackend : LawfulCapability where
  model := booleanModel
  capability := truthCapability

def allBackend : LawfulCapability where
  model := booleanModel
  capability := allBooleanCapability

/-- Identity on the WM reading is a valid map from narrow to wide support. -/
def widenSupport : truthBackend ⟶ allBackend where
  readingMap := 𝟙 booleanModel
  support_forward := by
    intro state query supported
    trivial

/-- The wider target has an answer at a request rejected by the source. -/
theorem wide_false_receipt :
    Nonempty ((capabilityAnswerRelation allBooleanCapability).evidence
      (false, ()) false) := by
  exact ⟨⟨trivial, rfl⟩⟩

theorem narrow_false_no_receipt :
    ¬ Nonempty ((capabilityAnswerRelation truthCapability).evidence
      (false, ()) false) := by
  exact no_receipt_of_unsupported truthCapability (false, ())
    (by simp [truthCapability]) false

/-- No support-reflecting inverse exists for this backend map, even though
its underlying WM reading map is the identity. -/
theorem widenSupport_not_support_reflecting :
    ¬ (∀ state query,
      allBooleanCapability.supports state query →
        truthCapability.supports state query) := by
  intro reflects
  have impossible := reflects false () trivial
  exact (by simp [truthCapability] at impossible : False)

end Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism
