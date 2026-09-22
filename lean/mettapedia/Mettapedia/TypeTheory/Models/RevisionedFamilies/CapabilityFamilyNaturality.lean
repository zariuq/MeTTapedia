import Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
import Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism

/-!
# Behavioral backend maps transport observable capability families

Capability backend arrows act on raw checked receipts. They act on the
observable dependent families only when their state maps preserve WM
behavioral agreement, so that the state map descends to observation classes.
Under that exact extra hypothesis, the resulting dependent-fibre map
commutes with the already checked GSLT-IL receipt map on raw requests.

This does not assert a reverse map: widening support is an example where
forward transport exists but an unsupported source request becomes supported
in the target.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyNaturality

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyGSLTIL
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusCapabilityCategory
open Mettapedia.Logic.Bridges.WMNativeGSLTILMorphism
open Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTILMorphism

variable {source target : LawfulCapability} (hom : source ⟶ target)

/-- The exact additional condition needed to map observable state classes.
It is not supplied by every signature-preserving capability arrow. -/
def AgreementPreserving : Prop :=
  ∀ first second,
    source.model.reading.Agree .state first second →
      target.model.reading.Agree .state
        (hom.readingMap.mapState first) (hom.readingMap.mapState second)

/-- A compatible backend state map induces a map of observation classes. -/
def observableStateMap (preserves : AgreementPreserving hom) :
    ObsState source.model.reading → ObsState target.model.reading :=
  Quotient.lift
    (fun state => classOf target.model.reading (hom.readingMap.mapState state))
    (by
      intro first second agree
      exact (classOf_eq_iff_agree target.model.reading _ _).2
        (preserves first second agree))

/-- The same map, with the query component retained, is a substitution
between Prime's observable request contexts. -/
def observableRequestMap (preserves : AgreementPreserving hom) :
    Mettapedia.TypeTheory.Calculi.StagedScopedReflective.familiesCwF.Sub
      (observableRequestContext source.model.reading)
      (observableRequestContext target.model.reading) :=
  fun request =>
    (observableStateMap hom preserves request.1,
      hom.readingMap.mapQuery request.2)

theorem observableRequestMap_raw (preserves : AgreementPreserving hom)
    (request : source.model.State × source.model.Query) :
    observableRequestMap hom preserves
        (observationRequestSub source.model.reading request) =
      observationRequestSub target.model.reading
        (mapRequest hom.readingMap request) := by
  rfl

/-- A supported, checked dependent answer moves forward along a backend
map, now at the observable quotient-context level. -/
def mapObservableReceipt (preserves : AgreementPreserving hom)
    (request : observableRequestContext source.model.reading)
    (answer : source.model.Evidence) :
    ObservableReceipt source.capability request answer →
      ObservableReceipt target.capability
        (observableRequestMap hom preserves request)
        (hom.readingMap.mapEvidence answer) := by
  rcases request with ⟨observedState, query⟩
  intro receipt
  refine ⟨?_, ?_⟩
  · induction observedState using Quotient.inductionOn with
    | _ state =>
        exact hom.support_forward state query receipt.supported
  · induction observedState using Quotient.inductionOn with
    | _ state =>
      change target.model.reading.extract
          (hom.readingMap.mapState state) (hom.readingMap.mapQuery query) =
        hom.readingMap.mapEvidence answer
      have checked : source.model.reading.extract state query = answer :=
        receipt.checked
      rw [← hom.readingMap.extract_comm, checked]

/-- Naturality at raw requests: first reinterpret the GSLT-IL receipt as a
Prime observable dependent fibre and then map the fibre, or first map the
proof-relevant receipt and then reinterpret it, yields the same inhabitant.
No middle request or support proof is silently dropped. -/
theorem mapObservableReceipt_raw_square
    (preserves : AgreementPreserving hom)
    (request : source.model.State × source.model.Query)
    (answer : source.model.Evidence)
    (receipt : Mettapedia.Logic.Bridges.WMNativeCapabilityGSLTIL.CapabilityAnswerReceipt
      source.capability request answer) :
    mapObservableReceipt hom preserves
        (observationRequestSub source.model.reading request) answer
        ((rawReceiptEquiv source.capability request answer) receipt) =
      (observableRequestMap_raw hom preserves request) ▸
        ((rawReceiptEquiv target.capability
          (mapRequest hom.readingMap request)
          (hom.readingMap.mapEvidence answer))
          (mapCapabilityReceipt hom request answer receipt)) := by
  cases receipt
  rfl

/-- Widening support does preserve the underlying reading's agreement, so
its forward receipt map really does descend to observable request families. -/
theorem widenSupport_agreementPreserving :
    AgreementPreserving widenSupport := by
  intro first second agree
  exact agree

/-- The wider Boolean backend adds a previously unsupported observable
answer fibre even though its state, query, and evidence maps are identities. -/
theorem wide_false_observable_receipt :
    Nonempty (observableReceiptFamily allBooleanCapability false
      (classOf
        Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading
          false, ())) := by
  exact ⟨⟨trivial, rfl⟩⟩

/-- Hence forward CwF receipt transport along the widening map has no
fibrewise inverse at that request. -/
theorem widenSupport_no_false_fibre_equiv :
    ¬ Nonempty
      (observableReceiptFamily
          Mettapedia.OSLF.Framework.WMCalculusNativeCapabilityExample.truthCapability
          false
          (classOf
            Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading
              false, ()) ≃
        observableReceiptFamily allBooleanCapability false
          (classOf
            Mettapedia.OSLF.Framework.WMCalculusNativeContextExample.booleanReading
              false, ())) := by
  rintro ⟨equiv⟩
  obtain ⟨witness⟩ := wide_false_observable_receipt
  exact false_receipt_empty false
    ⟨equiv.symm witness⟩

end Mettapedia.TypeTheory.Models.RevisionedFamilies.CapabilityFamilyNaturality
