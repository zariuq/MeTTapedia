import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedSpecifications
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecificationControls

/-!
# Complete origins and dependent answers in generated compiler receipts

Two independently authored caller origins remain distinct generated values
over the same compiled program. Generated specification readouts retain
those origins and the actual dependent finite answer of the native function
specification. A returning program still has no generated receipt in the
empty certificate profile, and its program value cannot select the supplied
origin. Natural-number answers here belong to native specification evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafSlicePi DisplayedPresheafPi
open DisplayedPresheafEvidenceApplication
open NamePassingDependentEvidence NamePassingDependentEvidenceControls
open NamePassingDependentSpecifications NamePassingDependentSpecificationControls
open NamePassingGeneratedIndexedEvidence NamePassingGeneratedIndexedSpecifications

noncomputable section

def firstOrigin : NativeReceipt insertionFamily targetPoint :=
  suppliedReceipt insertionFamily sourcePoint immediateOrigin

def secondOrigin : NativeReceipt insertionFamily targetPoint :=
  suppliedReceipt insertionFamily sourcePoint renamedOrigin

theorem generated_origins_distinct : firstOrigin ≠ secondOrigin :=
  fun same => origins_distinct (supplied_receipt_injective insertionFamily sourcePoint same)

theorem generated_caller_specifications_distinct :
    NamePassingGeneratedIndexedSpecifications.specificationEquiv callerSpecification targetPoint
        (applySpecification sourceCallerReadout targetPoint firstOrigin) ≠
      NamePassingGeneratedIndexedSpecifications.specificationEquiv callerSpecification targetPoint
        (applySpecification sourceCallerReadout targetPoint secondOrigin) := by
  rw [firstOrigin, secondOrigin, supplied_specification_computes, supplied_specification_computes]
  intro same
  apply callerReadout_distinguishes_origins
  rw [callerReadout_computes, callerReadout_computes]
  exact same

theorem program_value_cannot_choose_generated_origin :
    ¬ ∃ recover : compiledPrograms.obj sourcePoint.1 → NativeReceipt insertionFamily targetPoint,
      recover (compilerMap.app sourcePoint.1 sourcePoint.2) = firstOrigin ∧
        recover (compilerMap.app sourcePoint.1 sourcePoint.2) = secondOrigin := by
  rintro ⟨_, first, second⟩
  exact generated_origins_distinct (first.symm.trans second)

def emptyCertificates : DisplayedFamily sourcePrograms :=
  (Functor.const sourcePrograms.Elements).obj Empty

theorem empty_certificate_profile_has_no_generated_receipt (point : compiledPrograms.Elements) :
    IsEmpty (NativeReceipt emptyCertificates point) :=
  ⟨fun supplied => Empty.elim (receiptEquiv emptyCertificates point supplied).val.2⟩

theorem actual_return_does_not_supply_an_empty_profile_certificate :
    NamePassingObserverAdequacy.ProtocolMayReturn targetPoint.2 ∧
      IsEmpty (NativeReceipt emptyCertificates targetPoint) :=
  ⟨both_certificates_return, empty_certificate_profile_has_no_generated_receipt targetPoint⟩

def functionBody : insertionFamily ⟶ reindexDisplayed compilerMap (piDisplayed arguments answers) :=
  sourceCallerReadout ≫ (reindexFunctor compilerMap).map functionConstructor

def dependentAnswer (origin : insertionFamily.obj sourcePoint) (n : Nat) :=
  (applyAt arguments answers (argumentSection n)).app targetPoint
    (NamePassingGeneratedIndexedSpecifications.specificationEquiv (piDisplayed arguments answers)
      targetPoint (applySpecification functionBody targetPoint
        (suppliedReceipt insertionFamily sourcePoint origin)))

theorem complete_dependent_answer (origin : insertionFamily.obj sourcePoint) (n : Nat) :
    dependentAnswer origin n =
      (⟨compilerMap.mapElements.map origin, ⟨n, Nat.lt_succ_self n⟩⟩ :
        answers.obj ((sectionLift arguments (argumentSection n)).mapElements.obj targetPoint)) := by
  change (applyAt arguments answers (argumentSection n)).app targetPoint
    (NamePassingGeneratedIndexedSpecifications.specificationEquiv (piDisplayed arguments answers)
      targetPoint (applySpecification functionBody targetPoint
        (suppliedReceipt insertionFamily sourcePoint origin))) = _
  rw [specification_current_read, supplied_receipt_read]
  exact functionReadout_application sourcePoint origin n

theorem dependent_answers_keep_origins (n : Nat) :
    dependentAnswer immediateOrigin n ≠ dependentAnswer renamedOrigin n := by
  rw [complete_dependent_answer, complete_dependent_answer]
  intro same
  apply callerReadout_distinguishes_origins
  rw [callerReadout_computes, callerReadout_computes]
  exact congrArg Prod.fst same

theorem wrong_dependent_witness_rejected (origin : insertionFamily.obj sourcePoint) (n : Nat)
    (wrong : Fin (n + 1)) (different : wrong.val ≠ n) :
    (dependentAnswer origin n).2 ≠ wrong := by
  rw [complete_dependent_answer]
  intro same
  exact different (congrArg Fin.val same).symm

theorem actual_caller_restricts_the_whole_generated_receipt
    (origin : insertionFamily.obj sourcePoint) :
    restrictReceipt insertionFamily (compilerMap.mapElements.map callingArrow)
        (suppliedReceipt insertionFamily sourcePoint origin) =
      suppliedReceipt insertionFamily calledPoint (insertionFamily.map callingArrow origin) := by
  apply (receiptEquiv insertionFamily (compilerMap.mapElements.obj calledPoint)).injective
  rw [restriction_read, supplied_receipt_read, supplied_receipt_read]
  exact ((carry insertionFamily).naturality_apply callingArrow origin).symm

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedControls
