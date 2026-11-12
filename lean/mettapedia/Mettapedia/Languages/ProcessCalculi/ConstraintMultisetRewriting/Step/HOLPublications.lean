import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLObserverAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls

/-! # Prepared payloads and admitted success records in the loaded model

Payloads are encoded at a prepared result without asking for permission.
Their successful observation uses the received pullback operation. The
constrained-admission control retains the inherited payload, records the new
success and refuses a success event in the original guarded profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPublications

open Mettapedia.Languages.OpenTheory.TypeFamilySemantics

universe uO uT uH uOcc uS uF

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {E : EffectCore X O State Firing}
  (D : PreparedPublications E) (allow : E.Admission)

def preparedPayload {s : State} (firing : Firing s) (prepared : E.Prepares firing) :
    HOLObserverEncoding.RawRecord E allow (D.observer allow) :=
  HOLObserverEncoding.encode E allow (D.observer allow)
    (s := E.preparedResult firing prepared) (D.names firing prepared, D.records firing)

theorem prepared_payload_valid {s : State} (firing : Firing s) (prepared : E.Prepares firing) :
    HOLObserverEncoding.Valid E allow (D.observer allow) (E.preparedResult firing prepared)
      (preparedPayload D allow firing prepared) :=
  ⟨(D.names firing prepared, D.records firing), rfl⟩

theorem loaded_event_update (input : HOLRunModel.Input)
    (other : OperatorFamilies.{max uS uF uT uOcc}) (prior : Assignment.{max uS uF uT uOcc})
    {s : State} (firing : Firing s) (prepared : E.Prepares firing) (permitted : allow firing prepared)
    (past : List (Tm (E.frame s)) × Observation.Record O) :
    HOLObserverModel.record E allow (D.observer allow) input other prior
      (HOLPreparedRunEncoding.word E allow
        ((Quiver.Path.nil).cons (show E.Event allow s (E.preparedResult firing prepared) from
          ⟨firing, prepared, permitted, rfl⟩)))
      (HOLObserverEncoding.encode E allow (D.observer allow) (s := s) past) =
      HOLObserverEncoding.encode E allow (D.observer allow) (s := E.preparedResult firing prepared)
        (past.1.map (X.act (E.along firing prepared)) ++ D.names firing prepared,
          past.2 ++ D.records firing) := by
  rw [HOLObserverModel.record_eq_native]
  rfl

theorem loaded_event_payload (input : HOLRunModel.Input)
    (other : OperatorFamilies.{max uS uF uT uOcc}) (prior : Assignment.{max uS uF uT uOcc})
    {s : State} (firing : Firing s) (prepared : E.Prepares firing) (permitted : allow firing prepared) :
    HOLObserverModel.record E allow (D.observer allow) input other prior
      (HOLPreparedRunEncoding.word E allow
        ((Quiver.Path.nil).cons (show E.Event allow s (E.preparedResult firing prepared) from
          ⟨firing, prepared, permitted, rfl⟩)))
      (HOLObserverEncoding.encode E allow (D.observer allow) (s := s) ([], [])) =
        preparedPayload D allow firing prepared := by
  rw [HOLObserverModel.record_eq_native]
  rfl

end General

namespace Controls

open PreparedStep.Controls PreparedPublicationsControls

variable (input : HOLRunAdmissionJoin.Input) (other : OperatorFamilies.{0}) (prior : Assignment.{0})

theorem inherited_publication_recorded :
    HOLObserverModel.record EventControls.restricted.effectCore EventControls.restricted.eventAdmission
      (inherited.observer EventControls.restricted.eventAdmission) input.toInput other prior
      (HOLPreparedRunEncoding.word EventControls.restricted.effectCore EventControls.restricted.eventAdmission
        EventControls.admittedPath)
      (HOLObserverEncoding.encode EventControls.restricted.effectCore EventControls.restricted.eventAdmission
        (inherited.observer EventControls.restricted.eventAdmission) (s := start) ([], [])) =
      HOLObserverEncoding.encode EventControls.restricted.effectCore EventControls.restricted.eventAdmission
        (inherited.observer EventControls.restricted.eventAdmission)
        (s := EventControls.restricted.result apart apart_admitted)
        ([bit, no], [Observation.Record.reference 0]) := by
  rw [HOLObserverModel.record_eq_native, new_receipt_without_base_receipt.1]

theorem fresh_success_recorded :
    HOLObserverModel.record EventControls.restricted.effectCore EventControls.restricted.eventAdmission
      EventControls.restricted.successObserver input.toInput other prior
      (HOLPreparedRunEncoding.word EventControls.restricted.effectCore EventControls.restricted.eventAdmission
        EventControls.admittedPath)
      (HOLObserverEncoding.encode EventControls.restricted.effectCore EventControls.restricted.eventAdmission
        EventControls.restricted.successObserver (s := start) []) =
      HOLObserverEncoding.encode EventControls.restricted.effectCore EventControls.restricted.eventAdmission
        EventControls.restricted.successObserver (s := EventControls.restricted.result apart apart_admitted)
        [⟨start, ⟨apart, apart_admitted⟩⟩] := by
  rw [HOLObserverModel.record_eq_native, new_receipt_without_base_receipt.2.1]

theorem base_loaded_preparation_available :
    let model := input.model guarded.step.effectCore other prior
    let code := input.admissionCoding guarded.step.effectCore other prior
    ∃ witness target,
      (model.constDen HOLLoadedPreparedEvent.symbol
        (HOLAdmissionCoding.preparationValue model code)
        (HOLAdmissionCoding.resultValue model code (HOLPreparedEffectEncoding.next guarded.step.effectCore))
        (code.states.symm (some ())) (code.firings.symm (some ⟨(), ()⟩)) witness target).down := by
  exact (HOLAdmissionEventSpecialization.prepared_exists_iff
    (input.model guarded.step.effectCore other prior) (input.admissionCoding guarded.step.effectCore other prior)
    (input.toInput.fullDomains guarded.step.effectCore other
      (HOLRunAdmissionJoin.Input.admissionPrior guarded.step.effectCore prior))
    (input.equations guarded.step.effectCore other prior) (HOLPreparedEffectEncoding.next guarded.step.effectCore)
    ()).mpr ⟨EventControls.prepared⟩

theorem base_loaded_event_refused :
    ¬(input.admittedValue guarded.step.effectCore other prior guarded.step.eventAdmission
      ((input.runCoding guarded.step.effectCore other prior).states.symm (some ()))
      ((input.runCoding guarded.step.effectCore other prior).events.symm
        (HOLPreparedEffectEncoding.toPacket guarded.step.effectCore EventControls.unfilteredEvent).val)
      ((input.runCoding guarded.step.effectCore other prior).states.symm (some ()))).down := by
  rw [input.admittedValue_eq_step]
  simp only [HOLRunSpecialization.stepValue, Equiv.apply_symm_apply]
  intro admitted
  obtain ⟨event, _⟩ := (HOLPreparedRunEncoding.step_iff_event guarded.step.effectCore
    guarded.step.eventAdmission () () _).mp admitted
  exact EventControls.guarded_event_absent ⟨event⟩

omit input other prior in
theorem base_prepared_payload_available :
    HOLObserverEncoding.Valid guarded.step.effectCore guarded.step.eventAdmission
      (payload.observer guarded.step.eventAdmission) ()
      (preparedPayload payload guarded.step.eventAdmission () EventControls.prepared) :=
  prepared_payload_valid payload guarded.step.eventAdmission () EventControls.prepared

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPublications
