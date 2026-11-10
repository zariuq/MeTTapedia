import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionEventSpecialization

/-! # One constructed interpretation of effects, preparations and permission

The event carrier and the earlier frame/store carriers share the same
definition-history model. Every permission profile is interpreted explicitly;
preparation existence agrees without selecting or enumerating candidates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionModel

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLPreparationEncoding

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing)

structure Agreement (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (frames : HOLFrameCoding.Coding model Obj Tm Hom) (occurrences : HOLOccurrenceCoding.Coding model O)
    (events : HOLAdmissionCoding.Coding model State Firing (HOLPreparedEffectEncoding.Witness E)) : Prop where
  definitions : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula
  effects : HOLSemanticEffectSpecialization.Agreement model X frames occurrences
  preparation : ∀ (s : State) (f : Firing s),
    (∃ p t, (model.constDen HOLLoadedPreparedEvent.symbol (HOLAdmissionCoding.preparationValue model events)
      (HOLAdmissionCoding.resultValue model events (HOLPreparedEffectEncoding.next E))
      (events.states.symm (some s)) (events.firings.symm (encodeFiring State Firing f)) p t).down) ↔ E.Prepares f
  admission : ∀ (allow : E.Admission) (s t : State), Nonempty
    (E.Event allow s t ≃ HOLAdmissionEventSpecialization.EventPacket model events
      (HOLPreparedEffectEncoding.next E) (HOLPreparedEffectEncoding.permits E allow) s t)

theorem constructed_agreement
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc uS uF})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc uS uF}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc uS uF)+1} AtomicTy Symbol)
      (frames : HOLFrameCoding.Coding actual Obj Tm Hom) (occurrences : HOLOccurrenceCoding.Coding actual O)
      (events : HOLAdmissionCoding.Coding actual State Firing (HOLPreparedEffectEncoding.Witness E)),
      Agreement E actual frames occurrences events := by
  obtain ⟨actual, same, full, equations⟩ := HOLAdmissionDomains.loaded_model_exists Obj Tm Hom O State Firing
    (HOLPreparedEffectEncoding.Witness E) other prior
  let frames := (HOLAdmissionDomains.frameCoding Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E)
    other prior).changeModel actual same
  let occurrences := HOLOccurrenceCoding.changeModel
    (HOLAdmissionDomains.occurrenceCoding Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E) other prior) actual same
  let events := (HOLAdmissionDomains.eventCoding Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E)
    other prior).changeModel actual same
  refine ⟨actual,frames,occurrences,events,equations,?_,?_,?_⟩
  · exact HOLSemanticEffectSpecialization.agreement_of_cache actual X frames occurrences full
      (HOLAdmissionDefinitions.earlier_equations actual equations)
  · intro s f
    exact (HOLAdmissionEventSpecialization.prepared_exists_iff actual events full equations
      (HOLPreparedEffectEncoding.next E) f).trans ⟨fun ⟨p⟩ => p,fun p => ⟨p⟩⟩
  · intro allow s t
    exact ⟨HOLAdmissionEventSpecialization.native_event_equiv actual full equations E events allow s t⟩

#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionModel
