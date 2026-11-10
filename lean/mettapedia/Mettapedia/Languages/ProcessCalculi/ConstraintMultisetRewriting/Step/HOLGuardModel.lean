import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLGuardSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLProfileInclusionSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionModel

/-! # One constructed model for the explicit admission constructors

The same model interprets effects and events, all future solution morphisms,
the guard constructor, readiness-based preparation and profile inclusion.
The general admission interface continues to admit arbitrary predicates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLGuardModel

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLPreparationEncoding HOLSolutionCoding

universe w uO uT uH uOcc uS uF uP

def initialSolutions (Obj : Type uO) (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (O : Type uOcc)
    (State : Type uS) (Firing : State → Type uF) (Preparation : (s : State) → Firing s → Sort uP)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc uS uF uP}) :
    Coding (HOLAdmissionDomains.initial Obj Tm Hom O State Firing Preparation other prior) Obj Hom :=
  (HOLAdmissionDomains.parameterCoding Obj Tm Hom O State Firing Preparation other prior .solutions).trans Equiv.ulift

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing)

structure Agreement (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (frames : HOLFrameCoding.Coding model Obj Tm Hom) (occurrences : HOLOccurrenceCoding.Coding model O)
    (events : HOLAdmissionCoding.Coding model State Firing (HOLPreparedEffectEncoding.Witness E))
    (solutions : Coding model Obj Hom) : Prop extends toAdmission : HOLAdmissionModel.Agreement E model frames occurrences events where
  guard : ∀ (holds : {s : State} → (f : Firing s) → (b : Obj) → Hom (E.target f) b → Prop)
    (s : State) (f : Firing s) (p : E.Prepares f),
    (model.constDen HOLLoadedGuardProfile.symbol (solutionsValue model X events solutions E.target E.information)
      (holdsValue model events solutions E.target (fun _ f _ => holds f))
      (events.states.symm (some s)) (events.firings.symm (encodeFiring State Firing f))
      (events.witnesses.symm (encodeWitness State Firing (HOLPreparedEffectEncoding.Witness E) f p))).down ↔
      E.guardAdmission holds f p
  prepared : ∀ (s : State) (f : Firing s) (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType),
    (model.constDen HOLLoadedSolutionPreparation.symbol (readyValue model events (HOLGuardSpecialization.effectReady E))
      (solutionsValue model X events solutions E.target E.information) (HOLAdmissionCoding.preparationValue model events)
      (events.states.symm (some s)) (events.firings.symm (encodeFiring State Firing f)) p).down ↔
      (HOLAdmissionCoding.preparationValue model events (events.states.symm (some s))
        (events.firings.symm (encodeFiring State Firing f)) p).down
  inclusion : ∀ (first second : E.Admission),
    (model.constDen HOLLoadedProfileInclusion.symbol (HOLAdmissionCoding.preparationValue model events)
      (HOLAdmissionCoding.permissionValue model events (HOLPreparedEffectEncoding.permits E first))
      (HOLAdmissionCoding.permissionValue model events (HOLPreparedEffectEncoding.permits E second))).down ↔
      ∀ {s : State} (f : Firing s) (p : E.Prepares f), first f p → second f p

theorem constructed_agreement
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc uS uF})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc uS uF}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc uS uF)+1} AtomicTy Symbol)
      (frames : HOLFrameCoding.Coding actual Obj Tm Hom) (occurrences : HOLOccurrenceCoding.Coding actual O)
      (events : HOLAdmissionCoding.Coding actual State Firing (HOLPreparedEffectEncoding.Witness E))
      (solutions : Coding actual Obj Hom), Agreement E actual frames occurrences events solutions := by
  obtain ⟨actual,same,full,equations⟩ := HOLAdmissionDomains.loaded_model_exists Obj Tm Hom O State Firing
    (HOLPreparedEffectEncoding.Witness E) other prior
  let frames := (HOLAdmissionDomains.frameCoding Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E)
    other prior).changeModel actual same
  let occurrences := HOLOccurrenceCoding.changeModel
    (HOLAdmissionDomains.occurrenceCoding Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E) other prior) actual same
  let events := (HOLAdmissionDomains.eventCoding Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E)
    other prior).changeModel actual same
  let solutions := HOLSolutionCoding.changeModel
    (initialSolutions Obj Tm Hom O State Firing (HOLPreparedEffectEncoding.Witness E) other prior) actual same
  refine ⟨actual,frames,occurrences,events,solutions,?_,?_,?_,?_⟩
  · refine ⟨equations, ?_, ?_, ?_⟩
    · exact HOLSemanticEffectSpecialization.agreement_of_cache actual X frames occurrences full
        (HOLAdmissionDefinitions.earlier_equations actual equations)
    · intro s f
      exact (HOLAdmissionEventSpecialization.prepared_exists_iff actual events full equations
        (HOLPreparedEffectEncoding.next E) f).trans ⟨fun ⟨p⟩ => p,fun p => ⟨p⟩⟩
    · intro allow s t
      exact ⟨HOLAdmissionEventSpecialization.native_event_equiv actual full equations E events allow s t⟩
  · intro holds s f p
    exact HOLGuardSpecialization.effect_guard_iff actual X solutions full equations E events holds f p
  · intro s f p
    exact HOLGuardSpecialization.effect_preparation_iff actual X solutions full equations E events f p
  · intro first second
    exact HOLProfileInclusionSpecialization.effect_inclusion_iff actual full equations E events first second

#print axioms initialSolutions
#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLGuardModel
