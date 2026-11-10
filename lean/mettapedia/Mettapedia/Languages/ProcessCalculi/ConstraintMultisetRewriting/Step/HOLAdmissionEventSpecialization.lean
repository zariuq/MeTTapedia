import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedAdmittedEvent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionDomains
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedEffectEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticEffectSpecialization

/-! # Loaded preparation and admission preserve complete indexed events

The concrete carrier conversions connect the independently loaded predicates
to indexed witness packets. The resulting equivalence retains the candidate,
witness and endpoints, including distinct events with identical endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionEventSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLAdmissionCoding HOLPreparationEncoding

universe w uS uF uP

variable {State : Type uS} {Firing : State → Type uF} {Preparation : (s : State) → Firing s → Sort uP}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (code : Coding model State Firing Preparation)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem prepared_raw_iff (next : (s : State) → (f : Firing s) → Preparation s f → State)
    (s t : States State) (f : RawFirings State Firing) (p : RawWitnesses State Firing Preparation) :
    (model.constDen HOLLoadedPreparedEvent.symbol (preparationValue model code) (resultValue model code next)
      (code.states.symm s) (code.firings.symm f) (code.witnesses.symm p) (code.states.symm t)).down ↔
      prepares State Firing Preparation s f p ∧ t = result State Firing Preparation next p := by
  have evaluated := HOLLoadedPreparedEvent.operational_meaning model full equations
    (preparationValue model code) (resultValue model code next)
    (code.states.symm s) (code.states.symm t) (code.firings.symm f) (code.witnesses.symm p)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  simp only [preparationValue, resultValue, Equiv.apply_symm_apply]
  exact and_congr Iff.rfl code.states.symm.injective.eq_iff

include full equations in
theorem admitted_raw_iff (next : (s : State) → (f : Firing s) → Preparation s f → State)
    (allow : (s : State) → (f : Firing s) → Preparation s f → Prop)
    (s t : States State) (f : RawFirings State Firing) (p : RawWitnesses State Firing Preparation) :
    (model.constDen HOLLoadedAdmittedEvent.symbol (preparationValue model code) (resultValue model code next)
      (permissionValue model code allow) (code.states.symm s) (code.firings.symm f)
      (code.witnesses.symm p) (code.states.symm t)).down ↔
      prepares State Firing Preparation s f p ∧ t = result State Firing Preparation next p ∧
        permission State Firing Preparation allow p := by
  have evaluated := HOLLoadedAdmittedEvent.operational_meaning model full equations
    (preparationValue model code) (permissionValue model code allow) (resultValue model code next)
    (code.states.symm s) (code.states.symm t) (code.firings.symm f) (code.witnesses.symm p)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  simp only [preparationValue, resultValue, permissionValue, Equiv.apply_symm_apply]
  exact and_congr Iff.rfl (and_congr code.states.symm.injective.eq_iff Iff.rfl)

include full equations in
theorem prepared_exists_iff (next : (s : State) → (f : Firing s) → Preparation s f → State)
    {s : State} (f : Firing s) :
    (∃ p t, (model.constDen HOLLoadedPreparedEvent.symbol (preparationValue model code) (resultValue model code next)
      (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f)) p t).down) ↔
      Nonempty (Preparation s f) := by
  constructor
  · rintro ⟨p,t,valid⟩
    have evaluated := HOLLoadedPreparedEvent.operational_meaning model full equations
      (preparationValue model code) (resultValue model code next)
      (code.states.symm (some s)) t (code.firings.symm (encodeFiring State Firing f)) p
    exact (HOLAdmissionCoding.preparation_exists_iff model code f).mp
      ⟨p, ((iff_of_eq (congrArg ULift.down evaluated)).mp valid).1⟩
  · rintro ⟨p⟩
    refine ⟨code.witnesses.symm (encodeWitness State Firing Preparation f p),
      code.states.symm (some (next s f p)), ?_⟩
    apply (prepared_raw_iff model code full equations next (some s) (some (next s f p))
      (encodeFiring State Firing f) (encodeWitness State Firing Preparation f p)).mpr
    exact ⟨prepares_encoded State Firing Preparation f p,rfl⟩

abbrev EventPacket (next : (s : State) → (f : Firing s) → Preparation s f → State)
    (allow : (s : State) → (f : Firing s) → Preparation s f → Prop) (s t : State) :=
  { pair : HOL.Ty.denote.{0,w+1} model.Carrier firingType × HOL.Ty.denote.{0,w+1} model.Carrier witnessType //
    (model.constDen HOLLoadedAdmittedEvent.symbol (preparationValue model code) (resultValue model code next)
      (permissionValue model code allow) (code.states.symm (some s)) pair.1 pair.2 (code.states.symm (some t))).down }

include full equations in
def packetEquiv (next : (s : State) → (f : Firing s) → Preparation s f → State)
    (allow : (s : State) → (f : Firing s) → Preparation s f → Prop) (s t : State) :
    EventPacket model code next allow s t ≃
      { pair : RawFirings State Firing × RawWitnesses State Firing Preparation //
        prepares State Firing Preparation (some s) pair.1 pair.2 ∧
        some t = result State Firing Preparation next pair.2 ∧ permission State Firing Preparation allow pair.2 } where
  toFun packet := ⟨(code.firings packet.1.1, code.witnesses packet.1.2),
    (admitted_raw_iff model code full equations next allow (some s) (some t) _ _).mp
      (by simpa only [Equiv.symm_apply_apply] using packet.2)⟩
  invFun packet := ⟨(code.firings.symm packet.1.1, code.witnesses.symm packet.1.2),
    (admitted_raw_iff model code full equations next allow (some s) (some t) _ _).mpr packet.2⟩
  left_inv packet := by
    apply Subtype.ext
    exact Prod.ext (code.firings.symm_apply_apply _) (code.witnesses.symm_apply_apply _)
  right_inv packet := by
    apply Subtype.ext
    exact Prod.ext (code.firings.apply_symm_apply _) (code.witnesses.apply_symm_apply _)

universe uO uT uH uOcc

include full equations in
def native_event_equiv {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
    (E : EffectCore X O State Firing)
    (encoding : Coding model State Firing (HOLPreparedEffectEncoding.Witness E))
    (allow : E.Admission) (s t : State) : E.Event allow s t ≃
      EventPacket model encoding (HOLPreparedEffectEncoding.next E) (HOLPreparedEffectEncoding.permits E allow) s t :=
  (HOLPreparedEffectEncoding.eventEquiv E allow s t).trans
    (packetEquiv model encoding full equations (HOLPreparedEffectEncoding.next E)
      (HOLPreparedEffectEncoding.permits E allow) s t).symm

include full equations in
theorem native_event_firing {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
    (E : EffectCore X O State Firing)
    (encoding : Coding model State Firing (HOLPreparedEffectEncoding.Witness E))
    (allow : E.Admission) {s t : State} (event : E.Event allow s t) :
    encoding.firings (native_event_equiv model full equations E encoding allow s t event).1.1 =
      encodeFiring State Firing event.firing := by
  change encoding.firings (encoding.firings.symm (encodeFiring State Firing event.firing)) = _
  exact encoding.firings.apply_symm_apply _

#print axioms prepared_raw_iff
#print axioms admitted_raw_iff
#print axioms packetEquiv
#print axioms native_event_equiv
#print axioms prepared_exists_iff
#print axioms native_event_firing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionEventSpecialization
