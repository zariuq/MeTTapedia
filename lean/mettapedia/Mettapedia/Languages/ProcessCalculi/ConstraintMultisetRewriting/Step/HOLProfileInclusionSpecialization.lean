import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedProfileInclusion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionEventSpecialization

/-! # Loaded profile inclusion is relative to genuine preparations

The law concerns the domain admitted by the first profile. It supplies the
existing event restriction without changing the candidate or witness data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLProfileInclusionSpecialization

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
theorem inclusion_iff (first second : (s : State) → (f : Firing s) → Preparation s f → Prop) :
    (model.constDen HOLLoadedProfileInclusion.symbol (preparationValue model code)
      (permissionValue model code first) (permissionValue model code second)).down ↔
      ∀ s f p, first s f p → second s f p := by
  have evaluated := HOLLoadedProfileInclusion.operational_meaning model full equations
    (preparationValue model code) (permissionValue model code first) (permissionValue model code second)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  constructor
  · intro included s f p allowed
    have actual := included (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f))
      (code.witnesses.symm (encodeWitness State Firing Preparation f p))
      (by simpa only [preparationValue, Equiv.apply_symm_apply] using prepares_encoded State Firing Preparation f p)
      ((permission_at model code first f p).mpr allowed)
    exact (permission_at model code second f p).mp actual
  · intro included s f p _ allowed
    change permission State Firing Preparation first (code.witnesses p) at allowed
    change permission State Firing Preparation second (code.witnesses p)
    cases raw : code.witnesses p with
    | none => simp only [raw, permission] at allowed
    | some witness =>
        rcases witness with ⟨⟨source,candidate⟩,prepared⟩
        exact included source candidate prepared.down (by simpa only [raw, permission] using allowed)

universe uO uT uH uOcc

include full equations in
theorem effect_inclusion_iff {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] (E : EffectCore X O State Firing)
    (encoding : Coding model State Firing (HOLPreparedEffectEncoding.Witness E)) (first second : E.Admission) :
    (model.constDen HOLLoadedProfileInclusion.symbol (preparationValue model encoding)
      (permissionValue model encoding (HOLPreparedEffectEncoding.permits E first))
      (permissionValue model encoding (HOLPreparedEffectEncoding.permits E second))).down ↔
      ∀ {s : State} (f : Firing s) (p : E.Prepares f), first f p → second f p :=
  inclusion_iff model encoding full equations (HOLPreparedEffectEncoding.permits E first) (HOLPreparedEffectEncoding.permits E second)

include full equations in
theorem restriction_keeps_packet {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] (E : EffectCore X O State Firing)
    (encoding : Coding model State Firing (HOLPreparedEffectEncoding.Witness E)) (first second : E.Admission)
    (included : ∀ {s : State} (f : Firing s) (p : E.Prepares f), first f p → second f p)
    {s t : State} (event : E.Event first s t) :
    (HOLAdmissionEventSpecialization.native_event_equiv model full equations E encoding second s t
      (EffectCore.Event.restrict E included event)).1 =
      (HOLAdmissionEventSpecialization.native_event_equiv model full equations E encoding first s t event).1 := by
  rfl

#print axioms inclusion_iff
#print axioms effect_inclusion_iff
#print axioms restriction_keeps_packet

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLProfileInclusionSpecialization
