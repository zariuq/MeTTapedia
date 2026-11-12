import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedWordPackets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunSpecialization

/-!
# The loaded prepared-word operators on native indexed packets

The source state and event equivalences are the existing run encoding.
Preparation and permission are interpreted independently, and the target
operation agrees even on refused proposals. The domain is equivalent to
existence of a native event path with the complete specified word.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open HOLPreparedRunEncoding HOLPreparationEncoding

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)
  (signature : HOLPreparedWordSemantics.Signature)
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (code : HOLRunSpecialization.Coding E signature.runs model)
  (agreement : HOLPreparedWordReadback.Correspondence signature model)

def preparationValue : signature.State model → signature.Event model → ULift.{w+1} Prop :=
  fun source event => ULift.up (HOLPreparedWordPackets.preparation E (code.states source) (code.events event))

def resultValue : signature.State model → signature.Event model → signature.State model :=
  fun source event => code.states.symm (HOLPreparedWordPackets.result E (code.states source) (code.events event))

def permissionValue (allow : E.Admission) : signature.State model → signature.Event model → ULift.{w+1} Prop :=
  fun source event => ULift.up (HOLPreparedWordPackets.permission E allow (code.states source) (code.events event))

def wordValue (events : List (RawEvent E)) : signature.runs.lists.Carrier model :=
  HOLRunSpecialization.wordValue E signature.runs model code agreement.runs events

theorem target_native (events : List (RawEvent E)) (source : States State) :
    signature.targetValue model (resultValue E signature model code)
      (wordValue E signature model code agreement events) (code.states.symm source) =
        code.states.symm (PreparedWords.target (HOLPreparedWordPackets.result E) events source) := by
  exact (agreement.target _ _ _).trans
    (PreparedWords.result_transport code.states code.events (HOLPreparedWordPackets.result E) events source)

theorem domain_native (allow : E.Admission) (events : List (RawEvent E)) (source : States State) :
    (signature.domainValue model (preparationValue E signature model code) (resultValue E signature model code)
      (permissionValue E signature model code allow) (wordValue E signature model code agreement events)
      (code.states.symm source)).down ↔
        PreparedWords.Domain (HOLPreparedWordPackets.preparation E) (HOLPreparedWordPackets.result E)
          (HOLPreparedWordPackets.permission E allow) events source :=
  (agreement.domain _ _ _ _ _).trans
    (PreparedWords.domain_transport code.states code.events (HOLPreparedWordPackets.preparation E)
      (HOLPreparedWordPackets.result E) (HOLPreparedWordPackets.permission E allow) events source)

theorem native_path_iff (allow : E.Admission) (events : List (RawEvent E)) (source destination : State) :
    ((signature.domainValue model (preparationValue E signature model code) (resultValue E signature model code)
      (permissionValue E signature model code allow) (wordValue E signature model code agreement events)
      (code.states.symm (some source))).down ∧
      code.states.symm (some destination) = signature.targetValue model (resultValue E signature model code)
        (wordValue E signature model code agreement events) (code.states.symm (some source))) ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source destination,
        HOLPreparedRunEncoding.word E allow path = events := by
  rw [domain_native, target_native, code.states.symm.injective.eq_iff]
  exact (HOLPreparedWordPackets.native_path_iff E allow events source destination).symm

theorem domain_iff_native_path_exists (allow : E.Admission) (events : List (RawEvent E)) (source : State) :
    (signature.domainValue model (preparationValue E signature model code) (resultValue E signature model code)
      (permissionValue E signature model code allow) (wordValue E signature model code agreement events)
      (code.states.symm (some source))).down ↔
        ∃ (destination : State) (path : @Quiver.Path (EffectCore.EventObject E allow) _ source destination),
          HOLPreparedRunEncoding.word E allow path = events :=
  (domain_native E signature model code agreement allow events (some source)).trans
    (HOLPreparedWordPackets.domain_iff_native_path_exists E allow events source)

theorem domain_append (allow : E.Admission) (first second : List (RawEvent E)) (source : States State) :
    (signature.domainValue model (preparationValue E signature model code) (resultValue E signature model code)
      (permissionValue E signature model code allow) (wordValue E signature model code agreement (first ++ second))
      (code.states.symm source)).down ↔
    (signature.domainValue model (preparationValue E signature model code) (resultValue E signature model code)
      (permissionValue E signature model code allow) (wordValue E signature model code agreement first)
      (code.states.symm source)).down ∧
    (signature.domainValue model (preparationValue E signature model code) (resultValue E signature model code)
      (permissionValue E signature model code allow) (wordValue E signature model code agreement second)
      (signature.targetValue model (resultValue E signature model code)
        (wordValue E signature model code agreement first) (code.states.symm source))).down := by
  rw [domain_native, target_native, domain_native, domain_native]
  exact PreparedWords.domain_append _ _ _ _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordSpecialization
