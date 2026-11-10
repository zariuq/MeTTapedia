import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedRunEncoding
import Mettapedia.Languages.HOLLight.RunSourceReadback

/-!
# The loaded path operation on native admitted-event packets

State and event carrier conversions turn the source path operation into the
raw prepared-event relation. The finite-run equivalence retains the entire
candidate/preparation word and fixes the admission profile throughout a run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open RunModelCorrespondence HOLPreparedRunEncoding HOLPreparationEncoding

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (E : EffectCore X O State Firing)

structure Coding (signature : RunModelCorrespondence.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) where
  states : signature.State model ≃ States State
  events : signature.lists.Element model ≃ RawEvent E

variable (signature : RunModelCorrespondence.Signature)
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (code : Coding E signature model)
  (agreement : RunSourceReadback.Correspondence signature model)

def stepValue (allow : E.Admission) :
    signature.State model → signature.lists.Element model → signature.State model → ULift.{w+1} Prop :=
  fun source event target => ULift.up
    (HOLPreparedRunEncoding.step E allow (code.states source) (code.events event) (code.states target))

def wordValue (events : List (RawEvent E)) : signature.lists.Carrier model :=
  agreement.lists.equivalence (events.map code.events.symm)

theorem raw_path_iff (allow : E.Admission) (events : List (RawEvent E))
    (source target : States State) :
    (signature.pathValue model (stepValue E signature model code allow)
      (wordValue E signature model code agreement events)
      (code.states.symm source) (code.states.symm target)).down ↔
      WordRun (HOLPreparedRunEncoding.step E allow) events source target := by
  exact (agreement.path _ _ _ _).trans
    (wordRun_transport code.states code.events (HOLPreparedRunEncoding.step E allow) events source target)

theorem native_path_iff (allow : E.Admission) (events : List (RawEvent E)) (source target : State) :
    (signature.pathValue model (stepValue E signature model code allow)
      (wordValue E signature model code agreement events)
      (code.states.symm (some source)) (code.states.symm (some target))).down ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source target,
        HOLPreparedRunEncoding.word E allow path = events :=
  (raw_path_iff E signature model code agreement allow events (some source) (some target)).trans
    (HOLPreparedRunEncoding.finite_run_iff E allow events source target)

theorem wordValue_injective : Function.Injective (wordValue E signature model code agreement) := by
  intro first second same
  apply List.map_injective_iff.mpr code.events.symm.injective
  exact agreement.lists.equivalence.injective same

theorem encoded_native_path (allow : E.Admission) {source target : EffectCore.EventObject E allow}
    (path : Quiver.Path source target) :
    (signature.pathValue model (stepValue E signature model code allow)
      (wordValue E signature model code agreement (HOLPreparedRunEncoding.word E allow path))
      (code.states.symm (some source)) (code.states.symm (some target))).down :=
  (native_path_iff E signature model code agreement allow _ source target).mpr ⟨path, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunSpecialization
