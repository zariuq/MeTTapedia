import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedEventPaths

/-!
# Permission lifting into the existing endpoint-indexed runs

The event-path equivalence makes a permitted prepared word determine exactly
one existing run. The initial state and the complete prepared word are fixed;
equal final states alone do not determine a run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)

def preparedRunPath {source target : State} (run : {r : P.Run source // r.last = target}) :
    @Quiver.Path P.effectCore.PreparedObject _ source target :=
  P.effectCore.forgetEventPath P.eventAdmission (P.endpointPath run)

theorem preparedRunPath_injective {source target : State} :
    Function.Injective (P.preparedRunPath (source := source) (target := target)) := by
  intro first second same
  apply P.endpointPath_injective
  exact P.effectCore.forgetEventPath_injective P.eventAdmission same

theorem run_lift_exists_unique_iff {source target : State}
    (path : @Quiver.Path P.effectCore.PreparedObject _ source target) :
    (∃! run : {r : P.Run source // r.last = target}, P.preparedRunPath run = path) ↔
      GuardedPaths.Permitted (P.effectCore.admittedSubquiver P.eventAdmission) path := by
  constructor
  · rintro ⟨run, agrees, _⟩
    apply (P.effectCore.eventPath_exists_unique_iff P.eventAdmission path).mp
    refine ⟨P.endpointPath run, agrees, ?_⟩
    intro other same
    exact P.effectCore.forgetEventPath_injective P.eventAdmission (same.trans agrees.symm)
  · intro permitted
    obtain ⟨admitted, agrees, unique⟩ :=
      (P.effectCore.eventPath_exists_unique_iff P.eventAdmission path).mpr permitted
    have decoded : P.endpointPath (P.runOfEventPath admitted) = admitted :=
      (P.runPathEquiv source target).right_inv admitted
    refine ⟨P.runOfEventPath admitted, ?_, ?_⟩
    · exact (congrArg (P.effectCore.forgetEventPath P.eventAdmission) decoded).trans agrees
    · intro other same
      apply P.endpointPath_injective
      exact (unique _ same).trans decoded.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
