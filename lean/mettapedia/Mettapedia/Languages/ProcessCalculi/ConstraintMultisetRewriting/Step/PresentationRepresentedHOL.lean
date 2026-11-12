import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRepresentedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin

/-!
# Represented source runs and the actual loaded HOL path operation

The source codecs apply only to represented data. The loaded model interprets
the unrestricted semantic effect and its admission directly. The connection
retains the complete semantic event word. Reflection to source executions
requires coverage of the declared permitted candidates at represented states;
the model itself neither supplies that coverage nor a semantic-state codec.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedHOL

open Interface Mettapedia.Languages.OpenTheory
open HOLPreparedRunEncoding HOLRunSpecialization

universe uO uT uH uOcc uS uF uR uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing) (allow : E.Admission)
  {Represented : Type uR} {Candidate : Represented → Type uC}
  (R : E.Representation Represented Candidate)
  (code : Encoding Represented Candidate) (decision : Decisions R.effect (R.admission allow))
  (input : HOLRunAdmissionJoin.Input)
  (other : TypeFamilySemantics.OperatorFamilies.{max uS uF})
  (prior : TypeFamilySemantics.Assignment.{max uS uF})

noncomputable def accepts (events : List (RawEvent E)) (source target : State) : Prop :=
  (input.operations.signature.pathValue (input.model E other prior)
    (input.admittedValue E other prior allow)
    (wordValue E _ _ (input.runCoding E other prior) (input.runAgreement E other prior) events)
    ((input.runCoding E other prior).states.symm (some source))
    ((input.runCoding E other prior).states.symm (some target))).down

theorem accepts_iff_path (events : List (RawEvent E)) (source target : State) :
    accepts E allow input other prior events source target ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject E allow) _ source target,
        word E allow path = events :=
  input.admitted_path_iff E other prior allow events source target

theorem source_run_preserves (start : EffectCore.EventObject R.effect (R.admission allow))
    (sourceRun : @Quiver.PathStar (RepresentedRuns.Source R allow code decision) _
      (code.state.view (sort := ()) start)) :
    accepts E allow input other prior
      (word E allow (RepresentedRuns.interpretRun R allow code decision start sourceRun).2)
      (R.state start) (RepresentedRuns.interpretRun R allow code decision start sourceRun).1 :=
  (accepts_iff_path E allow input other prior _ _ _).mpr ⟨_, rfl⟩

/-- Reflection preserves the exact received event word, while allowing a
represented endpoint whose interpretation is the semantic endpoint. -/
theorem source_run_reflects (coverage : R.Covers allow)
    (start : EffectCore.EventObject R.effect (R.admission allow))
    (events : List (RawEvent E)) (target : State)
    (accepted : accepts E allow input other prior events (R.state start) target) :
    ∃ sourceRun : @Quiver.PathStar (RepresentedRuns.Source R allow code decision) _
        (code.state.view (sort := ()) start),
      (RepresentedRuns.interpretRun R allow code decision start sourceRun).1 = target ∧
      word E allow (RepresentedRuns.interpretRun R allow code decision start sourceRun).2 = events := by
  obtain ⟨path, sameWord⟩ := (accepts_iff_path E allow input other prior events (R.state start) target).mp accepted
  obtain ⟨sourceRun, same⟩ := RepresentedRuns.covers_semantic_runs R allow code decision coverage start ⟨target, path⟩
  refine ⟨sourceRun, congrArg Sigma.fst same, ?_⟩
  exact (congrArg
    (fun run : @Quiver.PathStar (EffectCore.EventObject E allow) _ (R.state start) => word E allow run.2)
    same).trans sameWord

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedHOL
