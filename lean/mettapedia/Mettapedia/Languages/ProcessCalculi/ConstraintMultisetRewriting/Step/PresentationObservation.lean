import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-! # Observations and OSLF across the event presentation

The generated future modality agrees with independently specified effects.
Stateful observations commute with the actual execution map on whole runs.
Neither statement erases records subsequently read by execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Interface

universe uO uT uH uOcc uS uF uR

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing) (allow : E.Admission)
  (code : Encoding State Firing) (decision : Decisions E allow)

theorem diamond_iff_candidate_event {s t : State} (f : Firing s) :
    langDiamondUsing (effectQueries E allow code decision).relations language
      (observation (effectQueries E allow code decision).relations
        (· = atState (code.state.view (sort := ()) t)))
      (request (code.state.view (sort := ()) s) (code.firing.view (sort := ()) ⟨s, f⟩)) ↔
      ∃ event : E.Event allow s t, event.firing = f := by
  rw [diamond_reads]
  simpa using execution_iff_event E allow code decision f

variable (observer : EventObserver.{0, 0, uR}
  (ExecutionObject (effectQueries E allow code decision)))

/-- Runtime-boundary observations interpret the same source event path. -/
theorem records_agree {s t : EffectCore.EventObject E allow}
    (path : Quiver.Path s t)
    (record : observer.Data ((executionMap E allow code decision).obj s)) :
    (observer.comap (executionMap E allow code decision)).evaluate path record =
      observer.evaluate ((executionMap E allow code decision).mapPath path) record :=
  observer.evaluate_comap _ path record

/-- Fixing the initial record gives exactly one observation-bearing execution
of each translated abstract run. -/
theorem recorded_execution_unique {s t : EffectCore.EventObject E allow}
    (path : Quiver.Path s t)
    (record : observer.Data ((executionMap E allow code decision).obj s)) :
    ∃! lifted : Quiver.PathStar
        (⟨(executionMap E allow code decision).obj s, record⟩ : observer.Observed),
      observer.forget.pathStar _ lifted =
        ⟨_, (executionMap E allow code decision).mapPath path⟩ :=
  observer.unique_lift _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
