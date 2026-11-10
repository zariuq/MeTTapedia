import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-!
# Existing escaping runs are the unique observer lifts

The escaping step and the admitted-event observer have the same transition
data, including the transported public terms and appended relations. Their
maps agree on complete firing words. The existing escaping run therefore
constructs the unique decorated path above its original forgotten run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

namespace Transport.Escape

variable (D : T.Escape)

def observedState (source : Escaped P) : D.eventObserver.Observed :=
  ⟨source.state, source.names, source.record⟩

def forgetEvents : EffectCore.EventObject D.step.effectCore D.step.eventAdmission ⥤q
    EffectCore.EventObject P.effectCore P.eventAdmission where
  obj source := source.state
  map event := ⟨event.firing, event.prepared, event.permitted, congrArg Escaped.state event.target_eq⟩

def liftEvents : EffectCore.EventObject D.step.effectCore D.step.eventAdmission ⥤q D.eventObserver.Observed where
  obj := D.observedState
  map event := {
    event := D.forgetEvents.map event
    recorded := by
      rcases event with ⟨firing, prepared, permitted, ends⟩
      cases ends
      rfl }

theorem forget_liftEvents : D.liftEvents ⋙q D.eventObserver.forget = D.forgetEvents := rfl

theorem forgetEvents_word {source target : EffectCore.EventObject D.step.effectCore D.step.eventAdmission}
    (path : Quiver.Path source target) :
    P.eventWord (D.forgetEvents.mapPath path) =
      (D.step.eventWord path).map (fun entry => ⟨entry.1.state, entry.2⟩) := by
  induction path with
  | nil => simp only [Prefunctor.mapPath_nil, Step.eventWord, List.map_nil]
  | cons path event ih =>
      simp only [Prefunctor.mapPath_cons, Step.eventWord, ih, List.map_append, List.map_cons, List.map_nil]
      rfl

theorem forgotten_last : ∀ {source : Escaped P} (run : D.step.Run source),
    (D.forget run).last = run.last.state
  | _, .nil _ => rfl
  | _, .cons _ _ rest => forgotten_last rest

theorem forgotten_word : ∀ {source : Escaped P} (run : D.step.Run source),
    (D.forget run).word = run.word.map (fun entry => ⟨entry.1.state, entry.2⟩)
  | _, .nil _ => rfl
  | _, .cons _ _ rest => congrArg (List.cons _) (forgotten_word rest)

/-- The path map forgets exactly the same data as the established run map. -/
theorem forgetEvents_run {source : Escaped P} (run : D.step.Run source) :
    D.forgetEvents.mapPath (run.eventPath D.step) =
      P.endpointPath ⟨D.forget run, D.forgotten_last run⟩ := by
  apply P.eventWord_injective
  rw [D.forgetEvents_word, Step.Run.eventPath_word, Step.endpointPath_word, D.forgotten_word]

theorem lifted_run_erases {source : Escaped P} (run : D.step.Run source) :
    D.eventObserver.forget.mapPath (D.liftEvents.mapPath (run.eventPath D.step)) =
      P.endpointPath ⟨D.forget run, D.forgotten_last run⟩ := by
  calc
    _ = (D.liftEvents ⋙q D.eventObserver.forget).mapPath (run.eventPath D.step) :=
      (Prefunctor.mapPath_comp_apply _ _ _).symm
    _ = D.forgetEvents.mapPath (run.eventPath D.step) := rfl
    _ = _ := D.forgetEvents_run run

/-- The actual escaping execution is the unique decorated path above its
forgotten run when the initial public terms and record are fixed. -/
theorem escaping_run_unique {source : Escaped P} (run : D.step.Run source)
    (other : Quiver.PathStar (D.observedState source))
    (erases : D.eventObserver.forget.pathStar (D.observedState source) other =
      ⟨run.last.state, P.endpointPath ⟨D.forget run, D.forgotten_last run⟩⟩) :
    other = D.liftEvents.pathStar source ⟨run.last, run.eventPath D.step⟩ := by
  apply Prefunctor.pathStar_injective D.eventObserver.forget D.eventObserver.forget_star_injective
    (D.observedState source)
  refine erases.trans ?_
  change (⟨run.last.state, P.endpointPath ⟨D.forget run, D.forgotten_last run⟩⟩ :
    @Quiver.PathStar (EffectCore.EventObject P.effectCore P.eventAdmission) _ source.state) =
      ⟨run.last.state, D.eventObserver.forget.mapPath (D.liftEvents.mapPath (run.eventPath D.step))⟩
  rw [D.lifted_run_erases]

end Transport.Escape

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
