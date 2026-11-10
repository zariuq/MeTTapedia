import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mathlib.CategoryTheory.PathCategory.Basic

/-! # The free category of admitted events

The quiver retains complete candidates, rather than just their endpoints or
observable labels. Its path category has the universal property for arbitrary
target categories. No scheduler or trace quotient is part of this construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open CategoryTheory

universe uO uT uH uOcc uS uF uV uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

namespace EffectCore

/-- A separate object carrier prevents competing quiver instances on `State`. -/
def EventObject (E : EffectCore X O State Firing) (_allow : E.Admission) := State

instance eventQuiver (E : EffectCore X O State Firing) (allow : E.Admission) :
    Quiver (EventObject E allow) where
  Hom s t := E.Event allow s t

abbrev RunCategory (E : EffectCore X O State Firing) (allow : E.Admission) :=
  Paths (EventObject E allow)

variable (E : EffectCore X O State Firing) (allow : E.Admission)

/-- Extend a generator interpretation; composition is fixed by the target category. -/
def interpret {C : Type uC} [Category.{uV} C] (generators : EventObject E allow ⥤q C) :
    RunCategory E allow ⥤ C := Paths.lift generators

/-- Initiality relative to the generating event quiver. -/
theorem interpretation_exists_unique {C : Type uC} [Category.{uV} C]
    (generators : EventObject E allow ⥤q C) :
    ∃! interpretation : RunCategory E allow ⥤ C,
      Paths.of (EventObject E allow) ⋙q interpretation.toPrefunctor = generators := by
  refine ⟨E.interpret allow generators, Paths.lift_spec generators, ?_⟩
  intro other agrees
  exact Paths.lift_unique generators other agrees

/-- Restriction maps events, without changing their underlying candidate. -/
def inclusion {first second : E.Admission}
    (included : ∀ {s : State} (f : Firing s) (p : E.Prepares f), first f p → second f p) :
    EventObject E first ⥤q EventObject E second where
  obj s := s
  map e := e.restrict E included

def includeRuns {first second : E.Admission}
    (included : ∀ {s : State} (f : Firing s) (p : E.Prepares f), first f p → second f p) :
    RunCategory E first ⥤ RunCategory E second :=
  Paths.lift (E.inclusion included ⋙q Paths.of (EventObject E second))

/-- Pullback through a path is composed in reverse execution order. -/
def pathAlong : ∀ {s t : EventObject E allow}, Quiver.Path s t → Hom (E.frame s) (E.frame t)
  | s, _, .nil => X.id (E.frame s)
  | _, _, .cons path event => X.comp (E.eventAlong event) (pathAlong path)

theorem path_models : ∀ {s t : EventObject E allow} (path : Quiver.Path s t)
    {b : Obj} (σ : Hom (E.frame t) b), X.Models σ (E.knowledge t) →
      X.Models (X.comp σ (E.pathAlong allow path)) (E.knowledge s)
  | _, _, .nil, _, σ, solved => by
      simp only [pathAlong]
      exact (Frames.models_congr (fun t => Frames.act_comp_id σ t) _).mp solved
  | _, _, .cons path event, _, σ, solved => by
      simp only [pathAlong]
      have back := path_models path _ (E.event_models event σ solved)
      exact (Frames.models_congr
        (fun t => Frames.act_comp_assoc (E.pathAlong allow path) (E.eventAlong event) σ t) _).mp back

end EffectCore

namespace Step

variable (P : Step X O State Firing)

/-- The existing dependent run embeds without identifying any of its firings. -/
def Run.eventPath : {s : State} → (r : P.Run s) →
    @Quiver.Path (EffectCore.EventObject P.effectCore P.eventAdmission) _ s r.last
  | _, .nil _ => .nil
  | _, .cons f admitted rest =>
      (Quiver.Path.cons Quiver.Path.nil (P.event f admitted)).comp (eventPath rest)

/-- Read complete candidate data from a path. -/
def eventWord : ∀ {s t : EffectCore.EventObject P.effectCore P.eventAdmission},
    Quiver.Path s t → List ((s : State) × Firing s)
  | _, _, .nil => []
  | _, _, .cons path e => eventWord path ++ [⟨_, e.firing⟩]

theorem eventWord_comp : ∀ {s t u : EffectCore.EventObject P.effectCore P.eventAdmission}
    (first : Quiver.Path s t) (second : Quiver.Path t u),
    P.eventWord (first.comp second) = P.eventWord first ++ P.eventWord second := by
  intro s t u first second
  induction second with
  | nil => simp [eventWord]
  | cons rest e ih => simp only [Quiver.Path.comp_cons, eventWord, ih, List.append_assoc]

theorem Run.eventPath_word : ∀ {s : State} (r : P.Run s),
    P.eventWord (r.eventPath P) = r.word
  | _, .nil _ => by simp [Run.eventPath, eventWord, Run.word]
  | _, .cons f admitted rest => by
      rw [Run.eventPath, P.eventWord_comp, Run.eventPath_word]
      simp [eventWord, event, Run.word]

/-- Complete firing words determine admitted runs; proof certificates add no branch data. -/
theorem Run.eq_of_word_eq : ∀ {s : State} (first second : P.Run s),
    first.word = second.word → first = second
  | _, .nil _, .nil _, _ => rfl
  | _, .nil _, .cons _ _ _, same => by simp [Run.word] at same
  | _, .cons _ _ _, .nil _, same => by simp [Run.word] at same
  | _, .cons f a rest, .cons g b later, same => by
      have parts := List.cons.inj same
      have firing_eq : f = g := eq_of_heq (Sigma.mk.inj parts.1).2
      subst g
      have tail_eq := eq_of_word_eq rest later parts.2
      subst later
      rfl

theorem eventWord_cast {s t u : EffectCore.EventObject P.effectCore P.eventAdmission}
    (path : Quiver.Path s t) (same : t = u) :
    P.eventWord (same ▸ path) = P.eventWord path := by
  cases same
  rfl

/-- The endpoint-indexed encoding retains the actual firing word. -/
def endpointPath {s t : State} (run : {r : P.Run s // r.last = t}) :
    @Quiver.Path (EffectCore.EventObject P.effectCore P.eventAdmission) _ s t :=
  run.property ▸ run.val.eventPath P

theorem endpointPath_word {s t : State} (run : {r : P.Run s // r.last = t}) :
    P.eventWord (P.endpointPath run) = run.val.word := by
  rcases run with ⟨run, ends⟩
  cases ends
  exact Run.eventPath_word P run

/-- Existing runs are represented faithfully in each hom of the event category. -/
theorem endpointPath_injective {s t : State} :
    Function.Injective (P.endpointPath (s := s) (t := t)) := by
  intro first second same
  apply Subtype.ext
  apply Run.eq_of_word_eq P
  have words := congrArg (P.eventWord) same
  simpa only [endpointPath_word] using words

/-- Reconstruct a run from a complete event path, retaining its endpoint. -/
def runOfEventPath {s : EffectCore.EventObject P.effectCore P.eventAdmission} :
    {t : EffectCore.EventObject P.effectCore P.eventAdmission} → Quiver.Path s t →
      {r : P.Run s // r.last = t}
  | _, .nil => ⟨.nil s, rfl⟩
  | _, .cons path e => by
      obtain ⟨run, ends⟩ := runOfEventPath path
      have admitted := (P.eventAdmission_iff e.firing e.prepared).mp e.permitted
      let tail : P.Run _ := .cons e.firing admitted (.nil _)
      refine ⟨run.append (ends.symm ▸ tail), ?_⟩
      rw [Run.last_append]
      cases ends
      exact e.target_eq

theorem runOfEventPath_word {s t : EffectCore.EventObject P.effectCore P.eventAdmission}
    (path : Quiver.Path s t) : (P.runOfEventPath path).val.word = P.eventWord path := by
  induction path with
  | nil => simp [runOfEventPath, Run.word, eventWord]
  | cons path e ih =>
      rw [runOfEventPath]
      generalize decoded_eq : P.runOfEventPath path = decoded at *
      rcases decoded with ⟨run, ends⟩
      cases ends
      simpa only [Run.word_append, Run.word, eventWord] using
        congrArg (fun word => word ++ [⟨run.last, e.firing⟩]) ih

/-- Two paths with the same complete candidate word are the same path. -/
theorem eventWord_injective {s t : EffectCore.EventObject P.effectCore P.eventAdmission} :
    Function.Injective (P.eventWord (s := s) (t := t)) := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons path e => simp [eventWord] at same
  | cons path e ih =>
      intro second same
      cases second with
      | nil => simp [eventWord] at same
      | cons other edge =>
          simp only [eventWord] at same
          have parts := List.append_inj' same (by rfl)
          have last_eq := (List.cons.inj parts.2).1
          obtain ⟨state_eq, firing_eq⟩ := Sigma.mk.inj last_eq
          cases state_eq
          have same_firing := eq_of_heq firing_eq
          have same_edge : e = edge := by
            cases e
            cases edge
            cases same_firing
            rfl
          subst edge
          rw [ih parts.1]

/-- Endpoint-indexed admitted runs and complete event paths are equivalent. -/
def runPathEquiv (s t : State) :
    {r : P.Run s // r.last = t} ≃
      @Quiver.Path (EffectCore.EventObject P.effectCore P.eventAdmission) _ s t where
  toFun := P.endpointPath
  invFun := P.runOfEventPath
  left_inv run := by
    apply Subtype.ext
    apply Run.eq_of_word_eq P
    rw [runOfEventPath_word, endpointPath_word]
  right_inv path := by
    apply P.eventWord_injective
    rw [endpointPath_word, runOfEventPath_word]

theorem endpointPath_identity (s : State) :
    P.endpointPath ⟨Run.nil (P := P) s, rfl⟩ = Quiver.Path.nil := by
  apply P.eventWord_injective
  rw [endpointPath_word]
  simp [Run.word, eventWord]

/-- The equivalence preserves composition, not just the sets of paths. -/
theorem endpointPath_append {s : State} (first : P.Run s) (second : P.Run first.last) :
    P.endpointPath ⟨first.append second, first.last_append second⟩ =
      (first.eventPath P).comp (second.eventPath P) := by
  apply P.eventWord_injective
  rw [endpointPath_word, eventWord_comp, Run.eventPath_word, Run.eventPath_word, Run.word_append]

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
