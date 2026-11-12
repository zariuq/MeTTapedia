import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-!
# Finite paths of represented effects

Candidate coverage is relative to the declared admission profile at represented
states. It is separate from closure under preparation and need not hold for
all mathematical native firings. Under coverage, every permitted semantic path
from a represented state lifts. Faithful candidate interpretation additionally
gives uniqueness; state injectivity is not required for this outgoing-path law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore.Representation

universe uO uT uH uOcc uS uF uR uC uD

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {E : EffectCore X O State Firing} {Represented : Type uR} {Candidate : Represented → Type uC}
  (R : E.Representation Represented Candidate) (allow : E.Admission)

def Covers : Prop :=
  ∀ (source : Represented) (firing : Firing (R.state source)) (prepared : E.Prepares firing),
    allow firing prepared → ∃ selected : Candidate source, R.firing selected = firing

theorem covers_of_inclusion {narrow broad : E.Admission}
    (included : ∀ {s : State} (f : Firing s) (p : E.Prepares f), narrow f p → broad f p)
    (coverage : R.Covers broad) : R.Covers narrow :=
  fun source firing prepared permitted => coverage source firing prepared (included firing prepared permitted)

theorem mapEvent_firing {s t : Represented} (event : R.effect.Event (R.admission allow) s t) :
    (R.mapEvent event).firing = R.firing event.firing := rfl

private theorem event_heq {source firstTarget secondTarget : State}
    (first : E.Event allow source firstTarget) (second : E.Event allow source secondTarget)
    (same : first.firing = second.firing) : HEq first second := by
  rcases first with ⟨first, readyFirst, allowedFirst, firstResult⟩
  rcases second with ⟨second, readySecond, allowedSecond, secondResult⟩
  dsimp only at same
  subst second
  have preparations : readySecond = readyFirst := Subsingleton.elim _ _
  subst readySecond
  cases firstResult
  cases secondResult
  rfl

theorem star_surjective (coverage : R.Covers allow)
    (source : EventObject R.effect (R.admission allow)) :
    Function.Surjective ((R.mapEvents allow).star source) := by
  rintro ⟨target, event⟩
  rcases event with ⟨firing, prepared, permitted, rfl⟩
  obtain ⟨selected, same⟩ := coverage source firing prepared permitted
  subst firing
  refine ⟨⟨R.preparedResult selected prepared, ⟨selected, prepared, permitted, rfl⟩⟩, ?_⟩
  apply Sigma.ext (R.result_eq selected prepared)
  exact event_heq allow _ _ rfl

theorem path_surjective (coverage : R.Covers allow)
    (source : EventObject R.effect (R.admission allow)) :
    Function.Surjective ((R.mapEvents allow).pathStar source) :=
  Prefunctor.pathStar_surjective _ (R.star_surjective allow coverage) source

/-- Injectivity of the interpreted candidate suffices, even when distinct
represented states can denote the same semantic state. -/
theorem star_injective (faithful : ∀ source : Represented, Function.Injective (R.firing (s := source)))
    (source : EventObject R.effect (R.admission allow)) :
    Function.Injective ((R.mapEvents allow).star source) := by
  rintro ⟨target, first⟩ ⟨other, second⟩ same
  have firings : R.firing first.firing = R.firing second.firing :=
    congrArg (fun edge : (target : State) × E.Event allow (R.state source) target => edge.2.firing) same
  have candidates : first.firing = second.firing := faithful source firings
  rcases first with ⟨first, readyFirst, permittedFirst, firstTarget⟩
  rcases second with ⟨second, readySecond, permittedSecond, secondTarget⟩
  dsimp only at candidates
  subst second
  have preparations : readySecond = readyFirst := Subsingleton.elim _ _
  subst readySecond
  cases firstTarget
  cases secondTarget
  rfl

theorem path_bijective (coverage : R.Covers allow)
    (faithful : ∀ source : Represented, Function.Injective (R.firing (s := source)))
    (source : EventObject R.effect (R.admission allow)) :
    Function.Bijective ((R.mapEvents allow).pathStar source) :=
  ⟨Prefunctor.pathStar_injective _ (R.star_injective allow faithful) source,
    R.path_surjective allow coverage source⟩

theorem unique_path_lift (coverage : R.Covers allow)
    (faithful : ∀ source : Represented, Function.Injective (R.firing (s := source)))
    (source : EventObject R.effect (R.admission allow))
    (path : @Quiver.PathStar (EventObject E allow) _ (R.state source)) :
    ∃! represented : Quiver.PathStar source, (R.mapEvents allow).pathStar source represented = path :=
  (R.path_bijective allow coverage faithful source).existsUnique path

theorem mapPath_comp {s t u : EventObject R.effect (R.admission allow)}
    (first : Quiver.Path s t) (second : Quiver.Path t u) :
    (R.mapEvents allow).mapPath (first.comp second) =
      ((R.mapEvents allow).mapPath first).comp ((R.mapEvents allow).mapPath second) :=
  Prefunctor.mapPath_comp _ first second

def observer (D : @EventObserver (EventObject E allow) _ ) :
    EventObserver (EventObject R.effect (R.admission allow)) := D.comap (R.mapEvents allow)

theorem observer_commutes (D : @EventObserver (EventObject E allow) _ )
    {s t : EventObject R.effect (R.admission allow)} (path : Quiver.Path s t)
    (record : D.Data (R.state s)) :
    (R.observer allow D).evaluate path record = D.evaluate ((R.mapEvents allow).mapPath path) record :=
  D.evaluate_comap (R.mapEvents allow) path record

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EffectCore.Representation
