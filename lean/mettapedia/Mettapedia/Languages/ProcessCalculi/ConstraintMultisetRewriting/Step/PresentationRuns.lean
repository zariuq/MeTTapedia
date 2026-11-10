import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationInterpretation
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Finite-run correspondence for the authored event interface

An executed edge records the requested firing and an actual `Request` to `At`
reduction. Composing these boundary events permits a caller to submit the
next request; it does not add an implicit evaluator to `At`. The raw edge
quiver admits every pattern as a possible state. Reflection proves that paths
starting from encoded states remain in the encoded image and lift uniquely.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Interface _root_.CategoryTheory

universe uO uT uH uOcc uS uF

structure ExecutedEvent (queries : Queries) (source target : Pattern) where
  firing : Pattern
  executed : atState target ∈ rewriteStepWithPremisesUsing queries.relations language
    (request source firing)

def ExecutionObject (_queries : Queries) := Pattern

instance executionQuiver (queries : Queries) : Quiver (ExecutionObject queries) where
  Hom s t := ExecutedEvent queries s t

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing) (allow : E.Admission)
  (code : Encoding State Firing) (decision : Decisions E allow)

def executionMap : EffectCore.EventObject E allow ⥤q
    ExecutionObject (effectQueries E allow code decision) where
  obj s := code.state.view (sort := ()) s
  map {s _} event :=
    ⟨code.firing.view (sort := ()) ⟨s, event.firing⟩,
      (execution_iff_event E allow code decision event.firing).mpr ⟨event, rfl⟩⟩

/-- Source and candidate encodings retain distinct outgoing events. -/
theorem execution_star_injective (s : EffectCore.EventObject E allow) :
    Function.Injective ((executionMap E allow code decision).star s) := by
  rintro ⟨t, first⟩ ⟨u, second⟩ same
  have targets := congrArg Sigma.fst same
  have target_eq : t = u := code.state.view_injective targets
  subst u
  have edges := eq_of_heq (Sigma.mk.inj same).2
  have firings := congrArg ExecutedEvent.firing edges
  have candidates := code.firing.view_injective firings
  have firing_eq : first.firing = second.firing := eq_of_heq (Sigma.mk.inj candidates).2
  cases first
  cases second
  cases firing_eq
  rfl

/-- Every raw outgoing edge from an encoded state is an authorized effect. -/
theorem execution_star_surjective (s : EffectCore.EventObject E allow) :
    Function.Surjective ((executionMap E allow code decision).star s) := by
  rintro ⟨target, ⟨firing, executed⟩⟩
  obtain ⟨⟨source, f⟩, p, source_eq, firing_eq, permitted, target_eq⟩ :=
    execution_reflects E allow code decision executed
  have source_same : source = s := code.state.view_injective source_eq
  subst source
  have targets := (List.cons.inj (Pattern.apply.inj target_eq).2).1
  change target = code.state.view (sort := ()) (E.preparedResult f p) at targets
  subst target
  subst firing
  exact ⟨⟨E.preparedResult f p, ⟨f, p, permitted, rfl⟩⟩, rfl⟩

/-- The correspondence is exact for arbitrary finite runs, including order and
distinct events with identical endpoints. Only a starting state is supplied. -/
theorem execution_paths_bijective (s : EffectCore.EventObject E allow) :
    Function.Bijective ((executionMap E allow code decision).pathStar s) :=
  ⟨Prefunctor.pathStar_injective _ (execution_star_injective E allow code decision) s,
   Prefunctor.pathStar_surjective _ (execution_star_surjective E allow code decision) s⟩

noncomputable def executionRunEquiv (s : EffectCore.EventObject E allow) :
    Quiver.PathStar s ≃ Quiver.PathStar ((executionMap E allow code decision).obj s) :=
  Equiv.ofBijective _ (execution_paths_bijective E allow code decision s)

theorem execution_run_unique (s : EffectCore.EventObject E allow)
    (targetRun : Quiver.PathStar ((executionMap E allow code decision).obj s)) :
    ∃! sourceRun : Quiver.PathStar s,
      (executionMap E allow code decision).pathStar s sourceRun = targetRun :=
  (execution_paths_bijective E allow code decision s).existsUnique targetRun

theorem execution_preserves_composition {s t u : EffectCore.EventObject E allow}
    (first : Quiver.Path s t) (second : Quiver.Path t u) :
    (executionMap E allow code decision).mapPath (first.comp second) =
      ((executionMap E allow code decision).mapPath first).comp
        ((executionMap E allow code decision).mapPath second) :=
  Prefunctor.mapPath_comp _ first second

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
