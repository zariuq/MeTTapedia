import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuns

/-!
# Explicit submission and administrative lowering

The authored `Request` to `At` rule executes one submitted candidate. A caller
selects the next candidate in a separate administrative transition. Selection
does not change the observed store or grant permission. A complete boundary
event lowers to precisely these two steps. Every ready-to-ready finite run
reflects to the boundary events, retaining their firing identities and order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Submission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

inductive Configuration where
  | ready (state : Pattern)
  | waiting (state firing : Pattern)

inductive Transition (queries : Queries) : Configuration → Configuration → Type
  | select (state firing : Pattern) : Transition queries (.ready state) (.waiting state firing)
  | execute {state firing target : Pattern}
      (admitted : atState target ∈ rewriteStepWithPremisesUsing queries.relations language
        (request state firing)) :
      Transition queries (.waiting state firing) (.ready target)

def Machine (_queries : Queries) := Configuration

instance machineQuiver (queries : Queries) : Quiver (Machine queries) where
  Hom := Transition queries

def observe : Configuration → Pattern
  | .ready state => state
  | .waiting state _ => state

theorem selection_preserves_observation (state firing : Pattern) :
    observe (.ready state) = observe (.waiting state firing) := rfl

variable (queries : Queries)

def lower {s : ExecutionObject queries} : {t : ExecutionObject queries} → Quiver.Path s t →
    @Quiver.Path (Machine queries) _ (.ready s) (.ready t)
  | _, .nil => .nil
  | _, .cons path event =>
      .cons (.cons (lower path) (.select _ event.firing)) (.execute event.executed)

def observedEdge {s t : Machine queries} (edge : s ⟶ t) :
    @Quiver.Path (ExecutionObject queries) _ (observe s) (observe t) := by
  cases edge with
  | select _ _ => exact .nil
  | @execute state firing target admitted => exact .cons .nil ⟨firing, admitted⟩

def reflect {s : Machine queries} : {t : Machine queries} →
    Quiver.Path s t → @Quiver.Path (ExecutionObject queries) _ (observe s) (observe t)
  | _, .nil => .nil
  | _, .cons path edge => (reflect path).comp (observedEdge queries edge)

theorem reflect_lower {s t : ExecutionObject queries} (path : Quiver.Path s t) :
    reflect queries (lower queries path) = path := by
  induction path with
  | nil => rfl
  | cons path event ih =>
      change (reflect queries (lower queries path)).cons _ = _
      rw [ih]
      cases event
      rfl

theorem lower_reflect : ∀ {s t : ExecutionObject queries}
    (path : @Quiver.Path (Machine queries) _ (.ready s) (.ready t)),
    lower queries (reflect queries path) = path
  | _, _, .nil => rfl
  | _, _, .cons (.cons path (.select _ firing)) (.execute admitted) => by
      change ((lower queries (reflect queries path)).cons (.select _ firing)).cons
        (.execute admitted) = _
      rw [lower_reflect path]
      rfl
termination_by _ _ path => path.length
decreasing_by simp [Quiver.Path.length_cons]

def completedRunEquiv (s t : ExecutionObject queries) :
    Quiver.Path s t ≃ @Quiver.Path (Machine queries) _ (.ready s) (.ready t) where
  toFun := lower queries
  invFun := reflect queries
  left_inv := reflect_lower queries
  right_inv := lower_reflect queries

theorem lower_comp {s t u : ExecutionObject queries}
    (first : Quiver.Path s t) (second : Quiver.Path t u) :
    lower queries (first.comp second) = (lower queries first).comp (lower queries second) := by
  induction second with
  | nil => simp [lower]
  | cons path event ih => simp only [Quiver.Path.comp_cons, lower, ih]

/-- Administrative lowering changes path length without inventing semantic firings. -/
theorem lower_length {s t : ExecutionObject queries} (path : Quiver.Path s t) :
    (lower queries path).length = 2 * path.length := by
  induction path with
  | nil => simp [lower]
  | cons path event ih => simp [lower, ih, Nat.mul_add]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Submission
