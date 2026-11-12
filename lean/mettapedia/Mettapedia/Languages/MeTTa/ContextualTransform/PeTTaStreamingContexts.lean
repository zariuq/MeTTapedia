import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContexts
import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes

/-!
# Arbitrarily nested source contexts in the streaming controller

The existing source-shell grammar is extended by first demand. A structural
layout records ordinary return frames and required collection/first markers.
Every admitted context reaches its hole in exactly one controller step per
shell, preserving its world and older alternatives. The continuation may
subsequently diverge, raise, suspend or change spaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Streaming

inductive Shell where
  | source (shell : PeTTaContexts.Shell)
  | first

def Shell.plug : Shell → Atom → Atom
  | .source shell, inner => shell.plug inner
  | .first, inner => .expression [.symbol "once",inner]

structure Layout where
  frames : List Frame
  older : List Job
  nextBoundary : Nat

def Layout.focus (layout : Layout) (base : State) (bindings : Subst) (expression : Atom) : State :=
  {base with
    agenda := [.execute ⟨.evaluate bindings expression,layout.frames⟩] ++ layout.older
    nextBoundary := layout.nextBoundary}

def Shell.place? (shell : Shell) (bindings : Subst) (layout : Layout) : Option Layout :=
  match shell with
  | .first =>
      some ⟨.first layout.nextBoundary :: layout.frames,
        .first layout.nextBoundary :: layout.older,layout.nextBoundary + 1⟩
  | .source shell => do
      let frame ← shell.frame? bindings
      match frame with
      | .collect outer =>
          some ⟨.collection layout.nextBoundary :: layout.frames,
            .collect layout.nextBoundary outer layout.frames [] :: layout.older,layout.nextBoundary + 1⟩
      | .sequence _ _ | .dynamicCall => none
      | frame => some ⟨.source frame :: layout.frames,layout.older,layout.nextBoundary⟩

theorem Shell.step_place (registry : SpaceSemantics.Program) (shell : Shell) (bindings : Subst)
    (inner : Atom) (base : State) (layout target : Layout)
    (ready : shell.place? bindings layout = some target) :
    step registry (layout.focus base bindings (shell.plug inner)) =
      some (target.focus base bindings inner) := by
  cases shell with
  | first =>
      simp only [Shell.place?,Option.some.injEq] at ready
      subst target
      rfl
  | source shell =>
      cases shell with
      | letValue pattern body =>
          simp only [Shell.place?,PeTTaContexts.Shell.frame?,bind,Option.bind_some,Option.some.injEq] at ready
          subst target
          exact Transition.computed (.phase rfl rfl (.let_enter rfl) (.waiting rfl rfl))
      | caseValue rows =>
          cases parsed : Eval.readCases rows with
          | none => simp [Shell.place?,PeTTaContexts.Shell.frame?,parsed] at ready
          | some cases =>
              simp only [Shell.place?,PeTTaContexts.Shell.frame?,parsed,Option.map_some,bind,
                Option.bind_some,Option.some.injEq] at ready
              subst target
              exact Transition.computed (.phase rfl rfl (.case_enter rfl parsed) (.waiting rfl rfl))
      | condition yes no =>
          simp only [Shell.place?,PeTTaContexts.Shell.frame?,bind,Option.bind_some,Option.some.injEq] at ready
          subst target
          exact Transition.computed (.phase rfl rfl (.if_enter rfl) (.waiting rfl rfl))
      | collect =>
          simp only [Shell.place?,PeTTaContexts.Shell.frame?,bind,Option.bind_some,Option.some.injEq] at ready
          subst target
          exact Transition.computed (.collection_enter rfl)
      | matchSpace pattern body =>
          simp only [Shell.place?,PeTTaContexts.Shell.frame?,bind,Option.bind_some,Option.some.injEq] at ready
          subst target
          exact Transition.computed (.phase rfl rfl (.query_enter rfl) (.waiting rfl rfl))

abbrev Context := List Shell

def plug : Context → Atom → Atom
  | [], inner => inner
  | shell :: rest, inner => shell.plug (plug rest inner)

def place? : Context → Subst → Layout → Option Layout
  | [], _, layout => some layout
  | shell :: rest, bindings, layout => do
      let entered ← shell.place? bindings layout
      place? rest bindings entered

theorem plug_append (outside inside : Context) (inner : Atom) :
    plug (outside ++ inside) inner = plug outside (plug inside inner) := by
  induction outside with
  | nil => rfl
  | cons shell rest ih => simp only [List.cons_append,plug,ih]

theorem place_append (outside inside : Context) (bindings : Subst) (layout : Layout) :
    place? (outside ++ inside) bindings layout =
      (place? outside bindings layout).bind (place? inside bindings) := by
  induction outside generalizing layout with
  | nil => rfl
  | cons shell rest ih =>
      simp only [List.cons_append,place?,bind,Option.bind_assoc,ih]

/-- No source completion is assumed. The context itself supplies exactly
its entry prefix, even if the hole or its caller never returns. -/
theorem advance_context (registry : SpaceSemantics.Program) (context : Context) (bindings : Subst)
    (inner : Atom) (base : State) (layout target : Layout)
    (ready : place? context bindings layout = some target) :
    advance registry context.length (layout.focus base bindings (plug context inner)) =
      target.focus base bindings inner := by
  induction context generalizing layout with
  | nil =>
      simp only [place?,Option.some.injEq] at ready
      subst target
      rfl
  | cons shell rest ih =>
      simp only [place?,bind,Option.bind_eq_some_iff] at ready
      obtain ⟨entered,first,remaining⟩ := ready
      have single : advance registry 1 (layout.focus base bindings (shell.plug (plug rest inner))) =
          entered.focus base bindings (plug rest inner) := by
        simp only [advance,Mettapedia.Machines.BoundedDeterministicRun.run,
          shell.step_place registry bindings (plug rest inner) base layout entered first]
      change advance registry (rest.length + 1)
        (layout.focus base bindings (shell.plug (plug rest inner))) = _
      rw [Nat.add_comm rest.length 1,Streaming.advance_add,single]
      exact ih entered remaining

theorem run_context (registry : SpaceSemantics.Program) (context : Context) (bindings : Subst)
    (inner : Atom) (base : State) (layout target : Layout)
    (ready : place? context bindings layout = some target) (remaining : Nat) :
    run registry (context.length + remaining) (layout.focus base bindings (plug context inner)) =
      run registry remaining (target.focus base bindings inner) := by
  simp only [run,Streaming.advance_add,advance_context registry context bindings inner base layout target ready]

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStreamingContexts
