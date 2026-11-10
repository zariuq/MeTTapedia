import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRetainedFrames

/-!
# PeTTa source contexts and their retained continuations

These are actual evaluation-position constructors of the existing source
machine. A context is an arbitrarily nested list of such shells. Entering it
reaches the hole above the original caller frames, without changing the store,
input, output, branch substitution or freshness counter. The exact runner law
charges one administrative transition per shell.

Case-row parsing is an explicit admission condition: malformed case syntax can
fault before its key runs. Quotation is deliberately not an evaluating shell.
Body contexts, application arguments and typed source interfaces are separate
parts of the surrounding contextual-execution goal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying

/-- A hole at the next evaluated source position, before its continuation runs. -/
inductive Shell where
  | letValue (pattern body : Atom)
  | caseValue (rows : List Atom)
  | condition (yes no : Atom)
  | collect
  | matchSpace (pattern body : Atom)

def Shell.plug : Shell → Atom → Atom
  | .letValue pattern body, inner => .expression [.symbol "let", pattern, inner, body]
  | .caseValue rows, inner => .expression [.symbol "case", inner, .expression rows]
  | .condition yes no, inner => .expression [.symbol "if", inner, yes, no]
  | .collect, inner => .expression [.symbol "collapse", inner]
  | .matchSpace pattern body, inner => .expression [.symbol "match", inner, pattern, body]

def Shell.frame? (bindings : Subst) : Shell → Option Frame
  | .letValue pattern body => some (.bind pattern body)
  | .caseValue rows => (Eval.readCases rows).map Frame.select
  | .condition yes no => some (.branch yes no)
  | .collect => some (.collect bindings)
  | .matchSpace pattern body => some (.query pattern body)

/-- The hole is interpreted with its incoming substitution, not substituted and reclassified. -/
def atExpression (base : Configuration) (bindings : Subst) (expression : Atom) : Configuration :=
  { base with control := .evaluate bindings expression }

theorem shell_enters (registry : SpaceSemantics.Program) (shell : Shell)
    (base : Configuration) (bindings : Subst) (inner : Atom) (frame : Frame)
    (ready : shell.frame? bindings = some frame) :
    Transition registry (atExpression base bindings (shell.plug inner))
      (atExpression { base with frames := frame :: base.frames } bindings inner) := by
  cases shell with
  | letValue pattern body =>
      simp only [Shell.frame?, Option.some.injEq] at ready
      subst frame
      exact .let_enter rfl
  | caseValue rows =>
      cases parsed : Eval.readCases rows with
      | none => simp [Shell.frame?, parsed] at ready
      | some cases =>
          simp only [Shell.frame?, parsed, Option.map_some, Option.some.injEq] at ready
          subst frame
          exact .case_enter rfl parsed
  | condition yes no =>
      simp only [Shell.frame?, Option.some.injEq] at ready
      subst frame
      exact .if_enter rfl
  | collect =>
      simp only [Shell.frame?, Option.some.injEq] at ready
      subst frame
      exact .collapse_enter rfl
  | matchSpace pattern body =>
      simp only [Shell.frame?, Option.some.injEq] at ready
      subst frame
      exact .query_enter rfl

/-- Outermost shell first. -/
abbrev Context := List Shell

def plug : Context → Atom → Atom
  | [], inner => inner
  | shell :: rest, inner => shell.plug (plug rest inner)

def frames? (bindings : Subst) : Context → Option (List Frame)
  | [] => some []
  | shell :: rest => do
      let frame ← shell.frame? bindings
      let nested ← frames? bindings rest
      pure (nested ++ [frame])

theorem plug_append (outside inside : Context) (inner : Atom) :
    plug (outside ++ inside) inner = plug outside (plug inside inner) := by
  induction outside with
  | nil => rfl
  | cons shell rest ih => simp [plug, ih]

/-- Context composition preserves the exact continuation order. -/
theorem frames_append (bindings : Subst) (outside inside : Context)
    (outerFrames innerFrames : List Frame)
    (outerReady : frames? bindings outside = some outerFrames)
    (innerReady : frames? bindings inside = some innerFrames) :
    frames? bindings (outside ++ inside) = some (innerFrames ++ outerFrames) := by
  induction outside generalizing outerFrames with
  | nil => simp [frames?] at outerReady; subst outerFrames; simpa using innerReady
  | cons shell rest ih =>
      cases frame : shell.frame? bindings with
      | none => simp [frames?, frame] at outerReady
      | some saved =>
          cases nested : frames? bindings rest with
          | none => simp [frames?, frame, nested] at outerReady
          | some fs =>
              simp [frames?, frame, nested] at outerReady
              subst outerFrames
              simp [frames?, frame, ih fs nested, List.append_assoc]

/-- The source syntax reaches its hole above the original caller, for arbitrary nesting. -/
theorem enter_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (inner : Atom) (frames : List Frame)
    (ready : frames? bindings context = some frames) :
    Relation.ReflTransGen (Transition registry)
      (atExpression base bindings (plug context inner))
      (atExpression { base with frames := frames ++ base.frames } bindings inner) := by
  induction context generalizing base frames with
  | nil => simp [frames?] at ready; subst frames; exact .refl
  | cons shell rest ih =>
      cases frame : shell.frame? bindings with
      | none => simp [frames?, frame] at ready
      | some saved =>
          cases nested : frames? bindings rest with
          | none => simp [frames?, frame, nested] at ready
          | some fs =>
              simp [frames?, frame, nested] at ready
              subst frames
              have entered := shell_enters registry shell base bindings (plug rest inner) saved frame
              have continued := ih { base with frames := saved :: base.frames } fs nested
              simpa [plug, atExpression, List.append_assoc] using
                Relation.ReflTransGen.head entered continued

/-- The real fuelled source runner accounts exactly for the context's administrative prefix. -/
theorem run_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (inner : Atom) (frames : List Frame)
    (ready : frames? bindings context = some frames) (fuel : Nat) :
    run registry (context.length + fuel) (atExpression base bindings (plug context inner)) =
      run registry fuel (atExpression { base with frames := frames ++ base.frames } bindings inner) := by
  induction context generalizing base frames with
  | nil => simp [frames?] at ready; subst frames; simp [plug, atExpression]
  | cons shell rest ih =>
      cases frame : shell.frame? bindings with
      | none => simp [frames?, frame] at ready
      | some saved =>
          cases nested : frames? bindings rest with
          | none => simp [frames?, frame, nested] at ready
          | some fs =>
              simp [frames?, frame, nested] at ready
              subst frames
              have entered := transition_step (shell_enters registry shell base bindings
                (plug rest inner) saved frame)
              rw [List.length_cons, Nat.succ_add, Nat.succ_eq_add_one, plug,
                run_succ_of_step registry (rest.length + fuel) _ _ entered]
              simpa [atExpression, List.append_assoc] using
                ih { base with frames := saved :: base.frames } fs nested

/-- A real hole step is reached through the source context, above its retained continuation. -/
theorem hole_step_reached (registry : SpaceSemantics.Program)
    (context : Context) (base : Configuration) (bindings : Subst) (inner : Atom)
    (frames : List Frame) (ready : frames? bindings context = some frames)
    (target : Configuration)
    (holeStep : Transition registry
      (atExpression { base with frames := [] } bindings inner) target) :
    Relation.ReflTransGen (Transition registry)
      (atExpression base bindings (plug context inner))
      (appendFrames target (frames ++ base.frames)) := by
  have entered := enter_context registry context base bindings inner frames ready
  have lifted := holeStep.append_frames (frames ++ base.frames)
  apply entered.tail
  simpa [appendFrames, atExpression] using lifted

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContexts
