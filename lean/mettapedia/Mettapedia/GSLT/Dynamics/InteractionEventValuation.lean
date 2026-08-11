import Mettapedia.GSLT.Core.InteractionComposition
import Mettapedia.GSLT.Dynamics.IndexedEventValuation
import Mathlib.Algebra.Ring.Nat

/-!
# Valuations of authenticated interaction paths

This module connects occurrence-preserving interaction paths to the generic
indexed valuation algebra.  Cost, provenance, evidence, and attention remain
independent observers of the same event history; they do not add semantic
steps.  Chronological path composition is reflected exactly by valuation
composition.
-/

namespace Mettapedia.GSLT.Dynamics.InteractionEventValuation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

universe uSite uEvent uGrade

variable {theory : GSLT}
  (presentation : InteractionPresentation.{uSite, uEvent} theory)

/-- One event packaged with the source indexing its evidence. -/
abbrev Occurrence : Type _ :=
  Σ source, presentation.Enabled source

namespace EventPath

/-- The chronological occurrence history retained by a path. -/
def events : {source target : theory.Term} →
    Core.InteractionComposition.EventPath presentation source target →
      List (Occurrence presentation)
  | _, _, .nil _ => []
  | source, _, .cons (site := site) event rest =>
      ⟨source, { site := site, target := _, evidence := event }⟩ ::
        events rest

/-- Path composition is chronological event-list concatenation. -/
@[simp] theorem events_append {source middle target : theory.Term}
    (first : Core.InteractionComposition.EventPath
      presentation source middle)
    (second : Core.InteractionComposition.EventPath
      presentation middle target) :
    events presentation
        (Core.InteractionComposition.EventPath.append presentation first second) =
      events presentation first ++ events presentation second := by
  induction first with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [Core.InteractionComposition.EventPath.append, events,
        List.cons_append]
      rw [inductionHypothesis]

/-- Value an exact path without changing its endpoints or event evidence. -/
def grade
    (valuation : Valuation (Occurrence presentation))
    {source target : theory.Term}
    (path : Core.InteractionComposition.EventPath
      presentation source target) :
    Option valuation.Grade :=
  valuation.historyGrade (events presentation path)

/-- Path valuation composes in the same chronological order as path
composition. -/
theorem grade_append
    (valuation : Valuation (Occurrence presentation))
    {source middle target : theory.Term}
    (first : Core.InteractionComposition.EventPath
      presentation source middle)
    (second : Core.InteractionComposition.EventPath
      presentation middle target) :
    grade presentation valuation
        (Core.InteractionComposition.EventPath.append presentation first second) =
      (grade presentation valuation first).bind fun left =>
        (grade presentation valuation second).bind fun right =>
          valuation.algebra.op left right := by
  unfold grade
  rw [events_append, Valuation.historyGrade_append]

/-- Count authenticated event occurrences independently of their endpoints,
payloads, and producer. -/
abbrev eventCountValuation : Valuation (Occurrence presentation) :=
  additive fun _ => (1 : Nat)

/-- Event-count grade is exactly the proof-relevant path length. -/
theorem eventCount_grade
    {source target : theory.Term}
    (path : Core.InteractionComposition.EventPath
      presentation source target) :
    grade presentation (eventCountValuation presentation) path =
      some (Core.InteractionComposition.EventPath.pathLength presentation
        path) := by
  induction path with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [grade, events, Valuation.historyGrade_cons]
      change
        (some 1).bind (fun head =>
          ((eventCountValuation presentation).historyGrade
            (events presentation rest)).bind fun tail =>
              some (head + tail)) = _
      rw [show
        (eventCountValuation presentation).historyGrade
            (events presentation rest) =
          grade presentation (eventCountValuation presentation) rest from rfl]
      rw [inductionHypothesis]
      rfl

end EventPath

/-- Interpret an existing occurrence-indexed cost assignment in any additive
cost algebra. -/
abbrev additiveEventCost {Cost : Type uGrade} [AddMonoid Cost]
    (cost : InteractionPresentation.EventCost presentation Cost) :
    Valuation (Occurrence presentation) :=
  additive fun occurrence => cost.cost occurrence.2.evidence

end Mettapedia.GSLT.Dynamics.InteractionEventValuation
