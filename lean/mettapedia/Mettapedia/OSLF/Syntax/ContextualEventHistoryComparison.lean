import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mettapedia.OSLF.Syntax.RewriteClassEventHistory

/-!
# Comparing contextual events with the earlier closed event graph

The context-indexed operational graph has a canonical closed fibre. Each of
its authored events supplies the earlier proof-relevant class event: the rule
index, structural location, root assignment, and raw representatives are all
retained. The map lands at the same equation-class endpoints. The earlier
graph also permits extra representative choices around a firing, so this file
does not claim an event-object equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualEventHistoryComparison

open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.RewriteClassEventHistory
open Mettapedia.OSLF.Binding.RewriteEventHistory

variable {S : Signature}

/-- Forget the structural encoding of a selected occurrence into the earlier
term-with-a-linear-hole record, retaining the exact root firing. -/
def toOldStepFiring (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (event : PresentationInstance presentation [] sort) :
    UnpositionedRewrite.StepFiring (presentation.rules.get event.1)
      event.source event.target where
  context := event.2.context.toTerm
  redex := event.2.root.source
  reduct := event.2.root.target
  linear := LinCtx.holeCount_toTerm event.2.context
  root := event.2.root.toClosed
  source_eq := rfl
  target_eq := rfl

/-- The older equation-closed occurrence takes the event's own raw endpoints
as its representatives; equation changes remain available in its type. -/
def toOldEquationFiring (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (event : PresentationInstance presentation [] sort) :
    UnpositionedRewrite.EquationClosedFiring presentation.eqs
      (presentation.rules.get event.1) event.source event.target where
  source' := event.source
  target' := event.target
  before := EqClosure.refl _
  firing := toOldStepFiring presentation sort event
  after := EqClosure.refl _

/-- A contextual authored event maps to the existing closed class graph,
with identical equation-class endpoints and the same authored rule index. -/
def toOldClassEvent (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (event : PresentationInstance presentation [] sort) :
    ClassEvent (authoredSystem presentation sort)
      ⟨Quotient.mk (eqSetoid presentation.eqs [] sort) event.source⟩
      ⟨Quotient.mk (eqSetoid presentation.eqs [] sort) event.target⟩ where
  rawSource := event.source
  rawTarget := event.target
  sourceClass := rfl
  occurrence := ⟨event.1, toOldEquationFiring presentation sort event⟩
  targetClass := rfl

theorem toOldClassEvent_rule_index (presentation : UnpositionedPresentation S)
    (sort : S.Srt) (event : PresentationInstance presentation [] sort) :
    (toOldClassEvent presentation sort event).occurrence.1 = event.1 := rfl

end Mettapedia.OSLF.Binding.ContextualEventHistoryComparison
