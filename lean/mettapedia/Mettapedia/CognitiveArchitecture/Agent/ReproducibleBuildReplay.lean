import Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
import Mettapedia.GSLT.ReproducibleBuild.HattaProfile

/-!
# Open-ended context for reproducible event histories

An evolving system may keep its authoritative source-scoped event log outside
the bounded active context.  The active context can be the weakest view for a
finite query family, but no fixed lossy summary remains sufficient for every
state-separating open-ended query schedule.

The negative theorem below specializes the existing open-ended-context no-go
to event logs.  Both of its load-bearing premises remain visible: the query
schedule must separate log states, and the proposed permanent context must be
complete at every epoch.  It is not a claim that every finite or lossy context
is inadequate for every task.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildReplay

open Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

universe uState uEvent uSource uRevision uEpoch uQuery uAnswer uView

variable {State : Type uState} {Event : Type uEvent} {Source : Type uSource}
  {Revision : Type uRevision} {Epoch : Type uEpoch} {Query : Type uQuery}
  {Answer : Type uAnswer}

/-- At every epoch, the canonical finite active-query projection is sufficient
and is refined by every other view satisfying the same query contract. -/
theorem activeEventLogProjection_is_weakest_sufficient
    [DecidableEq Query] [Inhabited Answer]
    (answer : EventLog State Event Source Revision -> Query -> Answer)
    (active : Finset Query) :
    Mettapedia.CognitiveArchitecture.Agent.WorldState.PreservesRelevantQueries
        (fun query => query ∈ active) answer
        (activeProjection answer active) /\
      forall {View : Type uView}
        (view : EventLog State Event Source Revision -> View),
        Mettapedia.CognitiveArchitecture.Agent.WorldState.PreservesRelevantQueries
          (fun query => query ∈ active) answer view ->
          Refines view (activeProjection answer active) :=
  activeProjection_is_weakest_sufficient answer active

/-- A genuinely lossy permanent summary of source-scoped event logs cannot be
complete for a state-separating open-ended query schedule.  The proof invokes
`permanentlyComplete_injective` only after receiving both its separating and
permanent-completeness premises. -/
theorem no_lossy_permanent_eventLog_summary
    [DecidableEq Query]
    {answer : EventLog State Event Source Revision -> Query -> Answer}
    {schedule : Epoch -> Finset Query}
    {View : Type uView}
    {summary : EventLog State Event Source Revision -> View}
    (separating : ScheduleSeparating answer schedule)
    (lossy : Not (Function.Injective summary)) :
    Not (PermanentlyComplete answer schedule summary) := by
  intro complete
  exact lossy (permanentlyComplete_injective separating complete)

end Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildReplay

#print axioms Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildReplay.activeEventLogProjection_is_weakest_sufficient
#print axioms Mettapedia.CognitiveArchitecture.Agent.ReproducibleBuildReplay.no_lossy_permanent_eventLog_summary
