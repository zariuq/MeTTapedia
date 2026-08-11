import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Languages.MeTTa.PrimeNeedInteractionAuthority

/-!
# Cost of occurrence-authenticated Prime Need paths

The reference machine already carries an exact abstract transition clock.
The generic interaction-path event count agrees with that clock: no
independent cost semantics is introduced.  Richer physical costs, evidence,
provenance, and attention may be product valuations over the same events.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedInteractionValuation

open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.PrimeNeedReference
open Mettapedia.Languages.MeTTa.PrimeNeedInteractionAuthority

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

/-- The reference transition counter is exactly the length of every
occurrence-authenticated interaction path. -/
theorem transitions_eq_pathLength
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    → (path : EventPath (machinePresentation spec) initial final) →
      final.work.transitions = initial.work.transitions +
        EventPath.pathLength (machinePresentation spec) path
  | _, _, .nil _ => rfl
  | source, target, .cons (middle := middle) (site := site) event rest => by
      have occurrence : StepOccurrence spec source middle :=
        { index := site
          successorAt := event.successorAt }
      have oneStep := step_increments_transition spec source middle
        (occurrence.mem spec)
      have inductionHypothesis := transitions_eq_pathLength spec rest
      calc
        target.work.transitions = middle.work.transitions +
            EventPath.pathLength (machinePresentation spec) rest :=
          inductionHypothesis
        _ = (source.work.transitions + 1) +
            EventPath.pathLength (machinePresentation spec) rest := by
          rw [oneStep]
        _ = source.work.transitions +
            EventPath.pathLength (machinePresentation spec)
              (.cons event rest) := by
          simp only [EventPath.pathLength]
          omega

/-- The generic event-count valuation and Prime's reference work clock report
the same exact count on every authenticated path. -/
theorem eventCount_matches_workClock
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (path : EventPath (machinePresentation spec) initial final) :
    EventPath.grade (machinePresentation spec)
        (EventPath.eventCountValuation (machinePresentation spec)) path =
        some (EventPath.pathLength (machinePresentation spec) path) ∧
      final.work.transitions = initial.work.transitions +
        EventPath.pathLength (machinePresentation spec) path :=
  ⟨EventPath.eventCount_grade (machinePresentation spec) path,
    transitions_eq_pathLength spec path⟩

/-! ## Positive canary -/

namespace Canary

open Mettapedia.Languages.MeTTa.PrimeNeedInteractionAuthority.Canary

def oneStepPath :
    EventPath (machinePresentation demoSpec) start next :=
  .cons ⟨firstOccurrence.successorAt⟩
    (.nil (presentation := machinePresentation demoSpec) next)

theorem one_step_grade_and_clock :
    EventPath.grade (machinePresentation demoSpec)
        (EventPath.eventCountValuation (machinePresentation demoSpec))
        oneStepPath = some 1 ∧
      next.work.transitions = start.work.transitions + 1 := by
  exact eventCount_matches_workClock demoSpec oneStepPath

end Canary

end Mettapedia.Languages.MeTTa.PrimeNeedInteractionValuation
