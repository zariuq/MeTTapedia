import Mettapedia.GSLT.Dynamics.ObservationPolicyFactorization
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility

/-!
# Observation sufficiency for scheduler policies

An observation discipline retains witnesses in a container and reads a value
from that container.  A scheduler may subsequently score the retained
container.  This module gives the exact criterion under which the readout
contains enough information to perform maximum-score selection: equal
readouts must have equal target scores.

This criterion is deliberately weaker than faithfulness.  A lossy readout may
still be sufficient for one policy, while being insufficient for another.
Consequently, scheduler sufficiency is a relation between a declared readout
and a declared policy; it is not a property of the value carrier in isolation.
-/

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.Algebra

universe uEvent uContainer uValue

namespace ObservationDiscipline

/-- A discipline supports maximum selection for a target score when some
bag-level selector uses retained candidates only through the discipline's
readout and returns exactly the score-maximal candidates. -/
def SupportsMaxSelection {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container -> Nat) : Prop :=
  Mettapedia.GSLT.Core.ObservationSupportsMaxSelection
    discipline.readout score

/-- **Exact scheduler-sufficiency criterion.**  A readout supports maximum
selection for a score exactly when the score is constant on every readout
fibre.  No reconstruction of the retained witness container is required. -/
theorem supportsMaxSelection_iff {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container -> Nat) :
    discipline.SupportsMaxSelection score ↔
      ∀ ⦃first second : discipline.collection.Container⦄,
        discipline.readout first = discipline.readout second ->
          score first = score second :=
  Mettapedia.GSLT.Core.observationSupportsMaxSelection_iff
    discipline.readout score

/-- Every score computed from the declared readout is selection-sufficient.
This is the positive factorization direction. -/
theorem supportsMaxSelection_of_readoutScore {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.Value -> Nat) :
    discipline.SupportsMaxSelection (score ∘ discipline.readout) := by
  rw [supportsMaxSelection_iff]
  intro first second sameReadout
  exact congrArg score sameReadout

/-- A single readout collision whose target scores differ refutes scheduler
sufficiency for that score. -/
theorem not_supportsMaxSelection_of_collision {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container -> Nat)
    {first second : discipline.collection.Container}
    (sameReadout : discipline.readout first = discipline.readout second)
    (differentScore : score first ≠ score second) :
    ¬ discipline.SupportsMaxSelection score := by
  rw [supportsMaxSelection_iff]
  intro factors
  exact differentScore (factors sameReadout)

/-- Maximum-selection support is exactly ordinary policy factorization for
the target score.  The maximum selector adds no second information
criterion: both notions require the score to be constant on readout fibres. -/
theorem supportsMaxSelection_iff_supportsScorePolicy {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (score : discipline.collection.Container -> Nat) :
    discipline.SupportsMaxSelection score ↔
      discipline.SupportsPolicy score := by
  rw [supportsMaxSelection_iff,
    supportsPolicy_iff_constantOnReadoutFibers]
  rfl

end ObservationDiscipline

/-! ## Work/span controls

The full work/span value supports both work- and span-based policies.  Its
work-only scalarization remains sufficient for work selection despite being
lossy, but it cannot support span selection.  All three facts use the same
retained `WorkSpan` container; only the value readout changes.
-/

namespace WorkSpanSchedulerCanary

def unitCost : Unit -> WorkSpan :=
  fun _ => ⟨1, 1⟩

def full : ObservationDiscipline Unit :=
  WorkSpanObservation.discipline unitCost

def workOnly : ObservationDiscipline Unit :=
  WorkSpanObservation.workOnly unitCost

/-- Scalarization changes only the value dial; the retained witness container
is definitionally the same `WorkSpan`. -/
theorem workOnly_retains_container :
    workOnly.collection = full.collection :=
  rfl

/-- The full work/span readout supports a span-maximizing policy. -/
theorem full_supports_spanSelection :
    full.SupportsMaxSelection WorkSpan.span := by
  rw [ObservationDiscipline.supportsMaxSelection_iff]
  intro first second sameReadout
  change first = second at sameReadout
  exact congrArg WorkSpan.span sameReadout

/-- A work-only readout contains exactly the information required by a
work-maximizing policy. -/
theorem workOnly_supports_workSelection :
    workOnly.SupportsMaxSelection WorkSpan.work := by
  rw [ObservationDiscipline.supportsMaxSelection_iff]
  intro first second sameReadout
  exact sameReadout

/-- Work-only observation is genuinely lossy: parallel and chronological
two-event schedules have equal work but different span. -/
theorem workOnly_isLossy : workOnly.Lossy := by
  apply ObservationDiscipline.lossy_of_collision workOnly
      (first := (⟨2, 1⟩ : WorkSpan)) (second := ⟨2, 2⟩)
  · intro same
    have sameSpan := congrArg WorkSpan.span same
    norm_num at sameSpan
  · rfl

/-- Lossiness does not preclude policy-specific sufficiency. -/
theorem workOnly_lossy_but_workSelectionSufficient :
    workOnly.Lossy ∧ workOnly.SupportsMaxSelection WorkSpan.work :=
  ⟨workOnly_isLossy, workOnly_supports_workSelection⟩

/-- The same lossy readout is insufficient for span selection.  Thus
sufficiency belongs to the `(readout, policy)` pair, not to the readout
alone. -/
theorem workOnly_not_supports_spanSelection :
    ¬ workOnly.SupportsMaxSelection WorkSpan.span := by
  apply ObservationDiscipline.not_supportsMaxSelection_of_collision workOnly
      WorkSpan.span (first := (⟨2, 1⟩ : WorkSpan)) (second := ⟨2, 2⟩)
  · rfl
  · norm_num

end WorkSpanSchedulerCanary

#print axioms ObservationDiscipline.supportsMaxSelection_iff
#print axioms ObservationDiscipline.supportsMaxSelection_of_readoutScore
#print axioms ObservationDiscipline.not_supportsMaxSelection_of_collision
#print axioms ObservationDiscipline.supportsMaxSelection_iff_supportsScorePolicy
#print axioms WorkSpanSchedulerCanary.full_supports_spanSelection
#print axioms WorkSpanSchedulerCanary.workOnly_lossy_but_workSelectionSufficient
#print axioms WorkSpanSchedulerCanary.workOnly_not_supports_spanSelection

end Mettapedia.GSLT.Dynamics
