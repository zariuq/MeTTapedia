import Mettapedia.GSLT.Dynamics.InteractionEventValuation
import Mettapedia.Machines.BranchLocalNeed.InteractionAuthority
import Mettapedia.GSLT.Core.CostedOperational

/-!
# Cost of occurrence-authenticated reference Need paths

The reference machine already carries an exact abstract transition clock.
The generic interaction-path event count agrees with that clock: no
independent cost semantics is introduced.  Richer physical costs, evidence,
provenance, and attention may be product valuations over the same events.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation

open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational

/-- The reference transition metric is the existing constant writer grading.
It counts authentic machine transitions, not the other runtime event kinds. -/
abbrev transitionSpend
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :=
  WriterGSLT.constGrading (machineTheory spec) (Multiplicative.ofAdd (1 : Nat))

/-- Forgetting the meter preserves and reflects the actual reference machine's
steps. The generic writer cover supplies both directions. -/
def transitionMeterErasure
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    SemanticCoveredTranslation
      ((machineTheory spec).spendLift (transitionSpend spec)) (machineTheory spec) :=
  spendErasureCover (transitionSpend spec)
    (WriterGSLT.constGrading_total _)

theorem metered_step_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (before after : Nat) :
    ((machineTheory spec).spendLift (transitionSpend spec)).Step
      (source, Multiplicative.ofAdd before) (target, Multiplicative.ofAdd after) ↔
      (machineTheory spec).Step source target ∧ after = before + 1 := by
  change (∃ grade, ((machineTheory spec).Step source target ∧
    grade = Multiplicative.ofAdd (1 : Nat)) ∧
    Multiplicative.ofAdd after = Multiplicative.ofAdd before * grade) ↔ _
  constructor
  · rintro ⟨grade, ⟨step, rfl⟩, accumulated⟩
    exact ⟨step, congrArg Multiplicative.toAdd accumulated⟩
  · rintro ⟨step, accumulated⟩
    exact ⟨Multiplicative.ofAdd 1, ⟨step, rfl⟩,
      congrArg Multiplicative.ofAdd accumulated⟩

/-- The meter cannot change a cost-blind behavioural observation of this
machine. Cost inspection itself requires a richer observation than erasure. -/
theorem metered_bisimilar_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (before after : Nat) :
    ((machineTheory spec).spendLift (transitionSpend spec)).Bisimilar
      (source, Multiplicative.ofAdd before) (target, Multiplicative.ofAdd after) ↔
      (machineTheory spec).Bisimilar source target :=
  WriterGSLT.spendLift_bisimilar_iff (transitionSpend spec)
    (WriterGSLT.constGrading_total _) _ _

/-- When the meter begins at the existing clock, an actual metered step keeps
them aligned. No independent transition count is assigned to the evaluator. -/
theorem metered_step_preserves_clock
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (source target : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (before after : Nat)
    (aligned : before = source.work.transitions)
    (metered : ((machineTheory spec).spendLift (transitionSpend spec)).Step
      (source, Multiplicative.ofAdd before) (target, Multiplicative.ofAdd after)) :
    after = target.work.transitions := by
  obtain ⟨⟨occurrence⟩, accumulated⟩ := (metered_step_iff spec source target before after).mp metered
  rw [accumulated, aligned, step_increments_transition spec source target (occurrence.mem spec)]

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

/-- The generic event-count valuation and reference's reference work clock report
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

open Mettapedia.Machines.BranchLocalNeed.NeedInteractionAuthority.Canary

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

theorem metered_transition_advances :
    ((machineTheory demoSpec).spendLift (transitionSpend demoSpec)).Step
      (start, Multiplicative.ofAdd 4) (next, Multiplicative.ofAdd 5) :=
  (metered_step_iff demoSpec start next 4 5).mpr ⟨⟨firstOccurrence⟩, rfl⟩

theorem transition_does_not_reset_meter :
    ¬((machineTheory demoSpec).spendLift (transitionSpend demoSpec)).Step
      (start, Multiplicative.ofAdd 4) (next, Multiplicative.ofAdd 1) := by
  rw [metered_step_iff]
  rintro ⟨_, impossible⟩
  omega

end Canary

end Mettapedia.Machines.BranchLocalNeed.NeedInteractionValuation
