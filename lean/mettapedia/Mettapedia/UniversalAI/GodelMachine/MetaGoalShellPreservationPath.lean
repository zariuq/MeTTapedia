import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation

/-!
# Paths of Proof-Backed Meta-Goal-Preserving Rewrites

This module composes the single-step bridge from
`MetaGoalShellPreservation.lean`.

Each step improves Gödel-machine expected utility and preserves a protected
family of WM goals up to a shell bound.  A path of such steps therefore gives:

- cumulative utility improvement, and
- cumulative WM drift bounded by the sum of the step-wise shell tails.

This is the natural path-level form of proof-guided self-modification with
stable semantic identity.
-/

namespace Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A path of proof-backed rewrites preserving a fixed protected goal family.

Each step may use a different shell and even a different protected region, but
the original goal family must remain included in every step's protected goals. -/
inductive MetaGoalShellPreservationPath
    (protectedGoals : Finset (ConstraintQuery Atom)) : Type _ where
  | single
      (first : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId))
      (hgoals : protectedGoals ⊆ first.protectedGoals.goals) :
      MetaGoalShellPreservationPath protectedGoals
  | step
      (path : MetaGoalShellPreservationPath protectedGoals)
      (next : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId))
      (hgoals : protectedGoals ⊆ next.protectedGoals.goals) :
      MetaGoalShellPreservationPath protectedGoals

/-- The starting Gödel-machine state. -/
def MetaGoalShellPreservationPath.startMachine
    {protectedGoals : Finset (ConstraintQuery Atom)} :
    MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals →
      GodelMachineState
  | .single first _ => first.oldMachine
  | .step path _ _ => path.startMachine

/-- The ending Gödel-machine state. -/
def MetaGoalShellPreservationPath.endMachine
    {protectedGoals : Finset (ConstraintQuery Atom)} :
    MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals →
      GodelMachineState
  | .single first _ => first.newMachine
  | .step _ next _ => next.newMachine

/-- The starting Markov-logic specification. -/
def MetaGoalShellPreservationPath.startSpec
    {protectedGoals : Finset (ConstraintQuery Atom)} :
    MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals →
      ClassicalInfiniteGroundMLNSpec Atom ClauseId
  | .single first _ => first.oldSpec
  | .step path _ _ => path.startSpec

/-- The ending Markov-logic specification. -/
def MetaGoalShellPreservationPath.endSpec
    {protectedGoals : Finset (ConstraintQuery Atom)} :
    MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals →
      ClassicalInfiniteGroundMLNSpec Atom ClauseId
  | .single first _ => first.newSpec
  | .step _ next _ => next.newSpec

/-- Coherence means successive rewrites really form a chain on both the
Gödel-machine state and the Markov-logic specification. -/
def MetaGoalShellPreservationPath.Coherent
    {protectedGoals : Finset (ConstraintQuery Atom)} :
    MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals → Prop
  | .single _ _ => True
  | .step path next _ =>
      path.Coherent ∧
      path.endMachine = next.oldMachine ∧
      path.endSpec = next.oldSpec

/-- Sum of the step-wise shell-tail bounds. -/
noncomputable def MetaGoalShellPreservationPath.totalErrorBound
    {protectedGoals : Finset (ConstraintQuery Atom)} :
    MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals → ℝ
  | .single first _ => first.errorBound
  | .step path next _ => path.totalErrorBound + next.errorBound

theorem MetaGoalShellPreservationPath.totalErrorBound_nonneg
    {protectedGoals : Finset (ConstraintQuery Atom)}
    (path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals) :
    0 ≤ path.totalErrorBound := by
  induction path with
  | single first _ =>
      simpa [MetaGoalShellPreservationPath.totalErrorBound] using first.errorBound_nonneg
  | step path next _ ih =>
      simp [MetaGoalShellPreservationPath.totalErrorBound]
      nlinarith [ih, next.errorBound_nonneg]

/-- DLR witnesses for every specification along a meta-goal-preserving path. -/
inductive MetaGoalShellPreservationPathDLR :
    {protectedGoals : Finset (ConstraintQuery Atom)} →
    (path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals) →
    Type _ where
  | single
      {protectedGoals : Finset (ConstraintQuery Atom)}
      {first : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)}
      {hgoals : protectedGoals ⊆ first.protectedGoals.goals}
      (μ₀ : ProbabilityMeasure (InfiniteWorld Atom))
      (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
      (hμ₀ : FixedRegionCylinderDLR first.oldSpec.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₀ : Measure (InfiniteWorld Atom)))
      (hμ₁ : FixedRegionCylinderDLR first.newSpec.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₁ : Measure (InfiniteWorld Atom))) :
      MetaGoalShellPreservationPathDLR (.single first hgoals)
  | step
      {protectedGoals : Finset (ConstraintQuery Atom)}
      {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
      {next : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)}
      {hgoals : protectedGoals ⊆ next.protectedGoals.goals}
      (prev : MetaGoalShellPreservationPathDLR path)
      (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
      (hμ₂ : FixedRegionCylinderDLR next.newSpec.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₂ : Measure (InfiniteWorld Atom))) :
      MetaGoalShellPreservationPathDLR (.step path next hgoals)

noncomputable def MetaGoalShellPreservationPathDLR.startMeasure
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path) :
    ProbabilityMeasure (InfiniteWorld Atom) := by
  induction measures with
  | single μ₀ _ _ _ => exact μ₀
  | step prev _ _ ih => exact ih

noncomputable def MetaGoalShellPreservationPathDLR.endMeasure
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path) :
    ProbabilityMeasure (InfiniteWorld Atom) := by
  induction measures with
  | single _ μ₁ _ _ => exact μ₁
  | step _ μ₂ _ => exact μ₂

theorem MetaGoalShellPreservationPathDLR.startDLR
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path) :
    FixedRegionCylinderDLR path.startSpec.toStrictlyPositiveInfiniteGroundMLNSpec
      ((measures.startMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
        Measure (InfiniteWorld Atom)) := by
  induction measures with
  | single _ _ hμ₀ _ =>
      simpa [MetaGoalShellPreservationPath.startSpec,
        MetaGoalShellPreservationPathDLR.startMeasure] using hμ₀
  | step prev _ _ ih =>
      simpa [MetaGoalShellPreservationPath.startSpec,
        MetaGoalShellPreservationPathDLR.startMeasure] using ih

theorem MetaGoalShellPreservationPathDLR.endDLR
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path) :
    FixedRegionCylinderDLR path.endSpec.toStrictlyPositiveInfiniteGroundMLNSpec
      ((measures.endMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
        Measure (InfiniteWorld Atom)) := by
  induction measures with
  | single _ _ _ hμ₁ =>
      simpa [MetaGoalShellPreservationPath.endSpec,
        MetaGoalShellPreservationPathDLR.endMeasure] using hμ₁
  | step _ _ hμ₂ =>
      simpa [MetaGoalShellPreservationPath.endSpec,
        MetaGoalShellPreservationPathDLR.endMeasure] using hμ₂

theorem MetaGoalShellPreservationPath.utility_improves
    {protectedGoals : Finset (ConstraintQuery Atom)}
    (path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals)
    (hcoh : path.Coherent) :
    expectedUtilityFromStart path.endMachine >
      expectedUtilityFromStart path.startMachine := by
  induction path with
  | single first _ =>
      simpa [MetaGoalShellPreservationPath.startMachine,
        MetaGoalShellPreservationPath.endMachine] using first.utility_improves
  | step path next _ ih =>
      have hcoh' :
          path.Coherent ∧
          path.endMachine = next.oldMachine ∧
          path.endSpec = next.oldSpec := by
        simpa [MetaGoalShellPreservationPath.Coherent] using hcoh
      rcases hcoh' with ⟨hcohPrev, hmachines, _hspecs⟩
      calc
        expectedUtilityFromStart path.startMachine <
            expectedUtilityFromStart path.endMachine := ih hcohPrev
        _ = expectedUtilityFromStart next.oldMachine := by
              simpa [MetaGoalShellPreservationPath.endMachine] using
                congrArg expectedUtilityFromStart hmachines
        _ < expectedUtilityFromStart next.newMachine := next.utility_improves

/-- Cumulative drift of a protected query family at the `queryProb` level. -/
theorem MetaGoalShellPreservationPathDLR.goal_queryProb_cumulative_drift
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedGoals) :
    |((infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR).queryProb q).toReal -
      ((infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR).queryProb q).toReal| ≤
        path.totalErrorBound := by
  induction path generalizing q with
  | single first hgoals =>
      cases measures with
      | single μ₀ μ₁ hμ₀ hμ₁ =>
          simp only [MetaGoalShellPreservationPath.Coherent] at hcoh
          have hq' : q ∈ first.protectedGoals.goals := hgoals hq
          let cross : CrossSpecDLR first.oldSpec first.newSpec :=
            { oldMeasure := μ₀
              newMeasure := μ₁
              oldDLR := hμ₀
              newDLR := hμ₁ }
          simpa [MetaGoalShellPreservationPath.startSpec,
            MetaGoalShellPreservationPath.endSpec,
            MetaGoalShellPreservationPath.totalErrorBound,
            MetaGoalShellPreservationPathDLR.startMeasure,
            MetaGoalShellPreservationPathDLR.endMeasure,
            MetaGoalShellPreservationPathDLR.startDLR,
            MetaGoalShellPreservationPathDLR.endDLR, cross]
            using first.goal_queryProb_approximately_preserved_explicit cross hq'
  | step path next hgoals ih =>
      cases measures with
      | step prev μ₂ hμ₂ =>
          have hcoh' :
              path.Coherent ∧
              path.endMachine = next.oldMachine ∧
              path.endSpec = next.oldSpec := by
            simpa [MetaGoalShellPreservationPath.Coherent] using hcoh
          rcases hcoh' with ⟨hcohPrev, _hmachines, hspecs⟩
          have hprev := ih prev hcohPrev hq
          have hqNext : q ∈ next.protectedGoals.goals := hgoals hq
          have hprevDLR :
              FixedRegionCylinderDLR next.oldSpec.toStrictlyPositiveInfiniteGroundMLNSpec
                ((prev.endMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
                  Measure (InfiniteWorld Atom)) := by
            simpa [hspecs] using prev.endDLR
          have hprev' :
              |((infiniteMLNMassSemantics path.startSpec prev.startMeasure prev.startDLR).queryProb q).toReal -
                ((infiniteMLNMassSemantics next.oldSpec prev.endMeasure hprevDLR).queryProb q).toReal| ≤
                  path.totalErrorBound := by
            simpa [hspecs, hprevDLR] using hprev
          let cross : CrossSpecDLR next.oldSpec next.newSpec :=
            { oldMeasure := prev.endMeasure
              newMeasure := μ₂
              oldDLR := hprevDLR
              newDLR := hμ₂ }
          have hnext_raw := next.goal_queryProb_approximately_preserved_explicit cross hqNext
          let a : ℝ :=
            ((infiniteMLNMassSemantics path.startSpec prev.startMeasure prev.startDLR).queryProb q).toReal
          let b : ℝ :=
            ((infiniteMLNMassSemantics next.oldSpec prev.endMeasure hprevDLR).queryProb q).toReal
          let c : ℝ :=
            ((infiniteMLNMassSemantics next.newSpec μ₂ hμ₂).queryProb q).toReal
          have htri : |a - c| ≤ |a - b| + |b - c| := by
            calc
              |a - c| = |(a - b) + (b - c)| := by ring_nf
              _ ≤ |a - b| + |b - c| := abs_add_le _ _
          have hbound : |a - c| ≤ path.totalErrorBound + next.errorBound := by
            linarith [htri, hprev', hnext_raw]
          simpa [a, b, c,
            MetaGoalShellPreservationPath.startSpec,
            MetaGoalShellPreservationPath.endSpec,
            MetaGoalShellPreservationPath.totalErrorBound,
            MetaGoalShellPreservationPathDLR.startMeasure,
            MetaGoalShellPreservationPathDLR.endMeasure,
            MetaGoalShellPreservationPathDLR.startDLR,
            MetaGoalShellPreservationPathDLR.endDLR]
            using hbound

/-- Cumulative drift of a protected query family at the WM-truth-value layer. -/
theorem MetaGoalShellPreservationPathDLR.goal_wmStrength_cumulative_drift
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedGoals) :
    |(BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
          MassState (ConstraintQuery Atom)) q).toReal -
      (BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
          MassState (ConstraintQuery Atom)) q).toReal| ≤
        path.totalErrorBound := by
  simpa [queryStrength_singleton_eq_queryProb]
    using measures.goal_queryProb_cumulative_drift hcoh hq

/-- Combined path theorem: proof-backed utility improvement together with
bounded cumulative WM drift for every protected goal. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_goal_wmStrength_cumulative_drift
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedGoals) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) q).toReal| ≤
          path.totalErrorBound := by
  exact ⟨path.utility_improves hcoh, measures.goal_wmStrength_cumulative_drift hcoh hq⟩

/-- Corrigibility corollary: if "defer to operator" remains in the protected
goal family along a proof-backed rewrite path, then expected utility improves
while the WM truth value of that deference query drifts by at most the
cumulative shell bound. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_operatorDeference_drift_bounded
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    (operatorDeferenceQuery : ConstraintQuery Atom)
    (hq : operatorDeferenceQuery ∈ protectedGoals) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) operatorDeferenceQuery).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) operatorDeferenceQuery).toReal| ≤
          path.totalErrorBound := by
  exact measures.utility_improves_and_goal_wmStrength_cumulative_drift
    hcoh (q := operatorDeferenceQuery) hq

end Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
