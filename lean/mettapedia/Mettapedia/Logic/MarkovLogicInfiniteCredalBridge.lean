import Mettapedia.Logic.MarkovLogicInfiniteWorldModel
import Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
import Mettapedia.Logic.MarkovLogicInfiniteGlobalDLR
import Mettapedia.Logic.MarkovLogicInfiniteLimitFamily
import Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

/-!
# Infinite MLN Credal Bridge

This file connects the infinite-MLN/DLR surface to the projective credal
reading of imprecise probability.

The central object is the set of σ-additive DLR completions of an infinite MLN.
Taking the lower envelope of query probabilities over that set gives the
Walley-style conservative value for a finite query.  Under Dobrushin uniqueness
the envelope collapses to a point; when two completions disagree, the envelope
is nontrivial.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteCredalBridge

open Set
open MeasureTheory
open Filter
open scoped ENNReal

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteLimitFamily
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A σ-additive DLR completion of an infinite MLN specification.  This is the
MLN/Gibbs specialization of the generic projective credal completion set. -/
abbrev DLRCompletion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :=
  {μ : ProbabilityMeasure (InfiniteWorld Atom) //
    FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom))}

namespace DLRCompletion

/-- Convex mixture of two DLR completions.  The fixed-region cylinder DLR law
is affine in the ambient probability measure, so the mixture is again a DLR
completion. -/
noncomputable def mix
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (p : unitInterval) (μ ν : DLRCompletion M) :
    DLRCompletion M where
  val :=
    ⟨unitInterval.toNNReal p • (μ.1 : Measure (InfiniteWorld Atom)) +
      unitInterval.toNNReal (unitInterval.symm p) •
        (ν.1 : Measure (InfiniteWorld Atom)),
      inferInstance⟩
  property :=
    FixedRegionCylinderDLR.mix M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ.1 : Measure (InfiniteWorld Atom))
      (ν.1 : Measure (InfiniteWorld Atom)) μ.2 ν.2 p

end DLRCompletion

/-- Query probability supplied by one DLR completion, converted to a real
number for lower/upper-envelope comparisons. -/
noncomputable def dlrCompletionQueryProb
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) : ℝ :=
  ENNReal.toReal
    ((infiniteMLNMassSemantics M μ.1 μ.2).queryProb q)

/-- A DLR completion query probability is the real value of the completion's
measure on the corresponding measurable finite-cylinder event. -/
theorem dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    dlrCompletionQueryProb M q μ =
      ENNReal.toReal
        ((μ.1 : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q)) := by
  simp [dlrCompletionQueryProb,
    infiniteMLNMassSemantics_queryProb_eq_measure_infiniteQueryEvent]

/-- The 0/1 gamble associated to a finite infinite-MLN query.  This is the
query-as-gamble object used by the Walley lower/upper envelope layer. -/
def infiniteQueryIndicatorGamble
    (q : ConstraintQuery Atom) : Gamble (InfiniteWorld Atom) :=
  fun ω => if satisfiesConstraints ω q then 1 else 0

omit [DecidableEq Atom] in
@[simp] theorem infiniteQueryIndicatorGamble_apply
    (q : ConstraintQuery Atom) (ω : InfiniteWorld Atom) :
    infiniteQueryIndicatorGamble q ω =
      if satisfiesConstraints ω q then 1 else 0 :=
  rfl

omit [DecidableEq Atom] in
theorem infiniteQueryIndicatorGamble_nonneg
    (q : ConstraintQuery Atom) (ω : InfiniteWorld Atom) :
    0 ≤ infiniteQueryIndicatorGamble q ω := by
  by_cases h : satisfiesConstraints ω q
  · simp [infiniteQueryIndicatorGamble, h]
  · simp [infiniteQueryIndicatorGamble, h]

omit [DecidableEq Atom] in
theorem infiniteQueryIndicatorGamble_le_one
    (q : ConstraintQuery Atom) (ω : InfiniteWorld Atom) :
    infiniteQueryIndicatorGamble q ω ≤ 1 := by
  by_cases h : satisfiesConstraints ω q
  · simp [infiniteQueryIndicatorGamble, h]
  · simp [infiniteQueryIndicatorGamble, h]

omit [DecidableEq Atom] in
theorem infiniteQueryIndicatorGamble_mem_Icc
    (q : ConstraintQuery Atom) (ω : InfiniteWorld Atom) :
    infiniteQueryIndicatorGamble q ω ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨infiniteQueryIndicatorGamble_nonneg q ω,
    infiniteQueryIndicatorGamble_le_one q ω⟩

omit [DecidableEq Atom] in
theorem infiniteQueryIndicatorGamble_eq_one_iff
    (q : ConstraintQuery Atom) (ω : InfiniteWorld Atom) :
    infiniteQueryIndicatorGamble q ω = 1 ↔
      ω ∈ infiniteQueryEvent q := by
  by_cases h : satisfiesConstraints ω q
  · simp [infiniteQueryIndicatorGamble, infiniteQueryEvent, h]
  · simp [infiniteQueryIndicatorGamble, infiniteQueryEvent, h]

omit [DecidableEq Atom] in
theorem precisePrevision_infiniteQueryIndicatorGamble_nonneg
    (P : PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom) :
    0 ≤ P (infiniteQueryIndicatorGamble q) :=
  P.lower_bound (infiniteQueryIndicatorGamble q) 0
    (infiniteQueryIndicatorGamble_nonneg q)

omit [DecidableEq Atom] in
theorem precisePrevision_infiniteQueryIndicatorGamble_le_one
    (P : PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom) :
    P (infiniteQueryIndicatorGamble q) ≤ 1 :=
  P.upper_bound (infiniteQueryIndicatorGamble q) 1
    (infiniteQueryIndicatorGamble_le_one q)

/-- DLR query probabilities are nonnegative after conversion to real values. -/
theorem dlrCompletionQueryProb_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    0 ≤ dlrCompletionQueryProb M q μ := by
  rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
  exact ENNReal.toReal_nonneg

/-- DLR query probabilities are at most one after conversion to real values. -/
theorem dlrCompletionQueryProb_le_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    dlrCompletionQueryProb M q μ ≤ 1 := by
  rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
  have hle :
      ((μ.1 : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q)) ≤
        (1 : ENNReal) := by
    calc
      ((μ.1 : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q))
          ≤ (μ.1 : Measure (InfiniteWorld Atom)) Set.univ :=
            measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle

theorem dlrCompletionQueryProb_mem_Icc
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    dlrCompletionQueryProb M q μ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨dlrCompletionQueryProb_nonneg M q μ,
    dlrCompletionQueryProb_le_one M q μ⟩

/-- A finite query is DLR-determined when all σ-additive DLR completions give
the same query probability. -/
def dlrQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : Prop :=
  ∀ μ ν : DLRCompletion M,
    dlrCompletionQueryProb M q μ = dlrCompletionQueryProb M q ν

/-- A finite query has strict DLR width when two σ-additive DLR completions
strictly disagree on its probability. -/
def dlrQueryHasStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : Prop :=
  ∃ μ : DLRCompletion M, ∃ ν : DLRCompletion M,
    dlrCompletionQueryProb M q μ < dlrCompletionQueryProb M q ν

/-- The concrete binary finite-weight projection of a DLR completion along a
finite query: `true` receives the query probability and `false` receives its
complement. -/
noncomputable def dlrQueryOutcomeFiniteWeights
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    PrecisePrevision.FiniteWeights Bool where
  weight b := if b then dlrCompletionQueryProb M q μ
    else 1 - dlrCompletionQueryProb M q μ
  nonneg := by
    intro b
    cases b <;> simp [dlrCompletionQueryProb_nonneg,
      dlrCompletionQueryProb_le_one]
  total := by
    rw [Fintype.sum_bool]
    simp

/-- The concrete binary precise prevision induced by a DLR completion and a
finite query.  This is the PLN-facing two-outcome projection of the DLR
completion, not a full expectation functional on all infinite-world gambles. -/
noncomputable def dlrQueryOutcomePrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    PrecisePrevision Bool :=
  (dlrQueryOutcomeFiniteWeights M q μ).toPrecisePrevision

@[simp] theorem dlrQueryOutcomeFiniteWeights_true
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    (dlrQueryOutcomeFiniteWeights M q μ).weight true =
      dlrCompletionQueryProb M q μ :=
  rfl

@[simp] theorem dlrQueryOutcomeFiniteWeights_false
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    (dlrQueryOutcomeFiniteWeights M q μ).weight false =
      1 - dlrCompletionQueryProb M q μ :=
  rfl

@[simp] theorem dlrQueryOutcomePrevision_apply
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M)
    (X : Gamble Bool) :
    dlrQueryOutcomePrevision M q μ X =
      ∑ b, (dlrQueryOutcomeFiniteWeights M q μ).weight b * X b :=
  rfl

theorem dlrQueryOutcomePrevision_precise
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    (dlrQueryOutcomePrevision M q μ).toLowerPrevision.isPrecise :=
  PrecisePrevision.FiniteWeights.toPrecisePrevision_precise
    (dlrQueryOutcomeFiniteWeights M q μ)

theorem dlrQueryOutcomePrevision_true_atom
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    dlrQueryOutcomePrevision M q μ
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      dlrCompletionQueryProb M q μ := by
  rw [dlrQueryOutcomePrevision_apply, Fintype.sum_bool]
  simp [PrecisePrevision.FiniteWeights.atomGamble]

/-- The binary credal set obtained by projecting every DLR completion onto the
two outcomes of a fixed finite query. -/
def dlrQueryOutcomeCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : CredalPrevisionSet Bool :=
  {P | ∃ μ : DLRCompletion M, P = dlrQueryOutcomePrevision M q μ}

@[simp] theorem mem_dlrQueryOutcomeCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    dlrQueryOutcomePrevision M q μ ∈ dlrQueryOutcomeCredalSet M q :=
  ⟨μ, rfl⟩

theorem dlrQueryOutcomeCredalSet_nonempty
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeCredalSet M q).Nonempty := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact ⟨dlrQueryOutcomePrevision M q μ,
    mem_dlrQueryOutcomeCredalSet M q μ⟩

/-- The lower envelope of the binary DLR query-outcome credal set is below
every projected DLR completion. -/
theorem dlrQueryOutcomeLowerEnvelope_le_completion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M)
    (X : Gamble Bool) :
    lowerEnvelope (dlrQueryOutcomeCredalSet M q) X ≤
      dlrQueryOutcomePrevision M q μ X := by
  simpa using
    finiteLowerEnvelopePrevision_le_completion
      (dlrQueryOutcomeCredalSet M q)
      (⟨dlrQueryOutcomePrevision M q μ,
        mem_dlrQueryOutcomeCredalSet M q μ⟩)
      (P := dlrQueryOutcomePrevision M q μ)
      (mem_dlrQueryOutcomeCredalSet M q μ) X

/-- The lower envelope of the binary DLR query-outcome credal set is the
greatest lower prevision dominated by every projected DLR completion. -/
theorem dlrQueryOutcomeLowerEnvelope_greatest_lower_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom)
    (L : LowerPrevision Bool)
    (hL : ∀ μ : DLRCompletion M, ∀ X : Gamble Bool,
      L X ≤ dlrQueryOutcomePrevision M q μ X)
    (X : Gamble Bool) :
    L X ≤ lowerEnvelope (dlrQueryOutcomeCredalSet M q) X := by
  simpa using
    finiteLowerEnvelopePrevision_greatest_lower_bound
      (dlrQueryOutcomeCredalSet M q)
      (dlrQueryOutcomeCredalSet_nonempty M q) L
      (by
        intro P hP Y
        rcases hP with ⟨μ, rfl⟩
        exact hL μ Y)
      X

/-- Every projected DLR completion is below the upper envelope of the binary
query-outcome credal set. -/
theorem dlrQueryOutcomeCompletion_le_upperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M)
    (X : Gamble Bool) :
    dlrQueryOutcomePrevision M q μ X ≤
      upperEnvelope (dlrQueryOutcomeCredalSet M q) X := by
  simpa using
    finiteCompletion_le_upperEnvelopePrevision
      (dlrQueryOutcomeCredalSet M q)
      (⟨dlrQueryOutcomePrevision M q μ,
        mem_dlrQueryOutcomeCredalSet M q μ⟩)
      (P := dlrQueryOutcomePrevision M q μ)
      (mem_dlrQueryOutcomeCredalSet M q μ) X

/-- The upper envelope of the binary DLR query-outcome credal set is the least
upper prevision dominating every projected DLR completion. -/
theorem dlrQueryOutcomeUpperEnvelope_least_upper_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom)
    (U : UpperPrevision Bool)
    (hU : ∀ μ : DLRCompletion M, ∀ X : Gamble Bool,
      dlrQueryOutcomePrevision M q μ X ≤ U X)
    (X : Gamble Bool) :
    upperEnvelope (dlrQueryOutcomeCredalSet M q) X ≤ U X := by
  simpa using
    finiteUpperEnvelopePrevision_least_upper_bound
      (dlrQueryOutcomeCredalSet M q)
      (dlrQueryOutcomeCredalSet_nonempty M q) U
      (by
        intro P hP Y
        rcases hP with ⟨μ, rfl⟩
        exact hU μ Y)
      X

/-- If DLR completions determine a query, their concrete binary projected
credal set determines the `true` outcome gamble. -/
theorem dlrQueryOutcomeCredalSet_determines_true_atom_of_queryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hDet : dlrQueryDetermined M q) :
    credalSetDetermines (dlrQueryOutcomeCredalSet M q)
      (PrecisePrevision.FiniteWeights.atomGamble true) := by
  intro P hP Q hQ
  rcases hP with ⟨μ, rfl⟩
  rcases hQ with ⟨ν, rfl⟩
  rw [dlrQueryOutcomePrevision_true_atom,
    dlrQueryOutcomePrevision_true_atom, hDet μ ν]

/-- If two DLR completions strictly disagree on a query, the concrete binary
projected credal set has strict width on the `true` outcome gamble. -/
theorem dlrQueryOutcomeCredalSet_hasStrictWidth_true_atom_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    credalSetHasStrictWidth (dlrQueryOutcomeCredalSet M q)
      (PrecisePrevision.FiniteWeights.atomGamble true) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  refine ⟨dlrQueryOutcomePrevision M q μ,
    mem_dlrQueryOutcomeCredalSet M q μ,
    dlrQueryOutcomePrevision M q ν,
    mem_dlrQueryOutcomeCredalSet M q ν, ?_⟩
  rw [dlrQueryOutcomePrevision_true_atom,
    dlrQueryOutcomePrevision_true_atom]
  exact hlt

theorem dlrQueryOutcomeCredalSet_not_determines_true_atom_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    ¬ credalSetDetermines (dlrQueryOutcomeCredalSet M q)
      (PrecisePrevision.FiniteWeights.atomGamble true) :=
  not_credalSetDetermines_of_strictWidth
    (dlrQueryOutcomeCredalSet_hasStrictWidth_true_atom_of_queryStrictWidth
      M q hWidth)

/-- The concrete binary DLR query-outcome credal set, packaged as a one-window
projective local-credal specification. -/
def dlrQueryOutcomeProjectiveSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    ProjectiveLocalCredalSpec PUnit.{1} Bool :=
  identityCredalProjectiveSpec (dlrQueryOutcomeCredalSet M q)

@[simp] theorem dlrQueryOutcomeProjectiveSpec_projectiveLimitCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet =
      dlrQueryOutcomeCredalSet M q := by
  simp [dlrQueryOutcomeProjectiveSpec]

theorem dlrQueryOutcomeProjectiveSpec_hasCompatibleCompletion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeProjectiveSpec M q).hasCompatibleCompletion := by
  rw [dlrQueryOutcomeProjectiveSpec,
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact dlrQueryOutcomeCredalSet_nonempty M q

theorem dlrQueryOutcomeProjectiveSpec_determines_true_atom_of_queryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hDet : dlrQueryDetermined M q) :
    (dlrQueryOutcomeProjectiveSpec M q).determinesGlobalGamble
      (PrecisePrevision.FiniteWeights.atomGamble true) := by
  rw [dlrQueryOutcomeProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  exact dlrQueryOutcomeCredalSet_determines_true_atom_of_queryDetermined
    M q hDet

theorem dlrQueryOutcomeProjectiveSpec_hasStrictWidth_true_atom_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    (dlrQueryOutcomeProjectiveSpec M q).hasStrictGlobalWidth
      (PrecisePrevision.FiniteWeights.atomGamble true) := by
  rw [dlrQueryOutcomeProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  exact dlrQueryOutcomeCredalSet_hasStrictWidth_true_atom_of_queryStrictWidth
    M q hWidth

theorem dlrQueryOutcomeProjectiveSpec_not_determines_true_atom_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    ¬ (dlrQueryOutcomeProjectiveSpec M q).determinesGlobalGamble
      (PrecisePrevision.FiniteWeights.atomGamble true) := by
  rw [dlrQueryOutcomeProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  exact dlrQueryOutcomeCredalSet_not_determines_true_atom_of_queryStrictWidth
    M q hWidth

/-- Evaluating the concrete binary query-outcome credal set on the `true`
atom ranges over exactly the same values as the DLR query-probability map. -/
theorem dlrQueryOutcomeCredalSet_true_atom_value_image_eq_range
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    ((fun P : PrecisePrevision Bool =>
      P (PrecisePrevision.FiniteWeights.atomGamble true)) ''
        dlrQueryOutcomeCredalSet M q) =
      Set.range (dlrCompletionQueryProb M q) := by
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨μ, rfl⟩
    exact ⟨μ, by
      change dlrCompletionQueryProb M q μ =
        dlrQueryOutcomePrevision M q μ
          (PrecisePrevision.FiniteWeights.atomGamble true)
      rw [dlrQueryOutcomePrevision_true_atom]⟩
  · rintro ⟨μ, rfl⟩
    refine ⟨dlrQueryOutcomePrevision M q μ,
      mem_dlrQueryOutcomeCredalSet M q μ, ?_⟩
    change dlrQueryOutcomePrevision M q μ
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      dlrCompletionQueryProb M q μ
    rw [dlrQueryOutcomePrevision_true_atom]

/-! ## Concrete finite-window prevision adapters -/

/-- A finite-volume MLN assignment PMF induces an honest finite precise
prevision on local cylinder gambles.  This is the concrete adapter used before
one passes to global DLR completions. -/
noncomputable def finiteVolumeAssignmentPrevision
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    PrecisePrevision (LocalAssignment Atom Λ) :=
  PrecisePrevision.FiniteWeights.ofPMFPrevision
    (finiteVolumeAssignmentPMF M Λ ξ hZ)

@[simp] theorem finiteVolumeAssignmentPrevision_apply
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (X : Gamble (LocalAssignment Atom Λ)) :
    finiteVolumeAssignmentPrevision M Λ ξ hZ X =
      ∑ x, (finiteVolumeAssignmentPMF M Λ ξ hZ x).toReal * X x :=
  rfl

theorem finiteVolumeAssignmentPrevision_precise
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    (finiteVolumeAssignmentPrevision M Λ ξ hZ).toLowerPrevision.isPrecise :=
  PrecisePrevision.FiniteWeights.ofPMFPrevision_precise
    (finiteVolumeAssignmentPMF M Λ ξ hZ)

/-- A finite-volume local assignment law induces a finite-support precise
prevision on the full infinite-world space by patching sampled assignments
into the boundary condition.  This is a concrete global-world
measure-to-prevision adapter for finite-volume MLN cylinders; the fully
infinite DLR adapter is the weak*/limit refinement of this construction. -/
noncomputable def finiteVolumeWorldPrevision
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    PrecisePrevision (InfiniteWorld Atom) :=
  (PrecisePrevision.FiniteWeights.ofPMF
    (finiteVolumeAssignmentPMF M Λ ξ hZ)).pushForwardPrevision
      (fun x : LocalAssignment Atom Λ => patch Λ x ξ)

@[simp] theorem finiteVolumeWorldPrevision_apply
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (X : Gamble (InfiniteWorld Atom)) :
    finiteVolumeWorldPrevision M Λ ξ hZ X =
      ∑ x, (finiteVolumeAssignmentPMF M Λ ξ hZ x).toReal *
        X (patch Λ x ξ) :=
  rfl

theorem finiteVolumeWorldPrevision_precise
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    (finiteVolumeWorldPrevision M Λ ξ hZ).toLowerPrevision.isPrecise :=
  PrecisePrevision.FiniteWeights.pushForwardPrevision_precise
    (PrecisePrevision.FiniteWeights.ofPMF
      (finiteVolumeAssignmentPMF M Λ ξ hZ))
    (fun x : LocalAssignment Atom Λ => patch Λ x ξ)

/-- The same finite-volume local semantics adapted through its probability
measure on assignments.  This is the concrete measure-to-prevision adapter for
finite/cylinder MLN gambles; the infinite-world weak* adapter is a separate
functional-analysis refinement. -/
noncomputable def finiteVolumeAssignmentMeasurePrevision
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    PrecisePrevision (LocalAssignment Atom Λ) :=
  PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
    ((finiteVolumeAssignmentPMF M Λ ξ hZ).toMeasure)

@[simp] theorem finiteVolumeAssignmentMeasurePrevision_apply
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (X : Gamble (LocalAssignment Atom Λ)) :
    finiteVolumeAssignmentMeasurePrevision M Λ ξ hZ X =
      ∑ x,
        (((finiteVolumeAssignmentPMF M Λ ξ hZ).toMeasure)
          ({x} : Set (LocalAssignment Atom Λ))).toReal * X x :=
  rfl

theorem finiteVolumeAssignmentMeasurePrevision_precise
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    (finiteVolumeAssignmentMeasurePrevision M Λ ξ hZ).toLowerPrevision.isPrecise :=
  PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise
    ((finiteVolumeAssignmentPMF M Λ ξ hZ).toMeasure)

/-- The local 0/1 gamble associated to a finite-region DLR query. -/
noncomputable def localQueryIndicatorGamble
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    Gamble (LocalAssignment Atom Λ) := by
  classical
  exact fun x => if x ∈ localConstraintSet Λ q then 1 else 0

theorem localQueryIndicatorGamble_nonneg
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (x : LocalAssignment Atom Λ) :
    0 ≤ localQueryIndicatorGamble Λ q x := by
  classical
  unfold localQueryIndicatorGamble
  by_cases hx : x ∈ localConstraintSet Λ q <;> simp [hx]

theorem localQueryIndicatorGamble_le_one
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (x : LocalAssignment Atom Λ) :
    localQueryIndicatorGamble Λ q x ≤ 1 := by
  classical
  unfold localQueryIndicatorGamble
  by_cases hx : x ∈ localConstraintSet Λ q <;> simp [hx]

theorem localQueryIndicatorGamble_mem_Icc
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (x : LocalAssignment Atom Λ) :
    localQueryIndicatorGamble Λ q x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨localQueryIndicatorGamble_nonneg Λ q x,
    localQueryIndicatorGamble_le_one Λ q x⟩

/-- A σ-additive DLR completion induces a concrete finite-region precise
prevision by taking its finite-dimensional marginal. -/
noncomputable def dlrCompletionRegionPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) :
    PrecisePrevision (LocalAssignment Atom Λ) := by
  let ν : Measure (LocalAssignment Atom Λ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Λ
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  exact PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision ν

/-- A σ-additive DLR completion induces a bounded-measurable prevision on each
finite region by taking its finite-dimensional marginal. -/
noncomputable def dlrCompletionLocalBoundedMeasurablePrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) :
    BoundedMeasurablePrecisePrevision (LocalAssignment Atom Λ) := by
  let ν : Measure (LocalAssignment Atom Λ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Λ
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  exact BoundedMeasurablePrecisePrevision.ofProbabilityMeasure ν

/-- On a finite DLR region, the bounded-measurable marginal prevision agrees
with the raw finite-region prevision on every raw local gamble. -/
theorem dlrCompletionLocalBoundedMeasurablePrevision_ofFinite_eq_regionPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom)
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrCompletionLocalBoundedMeasurablePrevision M μ Λ
        (BoundedMeasurableGamble.ofFinite X) =
      dlrCompletionRegionPrevision M μ Λ X := by
  unfold dlrCompletionLocalBoundedMeasurablePrevision
    dlrCompletionRegionPrevision
  let ν : Measure (LocalAssignment Atom Λ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Λ
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  exact
    PrecisePrevision.FiniteWeights.boundedMeasurablePrevision_ofFinite_eq_finiteProbabilityMeasurePrevision
      ν X

/-- The raw finite-region DLR prevision is exactly the canonical finite raw
extension of its bounded-measurable marginal prevision. -/
theorem dlrCompletionRegionPrevision_eq_toRawFinitePrecisePrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) :
    dlrCompletionRegionPrevision M μ Λ =
      (dlrCompletionLocalBoundedMeasurablePrevision M μ Λ).toRawFinitePrecisePrevision := by
  ext X
  rw [BoundedMeasurablePrecisePrevision.toRawFinitePrecisePrevision_apply]
  exact
    (dlrCompletionLocalBoundedMeasurablePrevision_ofFinite_eq_regionPrevision
      M μ Λ X).symm

/-- Restricting the raw finite-region DLR prevision back to bounded-measurable
local observables recovers the bounded-measurable marginal prevision. -/
theorem dlrCompletionRegionPrevision_restrictBoundedMeasurable_eq_local
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) :
    (dlrCompletionRegionPrevision M μ Λ).restrictBoundedMeasurable =
      dlrCompletionLocalBoundedMeasurablePrevision M μ Λ := by
  rw [dlrCompletionRegionPrevision_eq_toRawFinitePrecisePrevision,
    BoundedMeasurablePrecisePrevision.restrictBoundedMeasurable_toRawFinitePrecisePrevision]

theorem dlrCompletionRegionPrevision_precise
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) :
    (dlrCompletionRegionPrevision M μ Λ).toLowerPrevision.isPrecise := by
  unfold dlrCompletionRegionPrevision
  exact PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_precise _

/-- Evaluating the finite-region indicator gamble in the marginal prevision
recovers the DLR completion's probability of the corresponding cylinder event. -/
theorem dlrCompletionRegionPrevision_localQueryIndicator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    dlrCompletionRegionPrevision M μ Λ (localQueryIndicatorGamble Λ q) =
      ENNReal.toReal
        ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q)) := by
  classical
  unfold dlrCompletionRegionPrevision localQueryIndicatorGamble
  let ν : Measure (LocalAssignment Atom Λ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Λ
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  change PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision ν
      (fun x => if x ∈ localConstraintSet Λ q then (1 : ℝ) else 0) =
    ENNReal.toReal
      ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q))
  calc
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision ν
        (fun x => if x ∈ localConstraintSet Λ q then (1 : ℝ) else 0)
        = (ν (localConstraintSet Λ q)).toReal := by
            exact
              PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_indicator
                ν (localConstraintSet Λ q)
    _ = ENNReal.toReal
          ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q)) := by
            rw [RegionExhaustion.limitMarginal_apply_localConstraintSet]

/-- Local finite-region query probability supplied by a DLR completion. -/
noncomputable def dlrCompletionLocalQueryProb
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (μ : DLRCompletion M) : ℝ :=
  ENNReal.toReal
    ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q))

/-- The finite-region credal set obtained by marginalizing every DLR completion
to the finite assignment space of `Λ`. -/
def dlrRegionCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) : CredalPrevisionSet (LocalAssignment Atom Λ) :=
  {P | ∃ μ : DLRCompletion M, P = dlrCompletionRegionPrevision M μ Λ}

@[simp] theorem mem_dlrRegionCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (μ : DLRCompletion M) :
    dlrCompletionRegionPrevision M μ Λ ∈ dlrRegionCredalSet M Λ :=
  ⟨μ, rfl⟩

theorem dlrRegionCredalSet_nonempty
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] (Λ : Region Atom) :
    (dlrRegionCredalSet M Λ).Nonempty := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact ⟨dlrCompletionRegionPrevision M μ Λ,
    mem_dlrRegionCredalSet M Λ μ⟩

/-- The finite-region DLR credal set packaged as a one-window projective local
credal specification.  The one window is the identity window on the finite local
assignment space; the credal content is the set of DLR finite-dimensional
marginal previsions. -/
def dlrRegionProjectiveSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) : ProjectiveLocalCredalSpec PUnit.{1} (LocalAssignment Atom Λ) :=
  identityCredalProjectiveSpec (dlrRegionCredalSet M Λ)

@[simp] theorem dlrRegionProjectiveSpec_projectiveLimitCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) :
    (dlrRegionProjectiveSpec M Λ).projectiveLimitCredalSet =
      dlrRegionCredalSet M Λ := by
  simp [dlrRegionProjectiveSpec]

theorem dlrRegionProjectiveSpec_hasCompatibleCompletion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] (Λ : Region Atom) :
    (dlrRegionProjectiveSpec M Λ).hasCompatibleCompletion := by
  rw [dlrRegionProjectiveSpec,
    identityCredalProjectiveSpec_hasCompatibleCompletion_iff]
  exact dlrRegionCredalSet_nonempty M Λ

theorem dlrRegionCredalSet_localQuery_value_image_eq_range
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    ((fun P : PrecisePrevision (LocalAssignment Atom Λ) =>
      P (localQueryIndicatorGamble Λ q)) '' dlrRegionCredalSet M Λ) =
      Set.range (dlrCompletionLocalQueryProb M Λ q) := by
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨μ, rfl⟩
    exact ⟨μ, (dlrCompletionRegionPrevision_localQueryIndicator M μ Λ q).symm⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨dlrCompletionRegionPrevision M μ Λ,
      mem_dlrRegionCredalSet M Λ μ,
      dlrCompletionRegionPrevision_localQueryIndicator M μ Λ q⟩

/-- Evaluating an arbitrary finite-region local gamble over the DLR region
credal set ranges over exactly the same values as evaluating it in each DLR
completion's finite-region prevision. -/
theorem dlrRegionCredalSet_localGamble_value_image_eq_range
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    ((fun P : PrecisePrevision (LocalAssignment Atom Λ) => P X) ''
        dlrRegionCredalSet M Λ) =
      Set.range (fun μ : DLRCompletion M =>
        dlrCompletionRegionPrevision M μ Λ X) := by
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨μ, rfl⟩
    exact ⟨μ, rfl⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨dlrCompletionRegionPrevision M μ Λ,
      mem_dlrRegionCredalSet M Λ μ, rfl⟩

/-- The lower DLR envelope for a finite-region local query. -/
noncomputable def dlrLocalQueryLowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : ℝ :=
  sInf (Set.range (dlrCompletionLocalQueryProb M Λ q))

/-- The upper DLR envelope for a finite-region local query. -/
noncomputable def dlrLocalQueryUpperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : ℝ :=
  sSup (Set.range (dlrCompletionLocalQueryProb M Λ q))

/-- Width of the finite-region DLR lower/upper local-query envelope. -/
noncomputable def dlrLocalQueryEnvelopeWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : ℝ :=
  dlrLocalQueryUpperEnvelope M Λ q - dlrLocalQueryLowerEnvelope M Λ q

/-- Width-complement confidence coordinate for a finite-region DLR local query. -/
noncomputable def dlrLocalQueryEnvelopeWidthComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : ℝ :=
  1 - dlrLocalQueryEnvelopeWidth M Λ q

/-- Midpoint strength coordinate for a finite-region DLR local query. -/
noncomputable def dlrLocalQueryEnvelopeMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : ℝ :=
  (dlrLocalQueryLowerEnvelope M Λ q + dlrLocalQueryUpperEnvelope M Λ q) / 2

/-- The lower DLR envelope for an arbitrary finite-region local gamble. -/
noncomputable def dlrLocalGambleLowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : ℝ :=
  sInf (Set.range (fun μ : DLRCompletion M =>
    dlrCompletionRegionPrevision M μ Λ X))

/-- The upper DLR envelope for an arbitrary finite-region local gamble. -/
noncomputable def dlrLocalGambleUpperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : ℝ :=
  sSup (Set.range (fun μ : DLRCompletion M =>
    dlrCompletionRegionPrevision M μ Λ X))

/-- Width of the finite-region DLR lower/upper local-gamble envelope. -/
noncomputable def dlrLocalGambleEnvelopeWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : ℝ :=
  dlrLocalGambleUpperEnvelope M Λ X - dlrLocalGambleLowerEnvelope M Λ X

/-- Width-complement confidence coordinate for a finite-region local gamble. -/
noncomputable def dlrLocalGambleEnvelopeWidthComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : ℝ :=
  1 - dlrLocalGambleEnvelopeWidth M Λ X

/-- Midpoint strength coordinate for a finite-region local gamble. -/
noncomputable def dlrLocalGambleEnvelopeMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : ℝ :=
  (dlrLocalGambleLowerEnvelope M Λ X +
    dlrLocalGambleUpperEnvelope M Λ X) / 2

theorem lowerEnvelope_dlrRegionCredalSet_localQuery_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    lowerEnvelope (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryLowerEnvelope M Λ q := by
  unfold lowerEnvelope dlrLocalQueryLowerEnvelope
  rw [dlrRegionCredalSet_localQuery_value_image_eq_range]

theorem upperEnvelope_dlrRegionCredalSet_localQuery_eq_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    upperEnvelope (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryUpperEnvelope M Λ q := by
  unfold upperEnvelope dlrLocalQueryUpperEnvelope
  rw [dlrRegionCredalSet_localQuery_value_image_eq_range]

theorem credalEnvelopeWidth_dlrRegionCredalSet_localQuery_eq_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    credalEnvelopeWidth (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeWidth M Λ q := by
  unfold credalEnvelopeWidth dlrLocalQueryEnvelopeWidth
  rw [upperEnvelope_dlrRegionCredalSet_localQuery_eq_upper,
    lowerEnvelope_dlrRegionCredalSet_localQuery_eq_lower]

theorem credalEnvelopeWidthComplement_dlrRegionCredalSet_localQuery_eq_complement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    credalEnvelopeWidthComplement (dlrRegionCredalSet M Λ)
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeWidthComplement M Λ q := by
  unfold credalEnvelopeWidthComplement dlrLocalQueryEnvelopeWidthComplement
  rw [credalEnvelopeWidth_dlrRegionCredalSet_localQuery_eq_width]

theorem credalEnvelopeMidpoint_dlrRegionCredalSet_localQuery_eq_midpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    credalEnvelopeMidpoint (dlrRegionCredalSet M Λ)
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeMidpoint M Λ q := by
  unfold credalEnvelopeMidpoint dlrLocalQueryEnvelopeMidpoint
  rw [lowerEnvelope_dlrRegionCredalSet_localQuery_eq_lower,
    upperEnvelope_dlrRegionCredalSet_localQuery_eq_upper]

theorem lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    lowerEnvelope (dlrRegionCredalSet M Λ) X =
      dlrLocalGambleLowerEnvelope M Λ X := by
  unfold lowerEnvelope dlrLocalGambleLowerEnvelope
  rw [dlrRegionCredalSet_localGamble_value_image_eq_range]

/-- The finite-region DLR local lower envelope is below every concrete DLR
completion's region prevision. -/
theorem dlrLocalGambleLowerEnvelope_le_completion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (μ : DLRCompletion M)
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrLocalGambleLowerEnvelope M Λ X ≤
      dlrCompletionRegionPrevision M μ Λ X := by
  rw [← lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]
  exact
    finiteLowerEnvelopePrevision_le_completion
      (dlrRegionCredalSet M Λ)
      ⟨dlrCompletionRegionPrevision M μ Λ, mem_dlrRegionCredalSet M Λ μ⟩
      (P := dlrCompletionRegionPrevision M μ Λ)
      (mem_dlrRegionCredalSet M Λ μ) X

/-- The finite-region DLR local lower envelope is the greatest lower prevision
dominated by every concrete DLR completion's region prevision. -/
theorem dlrLocalGambleLowerEnvelope_greatest_lower_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    (L : LowerPrevision (LocalAssignment Atom Λ))
    (hL : ∀ μ : DLRCompletion M,
      ∀ X : Gamble (LocalAssignment Atom Λ),
        L X ≤ dlrCompletionRegionPrevision M μ Λ X)
    (X : Gamble (LocalAssignment Atom Λ)) :
    L X ≤ dlrLocalGambleLowerEnvelope M Λ X := by
  rw [← lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]
  exact
    finiteLowerEnvelopePrevision_greatest_lower_bound
      (dlrRegionCredalSet M Λ) (dlrRegionCredalSet_nonempty M Λ) L
      (by
        intro P hP Y
        rcases hP with ⟨μ, rfl⟩
        exact hL μ Y)
      X

theorem upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    upperEnvelope (dlrRegionCredalSet M Λ) X =
      dlrLocalGambleUpperEnvelope M Λ X := by
  unfold upperEnvelope dlrLocalGambleUpperEnvelope
  rw [dlrRegionCredalSet_localGamble_value_image_eq_range]

/-- Every concrete DLR completion's region prevision is below the finite-region
DLR local upper envelope. -/
theorem dlrCompletion_le_localGambleUpperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (μ : DLRCompletion M)
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrCompletionRegionPrevision M μ Λ X ≤
      dlrLocalGambleUpperEnvelope M Λ X := by
  rw [← upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]
  exact
    finiteCompletion_le_upperEnvelopePrevision
      (dlrRegionCredalSet M Λ)
      ⟨dlrCompletionRegionPrevision M μ Λ, mem_dlrRegionCredalSet M Λ μ⟩
      (P := dlrCompletionRegionPrevision M μ Λ)
      (mem_dlrRegionCredalSet M Λ μ) X

/-- The finite-region DLR local upper envelope is the least upper prevision
dominating every concrete DLR completion's region prevision. -/
theorem dlrLocalGambleUpperEnvelope_least_upper_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    (U : UpperPrevision (LocalAssignment Atom Λ))
    (hU : ∀ μ : DLRCompletion M,
      ∀ X : Gamble (LocalAssignment Atom Λ),
        dlrCompletionRegionPrevision M μ Λ X ≤ U X)
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrLocalGambleUpperEnvelope M Λ X ≤ U X := by
  rw [← upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]
  exact
    finiteUpperEnvelopePrevision_least_upper_bound
      (dlrRegionCredalSet M Λ) (dlrRegionCredalSet_nonempty M Λ) U
      (by
        intro P hP Y
        rcases hP with ⟨μ, rfl⟩
        exact hU μ Y)
      X

theorem credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalEnvelopeWidth (dlrRegionCredalSet M Λ) X =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  unfold credalEnvelopeWidth dlrLocalGambleEnvelopeWidth
  rw [upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper,
    lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]

theorem credalEnvelopeWidthComplement_dlrRegionCredalSet_localGamble_eq_complement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalEnvelopeWidthComplement (dlrRegionCredalSet M Λ) X =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  unfold credalEnvelopeWidthComplement dlrLocalGambleEnvelopeWidthComplement
  rw [credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width]

theorem credalEnvelopeMidpoint_dlrRegionCredalSet_localGamble_eq_midpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalEnvelopeMidpoint (dlrRegionCredalSet M Λ) X =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  unfold credalEnvelopeMidpoint dlrLocalGambleEnvelopeMidpoint
  rw [lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower,
    upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]

/-- If a finite-region DLR local gamble has lower envelope `0` and upper
envelope `1`, then its local midpoint coordinate is one half. -/
theorem dlrLocalGambleEnvelopeMidpoint_eq_half_of_unitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    dlrLocalGambleEnvelopeMidpoint M Λ X = (1 / 2 : ℝ) := by
  unfold dlrLocalGambleEnvelopeMidpoint
  rw [hL, hU]
  ring

/-- If a finite-region DLR local gamble has lower envelope `0` and upper
envelope `1`, then its local interval width is maximal. -/
theorem dlrLocalGambleEnvelopeWidth_eq_one_of_unitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    dlrLocalGambleEnvelopeWidth M Λ X = 1 := by
  unfold dlrLocalGambleEnvelopeWidth
  rw [hL, hU]
  ring

/-- If a finite-region DLR local gamble has lower envelope `0` and upper
envelope `1`, then its width-complement confidence coordinate is zero. -/
theorem dlrLocalGambleEnvelopeWidthComplement_eq_zero_of_unitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    dlrLocalGambleEnvelopeWidthComplement M Λ X = 0 := by
  unfold dlrLocalGambleEnvelopeWidthComplement
  rw [dlrLocalGambleEnvelopeWidth_eq_one_of_unitInterval M Λ X hL hU]
  ring

/-- Finite local assignment spaces make the range of DLR completion values on
an arbitrary local gamble bounded below. -/
theorem dlrCompletionLocalGamblePrevision_range_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    BddBelow (Set.range (fun μ : DLRCompletion M =>
      dlrCompletionRegionPrevision M μ Λ X)) := by
  rcases finite_gamble_uniformLowerBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨μ, rfl⟩
  exact (dlrCompletionRegionPrevision M μ Λ).lower_bound X c hc

/-- Finite local assignment spaces make the range of DLR completion values on
an arbitrary local gamble bounded above. -/
theorem dlrCompletionLocalGamblePrevision_range_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    BddAbove (Set.range (fun μ : DLRCompletion M =>
      dlrCompletionRegionPrevision M μ Λ X)) := by
  rcases finite_gamble_uniformUpperBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨μ, rfl⟩
  exact (dlrCompletionRegionPrevision M μ Λ).upper_bound X c hc

theorem dlrRegionProjectiveSpec_globalNaturalExtension_localQuery_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrRegionProjectiveSpec M Λ).globalNaturalExtension
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryLowerEnvelope M Λ q := by
  simp [ProjectiveLocalCredalSpec.globalNaturalExtension,
    lowerEnvelope_dlrRegionCredalSet_localQuery_eq_lower]

theorem dlrRegionProjectiveSpec_globalEnvelopeWidth_localQuery_eq_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidth
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeWidth M Λ q := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    credalEnvelopeWidth_dlrRegionCredalSet_localQuery_eq_width]

theorem dlrRegionProjectiveSpec_globalEnvelopeWidthComplement_localQuery_eq_complement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidthComplement
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeWidthComplement M Λ q := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    credalEnvelopeWidthComplement_dlrRegionCredalSet_localQuery_eq_complement]

theorem dlrRegionProjectiveSpec_globalEnvelopeMidpoint_localQuery_eq_midpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeMidpoint
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeMidpoint M Λ q := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    credalEnvelopeMidpoint_dlrRegionCredalSet_localQuery_eq_midpoint]

/-- The finite-region DLR projective natural extension of an arbitrary local
gamble is the lower envelope over DLR completions' finite-region previsions. -/
theorem dlrRegionProjectiveSpec_globalNaturalExtension_localGamble_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    (dlrRegionProjectiveSpec M Λ).globalNaturalExtension X =
      dlrLocalGambleLowerEnvelope M Λ X := by
  simp [ProjectiveLocalCredalSpec.globalNaturalExtension,
    lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]

/-- The finite-region DLR projective upper envelope of an arbitrary local gamble
is the upper envelope over DLR completions' finite-region previsions. -/
theorem dlrRegionProjectiveSpec_upperEnvelope_localGamble_eq_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    upperEnvelope (dlrRegionProjectiveSpec M Λ).projectiveLimitCredalSet X =
      dlrLocalGambleUpperEnvelope M Λ X := by
  simp [upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]

/-- The finite-region DLR projective width coordinate of an arbitrary local
gamble is the local DLR envelope width. -/
theorem dlrRegionProjectiveSpec_globalEnvelopeWidth_localGamble_eq_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidth X =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width]

/-- The finite-region DLR projective width-complement coordinate of an arbitrary
local gamble is the local DLR width-complement. -/
theorem dlrRegionProjectiveSpec_globalEnvelopeWidthComplement_localGamble_eq_complement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidthComplement X =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    credalEnvelopeWidthComplement_dlrRegionCredalSet_localGamble_eq_complement]

/-- The finite-region DLR projective midpoint coordinate of an arbitrary local
gamble is the local DLR lower/upper midpoint. -/
theorem dlrRegionProjectiveSpec_globalEnvelopeMidpoint_localGamble_eq_midpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeMidpoint X =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    credalEnvelopeMidpoint_dlrRegionCredalSet_localGamble_eq_midpoint]

/-- DLR finite-region local-query probabilities are nonnegative. -/
theorem dlrCompletionLocalQueryProb_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (μ : DLRCompletion M) :
    0 ≤ dlrCompletionLocalQueryProb M Λ q μ := by
  unfold dlrCompletionLocalQueryProb
  exact ENNReal.toReal_nonneg

/-- DLR finite-region local-query probabilities are at most one. -/
theorem dlrCompletionLocalQueryProb_le_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (μ : DLRCompletion M) :
    dlrCompletionLocalQueryProb M Λ q μ ≤ 1 := by
  unfold dlrCompletionLocalQueryProb
  have hle :
      ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q)) ≤
        (1 : ENNReal) := by
    calc
      ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q))
          ≤ (μ.1 : Measure (InfiniteWorld Atom)) Set.univ :=
            measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle

theorem dlrCompletionLocalQueryProb_mem_Icc
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (μ : DLRCompletion M) :
    dlrCompletionLocalQueryProb M Λ q μ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨dlrCompletionLocalQueryProb_nonneg M Λ q μ,
    dlrCompletionLocalQueryProb_le_one M Λ q μ⟩

/-- A finite-region local query is DLR-determined when all completions agree on
its finite-cylinder probability. -/
def dlrLocalQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : Prop :=
  ∀ μ ν : DLRCompletion M,
    dlrCompletionLocalQueryProb M Λ q μ =
      dlrCompletionLocalQueryProb M Λ q ν

/-- A finite-region local query has strict DLR width when two completions
strictly disagree on its finite-cylinder probability. -/
def dlrLocalQueryHasStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) : Prop :=
  ∃ μ : DLRCompletion M, ∃ ν : DLRCompletion M,
    dlrCompletionLocalQueryProb M Λ q μ <
      dlrCompletionLocalQueryProb M Λ q ν

/-- A finite-region local gamble is DLR-determined when all completions give
it the same local prevision.  This is the observable-valued version of
`dlrLocalQueryDetermined`, not restricted to 0/1 query indicators. -/
def dlrLocalGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : Prop :=
  ∀ μ ν : DLRCompletion M,
    dlrCompletionRegionPrevision M μ Λ X =
      dlrCompletionRegionPrevision M ν Λ X

/-- A finite-region local gamble has strict DLR width when two completions
strictly disagree on its local prevision. -/
def dlrLocalGambleHasStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) : Prop :=
  ∃ μ : DLRCompletion M, ∃ ν : DLRCompletion M,
    dlrCompletionRegionPrevision M μ Λ X <
      dlrCompletionRegionPrevision M ν Λ X

/-- If all DLR completions agree on an arbitrary local gamble, then the
completion-range lower and upper envelopes collapse. -/
theorem dlrLocalGambleEnvelope_precise_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    dlrLocalGambleLowerEnvelope M Λ X =
      dlrLocalGambleUpperEnvelope M Λ X := by
  classical
  obtain ⟨μ₀⟩ := (inferInstance : Nonempty (DLRCompletion M))
  have hRange :
      Set.range (fun μ : DLRCompletion M =>
        dlrCompletionRegionPrevision M μ Λ X) =
        ({dlrCompletionRegionPrevision M μ₀ Λ X} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨μ, rfl⟩
      simpa using hDet μ μ₀
    · intro hx
      have hx' : x = dlrCompletionRegionPrevision M μ₀ Λ X := by
        simpa using hx
      exact ⟨μ₀, hx'.symm⟩
  unfold dlrLocalGambleLowerEnvelope dlrLocalGambleUpperEnvelope
  rw [hRange, csInf_singleton, csSup_singleton]

/-- DLR-determined arbitrary local gambles have zero completion-range width. -/
theorem dlrLocalGambleEnvelopeWidth_eq_zero_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    dlrLocalGambleEnvelopeWidth M Λ X = 0 := by
  have h := dlrLocalGambleEnvelope_precise_of_localGambleDetermined
    M Λ X hDet
  unfold dlrLocalGambleEnvelopeWidth
  rw [h]
  ring

/-- Strict DLR disagreement on an arbitrary local gamble gives a nontrivial
completion-range lower/upper envelope. -/
theorem dlrLocalGambleEnvelope_nontrivial_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    dlrLocalGambleLowerEnvelope M Λ X <
      dlrLocalGambleUpperEnvelope M Λ X := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  unfold dlrLocalGambleLowerEnvelope dlrLocalGambleUpperEnvelope
  calc
    sInf (Set.range (fun μ : DLRCompletion M =>
        dlrCompletionRegionPrevision M μ Λ X))
        ≤ dlrCompletionRegionPrevision M μ Λ X :=
          csInf_le (dlrCompletionLocalGamblePrevision_range_bddBelow M Λ X)
            ⟨μ, rfl⟩
    _ < dlrCompletionRegionPrevision M ν Λ X := hlt
    _ ≤ sSup (Set.range (fun μ : DLRCompletion M =>
        dlrCompletionRegionPrevision M μ Λ X)) :=
          le_csSup (dlrCompletionLocalGamblePrevision_range_bddAbove M Λ X)
            ⟨ν, rfl⟩

/-- Strict DLR disagreement on an arbitrary local gamble gives positive
completion-range width. -/
theorem dlrLocalGambleEnvelopeWidth_pos_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    0 < dlrLocalGambleEnvelopeWidth M Λ X := by
  have hlt :=
    dlrLocalGambleEnvelope_nontrivial_of_localGambleStrictWidth
      M Λ X hWidth
  unfold dlrLocalGambleEnvelopeWidth
  linarith

/-- DLR-determined arbitrary local gambles have maximal completion-range
width-complement. -/
theorem dlrLocalGambleEnvelopeWidthComplement_eq_one_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    dlrLocalGambleEnvelopeWidthComplement M Λ X = 1 := by
  unfold dlrLocalGambleEnvelopeWidthComplement
  rw [dlrLocalGambleEnvelopeWidth_eq_zero_of_localGambleDetermined
    M Λ X hDet]
  ring

/-- Strict DLR disagreement on an arbitrary local gamble forces the
completion-range width-complement below one. -/
theorem dlrLocalGambleEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    dlrLocalGambleEnvelopeWidthComplement M Λ X < 1 := by
  have hpos :=
    dlrLocalGambleEnvelopeWidth_pos_of_localGambleStrictWidth M Λ X hWidth
  unfold dlrLocalGambleEnvelopeWidthComplement
  linarith

/-- Strict disagreement between DLR completions on an arbitrary finite-region
local gamble is realized by Walley dominating completions of the finite-region
natural extension.

This is the raw finite-region DLR endpoint theorem: the lower and upper
dominating precise previsions touch the local DLR lower and upper envelopes,
are strictly separated on the local gamble, and compute the PLN-facing
width, width-complement, and midpoint coordinates. -/
theorem dlrRegionProjectiveSpec_exists_dominatingStrictEndpointPairReadout_localGamble_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : PrecisePrevision (LocalAssignment Atom Λ),
      Plo ∈ dominatingPreciseCompletions
          ((dlrRegionProjectiveSpec M Λ).finiteGlobalNaturalExtensionPrevision
            (dlrRegionProjectiveSpec_hasCompatibleCompletion M Λ)) ∧
      ∃ Phi : PrecisePrevision (LocalAssignment Atom Λ),
        Phi ∈ dominatingPreciseCompletions
          ((dlrRegionProjectiveSpec M Λ).finiteGlobalNaturalExtensionPrevision
            (dlrRegionProjectiveSpec_hasCompatibleCompletion M Λ)) ∧
        Plo X = dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi X = dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo X < Phi X ∧
        dlrLocalGambleEnvelopeWidth M Λ X = Phi X - Plo X ∧
        dlrLocalGambleEnvelopeWidthComplement M Λ X =
          1 - (Phi X - Plo X) ∧
        dlrLocalGambleEnvelopeMidpoint M Λ X =
          (Plo X + Phi X) / 2 := by
  have hProjectiveWidth :
      (dlrRegionProjectiveSpec M Λ).hasStrictGlobalWidth X := by
    rcases hWidth with ⟨μ, ν, hlt⟩
    rw [dlrRegionProjectiveSpec,
      identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
    exact ⟨dlrCompletionRegionPrevision M μ Λ,
      mem_dlrRegionCredalSet M Λ μ,
      dlrCompletionRegionPrevision M ν Λ,
      mem_dlrRegionCredalSet M Λ ν, hlt⟩
  rcases
      ProjectiveLocalCredalSpec.finiteGlobalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        (S := dlrRegionProjectiveSpec M Λ)
        (dlrRegionProjectiveSpec_hasCompatibleCompletion M Λ) X
        hProjectiveWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hloLocal :
      Plo X = dlrLocalGambleLowerEnvelope M Λ X :=
    hlo.trans (dlrRegionProjectiveSpec_globalNaturalExtension_localGamble_eq_lower
      M Λ X)
  have hhiLocal :
      Phi X = dlrLocalGambleUpperEnvelope M Λ X :=
    hhi.trans (dlrRegionProjectiveSpec_upperEnvelope_localGamble_eq_upper M Λ X)
  refine ⟨Plo, ?_, Phi, ?_, hloLocal, hhiLocal, hlt, ?_, ?_, ?_⟩
  · exact hPlo
  · exact hPhi
  · calc
      dlrLocalGambleEnvelopeWidth M Λ X =
          (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidth X :=
        (dlrRegionProjectiveSpec_globalEnvelopeWidth_localGamble_eq_width M Λ X).symm
      _ = Phi X - Plo X := hWidthEq
  · calc
      dlrLocalGambleEnvelopeWidthComplement M Λ X =
          (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidthComplement X :=
        (dlrRegionProjectiveSpec_globalEnvelopeWidthComplement_localGamble_eq_complement M Λ X).symm
      _ = 1 - (Phi X - Plo X) := hCompEq
  · calc
      dlrLocalGambleEnvelopeMidpoint M Λ X =
          (dlrRegionProjectiveSpec M Λ).globalEnvelopeMidpoint X :=
        (dlrRegionProjectiveSpec_globalEnvelopeMidpoint_localGamble_eq_midpoint M Λ X).symm
      _ = (Plo X + Phi X) / 2 := hMidEq

/-- Closed finite-region DLR credal sets attain their strict-width endpoints.

Unlike the dominating-completion endpoint theorem above, the witnesses here are
members of the actual finite-region DLR credal set.  The closedness hypothesis
is explicit: this theorem does not pretend that compactness of the σ-additive
DLR completion family has already been proved. -/
theorem dlrRegionCredalSet_exists_endpointPairReadout_localGamble_of_finiteEvaluationClosed_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)]
    [Nonempty (LocalAssignment Atom Λ)]
    [DecidableEq (LocalAssignment Atom Λ)]
    (hClosed : @IsClosed (PrecisePrevision (LocalAssignment Atom Λ))
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology
        (Ω := LocalAssignment Atom Λ))
      (dlrRegionCredalSet M Λ))
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : PrecisePrevision (LocalAssignment Atom Λ),
      Plo ∈ dlrRegionCredalSet M Λ ∧
      ∃ Phi : PrecisePrevision (LocalAssignment Atom Λ),
        Phi ∈ dlrRegionCredalSet M Λ ∧
        Plo X = dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi X = dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo X < Phi X ∧
        dlrLocalGambleEnvelopeWidth M Λ X = Phi X - Plo X ∧
        dlrLocalGambleEnvelopeWidthComplement M Λ X =
          1 - (Phi X - Plo X) ∧
        dlrLocalGambleEnvelopeMidpoint M Λ X =
          (Plo X + Phi X) / 2 := by
  have hRegionWidth :
      credalSetHasStrictWidth (dlrRegionCredalSet M Λ) X :=
    by
      rcases hWidth with ⟨μ, ν, hlt⟩
      exact ⟨dlrCompletionRegionPrevision M μ Λ,
        mem_dlrRegionCredalSet M Λ μ,
        dlrCompletionRegionPrevision M ν Λ,
        mem_dlrRegionCredalSet M Λ ν, hlt⟩
  have hNonempty : (dlrRegionCredalSet M Λ).Nonempty := by
    rcases hRegionWidth with ⟨P, hP, _Q, _hQ, _hlt⟩
    exact ⟨P, hP⟩
  rcases
      credalEnvelope_exists_endpointPairReadout_of_finiteEvaluationClosed_strictWidth
        (dlrRegionCredalSet M Λ) hClosed hNonempty X hRegionWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hlt, ?_, ?_, ?_⟩
  · exact hlo.trans (lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower
      M Λ X)
  · exact hhi.trans (upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper
      M Λ X)
  · exact (credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width
      M Λ X).symm.trans hWidthEq
  · exact (credalEnvelopeWidthComplement_dlrRegionCredalSet_localGamble_eq_complement
      M Λ X).symm.trans hCompEq
  · exact (credalEnvelopeMidpoint_dlrRegionCredalSet_localGamble_eq_midpoint
      M Λ X).symm.trans hMidEq

/-- A local query is DLR-determined exactly when its indicator gamble is
DLR-determined as a local observable. -/
theorem dlrLocalQueryDetermined_iff_localGambleDetermined_indicator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    dlrLocalQueryDetermined M Λ q ↔
      dlrLocalGambleDetermined M Λ (localQueryIndicatorGamble Λ q) := by
  constructor
  · intro hDet μ ν
    rw [dlrCompletionRegionPrevision_localQueryIndicator,
      dlrCompletionRegionPrevision_localQueryIndicator]
    exact hDet μ ν
  · intro hDet μ ν
    have h := hDet μ ν
    rw [dlrCompletionRegionPrevision_localQueryIndicator,
      dlrCompletionRegionPrevision_localQueryIndicator] at h
    exact h

/-- A local query has strict DLR width exactly when its indicator gamble has
strict DLR width as a local observable. -/
theorem dlrLocalQueryHasStrictWidth_iff_localGambleHasStrictWidth_indicator
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    dlrLocalQueryHasStrictWidth M Λ q ↔
      dlrLocalGambleHasStrictWidth M Λ (localQueryIndicatorGamble Λ q) := by
  constructor
  · rintro ⟨μ, ν, hlt⟩
    refine ⟨μ, ν, ?_⟩
    rw [dlrCompletionRegionPrevision_localQueryIndicator,
      dlrCompletionRegionPrevision_localQueryIndicator]
    exact hlt
  · rintro ⟨μ, ν, hlt⟩
    refine ⟨μ, ν, ?_⟩
    rw [dlrCompletionRegionPrevision_localQueryIndicator,
      dlrCompletionRegionPrevision_localQueryIndicator] at hlt
    exact hlt

theorem dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    credalSetDetermines (dlrRegionCredalSet M Λ) X := by
  intro P hP Q hQ
  rcases hP with ⟨μ, rfl⟩
  rcases hQ with ⟨ν, rfl⟩
  exact hDet μ ν

theorem dlrRegionCredalSet_determines_localQuery_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    credalSetDetermines (dlrRegionCredalSet M Λ)
      (localQueryIndicatorGamble Λ q) := by
  exact dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
    M Λ (localQueryIndicatorGamble Λ q)
    ((dlrLocalQueryDetermined_iff_localGambleDetermined_indicator M Λ q).mp hDet)

theorem dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    credalSetHasStrictWidth (dlrRegionCredalSet M Λ) X := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  exact ⟨dlrCompletionRegionPrevision M μ Λ,
    mem_dlrRegionCredalSet M Λ μ,
    dlrCompletionRegionPrevision M ν Λ,
    mem_dlrRegionCredalSet M Λ ν, hlt⟩

/-- The DLR region credal set determines a local gamble exactly when all DLR
completions agree on that local gamble. -/
theorem dlrRegionCredalSet_determines_localGamble_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalSetDetermines (dlrRegionCredalSet M Λ) X ↔
      dlrLocalGambleDetermined M Λ X := by
  constructor
  · intro hDet μ ν
    exact hDet (dlrCompletionRegionPrevision M μ Λ)
      (mem_dlrRegionCredalSet M Λ μ)
      (dlrCompletionRegionPrevision M ν Λ)
      (mem_dlrRegionCredalSet M Λ ν)
  · exact dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
      M Λ X

/-- The DLR region credal set has strict width on a local gamble exactly when two
DLR completions strictly disagree on that local gamble. -/
theorem dlrRegionCredalSet_hasStrictWidth_localGamble_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalSetHasStrictWidth (dlrRegionCredalSet M Λ) X ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  constructor
  · intro hWidth
    rcases hWidth with ⟨P, hP, Q, hQ, hlt⟩
    rcases hP with ⟨μ, rfl⟩
    rcases hQ with ⟨ν, rfl⟩
    exact ⟨μ, ν, hlt⟩
  · exact dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
      M Λ X

/-- Local-gamble strict DLR width is exactly failure of DLR determination. -/
theorem dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    dlrLocalGambleHasStrictWidth M Λ X ↔
      ¬ dlrLocalGambleDetermined M Λ X := by
  rw [← dlrRegionCredalSet_hasStrictWidth_localGamble_iff_localGambleStrictWidth,
    ← dlrRegionCredalSet_determines_localGamble_iff_localGambleDetermined]
  exact credalSetHasStrictWidth_iff_not_determines (dlrRegionCredalSet M Λ) X

/-- The DLR local-gamble width-complement is maximal exactly when the local
gamble is determined by all DLR completions. -/
theorem dlrLocalGambleEnvelopeWidthComplement_eq_one_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrLocalGambleEnvelopeWidthComplement M Λ X = 1 ↔
      dlrLocalGambleDetermined M Λ X := by
  constructor
  · intro hEq
    by_contra hNot
    have hWidth : dlrLocalGambleHasStrictWidth M Λ X :=
      (dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined M Λ X).2 hNot
    have hLt :=
      dlrLocalGambleEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
        M Λ X hWidth
    exact (ne_of_lt hLt) hEq
  · intro hDet
    exact dlrLocalGambleEnvelopeWidthComplement_eq_one_of_localGambleDetermined
      M Λ X hDet

/-- The DLR local-gamble width-complement falls below one exactly when two DLR
completions strictly disagree on that local gamble. -/
theorem dlrLocalGambleEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrLocalGambleEnvelopeWidthComplement M Λ X < 1 ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  constructor
  · intro hLt
    refine
      (dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined M Λ X).2 ?_
    intro hDet
    have hEq :=
      dlrLocalGambleEnvelopeWidthComplement_eq_one_of_localGambleDetermined
        M Λ X hDet
    rw [hEq] at hLt
    exact (not_lt_of_ge le_rfl) hLt
  · intro hWidth
    exact dlrLocalGambleEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
      M Λ X hWidth

/-- Local-query strict DLR width is exactly failure of local-query
determination. -/
theorem dlrLocalQueryHasStrictWidth_iff_not_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    dlrLocalQueryHasStrictWidth M Λ q ↔
      ¬ dlrLocalQueryDetermined M Λ q := by
  constructor
  · intro hWidth hDet
    have hGambleWidth :
        dlrLocalGambleHasStrictWidth M Λ (localQueryIndicatorGamble Λ q) :=
      (dlrLocalQueryHasStrictWidth_iff_localGambleHasStrictWidth_indicator
        M Λ q).1 hWidth
    have hGambleDet :
        dlrLocalGambleDetermined M Λ (localQueryIndicatorGamble Λ q) :=
      (dlrLocalQueryDetermined_iff_localGambleDetermined_indicator
        M Λ q).1 hDet
    exact
      ((dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined
        M Λ (localQueryIndicatorGamble Λ q)).1 hGambleWidth) hGambleDet
  · intro hNot
    refine
      (dlrLocalQueryHasStrictWidth_iff_localGambleHasStrictWidth_indicator
        M Λ q).2 ?_
    refine
      (dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined
        M Λ (localQueryIndicatorGamble Λ q)).2 ?_
    intro hGambleDet
    exact hNot
      ((dlrLocalQueryDetermined_iff_localGambleDetermined_indicator
        M Λ q).2 hGambleDet)

theorem dlrRegionCredalSet_hasStrictWidth_localQuery_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    credalSetHasStrictWidth (dlrRegionCredalSet M Λ)
      (localQueryIndicatorGamble Λ q) := by
  exact dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
    M Λ (localQueryIndicatorGamble Λ q)
    ((dlrLocalQueryHasStrictWidth_iff_localGambleHasStrictWidth_indicator
      M Λ q).mp hWidth)

theorem dlrRegionCredalSet_not_determines_localQuery_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    ¬ credalSetDetermines (dlrRegionCredalSet M Λ)
      (localQueryIndicatorGamble Λ q) :=
  not_credalSetDetermines_of_strictWidth
    (dlrRegionCredalSet_hasStrictWidth_localQuery_of_localQueryStrictWidth
      M Λ q hWidth)

theorem dlrRegionCredalSet_not_determines_localGamble_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ¬ credalSetDetermines (dlrRegionCredalSet M Λ) X :=
  not_credalSetDetermines_of_strictWidth
    (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
      M Λ X hWidth)

theorem dlrRegionProjectiveSpec_determines_localQuery_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    (dlrRegionProjectiveSpec M Λ).determinesGlobalGamble
      (localQueryIndicatorGamble Λ q) := by
  rw [dlrRegionProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  exact dlrRegionCredalSet_determines_localQuery_of_localQueryDetermined
    M Λ q hDet

theorem dlrRegionProjectiveSpec_hasStrictWidth_localQuery_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    (dlrRegionProjectiveSpec M Λ).hasStrictGlobalWidth
      (localQueryIndicatorGamble Λ q) := by
  rw [dlrRegionProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  exact dlrRegionCredalSet_hasStrictWidth_localQuery_of_localQueryStrictWidth
    M Λ q hWidth

theorem dlrRegionProjectiveSpec_not_determines_localQuery_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    ¬ (dlrRegionProjectiveSpec M Λ).determinesGlobalGamble
      (localQueryIndicatorGamble Λ q) :=
  ProjectiveLocalCredalSpec.not_determinesGlobalGamble_of_strictWidth
    (dlrRegionProjectiveSpec M Λ)
    (dlrRegionProjectiveSpec_hasStrictWidth_localQuery_of_localQueryStrictWidth
      M Λ q hWidth)

theorem dlrCompletionLocalQueryProb_range_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddBelow (Set.range (dlrCompletionLocalQueryProb M Λ q)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨μ, rfl⟩
  exact dlrCompletionLocalQueryProb_nonneg M Λ q μ

theorem dlrCompletionLocalQueryProb_range_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddAbove (Set.range (dlrCompletionLocalQueryProb M Λ q)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨μ, rfl⟩
  exact dlrCompletionLocalQueryProb_le_one M Λ q μ

theorem dlrLocalQueryEnvelope_precise_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    dlrLocalQueryLowerEnvelope M Λ q =
      dlrLocalQueryUpperEnvelope M Λ q := by
  classical
  obtain ⟨μ₀⟩ := (inferInstance : Nonempty (DLRCompletion M))
  have hRange :
      Set.range (dlrCompletionLocalQueryProb M Λ q) =
        ({dlrCompletionLocalQueryProb M Λ q μ₀} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨μ, rfl⟩
      exact by
        rw [hDet μ μ₀]
        simp
    · intro hx
      have hx' : x = dlrCompletionLocalQueryProb M Λ q μ₀ := by
        simpa using hx
      exact ⟨μ₀, hx'.symm⟩
  unfold dlrLocalQueryLowerEnvelope dlrLocalQueryUpperEnvelope
  rw [hRange, csInf_singleton, csSup_singleton]

theorem dlrLocalQueryEnvelopeWidth_eq_zero_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    dlrLocalQueryEnvelopeWidth M Λ q = 0 := by
  have h := dlrLocalQueryEnvelope_precise_of_localQueryDetermined
    M Λ q hDet
  unfold dlrLocalQueryEnvelopeWidth
  rw [h]
  ring

theorem dlrLocalQueryEnvelope_nontrivial_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    dlrLocalQueryLowerEnvelope M Λ q <
      dlrLocalQueryUpperEnvelope M Λ q := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  unfold dlrLocalQueryLowerEnvelope dlrLocalQueryUpperEnvelope
  calc
    sInf (Set.range (dlrCompletionLocalQueryProb M Λ q))
        ≤ dlrCompletionLocalQueryProb M Λ q μ :=
          csInf_le (dlrCompletionLocalQueryProb_range_bddBelow M Λ q)
            ⟨μ, rfl⟩
    _ < dlrCompletionLocalQueryProb M Λ q ν := hlt
    _ ≤ sSup (Set.range (dlrCompletionLocalQueryProb M Λ q)) :=
          le_csSup (dlrCompletionLocalQueryProb_range_bddAbove M Λ q)
            ⟨ν, rfl⟩

theorem dlrLocalQueryEnvelopeWidth_pos_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    0 < dlrLocalQueryEnvelopeWidth M Λ q := by
  have hlt := dlrLocalQueryEnvelope_nontrivial_of_localQueryStrictWidth
    M Λ q hWidth
  unfold dlrLocalQueryEnvelopeWidth
  linarith

/-- DLR-determined local queries have maximal local width-complement. -/
theorem dlrLocalQueryEnvelopeWidthComplement_eq_one_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    dlrLocalQueryEnvelopeWidthComplement M Λ q = 1 := by
  unfold dlrLocalQueryEnvelopeWidthComplement
  rw [dlrLocalQueryEnvelopeWidth_eq_zero_of_localQueryDetermined M Λ q hDet]
  ring

/-- Strict DLR local-query width forces the local width-complement below one. -/
theorem dlrLocalQueryEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    dlrLocalQueryEnvelopeWidthComplement M Λ q < 1 := by
  have hpos :=
    dlrLocalQueryEnvelopeWidth_pos_of_localQueryStrictWidth M Λ q hWidth
  unfold dlrLocalQueryEnvelopeWidthComplement
  linarith

/-- The local-query width-complement is maximal exactly when the query is
determined by all DLR completions. -/
theorem dlrLocalQueryEnvelopeWidthComplement_eq_one_iff_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    dlrLocalQueryEnvelopeWidthComplement M Λ q = 1 ↔
      dlrLocalQueryDetermined M Λ q := by
  constructor
  · intro hEq
    by_contra hNot
    have hWidth : dlrLocalQueryHasStrictWidth M Λ q :=
      (dlrLocalQueryHasStrictWidth_iff_not_localQueryDetermined M Λ q).2 hNot
    have hLt :=
      dlrLocalQueryEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
        M Λ q hWidth
    exact (ne_of_lt hLt) hEq
  · intro hDet
    exact dlrLocalQueryEnvelopeWidthComplement_eq_one_of_localQueryDetermined
      M Λ q hDet

/-- The local-query width-complement falls below one exactly when two DLR
completions strictly disagree on the query. -/
theorem dlrLocalQueryEnvelopeWidthComplement_lt_one_iff_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    dlrLocalQueryEnvelopeWidthComplement M Λ q < 1 ↔
      dlrLocalQueryHasStrictWidth M Λ q := by
  constructor
  · intro hLt
    refine
      (dlrLocalQueryHasStrictWidth_iff_not_localQueryDetermined M Λ q).2 ?_
    intro hDet
    have hEq :=
      dlrLocalQueryEnvelopeWidthComplement_eq_one_of_localQueryDetermined
        M Λ q hDet
    rw [hEq] at hLt
    exact (not_lt_of_ge le_rfl) hLt
  · intro hWidth
    exact dlrLocalQueryEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
      M Λ q hWidth

theorem dlrRegionProjectiveSpec_globalEnvelopeWidth_eq_zero_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidth
        (localQueryIndicatorGamble Λ q) = 0 := by
  rw [dlrRegionProjectiveSpec_globalEnvelopeWidth_localQuery_eq_width]
  exact dlrLocalQueryEnvelopeWidth_eq_zero_of_localQueryDetermined M Λ q hDet

theorem dlrRegionProjectiveSpec_globalEnvelopeWidth_pos_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    0 < (dlrRegionProjectiveSpec M Λ).globalEnvelopeWidth
        (localQueryIndicatorGamble Λ q) := by
  rw [dlrRegionProjectiveSpec_globalEnvelopeWidth_localQuery_eq_width]
  exact dlrLocalQueryEnvelopeWidth_pos_of_localQueryStrictWidth M Λ q hWidth

/-- Restrict a local assignment on a larger finite region to a smaller finite
region. -/
def restrictLocalAssignment {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (x : LocalAssignment Atom Δ) : LocalAssignment Atom Λ :=
  fun a => x ⟨a.1, hΛΔ a.2⟩

omit [DecidableEq Atom] in
@[simp] theorem restrictLocalAssignment_apply {Λ Δ : Region Atom}
    (hΛΔ : Λ ≤ Δ) (x : LocalAssignment Atom Δ) (a : RegionAtom Atom Λ) :
    restrictLocalAssignment hΛΔ x a = x ⟨a.1, hΛΔ a.2⟩ :=
  rfl

/-- Marginalize a finite-volume assignment prevision from a larger finite
region `Δ` to a smaller finite region `Λ ⊆ Δ` by ordinary restriction of local
assignments.  This is deliberately not identified with the separately
normalized finite-volume law on `Λ`: interactions through `Δ \ Λ` can change
the marginal. -/
noncomputable def finiteVolumeAssignmentMarginalPrevision
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Δ ξ ≠ 0) :
    PrecisePrevision (LocalAssignment Atom Λ) where
  toFun X :=
    finiteVolumeAssignmentPrevision M Δ ξ hZ
      (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ))
  lower_bound := by
    intro X c hc
    exact (finiteVolumeAssignmentPrevision M Δ ξ hZ).lower_bound
      (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ)) c
      (fun xΔ => hc (restrictLocalAssignment hΛΔ xΔ))
  pos_homog := by
    intro r X hr
    exact (finiteVolumeAssignmentPrevision M Δ ξ hZ).pos_homog r
      (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ)) hr
  add := by
    intro X Y
    exact (finiteVolumeAssignmentPrevision M Δ ξ hZ).add
      (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ))
      (fun xΔ => Y (restrictLocalAssignment hΛΔ xΔ))

@[simp] theorem finiteVolumeAssignmentMarginalPrevision_apply
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Δ ξ ≠ 0)
    (X : Gamble (LocalAssignment Atom Λ)) :
    finiteVolumeAssignmentMarginalPrevision M hΛΔ ξ hZ X =
      ∑ xΔ, (finiteVolumeAssignmentPMF M Δ ξ hZ xΔ).toReal *
        X (restrictLocalAssignment hΛΔ xΔ) := by
  rfl

theorem finiteVolumeAssignmentMarginalPrevision_precise
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Δ ξ ≠ 0) :
    (finiteVolumeAssignmentMarginalPrevision M hΛΔ ξ hZ).toLowerPrevision.isPrecise :=
  PrecisePrevision.toLowerPrevision_precise
    (finiteVolumeAssignmentMarginalPrevision M hΛΔ ξ hZ)

/-- The genuine all-finite-regions cylinder system for infinite Boolean worlds:
windows are finite regions, locals are assignments on those regions, and
restriction is ordinary restriction of assignments. -/
def dlrAllRegionsCylinderSystem (Atom : Type*) [DecidableEq Atom] :
    ProjectiveCylinderSystem (Region Atom) (InfiniteWorld Atom) where
  Local Λ := LocalAssignment Atom Λ
  project Λ ω := worldRestriction Λ ω
  restrict := fun {Λ Δ} hΛΔ x => restrictLocalAssignment hΛΔ x
  project_restrict := by
    intro Λ Δ hΛΔ ω
    rfl

/-- Every finite-region local gamble is a bounded measurable observable.  This
is the local finite-cylinder face of the future σ-additive prevision carrier. -/
noncomputable def dlrLocalBoundedMeasurableGamble
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    BoundedMeasurableGamble (LocalAssignment Atom Λ) :=
  BoundedMeasurableGamble.ofFinite X

@[simp] theorem dlrLocalBoundedMeasurableGamble_apply
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (x : LocalAssignment Atom Λ) :
    dlrLocalBoundedMeasurableGamble Λ X x = X x :=
  rfl

/-- Pulling a finite-region local gamble back along the world-restriction map
gives a bounded measurable global cylinder observable. -/
noncomputable def dlrCylinderBoundedMeasurableGamble
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    BoundedMeasurableGamble (InfiniteWorld Atom) :=
  BoundedMeasurableGamble.pullback
    (worldRestriction (Atom := Atom) Λ)
    (measurable_worldRestriction (Atom := Atom) Λ)
    (dlrLocalBoundedMeasurableGamble Λ X)

@[simp] theorem dlrCylinderBoundedMeasurableGamble_apply
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (ω : InfiniteWorld Atom) :
    dlrCylinderBoundedMeasurableGamble Λ X ω =
      X (worldRestriction Λ ω) :=
  rfl

/-- The bounded-measurable DLR cylinder observable forgets to the same raw
global gamble used by the projective credal cylinder system. -/
theorem dlrCylinderBoundedMeasurableGamble_toGamble_eq_cylinderGamble
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    (dlrCylinderBoundedMeasurableGamble (Atom := Atom) Λ X).toGamble =
      (dlrAllRegionsCylinderSystem Atom).cylinderGamble Λ X := by
  rfl

/-- A DLR completion induces a σ-additive precise prevision on bounded
measurable infinite-world observables. -/
noncomputable def dlrCompletionBoundedMeasurablePrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) :
    BoundedMeasurablePrecisePrevision (InfiniteWorld Atom) :=
  BoundedMeasurablePrecisePrevision.ofProbabilityMeasure
    (μ.1 : Measure (InfiniteWorld Atom))

/-- The bounded-observable prevision induced by a mixed DLR completion is the
corresponding convex mixture of the two induced bounded-observable previsions. -/
theorem dlrCompletionBoundedMeasurablePrevision_mix_apply
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : DLRCompletion M)
    (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    dlrCompletionBoundedMeasurablePrevision M
        (DLRCompletion.mix M ⟨t, ht0, ht1⟩ μ ν) X =
      BoundedMeasurablePrecisePrevision.mix t
        (dlrCompletionBoundedMeasurablePrevision M μ)
        (dlrCompletionBoundedMeasurablePrevision M ν) ht0 ht1 X := by
  unfold dlrCompletionBoundedMeasurablePrevision DLRCompletion.mix
  rw [BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_apply]
  change ∫ ω, X ω ∂
        (unitInterval.toNNReal (⟨t, ht0, ht1⟩ : unitInterval) •
            (μ.1 : Measure (InfiniteWorld Atom)) +
          unitInterval.toNNReal
              (unitInterval.symm (⟨t, ht0, ht1⟩ : unitInterval)) •
            (ν.1 : Measure (InfiniteWorld Atom))) =
      t * BoundedMeasurablePrecisePrevision.ofProbabilityMeasure
          (μ.1 : Measure (InfiniteWorld Atom)) X +
        (1 - t) * BoundedMeasurablePrecisePrevision.ofProbabilityMeasure
          (ν.1 : Measure (InfiniteWorld Atom)) X
  rw [integral_add_measure (X.integrable _) (X.integrable _)]
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_apply,
    NNReal.smul_def, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, smul_eq_mul]

/-- On finite cylinders, the σ-additive bounded-observable expectation induced
by a DLR completion agrees with the finite-region singleton-mass prevision
already used by the projective credal layer. -/
theorem dlrCompletionBoundedCylinderPrevision_eq_regionPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    dlrCompletionBoundedMeasurablePrevision M μ
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrCompletionRegionPrevision M μ Λ X := by
  unfold dlrCompletionBoundedMeasurablePrevision
    dlrCylinderBoundedMeasurableGamble dlrLocalBoundedMeasurableGamble
    dlrCompletionRegionPrevision
  let νΛ : Measure (LocalAssignment Atom Λ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Λ
  haveI : IsProbabilityMeasure νΛ := by
    dsimp [νΛ]
    infer_instance
  have hmeasure :
      Measure.map (worldRestriction (Atom := Atom) Λ)
          (μ.1 : Measure (InfiniteWorld Atom)) = νΛ := by
    dsimp [νΛ]
    rfl
  have hpush :=
    BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_map_apply
      (μ.1 : Measure (InfiniteWorld Atom))
      (worldRestriction (Atom := Atom) Λ)
      (measurable_worldRestriction (Atom := Atom) Λ)
      (BoundedMeasurableGamble.ofFinite X)
  rw [← hpush]
  rw [BoundedMeasurablePrecisePrevision.ofProbabilityMeasure_apply]
  rw [hmeasure]
  exact
    PrecisePrevision.FiniteWeights.boundedMeasurablePrevision_ofFinite_eq_finiteProbabilityMeasurePrevision
      νΛ X

/-- The bounded-measurable DLR expectation of a global finite cylinder is the
bounded-measurable expectation of the corresponding local finite-dimensional
marginal. -/
theorem dlrCompletionBoundedCylinderPrevision_eq_localBoundedMeasurablePrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    dlrCompletionBoundedMeasurablePrevision M μ
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrCompletionLocalBoundedMeasurablePrevision M μ Λ
        (dlrLocalBoundedMeasurableGamble Λ X) := by
  rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision]
  exact
    (dlrCompletionLocalBoundedMeasurablePrevision_ofFinite_eq_regionPrevision
      M μ Λ X).symm

/-- Finite-region DLR marginals commute with convex mixtures of DLR
completions.  This is the local credal counterpart of the bounded-global
mixture theorem. -/
theorem dlrCompletionRegionPrevision_mix_apply
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : DLRCompletion M)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    dlrCompletionRegionPrevision M
        (DLRCompletion.mix M ⟨t, ht0, ht1⟩ μ ν) Λ X =
      PrecisePrevision.mix t (dlrCompletionRegionPrevision M μ Λ)
        (dlrCompletionRegionPrevision M ν Λ) ht0 ht1 X := by
  rw [← dlrCompletionBoundedCylinderPrevision_eq_regionPrevision
    M (DLRCompletion.mix M ⟨t, ht0, ht1⟩ μ ν) Λ X]
  rw [dlrCompletionBoundedMeasurablePrevision_mix_apply M t ht0 ht1 μ ν
    (dlrCylinderBoundedMeasurableGamble Λ X)]
  change t * dlrCompletionBoundedMeasurablePrevision M μ
        (dlrCylinderBoundedMeasurableGamble Λ X) +
      (1 - t) * dlrCompletionBoundedMeasurablePrevision M ν
        (dlrCylinderBoundedMeasurableGamble Λ X) =
    t * dlrCompletionRegionPrevision M μ Λ X +
      (1 - t) * dlrCompletionRegionPrevision M ν Λ X
  rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision M μ Λ X]
  rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision M ν Λ X]

/-- The finite-region DLR credal set is convex: mixing two DLR completions and
then taking the region marginal gives the affine mixture of the two marginal
previsions. -/
theorem dlrRegionCredalSet_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) :
    CredalPrevisionSet.IsConvex (dlrRegionCredalSet M Λ) := by
  intro P hP Q hQ t ht0 ht1
  rcases hP with ⟨μ, rfl⟩
  rcases hQ with ⟨ν, rfl⟩
  refine ⟨DLRCompletion.mix M ⟨t, ht0, ht1⟩ μ ν, ?_⟩
  ext X
  exact (dlrCompletionRegionPrevision_mix_apply
    M t ht0 ht1 μ ν Λ X).symm

/-- The bounded-measurable credal set generated by all DLR completions.  This
is the global sigma-additive carrier; finite-region DLR credal sets are its
cylinder shadows. -/
noncomputable def dlrCompletionBoundedMeasurableCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    BoundedMeasurableCredalSet (InfiniteWorld Atom) :=
  {P | ∃ μ : DLRCompletion M,
    P = dlrCompletionBoundedMeasurablePrevision M μ}

@[simp] theorem mem_dlrCompletionBoundedMeasurableCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) :
    dlrCompletionBoundedMeasurablePrevision M μ ∈
      dlrCompletionBoundedMeasurableCredalSet M :=
  ⟨μ, rfl⟩

/-- If a DLR completion exists, the bounded-measurable DLR credal set is
nonempty. -/
theorem dlrCompletionBoundedMeasurableCredalSet_nonempty
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    (dlrCompletionBoundedMeasurableCredalSet M).Nonempty := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact ⟨dlrCompletionBoundedMeasurablePrevision M μ,
    mem_dlrCompletionBoundedMeasurableCredalSet M μ⟩

/-- The raw bounded-measurable DLR credal carrier is convex because actual DLR
completions are closed under probability-measure mixtures. -/
theorem dlrCompletionBoundedMeasurableCredalSet_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    BoundedMeasurableCredalSet.IsConvex
      (dlrCompletionBoundedMeasurableCredalSet M) := by
  intro t ht0 ht1 P Q hP hQ
  rcases hP with ⟨μ, rfl⟩
  rcases hQ with ⟨ν, rfl⟩
  refine ⟨DLRCompletion.mix M ⟨t, ht0, ht1⟩ μ ν, ?_⟩
  ext X
  exact (dlrCompletionBoundedMeasurablePrevision_mix_apply
    M t ht0 ht1 μ ν X).symm

/-- The closed evaluation-topology credal object generated by all
bounded-measurable DLR completions.

This is the compact DLR credal carrier used by the weak*/compact branch: the
raw DLR image is not assumed closed; we take its honest compact closure in the
bounded-observable prevision carrier. -/
noncomputable def dlrCompletionBoundedMeasurableCompactCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    BoundedMeasurableCredalSet (InfiniteWorld Atom) :=
  boundedMeasurableCredalSetEvaluationClosure
    (dlrCompletionBoundedMeasurableCredalSet M)

/-- Every bounded-measurable DLR completion belongs to the closed compact DLR
credal carrier. -/
theorem mem_dlrCompletionBoundedMeasurableCompactCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) :
    dlrCompletionBoundedMeasurablePrevision M μ ∈
      dlrCompletionBoundedMeasurableCompactCredalSet M :=
  boundedMeasurableCredalSet_subset_evaluationClosure
    (dlrCompletionBoundedMeasurableCredalSet M)
    (mem_dlrCompletionBoundedMeasurableCredalSet M μ)

/-- The compact DLR bounded-measurable credal carrier is closed in the
evaluation topology. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_isClosed
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    @IsClosed (BoundedMeasurablePrecisePrevision (InfiniteWorld Atom))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := InfiniteWorld Atom))
      (dlrCompletionBoundedMeasurableCompactCredalSet M) :=
  boundedMeasurableCredalSetEvaluationClosure_isClosed
    (dlrCompletionBoundedMeasurableCredalSet M)

/-- The compact DLR bounded-measurable credal carrier is compact in the
evaluation topology. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_isCompact
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    @IsCompact (BoundedMeasurablePrecisePrevision (InfiniteWorld Atom))
      (BoundedMeasurablePrecisePrevision.evaluationTopology
        (Ω := InfiniteWorld Atom))
      (dlrCompletionBoundedMeasurableCompactCredalSet M) :=
  boundedMeasurableCredalSetEvaluationClosure_isCompact
    (dlrCompletionBoundedMeasurableCredalSet M)

/-- If a DLR completion exists, the compact DLR bounded-measurable credal
carrier is nonempty. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_nonempty
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    (dlrCompletionBoundedMeasurableCompactCredalSet M).Nonempty :=
  boundedMeasurableCredalSetEvaluationClosure_nonempty
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)

/-- The compact bounded-measurable DLR credal carrier is convex: compactifying
the raw convex DLR carrier by evaluation closure preserves convexity. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    BoundedMeasurableCredalSet.IsConvex
      (dlrCompletionBoundedMeasurableCompactCredalSet M) :=
  boundedMeasurableCredalSetEvaluationClosure_isConvex
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_isConvex M)

/-- The bounded-measurable natural extension generated by DLR completions has
an exact dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_hasExactDominatingPreciseEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCompletionBoundedMeasurableCredalSet_nonempty M)) :=
  boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)

/-- The Walley precise-completion carrier generated by DLR completions is
convex.  This is the coherent-completion object used by the bounded-measurable
DLR natural extension, not an assertion that the raw DLR image is closed under
mixing. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_dominatingCompletions_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    BoundedMeasurableCredalSet.IsConvex
      (boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCredalSet M)
          (dlrCompletionBoundedMeasurableCredalSet_nonempty M))) :=
  boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isConvex
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)

/-- The bounded-measurable DLR natural extension is below every actual DLR
completion on every bounded observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_le_completion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (μ : DLRCompletion M) (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X ≤
      dlrCompletionBoundedMeasurablePrevision M μ X :=
  boundedMeasurableNaturalExtensionPrevision_le_completion
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
    (mem_dlrCompletionBoundedMeasurableCredalSet M μ) X

/-- The bounded-measurable DLR natural extension is the greatest bounded lower
prevision below every actual DLR completion. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_greatest_lower_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (L : BoundedMeasurableLowerPrevision (InfiniteWorld Atom))
    (hL : ∀ μ : DLRCompletion M,
      ∀ X : BoundedMeasurableGamble (InfiniteWorld Atom),
        L X ≤ dlrCompletionBoundedMeasurablePrevision M μ X)
    (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    L X ≤
      boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X := by
  apply boundedMeasurableNaturalExtensionPrevision_greatest_lower_bound
  intro P hP Y
  rcases hP with ⟨μ, rfl⟩
  exact hL μ Y

/-- Every actual DLR completion lies below the bounded-measurable DLR natural
upper envelope on every bounded observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCredalSet_completion_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (μ : DLRCompletion M) (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    dlrCompletionBoundedMeasurablePrevision M μ X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X :=
  boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
    (mem_dlrCompletionBoundedMeasurableCredalSet M μ) X

/-- The bounded-measurable DLR natural upper envelope is the least bounded
upper prevision above every actual DLR completion. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCredalSet_least_upper_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (U : BoundedMeasurableUpperPrevision (InfiniteWorld Atom))
    (hU : ∀ μ : DLRCompletion M,
      ∀ X : BoundedMeasurableGamble (InfiniteWorld Atom),
        dlrCompletionBoundedMeasurablePrevision M μ X ≤ U X)
    (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X ≤
      U X := by
  apply boundedMeasurableNaturalUpperEnvelopePrevision_least_upper_bound
  intro P hP Y
  rcases hP with ⟨μ, rfl⟩
  exact hU μ Y

/-- Compactifying the DLR bounded-measurable credal carrier preserves the
dominating precise completions of the generated natural extension.  This is the
Walley completion-object form of the compact-carrier conservation theorem. -/
theorem boundedMeasurableDominatingPreciseCompletions_dlrCompletionCompactCredalSet_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCompactCredalSet M)
          (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)) =
      boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCredalSet M)
          (dlrCompletionBoundedMeasurableCredalSet_nonempty M)) := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  exact
    boundedMeasurableDominatingPreciseCompletions_naturalExtension_evaluationClosure_eq
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)

/-- The compact DLR bounded-measurable natural extension has an exact
dominating-precise-completion envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_hasExactDominatingPreciseEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    boundedMeasurableHasExactDominatingPreciseEnvelope
      (boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)) :=
  boundedMeasurableNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (dlrCompletionBoundedMeasurableCompactCredalSet M)
    (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)

/-- The Walley precise-completion carrier generated by the compact
bounded-measurable DLR credal carrier is convex. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_dominatingCompletions_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    BoundedMeasurableCredalSet.IsConvex
      (boundedMeasurableDominatingPreciseCompletions
        (boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCompactCredalSet M)
          (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M))) :=
  boundedMeasurableNaturalExtensionPrevision_dominatingCompletions_isConvex
    (dlrCompletionBoundedMeasurableCompactCredalSet M)
    (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)

/-- The compact DLR bounded-measurable natural extension is below every actual
DLR completion on every bounded observable. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_le_completion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (μ : DLRCompletion M) (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) X ≤
      dlrCompletionBoundedMeasurablePrevision M μ X :=
  boundedMeasurableNaturalExtensionPrevision_le_completion
    (dlrCompletionBoundedMeasurableCompactCredalSet M)
    (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
    (mem_dlrCompletionBoundedMeasurableCompactCredalSet M μ) X

/-- Every actual DLR completion lies below the compact DLR bounded-measurable
natural upper envelope on every bounded observable. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_completion_le
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (μ : DLRCompletion M) (X : BoundedMeasurableGamble (InfiniteWorld Atom)) :
    dlrCompletionBoundedMeasurablePrevision M μ X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) X :=
  boundedMeasurableNaturalUpperEnvelopePrevision_completion_le
    (dlrCompletionBoundedMeasurableCompactCredalSet M)
    (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
    (mem_dlrCompletionBoundedMeasurableCompactCredalSet M μ) X

/-- Evaluating a finite cylinder observable over the global bounded-measurable
DLR credal set ranges over exactly the same values as the existing
finite-region DLR prevision family. -/
theorem dlrCompletionBoundedMeasurableCredalSet_cylinder_value_image_eq_range
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    ((fun P : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom) =>
      P (dlrCylinderBoundedMeasurableGamble Λ X)) ''
        dlrCompletionBoundedMeasurableCredalSet M) =
      Set.range (fun μ : DLRCompletion M =>
        dlrCompletionRegionPrevision M μ Λ X) := by
  ext y
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨μ, rfl⟩
    exact ⟨μ, (dlrCompletionBoundedCylinderPrevision_eq_regionPrevision
      M μ Λ X).symm⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨dlrCompletionBoundedMeasurablePrevision M μ,
      mem_dlrCompletionBoundedMeasurableCredalSet M μ,
      dlrCompletionBoundedCylinderPrevision_eq_regionPrevision M μ Λ X⟩

/-- The global bounded-measurable DLR lower envelope, restricted to a finite
cylinder observable, is the existing finite-region lower envelope. -/
theorem boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableLowerEnvelope
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleLowerEnvelope M Λ X := by
  unfold boundedMeasurableLowerEnvelope dlrLocalGambleLowerEnvelope
  rw [dlrCompletionBoundedMeasurableCredalSet_cylinder_value_image_eq_range]

/-- The bounded-measurable natural extension generated by all DLR completions,
restricted to a finite cylinder observable, is the existing finite-region lower
envelope. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_cylinder_eq_localGambleLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hC : (dlrCompletionBoundedMeasurableCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCredalSet M) hC
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleLowerEnvelope M Λ X := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower]

/-- The global bounded-measurable DLR upper envelope, restricted to a finite
cylinder observable, is the existing finite-region upper envelope. -/
theorem boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableUpperEnvelope
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleUpperEnvelope M Λ X := by
  unfold boundedMeasurableUpperEnvelope dlrLocalGambleUpperEnvelope
  rw [dlrCompletionBoundedMeasurableCredalSet_cylinder_value_image_eq_range]

/-- The bounded-measurable natural upper envelope generated by all DLR
completions, restricted to a finite cylinder observable, is the existing
finite-region upper envelope. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCredalSet_cylinder_eq_localGambleUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hC : (dlrCompletionBoundedMeasurableCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCredalSet M) hC
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleUpperEnvelope M Λ X := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper]

/-- The bounded-measurable DLR envelope width on a finite cylinder is the
existing finite-region DLR width. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  unfold boundedMeasurableEnvelopeWidth dlrLocalGambleEnvelopeWidth
  rw [
    boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower,
    boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper]

/-- The bounded-measurable DLR width-complement on a finite cylinder is the
existing finite-region DLR confidence-like coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  unfold boundedMeasurableEnvelopeWidthComplement
    dlrLocalGambleEnvelopeWidthComplement
  rw [
    boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth]

/-- The bounded-measurable DLR midpoint on a finite cylinder is the existing
finite-region DLR strength-like coordinate. -/
theorem boundedMeasurableEnvelopeMidpoint_dlrCompletionCredalSet_cylinder_eq_localGambleMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeMidpoint
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  unfold boundedMeasurableEnvelopeMidpoint dlrLocalGambleEnvelopeMidpoint
  rw [
    boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower,
    boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper]

/-- Compactifying the DLR bounded-measurable credal carrier does not change the
finite-cylinder lower envelope. -/
theorem boundedMeasurableLowerEnvelope_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableLowerEnvelope
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleLowerEnvelope M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableLowerEnvelope_evaluationClosure_eq
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower]

/-- Compactifying the DLR bounded-measurable credal carrier does not change the
finite-cylinder upper envelope. -/
theorem boundedMeasurableUpperEnvelope_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableUpperEnvelope
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleUpperEnvelope M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableUpperEnvelope_evaluationClosure_eq
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper]

/-- The compact DLR bounded-measurable carrier contains a precise completion
attaining the finite-cylinder lower envelope.  The attainer may be a compact
evaluation-closure limit point, which is exactly the role of compactification. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_exists_lowerEndpoint_cylinder
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    ∃ P : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
      P ∈ dlrCompletionBoundedMeasurableCompactCredalSet M ∧
        P (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleLowerEnvelope M Λ X := by
  rcases boundedMeasurableLowerEnvelope_exists_mem_eq_of_isCompact
      (dlrCompletionBoundedMeasurableCompactCredalSet M)
      (dlrCompletionBoundedMeasurableCompactCredalSet_isCompact M)
      (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X) with
    ⟨P, hP, hEq⟩
  refine ⟨P, hP, ?_⟩
  rw [hEq]
  exact
    boundedMeasurableLowerEnvelope_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower
      M Λ X

/-- The compact DLR bounded-measurable carrier contains a precise completion
attaining the finite-cylinder upper envelope. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_exists_upperEndpoint_cylinder
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    ∃ P : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
      P ∈ dlrCompletionBoundedMeasurableCompactCredalSet M ∧
        P (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleUpperEnvelope M Λ X := by
  rcases boundedMeasurableUpperEnvelope_exists_mem_eq_of_isCompact
      (dlrCompletionBoundedMeasurableCompactCredalSet M)
      (dlrCompletionBoundedMeasurableCompactCredalSet_isCompact M)
      (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X) with
    ⟨P, hP, hEq⟩
  refine ⟨P, hP, ?_⟩
  rw [hEq]
  exact
    boundedMeasurableUpperEnvelope_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper
      M Λ X

/-- Strict DLR disagreement on a finite-cylinder observable is realized by a
pair of compact-carrier endpoint completions: one attains the lower endpoint,
one attains the upper endpoint, and the gap is strict. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_exists_endpointPair_cylinder_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
      Plo ∈ dlrCompletionBoundedMeasurableCompactCredalSet M ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
        Phi ∈ dlrCompletionBoundedMeasurableCompactCredalSet M ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) <
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  have hRawLt :
      dlrCompletionBoundedMeasurablePrevision M μ
          (dlrCylinderBoundedMeasurableGamble Λ X) <
        dlrCompletionBoundedMeasurablePrevision M ν
          (dlrCylinderBoundedMeasurableGamble Λ X) := by
    rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision,
      dlrCompletionBoundedCylinderPrevision_eq_regionPrevision]
    exact hlt
  rcases boundedMeasurableEnvelope_exists_endpointPairReadout_evaluationClosure_of_disagreement
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X)
      (mem_dlrCompletionBoundedMeasurableCredalSet M μ)
      (mem_dlrCompletionBoundedMeasurableCredalSet M ν) hRawLt with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hltEndpoints, _hWidth, _hComplement,
      _hMidpoint⟩
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hltEndpoints⟩
  · rw [hlo]
    exact
      boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower
        M Λ X
  · rw [hhi]
    exact
      boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper
        M Λ X

/-- The compact DLR bounded-measurable carrier has the same finite-cylinder
envelope width as the raw DLR completion carrier. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_localGambleWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeWidth_evaluationClosure_eq
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth]

/-- The compact DLR bounded-measurable carrier has the same finite-cylinder
width-complement confidence coordinate as the raw DLR completion carrier. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeWidthComplement_evaluationClosure_eq
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement]

/-- The compact DLR bounded-measurable carrier has the same finite-cylinder
midpoint strength coordinate as the raw DLR completion carrier. -/
theorem boundedMeasurableEnvelopeMidpoint_dlrCompletionCompactCredalSet_cylinder_eq_localGambleMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeMidpoint
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [
    boundedMeasurableEnvelopeMidpoint_evaluationClosure_eq
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    boundedMeasurableEnvelopeMidpoint_dlrCompletionCredalSet_cylinder_eq_localGambleMidpoint]

/-- The bounded-measurable natural extension of the compact DLR carrier agrees
with the finite-region DLR lower envelope on finite cylinders. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (hC : (dlrCompletionBoundedMeasurableCompactCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M) hC
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleLowerEnvelope M Λ X := by
  rw [boundedMeasurableNaturalExtensionPrevision_apply,
    boundedMeasurableLowerEnvelope_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower]

/-- The bounded-measurable natural upper envelope of the compact DLR carrier
agrees with the finite-region DLR upper envelope on finite cylinders. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (hC : (dlrCompletionBoundedMeasurableCompactCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M) hC
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      dlrLocalGambleUpperEnvelope M Λ X := by
  rw [boundedMeasurableNaturalUpperEnvelopePrevision_apply,
    boundedMeasurableUpperEnvelope_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper]

/-- If a finite-region DLR local gamble spans the full unit interval, then the
compact bounded-measurable DLR carrier reads midpoint strength one half on the
corresponding cylinder observable. -/
theorem boundedMeasurableEnvelopeMidpoint_dlrCompletionCompactCredalSet_cylinder_eq_half_of_localGambleUnitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    boundedMeasurableEnvelopeMidpoint
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = (1 / 2 : ℝ) := by
  apply boundedMeasurableEnvelopeMidpoint_eq_half_of_natural_interval
    (C := dlrCompletionBoundedMeasurableCompactCredalSet M)
    (hC := dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
  · rw [boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower]
    exact hL
  · rw [boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper]
    exact hU

/-- If a finite-region DLR local gamble spans the full unit interval, then the
compact bounded-measurable DLR carrier has maximal cylinder width. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_one_of_localGambleUnitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 1 := by
  apply boundedMeasurableEnvelopeWidth_eq_one_of_natural_interval
    (C := dlrCompletionBoundedMeasurableCompactCredalSet M)
    (hC := dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
  · rw [boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower]
    exact hL
  · rw [boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper]
    exact hU

/-- If a finite-region DLR local gamble spans the full unit interval, then the
compact bounded-measurable DLR carrier has zero width-complement confidence on
the corresponding cylinder observable. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_zero_of_localGambleUnitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 0 := by
  apply boundedMeasurableEnvelopeWidthComplement_eq_zero_of_natural_interval
    (C := dlrCompletionBoundedMeasurableCompactCredalSet M)
    (hC := dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
  · rw [boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower]
    exact hL
  · rw [boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper]
    exact hU

/-- Unit-valued finite-cylinder observables have bounded-measurable DLR
envelope width in `[0,1]`. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_in_unit_of_unit
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hC : (dlrCompletionBoundedMeasurableCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hX : ∀ x, X x ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ∈ Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeWidth_in_unit_of_unit
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCylinderBoundedMeasurableGamble Λ X) hC
    (by intro ω; exact hX (worldRestriction Λ ω))

/-- Unit-valued finite-cylinder observables have bounded-measurable DLR
width-complement confidence coordinate in `[0,1]`. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_in_unit_of_unit
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hC : (dlrCompletionBoundedMeasurableCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hX : ∀ x, X x ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ∈ Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeWidthComplement_in_unit_of_unit
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCylinderBoundedMeasurableGamble Λ X) hC
    (by intro ω; exact hX (worldRestriction Λ ω))

/-- Unit-valued finite-cylinder observables have bounded-measurable DLR
midpoint strength coordinate in `[0,1]`. -/
theorem boundedMeasurableEnvelopeMidpoint_dlrCompletionCredalSet_cylinder_in_unit_of_unit
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hC : (dlrCompletionBoundedMeasurableCredalSet M).Nonempty)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hX : ∀ x, X x ∈ Set.Icc (0 : ℝ) 1) :
    boundedMeasurableEnvelopeMidpoint
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ∈ Set.Icc (0 : ℝ) 1 :=
  boundedMeasurableEnvelopeMidpoint_in_unit_of_unit
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCylinderBoundedMeasurableGamble Λ X) hC
    (by intro ω; exact hX (worldRestriction Λ ω))

/-- DLR-determined finite-cylinder observables are also determined by the
global bounded-measurable DLR credal set. -/
theorem dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    boundedMeasurableCredalSetDetermines
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X) := by
  intro P hP Q hQ
  rcases hP with ⟨μ, rfl⟩
  rcases hQ with ⟨ν, rfl⟩
  rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision,
    dlrCompletionBoundedCylinderPrevision_eq_regionPrevision]
  exact hDet μ ν

/-- Strict DLR disagreement on a finite-cylinder observable gives strict width
in the global bounded-measurable DLR credal set. -/
theorem dlrCompletionBoundedMeasurableCredalSet_hasStrictWidth_cylinder_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    boundedMeasurableCredalSetHasStrictWidth
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  refine ⟨dlrCompletionBoundedMeasurablePrevision M μ,
    mem_dlrCompletionBoundedMeasurableCredalSet M μ,
    dlrCompletionBoundedMeasurablePrevision M ν,
    mem_dlrCompletionBoundedMeasurableCredalSet M ν, ?_⟩
  rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision,
    dlrCompletionBoundedCylinderPrevision_eq_regionPrevision]
  exact hlt

/-- The global bounded-measurable DLR credal set determines a finite-cylinder
observable exactly when all DLR completions agree on the corresponding local
gamble. -/
theorem dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableCredalSetDetermines
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ↔
      dlrLocalGambleDetermined M Λ X := by
  constructor
  · intro hDet μ ν
    have hEq := hDet
      (dlrCompletionBoundedMeasurablePrevision M μ)
      (mem_dlrCompletionBoundedMeasurableCredalSet M μ)
      (dlrCompletionBoundedMeasurablePrevision M ν)
      (mem_dlrCompletionBoundedMeasurableCredalSet M ν)
    rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision,
      dlrCompletionBoundedCylinderPrevision_eq_regionPrevision] at hEq
    exact hEq
  · exact dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_of_localGambleDetermined
      M Λ X

/-- The global bounded-measurable DLR credal set has strict width on a
finite-cylinder observable exactly when two DLR completions strictly disagree on
the corresponding local gamble. -/
theorem dlrCompletionBoundedMeasurableCredalSet_hasStrictWidth_cylinder_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableCredalSetHasStrictWidth
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  constructor
  · intro hWidth
    rcases hWidth with ⟨P, hP, Q, hQ, hlt⟩
    rcases hP with ⟨μ, rfl⟩
    rcases hQ with ⟨ν, rfl⟩
    rw [dlrCompletionBoundedCylinderPrevision_eq_regionPrevision,
      dlrCompletionBoundedCylinderPrevision_eq_regionPrevision] at hlt
    exact ⟨μ, ν, hlt⟩
  · exact dlrCompletionBoundedMeasurableCredalSet_hasStrictWidth_cylinder_of_localGambleStrictWidth
      M Λ X

/-- DLR-determined finite-cylinder observables remain determined after
compactifying the global bounded-measurable DLR credal set. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_determines_cylinder_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    boundedMeasurableCredalSetDetermines
      (dlrCompletionBoundedMeasurableCompactCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X) := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  exact boundedMeasurableCredalSetDetermines_evaluationClosure_of_determines
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
    (dlrCylinderBoundedMeasurableGamble Λ X)
    (dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_of_localGambleDetermined
      M Λ X hDet)

/-- Strict DLR disagreement on a finite-cylinder observable remains strict
width after compactifying the global bounded-measurable DLR credal set. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_hasStrictWidth_cylinder_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    boundedMeasurableCredalSetHasStrictWidth
      (dlrCompletionBoundedMeasurableCompactCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X) := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  exact boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_of_strictWidth
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCylinderBoundedMeasurableGamble Λ X)
    (dlrCompletionBoundedMeasurableCredalSet_hasStrictWidth_cylinder_of_localGambleStrictWidth
      M Λ X hWidth)

/-- The compact global bounded-measurable DLR credal carrier determines a
finite-cylinder observable exactly when all DLR completions agree on the
corresponding local gamble. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_determines_cylinder_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableCredalSetDetermines
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ↔
      dlrLocalGambleDetermined M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [boundedMeasurableCredalSetDetermines_evaluationClosure_iff
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
    (dlrCylinderBoundedMeasurableGamble Λ X)]
  exact dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_iff_localGambleDetermined
    M Λ X

/-- The compact global bounded-measurable DLR credal carrier has strict width on
a finite-cylinder observable exactly when two DLR completions strictly disagree
on the corresponding local gamble.  Compactification therefore does not create
spurious DLR imprecision on finite cylinders. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_hasStrictWidth_cylinder_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableCredalSetHasStrictWidth
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  unfold dlrCompletionBoundedMeasurableCompactCredalSet
  rw [boundedMeasurableCredalSetHasStrictWidth_evaluationClosure_iff
    (dlrCompletionBoundedMeasurableCredalSet M)
    (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
    (dlrCylinderBoundedMeasurableGamble Λ X)]
  exact dlrCompletionBoundedMeasurableCredalSet_hasStrictWidth_cylinder_iff_localGambleStrictWidth
    M Λ X

/-- Strict DLR disagreement on a finite-cylinder observable is realized by
Walley dominating completions of the compact DLR natural extension.

This is the DLR specialization of the generic bounded-measurable Walley
endpoint theorem: the endpoint completions dominate the compact DLR natural
extension, are strictly separated on the cylinder query, and compute the local
DLR PLN-facing width, width-complement, and midpoint coordinates. -/
theorem dlrCompletionBoundedMeasurableCompactCredalSet_exists_dominatingStrictEndpointPairReadout_cylinder_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionBoundedMeasurableCompactCredalSet M)
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionBoundedMeasurableCompactCredalSet M)
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)) ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) <
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) ∧
        dlrLocalGambleEnvelopeWidth M Λ X =
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
            Plo (dlrCylinderBoundedMeasurableGamble Λ X) ∧
        dlrLocalGambleEnvelopeWidthComplement M Λ X =
          1 -
            (Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
              Plo (dlrCylinderBoundedMeasurableGamble Λ X)) ∧
        dlrLocalGambleEnvelopeMidpoint M Λ X =
          (Plo (dlrCylinderBoundedMeasurableGamble Λ X) +
            Phi (dlrCylinderBoundedMeasurableGamble Λ X)) / 2 := by
  let C : BoundedMeasurableCredalSet (InfiniteWorld Atom) :=
    dlrCompletionBoundedMeasurableCompactCredalSet M
  let Z : BoundedMeasurableGamble (InfiniteWorld Atom) :=
    dlrCylinderBoundedMeasurableGamble Λ X
  have hStrict :
      boundedMeasurableCredalSetHasStrictWidth C Z := by
    dsimp [C, Z]
    exact
      dlrCompletionBoundedMeasurableCompactCredalSet_hasStrictWidth_cylinder_of_localGambleStrictWidth
        M Λ X hWidth
  rcases
      boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        C (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) Z
        hStrict with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hloLocal :
      Plo Z = dlrLocalGambleLowerEnvelope M Λ X := by
    calc
      Plo Z =
          boundedMeasurableNaturalExtensionPrevision C
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) Z :=
        hlo
      _ = dlrLocalGambleLowerEnvelope M Λ X := by
        dsimp [C, Z]
        exact
          boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower
            M (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) Λ X
  have hhiLocal :
      Phi Z = dlrLocalGambleUpperEnvelope M Λ X := by
    calc
      Phi Z =
          boundedMeasurableNaturalUpperEnvelopePrevision C
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) Z :=
        hhi
      _ = dlrLocalGambleUpperEnvelope M Λ X := by
        dsimp [C, Z]
        exact
          boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper
            M (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) Λ X
  have hWidthLocal :
      dlrLocalGambleEnvelopeWidth M Λ X = Phi Z - Plo Z := by
    calc
      dlrLocalGambleEnvelopeWidth M Λ X =
          boundedMeasurableEnvelopeWidth C Z := by
        dsimp [C, Z]
        exact
          (boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_localGambleWidth
            M Λ X).symm
      _ = Phi Z - Plo Z := hWidthEq
  have hCompLocal :
      dlrLocalGambleEnvelopeWidthComplement M Λ X = 1 - (Phi Z - Plo Z) := by
    calc
      dlrLocalGambleEnvelopeWidthComplement M Λ X =
          boundedMeasurableEnvelopeWidthComplement C Z := by
        dsimp [C, Z]
        exact
          (boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement
            M Λ X).symm
      _ = 1 - (Phi Z - Plo Z) := hCompEq
  have hMidLocal :
      dlrLocalGambleEnvelopeMidpoint M Λ X = (Plo Z + Phi Z) / 2 := by
    calc
      dlrLocalGambleEnvelopeMidpoint M Λ X =
          boundedMeasurableEnvelopeMidpoint C Z := by
        dsimp [C, Z]
        exact
          (boundedMeasurableEnvelopeMidpoint_dlrCompletionCompactCredalSet_cylinder_eq_localGambleMidpoint
            M Λ X).symm
      _ = (Plo Z + Phi Z) / 2 := hMidEq
  refine ⟨Plo, ?_, Phi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [C] using hPlo
  · simpa [C] using hPhi
  · simpa [Z] using hloLocal
  · simpa [Z] using hhiLocal
  · simpa [Z] using hlt
  · simpa [Z] using hWidthLocal
  · simpa [Z] using hCompLocal
  · simpa [Z] using hMidLocal

/-- DLR-determined finite-cylinder observables have zero compact-carrier
bounded-measurable DLR envelope width. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_zero_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 0 := by
  rw [
    boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_localGambleWidth]
  exact dlrLocalGambleEnvelopeWidth_eq_zero_of_localGambleDetermined
    M Λ X hDet

/-- Strict DLR disagreement on a finite-cylinder observable gives positive
compact-carrier bounded-measurable global envelope width. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_pos_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    0 < boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  letI : Nonempty (DLRCompletion M) := ⟨μ⟩
  rw [
    boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_localGambleWidth]
  exact dlrLocalGambleEnvelopeWidth_pos_of_localGambleStrictWidth
    M Λ X ⟨μ, ν, hlt⟩

/-- DLR-determined finite-cylinder observables have maximal compact-carrier
bounded-measurable DLR width-complement, the PLN-facing confidence-like
coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_one_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 1 := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_eq_one_of_localGambleDetermined
    M Λ X hDet

/-- Strict DLR disagreement on a finite-cylinder observable forces the
compact-carrier bounded-measurable DLR width-complement below one. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_lt_one_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) < 1 := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  letI : Nonempty (DLRCompletion M) := ⟨μ⟩
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
    M Λ X ⟨μ, ν, hlt⟩

/-- On the compact bounded-measurable DLR carrier, a finite-cylinder
width-complement is maximal exactly when the underlying local gamble is
DLR-determined. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_one_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 1 ↔
      dlrLocalGambleDetermined M Λ X := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_eq_one_iff_localGambleDetermined
    M Λ X

/-- On the compact bounded-measurable DLR carrier, a finite-cylinder
width-complement falls below one exactly when the underlying local gamble has
strict DLR width. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_lt_one_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) < 1 ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth
    M Λ X

/-- Strict DLR disagreement on a finite-cylinder observable gives positive
bounded-measurable global envelope width. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_pos_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    0 < boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) := by
  rw [
    boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth]
  exact dlrLocalGambleEnvelopeWidth_pos_of_localGambleStrictWidth M Λ X hWidth

/-- DLR-determined finite-cylinder observables have zero global
bounded-measurable DLR envelope width. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_zero_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 0 := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact
    boundedMeasurableEnvelopeWidth_eq_zero_of_determines
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (boundedMeasurableCredalRange_bddBelow
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X))
      (boundedMeasurableCredalRange_bddAbove
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X))
      (mem_dlrCompletionBoundedMeasurableCredalSet M μ)
      (dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_of_localGambleDetermined
        M Λ X hDet)

/-- DLR-determined finite-cylinder observables have maximal global
bounded-measurable DLR width-complement, the PLN-facing confidence-like
coordinate. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_one_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 1 := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact
    boundedMeasurableEnvelopeWidthComplement_eq_one_of_determines
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X)
      (dlrCompletionBoundedMeasurableCredalSet_nonempty M)
      (boundedMeasurableCredalRange_bddBelow
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X))
      (boundedMeasurableCredalRange_bddAbove
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X))
      (mem_dlrCompletionBoundedMeasurableCredalSet M μ)
      (dlrCompletionBoundedMeasurableCredalSet_determines_cylinder_of_localGambleDetermined
        M Λ X hDet)

/-- Strict DLR disagreement on a finite-cylinder observable forces the global
bounded-measurable DLR width-complement below one. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_lt_one_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) < 1 := by
  exact
    boundedMeasurableEnvelopeWidthComplement_lt_one_of_strictWidth
      (dlrCompletionBoundedMeasurableCredalSet M)
      (dlrCylinderBoundedMeasurableGamble Λ X)
      (boundedMeasurableCredalRange_bddBelow
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X))
      (boundedMeasurableCredalRange_bddAbove
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X))
      (dlrCompletionBoundedMeasurableCredalSet_hasStrictWidth_cylinder_of_localGambleStrictWidth
        M Λ X hWidth)

/-- On the raw bounded-measurable DLR completion carrier, a finite-cylinder
width-complement is maximal exactly when the underlying local gamble is
DLR-determined. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_one_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) = 1 ↔
      dlrLocalGambleDetermined M Λ X := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_eq_one_iff_localGambleDetermined
    M Λ X

/-- On the raw bounded-measurable DLR completion carrier, a finite-cylinder
width-complement falls below one exactly when the underlying local gamble has
strict DLR width. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_lt_one_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)] [Nonempty (LocalAssignment Atom Λ)]
    (X : Gamble (LocalAssignment Atom Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) < 1 ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth
    M Λ X

/-- Finite-dimensional marginals of a single DLR completion are compatible
under restriction of finite regions.  This is the cylinder-domain replacement
for a still-future weak*/all-gambles prevision adapter: it uses the already
proved projective law for `limitMarginal` PMFs, then transports it through the
finite measure/PMF prevision API. -/
theorem dlrCompletionRegionPrevision_restrict
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M)
    {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (X : Gamble (LocalAssignment Atom Λ)) :
    dlrCompletionRegionPrevision M μ Δ
        (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ)) =
      dlrCompletionRegionPrevision M μ Λ X := by
  unfold dlrCompletionRegionPrevision
  let νΔ : Measure (LocalAssignment Atom Δ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Δ
  let νΛ : Measure (LocalAssignment Atom Λ) :=
    RegionExhaustion.limitMarginal (Atom := Atom)
      (μ.1 : Measure (InfiniteWorld Atom)) Λ
  haveI : IsProbabilityMeasure νΔ := by
    dsimp [νΔ]
    infer_instance
  haveI : IsProbabilityMeasure νΛ := by
    dsimp [νΛ]
    infer_instance
  change PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision νΔ
      (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ)) =
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision νΛ X
  have hmeasure :
      Measure.map (restrictLocalAssignment hΛΔ) νΔ = νΛ := by
    dsimp [νΔ, νΛ]
    -- `restrictLocalAssignment hΛΔ` is definitionally `restrictAssignment hΛΔ`; under Lean 4.31
    -- `simpa … using` no longer bridges the two, so close by defeq directly.
    exact limitMarginal_map_restrictAssignment (Atom := Atom) μ.1 hΛΔ
  have hpush :
      @PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision
          (LocalAssignment Atom Λ) _ _ _
          (Measure.map (restrictLocalAssignment hΛΔ) νΔ)
          (Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable) X =
        PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision νΔ
          (fun xΔ => X (restrictLocalAssignment hΛΔ xΔ)) :=
    PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_map_apply
      νΔ (restrictLocalAssignment hΛΔ) Measurable.of_discrete X
  rw [← hpush]
  rw [PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_apply]
  rw [PrecisePrevision.FiniteWeights.ofFiniteProbabilityMeasurePrevision_apply]
  apply Finset.sum_congr rfl
  intro xΛ _hxΛ
  rw [hmeasure]

/-- A DLR completion induces a compatible cylinder-domain precise prevision:
one finite precise prevision for every finite region, with restriction
compatibility supplied by `dlrCompletionRegionPrevision_restrict`. -/
noncomputable def dlrCompletionCylinderPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) :
    (dlrAllRegionsCylinderSystem Atom).CylinderPrevision where
  toFun Λ X := dlrCompletionRegionPrevision M μ Λ X
  lower_bound := by
    intro Λ X c hc
    exact (dlrCompletionRegionPrevision M μ Λ).lower_bound X c hc
  pos_homog := by
    intro Λ r X hr
    exact (dlrCompletionRegionPrevision M μ Λ).pos_homog r X hr
  add := by
    intro Λ X Y
    exact (dlrCompletionRegionPrevision M μ Λ).add X Y
  restrict_compat := by
    intro Λ Δ hΛΔ X
    exact dlrCompletionRegionPrevision_restrict M μ hΛΔ X

@[simp] theorem dlrCompletionCylinderPrevision_localPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) (Λ : Region Atom) :
    (dlrCompletionCylinderPrevision M μ).localPrevision Λ =
      dlrCompletionRegionPrevision M μ Λ := by
  ext X
  rfl

/-- The finite-volume global-world prevision has the expected same-region
marginal: pulling a local gamble back along the all-regions cylinder projection
and evaluating the global finite-support prevision is the same as evaluating
the original finite-volume local assignment prevision. -/
theorem dlrAllRegionsCylinderSystem_marginalPrevision_finiteVolumeWorldPrevision_sameRegion
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ
        (finiteVolumeWorldPrevision M Λ ξ hZ) =
      finiteVolumeAssignmentPrevision M Λ ξ hZ := by
  ext X
  change finiteVolumeWorldPrevision M Λ ξ hZ
      ((dlrAllRegionsCylinderSystem Atom).cylinderGamble Λ X) =
    finiteVolumeAssignmentPrevision M Λ ξ hZ X
  rw [finiteVolumeWorldPrevision_apply, finiteVolumeAssignmentPrevision_apply]
  apply Finset.sum_congr rfl
  intro x _hx
  have hrestrict : worldRestriction Λ (patch Λ x ξ) = x := by
    funext a
    simp [worldRestriction, patch]
  have hcyl :
      ((dlrAllRegionsCylinderSystem Atom).cylinderGamble Λ X)
          (patch Λ x ξ) = X x := by
    change X (worldRestriction Λ (patch Λ x ξ)) = X x
    rw [hrestrict]
  rw [hcyl]

/-- More generally, if a finite-volume world prevision is generated on a
larger region `Δ`, its marginal to a smaller region `Λ ⊆ Δ` is the restriction
push-forward of the `Δ` assignment prevision.  This is the finite-support
prototype of projective consistency for DLR completions. -/
theorem dlrAllRegionsCylinderSystem_marginalPrevision_finiteVolumeWorldPrevision_subregion
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Δ ξ ≠ 0) :
    (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ
        (finiteVolumeWorldPrevision M Δ ξ hZ) =
      finiteVolumeAssignmentMarginalPrevision M hΛΔ ξ hZ := by
  ext X
  change finiteVolumeWorldPrevision M Δ ξ hZ
      ((dlrAllRegionsCylinderSystem Atom).cylinderGamble Λ X) =
    finiteVolumeAssignmentMarginalPrevision M hΛΔ ξ hZ X
  rw [finiteVolumeWorldPrevision_apply,
    finiteVolumeAssignmentMarginalPrevision_apply]
  apply Finset.sum_congr rfl
  intro x _hx
  have hrestrict :
      worldRestriction Λ (patch Δ x ξ) =
        restrictLocalAssignment hΛΔ x := by
    funext a
    have haΔ : (a.1 : Atom) ∈ Δ := hΛΔ a.2
    simp [worldRestriction, patch, restrictLocalAssignment, haΔ]
  have hcyl :
      ((dlrAllRegionsCylinderSystem Atom).cylinderGamble Λ X)
          (patch Δ x ξ) =
        X (restrictLocalAssignment hΛΔ x) := by
    change X (worldRestriction Λ (patch Δ x ξ)) =
      X (restrictLocalAssignment hΛΔ x)
    rw [hrestrict]
  rw [hcyl]

/-- The same subregion compatibility expressed at the restricted
cylinder-prevision layer.  This is the form a future σ-additive DLR
measure adapter should target: compatible finite-window previsions, not an
expectation functional on arbitrary global gambles. -/
theorem dlrAllRegionsCylinderSystem_cylinderPrevision_finiteVolumeWorldPrevision_subregion
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom} (hΛΔ : Λ ≤ Δ)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Δ ξ ≠ 0) :
    ((dlrAllRegionsCylinderSystem Atom).cylinderPrevisionOfPrecisePrevision
        (finiteVolumeWorldPrevision M Δ ξ hZ)).localPrevision Λ =
      finiteVolumeAssignmentMarginalPrevision M hΛΔ ξ hZ := by
  rw [ProjectiveCylinderSystem.cylinderPrevisionOfPrecisePrevision_localPrevision]
  exact
    dlrAllRegionsCylinderSystem_marginalPrevision_finiteVolumeWorldPrevision_subregion
      M hΛΔ ξ hZ

/-- The all-regions DLR local-credal specification.  Its local credal set at
region `Λ` is the set of finite-dimensional marginal previsions induced by DLR
completions on `Λ`.  A full global precise-prevision inhabitant is supplied by a
separate weak*/expectation adapter theorem. -/
def dlrAllRegionsProjectiveSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) where
  cylinders := dlrAllRegionsCylinderSystem Atom
  localCredal Λ := dlrRegionCredalSet M Λ

/-- Every local credal component of the all-regions DLR specification is
convex, because DLR completions are closed under affine mixture. -/
theorem dlrAllRegionsProjectiveSpec_localCredal_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    ∀ Λ, CredalPrevisionSet.IsConvex
      ((dlrAllRegionsProjectiveSpec M).localCredal Λ) := by
  intro Λ
  exact dlrRegionCredalSet_isConvex M Λ

/-- The all-regions DLR projective-limit credal carrier is convex whenever its
finite-region marginals are read through the projective specification. -/
theorem dlrAllRegionsProjectiveSpec_projectiveLimitCredalSet_isConvex
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    CredalPrevisionSet.IsConvex
      (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet := by
  exact ProjectiveLocalCredalSpec.projectiveLimitCredalSet_isConvex
    (dlrAllRegionsProjectiveSpec M)
    (dlrAllRegionsProjectiveSpec_localCredal_isConvex M)

/-- Compatible all-regions DLR cylinder-domain completions are closed under
affine mixture. -/
theorem dlrAllRegionsProjectiveSpec_projectiveCylinderCredalSet_mix_mem
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {K L : (dlrAllRegionsProjectiveSpec M).cylinders.CylinderPrevision}
    (hK : K ∈ (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet)
    (hL : L ∈ (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ProjectiveCylinderSystem.CylinderPrevision.mix t K L ht0 ht1 ∈
      (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet := by
  exact ProjectiveLocalCredalSpec.projectiveCylinderCredalSet_mix_mem_of_local_convex
    (dlrAllRegionsProjectiveSpec M)
    (dlrAllRegionsProjectiveSpec_localCredal_isConvex M)
    hK hL t ht0 ht1

/-- A DLR completion is a concrete compatible cylinder-domain completion of
the all-regions DLR credal specification. -/
theorem dlrAllRegionsProjectiveSpec_mem_projectiveCylinderCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M) :
    dlrCompletionCylinderPrevision M μ ∈
      (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet := by
  intro Λ
  exact mem_dlrRegionCredalSet M Λ μ

/-- If at least one DLR completion exists, then the all-regions DLR credal
specification has a compatible cylinder-domain completion.  This avoids the
stronger all-global-gambles prevision adapter, which belongs to the later
weak*/compact carrier layer. -/
theorem dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)] :
    (dlrAllRegionsProjectiveSpec M).hasCompatibleCylinderCompletion := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact ⟨dlrCompletionCylinderPrevision M μ,
    dlrAllRegionsProjectiveSpec_mem_projectiveCylinderCredalSet M μ⟩

/-- Cylinder-domain exactness for the all-regions DLR credal specification:
every finite-region DLR marginal prevision is lifted by the compatible
cylinder prevision induced from the same DLR completion. -/
theorem dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) :
    (dlrAllRegionsProjectiveSpec M).localCylinderCredalExactAt Λ := by
  intro R hR
  rcases hR with ⟨μ, rfl⟩
  exact ⟨dlrCompletionCylinderPrevision M μ,
    dlrAllRegionsProjectiveSpec_mem_projectiveCylinderCredalSet M μ,
    dlrCompletionCylinderPrevision_localPrevision M μ Λ⟩

/-- For the all-regions DLR specification, the image of compatible
cylinder-domain completions at a finite region is exactly the DLR region
credal set.  Thus the generic cylinder natural-extension object is not a
separate construction: it reads the same local credal family supplied by the
DLR completions. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) :
    (dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ =
      dlrRegionCredalSet M Λ := by
  simpa [dlrAllRegionsProjectiveSpec] using
    (ProjectiveLocalCredalSpec.cylinderLocalCredalSet_eq_localCredal_of_exact
      (S := dlrAllRegionsProjectiveSpec M) Λ
      (dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ))

/-- If all DLR completions agree on a finite-region local query, then the
all-regions cylinder-image credal set determines that local query. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_determines_localQuery
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    credalSetDetermines
      ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ)
      (localQueryIndicatorGamble Λ q) := by
  rw [dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet]
  exact dlrRegionCredalSet_determines_localQuery_of_localQueryDetermined
    M Λ q hDet

/-- If all DLR completions agree on an arbitrary finite-region local gamble,
then the all-regions cylinder-image credal set determines that gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_determines_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    credalSetDetermines
      ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ) X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet]
  exact dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
    M Λ X hDet

/-- If two DLR completions disagree on a finite-region local query, then the
all-regions cylinder-image credal set has strict width on that query. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_hasStrictWidth_localQuery
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    credalSetHasStrictWidth
      ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ)
      (localQueryIndicatorGamble Λ q) := by
  rw [dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet]
  exact dlrRegionCredalSet_hasStrictWidth_localQuery_of_localQueryStrictWidth
    M Λ q hWidth

/-- If two DLR completions disagree on an arbitrary finite-region local gamble,
then the all-regions cylinder-image credal set has strict width on that gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_hasStrictWidth_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    credalSetHasStrictWidth
      ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ) X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet]
  exact dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
    M Λ X hWidth

/-- The all-regions DLR cylinder-image credal set determines a local gamble
exactly when all DLR completions agree on that local gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_determines_localGamble_iff
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    credalSetDetermines
        ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ) X ↔
      dlrLocalGambleDetermined M Λ X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet]
  exact dlrRegionCredalSet_determines_localGamble_iff_localGambleDetermined
    M Λ X

/-- The all-regions DLR cylinder-image credal set has strict width on a local
gamble exactly when two DLR completions strictly disagree on that local gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_hasStrictWidth_localGamble_iff
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    credalSetHasStrictWidth
        ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ) X ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_eq_regionCredalSet]
  exact dlrRegionCredalSet_hasStrictWidth_localGamble_iff_localGambleStrictWidth
    M Λ X

/-- Strict DLR local-query width refutes determination at the all-regions
cylinder-image credal layer. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_not_determines_localQuery
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    ¬ credalSetDetermines
      ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ)
      (localQueryIndicatorGamble Λ q) := by
  exact not_credalSetDetermines_of_strictWidth
    (dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_hasStrictWidth_localQuery
      M Λ q hWidth)

/-- Strict DLR local-gamble width refutes determination at the all-regions
cylinder-image credal layer. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_not_determines_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ¬ credalSetDetermines
      ((dlrAllRegionsProjectiveSpec M).cylinderLocalCredalSet Λ) X := by
  exact not_credalSetDetermines_of_strictWidth
    (dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_hasStrictWidth_localGamble
      M Λ X hWidth)

/-- A supplied global prevision adapter is compatible with the all-regions DLR
projective spec when its finite-region marginals are the DLR completion
marginals.  This is the exact interface the future weak* measure-to-prevision
construction must inhabit. -/
theorem dlrAllRegionsProjectiveSpec_mem_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (μ : DLRCompletion M) :
    toPrecise μ ∈ (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet := by
  intro Λ
  change (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) ∈
    dlrRegionCredalSet M Λ
  rw [hMarginal μ Λ]
  exact mem_dlrRegionCredalSet M Λ μ

theorem dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ) :
    (dlrAllRegionsProjectiveSpec M).hasCompatibleCompletion := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact ⟨toPrecise μ,
    dlrAllRegionsProjectiveSpec_mem_of_marginal_eq M toPrecise hMarginal μ⟩

/-- Under a supplied global prevision adapter with exact finite-region
marginals, every local DLR finite-region prevision lifts to a compatible global
completion. -/
theorem dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom) :
    (dlrAllRegionsProjectiveSpec M).localCredalExactAt Λ := by
  intro R hR
  rcases hR with ⟨μ, rfl⟩
  exact ⟨toPrecise μ,
    dlrAllRegionsProjectiveSpec_mem_of_marginal_eq M toPrecise hMarginal μ,
    hMarginal μ Λ⟩

theorem dlrRegionCredalSet_localQuery_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddBelow ((fun P : PrecisePrevision (LocalAssignment Atom Λ) =>
      P (localQueryIndicatorGamble Λ q)) '' dlrRegionCredalSet M Λ) := by
  refine ⟨0, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.lower_bound (localQueryIndicatorGamble Λ q) 0
    (localQueryIndicatorGamble_nonneg Λ q)

theorem dlrRegionCredalSet_localQuery_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddAbove ((fun P : PrecisePrevision (LocalAssignment Atom Λ) =>
      P (localQueryIndicatorGamble Λ q)) '' dlrRegionCredalSet M Λ) := by
  refine ⟨1, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.upper_bound (localQueryIndicatorGamble Λ q) 1
    (localQueryIndicatorGamble_le_one Λ q)

theorem dlrAllRegionsProjectiveSpec_cylinderLocalQuery_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddBelow
      ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q))) ''
        (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet) := by
  refine ⟨0, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.lower_bound
    ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
      (localQueryIndicatorGamble Λ q)) 0
    (fun ω => localQueryIndicatorGamble_nonneg Λ q
      ((dlrAllRegionsProjectiveSpec M).cylinders.project Λ ω))

/-- The same local-query lower bound at the cylinder-completion layer. -/
theorem dlrAllRegionsProjectiveSpec_cylinderCompletionLocalQuery_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddBelow
      ((fun K : (dlrAllRegionsProjectiveSpec M).cylinders.CylinderPrevision =>
        K.toFun Λ (localQueryIndicatorGamble Λ q)) ''
        (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet) := by
  refine ⟨0, ?_⟩
  rintro y ⟨K, _hK, rfl⟩
  exact K.lower_bound Λ (localQueryIndicatorGamble Λ q) 0
    (localQueryIndicatorGamble_nonneg Λ q)

/-- The same local-query upper bound at the cylinder-completion layer. -/
theorem dlrAllRegionsProjectiveSpec_cylinderCompletionLocalQuery_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddAbove
      ((fun K : (dlrAllRegionsProjectiveSpec M).cylinders.CylinderPrevision =>
        K.toFun Λ (localQueryIndicatorGamble Λ q)) ''
        (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet) := by
  refine ⟨1, ?_⟩
  rintro y ⟨K, _hK, rfl⟩
  change K.localPrevision Λ (localQueryIndicatorGamble Λ q) ≤ 1
  exact (K.localPrevision Λ).upper_bound (localQueryIndicatorGamble Λ q) 1
    (localQueryIndicatorGamble_le_one Λ q)

theorem dlrAllRegionsProjectiveSpec_cylinderLocalQuery_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    BddAbove
      ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q))) ''
        (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet) := by
  refine ⟨1, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.upper_bound
    ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
      (localQueryIndicatorGamble Λ q)) 1
    (fun ω => localQueryIndicatorGamble_le_one Λ q
      ((dlrAllRegionsProjectiveSpec M).cylinders.project Λ ω))

/-- Finite local regions make the global compatible-completion expectation range
of any cylinder-lifted local gamble bounded below.  This is the all-global-gambles
counterpart of the cylinder-completion boundedness lemma. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    BddBelow
      ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) ''
        (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet) := by
  rcases finite_gamble_uniformLowerBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.lower_bound
    ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) c
    (fun ω => hc ((dlrAllRegionsProjectiveSpec M).cylinders.project Λ ω))

/-- Finite local regions make the global compatible-completion expectation range
of any cylinder-lifted local gamble bounded above. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    BddAbove
      ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) ''
        (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet) := by
  rcases finite_gamble_uniformUpperBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨P, _hP, rfl⟩
  exact P.upper_bound
    ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) c
    (fun ω => hc ((dlrAllRegionsProjectiveSpec M).cylinders.project Λ ω))

/-- Finite local regions make the cylinder-completion expectation range of any
local gamble bounded below.  This is the arbitrary-local-gamble replacement for
the special `0/1` local-query bound. -/
theorem dlrAllRegionsProjectiveSpec_cylinderCompletionLocalGamble_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    BddBelow
      ((fun K : (dlrAllRegionsProjectiveSpec M).cylinders.CylinderPrevision =>
        K.toFun Λ X) ''
        (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet) := by
  rcases finite_gamble_uniformLowerBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨K, _hK, rfl⟩
  exact K.lower_bound Λ X c hc

/-- Finite local regions make the cylinder-completion expectation range of any
local gamble bounded above. -/
theorem dlrAllRegionsProjectiveSpec_cylinderCompletionLocalGamble_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    BddAbove
      ((fun K : (dlrAllRegionsProjectiveSpec M).cylinders.CylinderPrevision =>
        K.toFun Λ X) ''
        (dlrAllRegionsProjectiveSpec M).projectiveCylinderCredalSet) := by
  rcases finite_gamble_uniformUpperBound X with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rintro y ⟨K, _hK, rfl⟩
  change K.localPrevision Λ X ≤ c
  exact (K.localPrevision Λ).upper_bound X c hc

/-- On finite local regions, the all-regions DLR cylinder natural extension of
an arbitrary local gamble is exactly the lower envelope of the DLR region credal
set.  No all-global-gambles prevision adapter is assumed. -/
theorem dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_lowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ X =
      lowerEnvelope (dlrRegionCredalSet M Λ) X := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hCylinderNonempty : S.hasCompatibleCylinderCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCylinderCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ
  have h := ProjectiveLocalCredalSpec.cylinderNaturalExtension_eq_localLowerEnvelope_of_exact
    (S := S) hCylinderNonempty Λ X hLocalNonempty
    (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
    (dlrAllRegionsProjectiveSpec_cylinderCompletionLocalGamble_bddBelow M Λ X)
    hExact
  rw [h]
  change lowerEnvelope (dlrRegionCredalSet M Λ) X =
    lowerEnvelope (dlrRegionCredalSet M Λ) X
  rfl

/-- On finite local regions, the all-regions DLR cylinder upper envelope of an
arbitrary local gamble is exactly the upper envelope of the DLR region credal
set. -/
theorem dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_upperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ X =
      upperEnvelope (dlrRegionCredalSet M Λ) X := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hCylinderNonempty : S.hasCompatibleCylinderCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCylinderCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ
  have h := ProjectiveLocalCredalSpec.cylinderUpperEnvelope_eq_localUpperEnvelope_of_exact
    (S := S) hCylinderNonempty Λ X hLocalNonempty
    (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
    (dlrAllRegionsProjectiveSpec_cylinderCompletionLocalGamble_bddAbove M Λ X)
    hExact
  rw [h]
  change upperEnvelope (dlrRegionCredalSet M Λ) X =
    upperEnvelope (dlrRegionCredalSet M Λ) X
  rfl

/-- On finite local regions, the all-regions DLR cylinder natural extension of
an arbitrary local gamble is the infimum over DLR completions' local prevision
values for that gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_localGambleLowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ X =
      dlrLocalGambleLowerEnvelope M Λ X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_lowerEnvelope,
    lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]

/-- On finite local regions, the all-regions DLR cylinder upper envelope of an
arbitrary local gamble is the supremum over DLR completions' local prevision
values for that gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_localGambleUpperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ X =
      dlrLocalGambleUpperEnvelope M Λ X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_upperEnvelope,
    upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]

/-- The local natural extension of the all-regions DLR projective spec is the
finite-region lower envelope supplied by DLR completions. -/
theorem dlrAllRegionsProjectiveSpec_localNaturalExtension_localGamble_eq_localGambleLowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).localNaturalExtension Λ X =
      dlrLocalGambleLowerEnvelope M Λ X := by
  change lowerEnvelope (dlrRegionCredalSet M Λ) X =
    dlrLocalGambleLowerEnvelope M Λ X
  exact lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower M Λ X

/-- The local upper envelope of the all-regions DLR projective spec is the
finite-region upper envelope supplied by DLR completions. -/
theorem dlrAllRegionsProjectiveSpec_localUpperEnvelope_localGamble_eq_localGambleUpperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).localUpperEnvelope Λ X =
      dlrLocalGambleUpperEnvelope M Λ X := by
  change upperEnvelope (dlrRegionCredalSet M Λ) X =
    dlrLocalGambleUpperEnvelope M Λ X
  exact upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper M Λ X

/-- On finite local regions, the all-regions DLR cylinder interval width of an
arbitrary local gamble is exactly the local DLR credal-envelope width.  This is
the local-gamble version of the PLN-facing imprecision coordinate. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_credalEnvelopeWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X =
      credalEnvelopeWidth (dlrRegionCredalSet M Λ) X := by
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeWidth credalEnvelopeWidth
  rw [dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_upperEnvelope,
    dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_lowerEnvelope]

/-- On finite local regions, the all-regions DLR cylinder width-complement of an
arbitrary local gamble is exactly the local DLR credal width-complement.  Under
the width-complement reading, this is the confidence-like coordinate of the
local credal interval. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_credalEnvelopeWidthComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X =
      credalEnvelopeWidthComplement (dlrRegionCredalSet M Λ) X := by
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeWidthComplement
    credalEnvelopeWidthComplement
  rw [
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_credalEnvelopeWidth]

/-- On finite local regions, the all-regions DLR cylinder midpoint of an
arbitrary local gamble is exactly the local DLR credal midpoint.  This is the
strength-like point-estimate coordinate associated to the local credal interval. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_credalEnvelopeMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ X =
      credalEnvelopeMidpoint (dlrRegionCredalSet M Λ) X := by
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeMidpoint
    credalEnvelopeMidpoint
  rw [dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_lowerEnvelope,
    dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_upperEnvelope]

/-- On finite local regions, the all-regions DLR cylinder interval width of an
arbitrary local gamble is the width of the completion-range lower/upper
envelope for that gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_localGambleEnvelopeWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  rw [dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_credalEnvelopeWidth,
    credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width]

/-- On finite local regions, the all-regions DLR cylinder width-complement of an
arbitrary local gamble is the width-complement of the completion-range envelope
for that gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_localGambleEnvelopeWidthComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  rw [
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_credalEnvelopeWidthComplement,
    credalEnvelopeWidthComplement_dlrRegionCredalSet_localGamble_eq_complement]

/-- On finite local regions, the all-regions DLR cylinder midpoint of an
arbitrary local gamble is the midpoint of the completion-range envelope for that
gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_localGambleEnvelopeMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ X =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  rw [
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_credalEnvelopeMidpoint,
    credalEnvelopeMidpoint_dlrRegionCredalSet_localGamble_eq_midpoint]

/-- If a finite-region DLR local gamble spans the full unit interval, then the
all-regions cylinder-domain projective credal view reads midpoint strength one
half. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_eq_half_of_localGambleUnitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ X =
      (1 / 2 : ℝ) := by
  rw [
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_localGambleEnvelopeMidpoint]
  exact dlrLocalGambleEnvelopeMidpoint_eq_half_of_unitInterval M Λ X hL hU

/-- If a finite-region DLR local gamble spans the full unit interval, then the
all-regions cylinder-domain projective credal view has maximal interval width. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_eq_one_of_localGambleUnitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X = 1 := by
  rw [
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_localGambleEnvelopeWidth]
  exact dlrLocalGambleEnvelopeWidth_eq_one_of_unitInterval M Λ X hL hU

/-- If a finite-region DLR local gamble spans the full unit interval, then the
all-regions cylinder-domain projective credal view has zero width-complement
confidence. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_zero_of_localGambleUnitInterval
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hL : dlrLocalGambleLowerEnvelope M Λ X = 0)
    (hU : dlrLocalGambleUpperEnvelope M Λ X = 1) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X = 0 := by
  rw [
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_localGambleEnvelopeWidthComplement]
  exact dlrLocalGambleEnvelopeWidthComplement_eq_zero_of_unitInterval M Λ X hL hU

/-- DLR-determined arbitrary local gambles have zero cylinder-domain credal
width in the all-regions projective specification. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_eq_zero_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X = 0 := by
  exact
    ProjectiveLocalCredalSpec.finiteCylinderEnvelopeWidth_eq_zero_of_localCredal_determines_of_exact
        (S := dlrAllRegionsProjectiveSpec M)
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M)
        Λ X
        (dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ)
        (dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
          M Λ X hDet)

/-- Strictly disagreeing DLR completions on an arbitrary local gamble give
nontrivial lower/upper cylinder envelopes in the all-regions projective
specification. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLowerUpperEnvelope_nontrivial_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ X <
      (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ X := by
  exact
    ProjectiveLocalCredalSpec.finiteCylinderLowerUpperEnvelope_nontrivial_of_localCredal_strictWidth_of_exact
        (S := dlrAllRegionsProjectiveSpec M)
        Λ X
        (dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ)
        (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
          M Λ X hWidth)

/-- Strictly disagreeing DLR completions on an arbitrary local gamble give
positive cylinder-domain credal width in the all-regions projective
specification. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_pos_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    0 < (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X := by
  exact
    ProjectiveLocalCredalSpec.finiteCylinderEnvelopeWidth_pos_of_localCredal_strictWidth_of_exact
        (S := dlrAllRegionsProjectiveSpec M)
        Λ X
        (dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ)
        (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
          M Λ X hWidth)

/-- Two concrete DLR completions that strictly disagree on a finite-region
local gamble give nontrivial lower/upper cylinder envelopes in the all-regions
projective specification.  This is the direct phase-witness shape needed by a
future Ising/nonunique-Gibbs canary. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLowerUpperEnvelope_nontrivial_of_completionDisagreement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (μ ν : DLRCompletion M)
    (hlt : dlrCompletionRegionPrevision M μ Λ X <
      dlrCompletionRegionPrevision M ν Λ X) :
    (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ X <
      (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ X :=
  dlrAllRegionsProjectiveSpec_cylinderLowerUpperEnvelope_nontrivial_of_localGambleStrictWidth
    M Λ X ⟨μ, ν, hlt⟩

/-- Two concrete DLR completions that strictly disagree on a finite-region
local gamble force positive PLN/Walley interval width in the all-regions
cylinder-domain credal view. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_pos_of_completionDisagreement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (μ ν : DLRCompletion M)
    (hlt : dlrCompletionRegionPrevision M μ Λ X <
      dlrCompletionRegionPrevision M ν Λ X) :
    0 < (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X :=
  dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_pos_of_localGambleStrictWidth
    M Λ X ⟨μ, ν, hlt⟩

/-- DLR-determined arbitrary local gambles have maximal cylinder-domain
width-complement, the PLN-facing confidence-like coordinate. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_of_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X = 1 := by
  exact
    ProjectiveLocalCredalSpec.finiteCylinderEnvelopeWidthComplement_eq_one_of_localCredal_determines_of_exact
        (S := dlrAllRegionsProjectiveSpec M)
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M)
        Λ X
        (dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ)
        (dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
          M Λ X hDet)

/-- Strict DLR local-gamble width forces the cylinder-domain width-complement
coordinate below one. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X < 1 := by
  exact
    ProjectiveLocalCredalSpec.finiteCylinderEnvelopeWidthComplement_lt_one_of_localCredal_strictWidth_of_exact
        (S := dlrAllRegionsProjectiveSpec M)
        Λ X
        (dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ)
        (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
          M Λ X hWidth)

/-- Two concrete DLR completions that strictly disagree on a finite-region
local gamble force the cylinder-domain width-complement confidence coordinate
below one. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_completionDisagreement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (μ ν : DLRCompletion M)
    (hlt : dlrCompletionRegionPrevision M μ Λ X <
      dlrCompletionRegionPrevision M ν Λ X) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X < 1 :=
  dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
    M Λ X ⟨μ, ν, hlt⟩

/-- At the all-regions cylinder-domain DLR layer, the width-complement
coordinate is maximal exactly when the finite-region local gamble is determined
by all DLR completions. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_iff_localGambleDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X = 1 ↔
      dlrLocalGambleDetermined M Λ X := by
  constructor
  · intro hEq
    by_contra hNot
    have hWidth : dlrLocalGambleHasStrictWidth M Λ X :=
      (dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined M Λ X).2 hNot
    have hLt :=
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
        M Λ X hWidth
    exact (ne_of_lt hLt) hEq
  · intro hDet
    exact
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_of_localGambleDetermined
        M Λ X hDet

/-- At the all-regions cylinder-domain DLR layer, the width-complement falls
below one exactly when two DLR completions strictly disagree on the finite-region
local gamble. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X < 1 ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  constructor
  · intro hLt
    refine
      (dlrLocalGambleHasStrictWidth_iff_not_localGambleDetermined M Λ X).2 ?_
    intro hDet
    have hEq :=
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_of_localGambleDetermined
        M Λ X hDet
    rw [hEq] at hLt
    exact (not_lt_of_ge le_rfl) hLt
  · intro hWidth
    exact
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth
        M Λ X hWidth

/-- The packaged finite-region DLR cylinder natural extension computes the lower
envelope of the DLR region credal set on any finite local gamble. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_localGamble_eq_lowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X =
      lowerEnvelope (dlrRegionCredalSet M Λ) X := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_apply]
  exact dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_lowerEnvelope
    M Λ X

/-- The packaged finite-region DLR cylinder upper-envelope prevision computes the
upper envelope of the DLR region credal set on any finite local gamble. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_localGamble_eq_upperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X =
      upperEnvelope (dlrRegionCredalSet M Λ) X := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderUpperEnvelopePrevision_apply]
  exact dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_upperEnvelope
    M Λ X

/-- The all-regions finite-cylinder DLR natural extension is below every
concrete DLR completion's finite-region prevision. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_le_completion_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (μ : DLRCompletion M)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X ≤
        dlrCompletionRegionPrevision M μ Λ X := by
  rw [
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_localGamble_eq_lowerEnvelope,
    lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]
  exact dlrLocalGambleLowerEnvelope_le_completion M Λ μ X

/-- The all-regions finite-cylinder DLR natural extension is the greatest lower
prevision dominated by every concrete DLR completion's finite-region prevision. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_greatest_lower_bound_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (L : LowerPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hL : ∀ μ : DLRCompletion M,
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        L X ≤ dlrCompletionRegionPrevision M μ Λ X)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    L X ≤
      ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X := by
  rw [
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_localGamble_eq_lowerEnvelope,
    lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]
  exact dlrLocalGambleLowerEnvelope_greatest_lower_bound M Λ L hL X

/-- Every concrete DLR completion's finite-region prevision is below the
all-regions finite-cylinder DLR upper envelope. -/
theorem dlrAllRegionsProjectiveSpec_completion_le_finiteCylinderUpperEnvelopePrevision_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (μ : DLRCompletion M)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    dlrCompletionRegionPrevision M μ Λ X ≤
      ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X := by
  rw [
    dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_localGamble_eq_upperEnvelope,
    upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]
  exact dlrCompletion_le_localGambleUpperEnvelope M Λ μ X

/-- The all-regions finite-cylinder DLR upper envelope is the least upper
prevision dominating every concrete DLR completion's finite-region prevision. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_least_upper_bound_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (U : UpperPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hU : ∀ μ : DLRCompletion M,
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        dlrCompletionRegionPrevision M μ Λ X ≤ U X)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X ≤
      U X := by
  rw [
    dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_localGamble_eq_upperEnvelope,
    upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]
  exact dlrLocalGambleUpperEnvelope_least_upper_bound M Λ U hU X

/-- Strict DLR disagreement on an arbitrary local gamble is realized by
Walley dominating completions of the finite-region cylinder natural extension.

Unlike the all-global-gamble theorem, this lives entirely in the finite-region
cylinder interface: it needs no supplied global prevision adapter and no
boundedness hypothesis beyond finite local state spaces.  The lower and upper
dominating precise previsions touch the DLR local lower/upper envelopes and
compute the PLN-facing width, width-complement, and midpoint coordinates. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_localGamble_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : PrecisePrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
      Plo ∈ dominatingPreciseCompletions
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) ∧
      ∃ Phi : PrecisePrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        Phi ∈ dominatingPreciseCompletions
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) ∧
        Plo X = dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi X = dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo X < Phi X ∧
        dlrLocalGambleEnvelopeWidth M Λ X = Phi X - Plo X ∧
        dlrLocalGambleEnvelopeWidthComplement M Λ X =
          1 - (Phi X - Plo X) ∧
        dlrLocalGambleEnvelopeMidpoint M Λ X =
          (Plo X + Phi X) / 2 := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hCylinderWidth :
      credalSetHasStrictWidth (S.cylinderLocalCredalSet Λ) X :=
    dlrAllRegionsProjectiveSpec_cylinderLocalCredalSet_hasStrictWidth_localGamble
      M Λ X hWidth
  rcases
      ProjectiveLocalCredalSpec.cylinderNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout
        (S := S) (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M)
        Λ
        (finite_credalRange_bddBelow (S.cylinderLocalCredalSet Λ))
        (finite_credalRange_bddAbove (S.cylinderLocalCredalSet Λ))
        X hCylinderWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hloDLR : Plo X = dlrLocalGambleLowerEnvelope M Λ X :=
    hlo.trans
      (dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_localGambleLowerEnvelope
        M Λ X)
  have hhiDLR : Phi X = dlrLocalGambleUpperEnvelope M Λ X :=
    hhi.trans
      (dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_localGambleUpperEnvelope
        M Λ X)
  refine ⟨Plo, ?_, Phi, ?_, hloDLR, hhiDLR, hlt, ?_, ?_, ?_⟩
  · simpa [S, ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision]
      using hPlo
  · simpa [S, ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision]
      using hPhi
  · exact
      (dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_localGambleEnvelopeWidth
        M Λ X).symm.trans hWidthEq
  · exact
      (dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_localGambleEnvelopeWidthComplement
        M Λ X).symm.trans hCompEq
  · exact
      (dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_localGambleEnvelopeMidpoint
        M Λ X).symm.trans hMidEq

/-- The compact bounded-measurable DLR natural extension and the all-regions
projective cylinder natural extension agree on finite cylinder observables.

This is the direct adapter theorem connecting the σ-additive compact DLR carrier
to the shared projective-cylinder Walley interface. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsFiniteCylinderNaturalExtensionPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleLower,
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_localGamble_eq_lowerEnvelope,
    lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower]

/-- The compact bounded-measurable DLR upper envelope and the all-regions
projective cylinder upper envelope agree on finite cylinder observables. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsFiniteCylinderUpperEnvelopePrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_localGambleUpper,
    dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_localGamble_eq_upperEnvelope,
    upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper]

/-- The compact bounded-measurable DLR natural extension on a finite cylinder is
below every concrete DLR completion's finite-region prevision. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_le_completionRegionPrevision
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (μ : DLRCompletion M)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ≤
      dlrCompletionRegionPrevision M μ Λ X := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsFiniteCylinderNaturalExtensionPrevision]
  exact
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_le_completion_localGamble
      M Λ μ X

/-- The compact bounded-measurable DLR natural extension on finite cylinders is
the greatest local lower prevision dominated by every concrete DLR completion's
finite-region prevision. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_greatest_lower_bound_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (L : LowerPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hL : ∀ μ : DLRCompletion M,
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        L X ≤ dlrCompletionRegionPrevision M μ Λ X)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    L X ≤
      boundedMeasurableNaturalExtensionPrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
        (dlrCylinderBoundedMeasurableGamble Λ X) := by
  rw [
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsFiniteCylinderNaturalExtensionPrevision]
  exact
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_greatest_lower_bound_localGamble
      M Λ L hL X

/-- Every concrete DLR completion's finite-region prevision is below the compact
bounded-measurable DLR natural upper envelope on the corresponding finite
cylinder. -/
theorem dlrCompletionRegionPrevision_le_boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (μ : DLRCompletion M)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    dlrCompletionRegionPrevision M μ Λ X ≤
      boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
        (dlrCylinderBoundedMeasurableGamble Λ X) := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsFiniteCylinderUpperEnvelopePrevision]
  exact
    dlrAllRegionsProjectiveSpec_completion_le_finiteCylinderUpperEnvelopePrevision_localGamble
      M Λ μ X

/-- The compact bounded-measurable DLR natural upper envelope on finite
cylinders is the least local upper prevision dominating every concrete DLR
completion's finite-region prevision. -/
theorem boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_least_upper_bound_localGamble
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (U : UpperPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hU : ∀ μ : DLRCompletion M,
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        dlrCompletionRegionPrevision M μ Λ X ≤ U X)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableNaturalUpperEnvelopePrevision
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
        (dlrCylinderBoundedMeasurableGamble Λ X) ≤
      U X := by
  rw [
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsFiniteCylinderUpperEnvelopePrevision]
  exact
    dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_least_upper_bound_localGamble
      M Λ U hU X

/-- The compact bounded-measurable DLR carrier and the all-regions projective
cylinder interface compute the same PLN-facing interval width on finite
cylinder observables. -/
theorem boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsCylinderEnvelopeWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableEnvelopeWidth
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X := by
  rw [
    boundedMeasurableEnvelopeWidth_dlrCompletionCompactCredalSet_cylinder_eq_localGambleWidth,
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_localGambleEnvelopeWidth]

/-- The compact bounded-measurable DLR carrier and the all-regions projective
cylinder interface compute the same PLN-facing width-complement confidence
coordinate on finite cylinder observables. -/
theorem boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsCylinderEnvelopeWidthComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableEnvelopeWidthComplement
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X := by
  rw [
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCompactCredalSet_cylinder_eq_localGambleComplement,
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_localGambleEnvelopeWidthComplement]

/-- The compact bounded-measurable DLR carrier and the all-regions projective
cylinder interface compute the same PLN-facing midpoint strength coordinate on
finite cylinder observables. -/
theorem boundedMeasurableEnvelopeMidpoint_dlrCompletionCompactCredalSet_cylinder_eq_allRegionsCylinderEnvelopeMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    boundedMeasurableEnvelopeMidpoint
        (dlrCompletionBoundedMeasurableCompactCredalSet M)
        (dlrCylinderBoundedMeasurableGamble Λ X) =
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ X := by
  rw [
    boundedMeasurableEnvelopeMidpoint_dlrCompletionCompactCredalSet_cylinder_eq_localGambleMidpoint,
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_localGambleEnvelopeMidpoint]

/-- Strict DLR disagreement on a finite-cylinder observable is realized by
compact bounded-measurable Walley endpoint completions whose readout is stated
directly in the all-regions finite-cylinder projective interface. -/
theorem boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_exists_dominatingStrictEndpointPairReadout_cylinder_eq_allRegions_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionBoundedMeasurableCompactCredalSet M)
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionBoundedMeasurableCompactCredalSet M)
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)) ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) =
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X ∧
        Phi (dlrCylinderBoundedMeasurableGamble Λ X) =
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) <
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) ∧
        (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X =
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
            Plo (dlrCylinderBoundedMeasurableGamble Λ X) ∧
        (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X =
          1 -
            (Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
              Plo (dlrCylinderBoundedMeasurableGamble Λ X)) ∧
        (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ X =
          (Plo (dlrCylinderBoundedMeasurableGamble Λ X) +
            Phi (dlrCylinderBoundedMeasurableGamble Λ X)) / 2 := by
  rcases
      dlrCompletionBoundedMeasurableCompactCredalSet_exists_dominatingStrictEndpointPairReadout_cylinder_of_localGambleStrictWidth
        M Λ X hWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hComplementEq,
      hMidpointEq⟩
  have hFiniteLower :
      dlrLocalGambleLowerEnvelope M Λ X =
        ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
          (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X := by
    exact
      ((dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_localGamble_eq_lowerEnvelope
          M Λ X).trans
        (lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower M Λ X)).symm
  have hFiniteUpper :
      dlrLocalGambleUpperEnvelope M Λ X =
        ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
          (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X := by
    exact
      ((dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_localGamble_eq_upperEnvelope
          M Λ X).trans
        (upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper M Λ X)).symm
  have hWidthAllRegions :
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X =
        Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
          Plo (dlrCylinderBoundedMeasurableGamble Λ X) := by
    exact
      (dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localGamble_eq_localGambleEnvelopeWidth
        M Λ X).trans hWidthEq
  have hComplementAllRegions :
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X =
        1 -
          (Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
            Plo (dlrCylinderBoundedMeasurableGamble Λ X)) := by
    exact
      (dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localGamble_eq_localGambleEnvelopeWidthComplement
        M Λ X).trans hComplementEq
  have hMidpointAllRegions :
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ X =
        (Plo (dlrCylinderBoundedMeasurableGamble Λ X) +
          Phi (dlrCylinderBoundedMeasurableGamble Λ X)) / 2 := by
    exact
      (dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localGamble_eq_localGambleEnvelopeMidpoint
        M Λ X).trans hMidpointEq
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hlt, hWidthAllRegions,
    hComplementAllRegions, hMidpointAllRegions⟩
  · exact hlo.trans hFiniteLower
  · exact hhi.trans hFiniteUpper

/-- The conjugate of the packaged finite-region DLR cylinder natural extension
computes the upper envelope of the DLR region credal set on any finite local
gamble.  This is the arbitrary-local-gamble Walley lower/upper duality. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_conjugate_localGamble_eq_upperEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ).conjugate) X =
      upperEnvelope (dlrRegionCredalSet M Λ) X := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_conjugate_eq_upperEnvelope]
  exact dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_upperEnvelope
    M Λ X

/-- The conjugate of the packaged finite-region DLR cylinder upper-envelope
prevision computes the lower envelope of the DLR region credal set on any finite
local gamble. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_conjugate_localGamble_eq_lowerEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ).conjugate) X =
      lowerEnvelope (dlrRegionCredalSet M Λ) X := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderUpperEnvelopePrevision_conjugate_eq_naturalExtension]
  exact dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_lowerEnvelope
    M Λ X

theorem dlrAllRegionsProjectiveSpec_globalNaturalExtension_localQuery_eq_lower_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
      dlrLocalQueryLowerEnvelope M Λ q := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hGlobalNonempty : S.hasCompatibleCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
      M toPrecise hMarginal
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
      M toPrecise hMarginal Λ
  have h := ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
    (S := S) hGlobalNonempty Λ (localQueryIndicatorGamble Λ q)
    hLocalNonempty (dlrRegionCredalSet_localQuery_bddBelow M Λ q)
    (dlrAllRegionsProjectiveSpec_cylinderLocalQuery_bddBelow M Λ q)
    hExact
  rw [h]
  change lowerEnvelope (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
    dlrLocalQueryLowerEnvelope M Λ q
  exact lowerEnvelope_dlrRegionCredalSet_localQuery_eq_lower M Λ q

/-- The cylinder-domain natural extension of a local DLR query agrees with
the DLR local lower envelope, without assuming any all-global-gambles
prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localQuery_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryLowerEnvelope M Λ q := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hCylinderNonempty : S.hasCompatibleCylinderCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCylinderCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ
  have h := ProjectiveLocalCredalSpec.cylinderNaturalExtension_eq_localLowerEnvelope_of_exact
    (S := S) hCylinderNonempty Λ (localQueryIndicatorGamble Λ q)
    hLocalNonempty (dlrRegionCredalSet_localQuery_bddBelow M Λ q)
    (dlrAllRegionsProjectiveSpec_cylinderCompletionLocalQuery_bddBelow M Λ q)
    hExact
  rw [h]
  change lowerEnvelope (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
    dlrLocalQueryLowerEnvelope M Λ q
  exact lowerEnvelope_dlrRegionCredalSet_localQuery_eq_lower M Λ q

/-- The cylinder-domain upper envelope of a local DLR query agrees with the
DLR local upper envelope, still without assuming an all-global-gambles
prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localQuery_eq_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryUpperEnvelope M Λ q := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hCylinderNonempty : S.hasCompatibleCylinderCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCylinderCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ
  have h := ProjectiveLocalCredalSpec.cylinderUpperEnvelope_eq_localUpperEnvelope_of_exact
    (S := S) hCylinderNonempty Λ (localQueryIndicatorGamble Λ q)
    hLocalNonempty (dlrRegionCredalSet_localQuery_bddAbove M Λ q)
    (dlrAllRegionsProjectiveSpec_cylinderCompletionLocalQuery_bddAbove M Λ q)
    hExact
  rw [h]
  change upperEnvelope (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
    dlrLocalQueryUpperEnvelope M Λ q
  exact upperEnvelope_dlrRegionCredalSet_localQuery_eq_upper M Λ q

/-- The cylinder-domain interval width of a local DLR query agrees with the
local DLR lower/upper envelope width. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localQuery_eq_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeWidth M Λ q := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hCylinderNonempty : S.hasCompatibleCylinderCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCylinderCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt M Λ
  have h := ProjectiveLocalCredalSpec.cylinderEnvelopeWidth_eq_localEnvelopeWidth_of_exact
    (S := S) hCylinderNonempty Λ (localQueryIndicatorGamble Λ q)
    hLocalNonempty (dlrRegionCredalSet_localQuery_bddBelow M Λ q)
    (dlrRegionCredalSet_localQuery_bddAbove M Λ q)
    (dlrAllRegionsProjectiveSpec_cylinderCompletionLocalQuery_bddBelow M Λ q)
    (dlrAllRegionsProjectiveSpec_cylinderCompletionLocalQuery_bddAbove M Λ q)
    hExact
  rw [h]
  change credalEnvelopeWidth (dlrRegionCredalSet M Λ)
      (localQueryIndicatorGamble Λ q) =
    dlrLocalQueryEnvelopeWidth M Λ q
  exact credalEnvelopeWidth_dlrRegionCredalSet_localQuery_eq_width M Λ q

/-- Determined DLR local queries have zero cylinder-domain credal width in the
all-regions projective specification. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_eq_zero_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ
        (localQueryIndicatorGamble Λ q) = 0 := by
  rw [dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localQuery_eq_width]
  exact dlrLocalQueryEnvelopeWidth_eq_zero_of_localQueryDetermined M Λ q hDet

/-- Strictly disagreeing DLR local completions give positive cylinder-domain
lower/upper interval width for the local query.  This is the query-indicator
special case of the arbitrary-local-gamble interval theorem. -/
theorem dlrAllRegionsProjectiveSpec_cylinderLowerUpperEnvelope_nontrivial_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ
        (localQueryIndicatorGamble Λ q) <
      (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ
        (localQueryIndicatorGamble Λ q) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  haveI : Nonempty (DLRCompletion M) := ⟨μ⟩
  rw [dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localQuery_eq_lower,
    dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localQuery_eq_upper]
  exact dlrLocalQueryEnvelope_nontrivial_of_localQueryStrictWidth
    M Λ q ⟨μ, ν, hlt⟩

/-- Strictly disagreeing DLR local completions give positive cylinder-domain
credal width in the all-regions projective specification. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_pos_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    0 < (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ
        (localQueryIndicatorGamble Λ q) := by
  have hlt :=
    dlrAllRegionsProjectiveSpec_cylinderLowerUpperEnvelope_nontrivial_of_localQueryStrictWidth
      M Λ q hWidth
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeWidth
  linarith

/-- Determined DLR local queries have maximal cylinder-domain width-complement,
the PLN-facing confidence coordinate derived from interval width. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_of_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hDet : dlrLocalQueryDetermined M Λ q) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ
        (localQueryIndicatorGamble Λ q) = 1 := by
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeWidthComplement
  rw [dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_eq_zero_of_localQueryDetermined
    M Λ q hDet]
  ring

/-- Strict DLR local-query width forces the cylinder-domain width-complement
coordinate below one.  This is the formal local DLR version of "phase
multiplicity lowers the width-complement confidence coordinate". -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ)
    (hWidth : dlrLocalQueryHasStrictWidth M Λ q) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ
        (localQueryIndicatorGamble Λ q) < 1 := by
  have hpos :=
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_pos_of_localQueryStrictWidth
      M Λ q hWidth
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeWidthComplement
  linarith

/-- At the all-regions cylinder-domain DLR layer, the local-query
width-complement is maximal exactly when all DLR completions determine the
query. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_iff_localQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ
        (localQueryIndicatorGamble Λ q) = 1 ↔
      dlrLocalQueryDetermined M Λ q := by
  constructor
  · intro hEq
    by_contra hNot
    have hWidth : dlrLocalQueryHasStrictWidth M Λ q :=
      (dlrLocalQueryHasStrictWidth_iff_not_localQueryDetermined M Λ q).2 hNot
    have hLt :=
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
        M Λ q hWidth
    exact (ne_of_lt hLt) hEq
  · intro hDet
    exact
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_of_localQueryDetermined
        M Λ q hDet

/-- At the all-regions cylinder-domain DLR layer, the local-query
width-complement falls below one exactly when two DLR completions strictly
disagree on the query. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_iff_localQueryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ
        (localQueryIndicatorGamble Λ q) < 1 ↔
      dlrLocalQueryHasStrictWidth M Λ q := by
  constructor
  · intro hLt
    refine
      (dlrLocalQueryHasStrictWidth_iff_not_localQueryDetermined M Λ q).2 ?_
    intro hDet
    have hEq :=
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_eq_one_of_localQueryDetermined
        M Λ q hDet
    rw [hEq] at hLt
    exact (not_lt_of_ge le_rfl) hLt
  · intro hWidth
    exact
      dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
        M Λ q hWidth

/-- The cylinder-domain width-complement coordinate of a local DLR query
agrees with the local DLR width-complement coordinate. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_localQuery_eq_complement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeWidthComplement M Λ q := by
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeWidthComplement
    dlrLocalQueryEnvelopeWidthComplement
  rw [dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_localQuery_eq_width]

/-- The cylinder-domain midpoint coordinate of a local DLR query agrees with
the local DLR midpoint coordinate. -/
theorem dlrAllRegionsProjectiveSpec_cylinderEnvelopeMidpoint_localQuery_eq_midpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeMidpoint Λ
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryEnvelopeMidpoint M Λ q := by
  unfold ProjectiveLocalCredalSpec.cylinderEnvelopeMidpoint
    dlrLocalQueryEnvelopeMidpoint
  rw [dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localQuery_eq_lower,
    dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localQuery_eq_upper]

/-- On finite local regions, the DLR cylinder natural extension is a genuine
Walley-coherent lower prevision on local gambles. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_isCoherent
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)] :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ).isCoherent :=
  ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_isCoherent
    (S := dlrAllRegionsProjectiveSpec M)
    (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ

/-- On finite local regions, the DLR cylinder natural extension is exactly
representable as the lower envelope of the precise previsions dominating it. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)] :
    hasExactDominatingPreciseEnvelope
      ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) :=
  ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_hasExactDominatingPreciseEnvelope
    (S := dlrAllRegionsProjectiveSpec M)
    (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ

/-- Re-enveloping the finite-region DLR cylinder natural extension by all
precise previsions dominating it recovers the same lower prevision. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_dominatingEnvelope_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)] :
    lowerEnvelopePrevision
        (dominatingPreciseCompletions
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ))
        (dominatingPreciseCompletions_nonempty
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ))
        (dominatingPreciseCompletions_bddBelow
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ)) =
      (dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ :=
  ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_dominatingEnvelope_eq
    (S := dlrAllRegionsProjectiveSpec M)
    (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ

/-- The packaged finite-region DLR cylinder natural extension computes the same
local-query lower envelope as the explicit DLR envelope API. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_localQuery_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (q : LocalConstraintQuery Atom Λ) :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ)
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryLowerEnvelope M Λ q := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_apply]
  exact dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localQuery_eq_lower M Λ q

/-- The packaged finite-region DLR cylinder upper-envelope prevision computes
the same local-query upper envelope as the explicit DLR envelope API. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_localQuery_eq_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (q : LocalConstraintQuery Atom Λ) :
    ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ)
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryUpperEnvelope M Λ q := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderUpperEnvelopePrevision_apply]
  exact dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localQuery_eq_upper M Λ q

/-- The conjugate of the packaged finite-region DLR cylinder natural extension
computes the explicit DLR local-query upper envelope. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_conjugate_localQuery_eq_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (q : LocalConstraintQuery Atom Λ) :
    (((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ).conjugate)
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryUpperEnvelope M Λ q := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderNaturalExtensionPrevision_conjugate_eq_upperEnvelope]
  exact dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localQuery_eq_upper M Λ q

/-- The conjugate of the packaged finite-region DLR cylinder upper-envelope
prevision computes the explicit DLR local-query lower envelope. -/
theorem dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_conjugate_localQuery_eq_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (q : LocalConstraintQuery Atom Λ) :
    (((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
      (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ).conjugate)
        (localQueryIndicatorGamble Λ q) =
      dlrLocalQueryLowerEnvelope M Λ q := by
  rw [ProjectiveLocalCredalSpec.finiteCylinderUpperEnvelopePrevision_conjugate_eq_naturalExtension]
  exact dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localQuery_eq_lower M Λ q

theorem dlrAllRegionsProjectiveSpec_globalUpperEnvelope_localQuery_eq_upper_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
      dlrLocalQueryUpperEnvelope M Λ q := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hGlobalNonempty : S.hasCompatibleCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
      M toPrecise hMarginal
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
      M toPrecise hMarginal Λ
  have h := ProjectiveLocalCredalSpec.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
    (S := S) hGlobalNonempty Λ (localQueryIndicatorGamble Λ q)
    hLocalNonempty (dlrRegionCredalSet_localQuery_bddAbove M Λ q)
    (dlrAllRegionsProjectiveSpec_cylinderLocalQuery_bddAbove M Λ q)
    hExact
  rw [h]
  change upperEnvelope (dlrRegionCredalSet M Λ) (localQueryIndicatorGamble Λ q) =
    dlrLocalQueryUpperEnvelope M Λ q
  exact upperEnvelope_dlrRegionCredalSet_localQuery_eq_upper M Λ q

theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidth_localQuery_eq_width_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
      dlrLocalQueryEnvelopeWidth M Λ q := by
  change
    upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) -
      (dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
    dlrLocalQueryUpperEnvelope M Λ q - dlrLocalQueryLowerEnvelope M Λ q
  rw [
    dlrAllRegionsProjectiveSpec_globalUpperEnvelope_localQuery_eq_upper_of_marginal_eq
      M toPrecise hMarginal Λ q,
    dlrAllRegionsProjectiveSpec_globalNaturalExtension_localQuery_eq_lower_of_marginal_eq
      M toPrecise hMarginal Λ q]

theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_localQuery_eq_complement_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
      dlrLocalQueryEnvelopeWidthComplement M Λ q := by
  change
    1 - (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
    1 - dlrLocalQueryEnvelopeWidth M Λ q
  rw [
    dlrAllRegionsProjectiveSpec_globalEnvelopeWidth_localQuery_eq_width_of_marginal_eq
      M toPrecise hMarginal Λ q]

theorem dlrAllRegionsProjectiveSpec_globalEnvelopeMidpoint_localQuery_eq_midpoint_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeMidpoint
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) =
      dlrLocalQueryEnvelopeMidpoint M Λ q := by
  change
    ((dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q)) +
      upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ
          (localQueryIndicatorGamble Λ q))) / 2 =
    (dlrLocalQueryLowerEnvelope M Λ q + dlrLocalQueryUpperEnvelope M Λ q) / 2
  rw [
    dlrAllRegionsProjectiveSpec_globalNaturalExtension_localQuery_eq_lower_of_marginal_eq
      M toPrecise hMarginal Λ q,
    dlrAllRegionsProjectiveSpec_globalUpperEnvelope_localQuery_eq_upper_of_marginal_eq
      M toPrecise hMarginal Λ q]

/-- With an exact global prevision adapter, the global natural extension of an
arbitrary finite-region cylinder gamble agrees with the DLR local lower envelope. -/
theorem dlrAllRegionsProjectiveSpec_globalNaturalExtension_localGamble_eq_lower_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
      dlrLocalGambleLowerEnvelope M Λ X := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hGlobalNonempty : S.hasCompatibleCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
      M toPrecise hMarginal
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
      M toPrecise hMarginal Λ
  have h := ProjectiveLocalCredalSpec.globalNaturalExtension_cylinder_eq_localNaturalExtension_of_exact
    (S := S) hGlobalNonempty Λ X hLocalNonempty
    (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
    (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
    hExact
  rw [h]
  change lowerEnvelope (dlrRegionCredalSet M Λ) X =
    dlrLocalGambleLowerEnvelope M Λ X
  exact lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower M Λ X

/-- With an exact global prevision adapter, the global upper envelope of an
arbitrary finite-region cylinder gamble agrees with the DLR local upper envelope. -/
theorem dlrAllRegionsProjectiveSpec_globalUpperEnvelope_localGamble_eq_upper_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
      dlrLocalGambleUpperEnvelope M Λ X := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hGlobalNonempty : S.hasCompatibleCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
      M toPrecise hMarginal
  have hLocalNonempty : (S.localCredal Λ).Nonempty := by
    change (dlrRegionCredalSet M Λ).Nonempty
    exact dlrRegionCredalSet_nonempty M Λ
  have hExact : S.localCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
      M toPrecise hMarginal Λ
  have h := ProjectiveLocalCredalSpec.globalUpperEnvelope_cylinder_eq_localUpperEnvelope_of_exact
    (S := S) hGlobalNonempty Λ X hLocalNonempty
    (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
    (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
    hExact
  rw [h]
  change upperEnvelope (dlrRegionCredalSet M Λ) X =
    dlrLocalGambleUpperEnvelope M Λ X
  exact upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper M Λ X

/-- With an exact global prevision adapter, global compatible-completion width on
an arbitrary finite-region cylinder gamble agrees with the DLR local-gamble width. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidth_localGamble_eq_width_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  change
    upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) -
      (dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
    dlrLocalGambleUpperEnvelope M Λ X - dlrLocalGambleLowerEnvelope M Λ X
  rw [
    dlrAllRegionsProjectiveSpec_globalUpperEnvelope_localGamble_eq_upper_of_marginal_eq
      M toPrecise hMarginal Λ X,
    dlrAllRegionsProjectiveSpec_globalNaturalExtension_localGamble_eq_lower_of_marginal_eq
      M toPrecise hMarginal Λ X]

/-- With an exact global prevision adapter, the global width-complement coordinate
of an arbitrary finite-region cylinder gamble agrees with the DLR local-gamble
width-complement. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_localGamble_eq_complement_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  change
    1 - (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
    1 - dlrLocalGambleEnvelopeWidth M Λ X
  rw [
    dlrAllRegionsProjectiveSpec_globalEnvelopeWidth_localGamble_eq_width_of_marginal_eq
      M toPrecise hMarginal Λ X]

/-- Under an exact all-global-gambles adapter, the global cylinder
width-complement is maximal exactly when the corresponding finite-region local
gamble is DLR-determined. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_eq_one_iff_localGambleDetermined_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) = 1 ↔
      dlrLocalGambleDetermined M Λ X := by
  rw [
    dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_localGamble_eq_complement_of_marginal_eq
      M toPrecise hMarginal Λ X]
  exact dlrLocalGambleEnvelopeWidthComplement_eq_one_iff_localGambleDetermined
    M Λ X

/-- Under an exact all-global-gambles adapter, the global cylinder
width-complement falls below one exactly when two DLR completions strictly
disagree on the corresponding finite-region local gamble. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) < 1 ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  rw [
    dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_localGamble_eq_complement_of_marginal_eq
      M toPrecise hMarginal Λ X]
  exact dlrLocalGambleEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth
    M Λ X

/-- With an exact global prevision adapter, the global midpoint coordinate of an
arbitrary finite-region cylinder gamble agrees with the DLR local-gamble midpoint. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeMidpoint_localGamble_eq_midpoint_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeMidpoint
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  change
    ((dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) +
      upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) / 2 =
    (dlrLocalGambleLowerEnvelope M Λ X +
      dlrLocalGambleUpperEnvelope M Λ X) / 2
  rw [
    dlrAllRegionsProjectiveSpec_globalNaturalExtension_localGamble_eq_lower_of_marginal_eq
      M toPrecise hMarginal Λ X,
    dlrAllRegionsProjectiveSpec_globalUpperEnvelope_localGamble_eq_upper_of_marginal_eq
      M toPrecise hMarginal Λ X]

/-- Closed finite-region DLR strict width is realized by actual all-regions
projective-limit completions under an exact marginal adapter.

This is the all-regions companion to the finite-region endpoint theorem: the
local closedness hypothesis supplies lower/upper DLR endpoint witnesses, and
exact local lifting transports those witnesses into the global projective
limit. -/
theorem dlrAllRegionsProjectiveSpec_projectiveLimit_exists_endpointPairReadout_localGamble_of_marginal_eq_finiteEvaluationClosed_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype (LocalAssignment Atom Λ)]
    [DecidableEq (LocalAssignment Atom Λ)]
    (hClosed : @IsClosed
      (PrecisePrevision (LocalAssignment Atom Λ))
      (PrecisePrevision.FiniteWeights.finiteEvaluationTopology
        (Ω := LocalAssignment Atom Λ))
      (dlrRegionCredalSet M Λ))
    (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : PrecisePrevision (InfiniteWorld Atom),
      Plo ∈ (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet ∧
      ∃ Phi : PrecisePrevision (InfiniteWorld Atom),
        Phi ∈ (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet ∧
        Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          (dlrAllRegionsProjectiveSpec M).globalNaturalExtension
            ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ∧
        Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
            ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ∧
        Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) <
          Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ∧
        (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
            ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) -
            Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ∧
        (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
            ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          1 - (Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) -
            Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) ∧
        (dlrAllRegionsProjectiveSpec M).globalEnvelopeMidpoint
            ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          (Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) +
            Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) / 2 := by
  set S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M with hSdef
  haveI : Fintype (S.cylinders.Local Λ) := by
    rw [hSdef]; exact inferInstanceAs (Fintype (LocalAssignment Atom Λ))
  haveI : Nonempty (S.cylinders.Local Λ) := by
    rw [hSdef]; exact inferInstanceAs (Nonempty (LocalAssignment Atom Λ))
  have hExact : S.localCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
      M toPrecise hMarginal Λ
  rcases
      dlrRegionCredalSet_exists_endpointPairReadout_localGamble_of_finiteEvaluationClosed_strictWidth
        M Λ hClosed X hWidth with
    ⟨Rlo, hRlo, Rhi, hRhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hRloS : Rlo ∈ S.localCredal Λ := by
    change Rlo ∈ dlrRegionCredalSet M Λ
    exact hRlo
  have hRhiS : Rhi ∈ S.localCredal Λ := by
    change Rhi ∈ dlrRegionCredalSet M Λ
    exact hRhi
  have hloS : Rlo X = S.localNaturalExtension Λ X := by
    change Rlo X = lowerEnvelope (dlrRegionCredalSet M Λ) X
    exact hlo.trans
      (lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower M Λ X).symm
  have hhiS : Rhi X = S.localUpperEnvelope Λ X := by
    change Rhi X = upperEnvelope (dlrRegionCredalSet M Λ) X
    exact hhi.trans
      (upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper M Λ X).symm
  have hWidthS :
      S.localEnvelopeWidth Λ X = Rhi X - Rlo X := by
    change credalEnvelopeWidth (dlrRegionCredalSet M Λ) X = Rhi X - Rlo X
    exact
      (credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width
        M Λ X).trans hWidthEq
  have hCompS :
      S.localEnvelopeWidthComplement Λ X = 1 - (Rhi X - Rlo X) := by
    change credalEnvelopeWidthComplement (dlrRegionCredalSet M Λ) X =
      1 - (Rhi X - Rlo X)
    exact
      (credalEnvelopeWidthComplement_dlrRegionCredalSet_localGamble_eq_complement
        M Λ X).trans hCompEq
  have hMidS :
      S.localEnvelopeMidpoint Λ X = (Rlo X + Rhi X) / 2 := by
    change credalEnvelopeMidpoint (dlrRegionCredalSet M Λ) X =
      (Rlo X + Rhi X) / 2
    exact
      (credalEnvelopeMidpoint_dlrRegionCredalSet_localGamble_eq_midpoint
        M Λ X).trans hMidEq
  simpa [S] using
    ProjectiveLocalCredalSpec.projectiveLimit_exists_endpointPairReadout_cylinder_of_localEndpointPairReadout_of_exact
      (S := S) (i := Λ) (X := X)
      (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
      (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
      hExact Rlo hRloS Rhi hRhiS hloS hhiS hlt hWidthS hCompS hMidS

/-- With an exact global prevision adapter, global determination of a finite-region
cylinder gamble is exactly DLR local-gamble determination. -/
theorem dlrAllRegionsProjectiveSpec_determinesGlobalGamble_localGamble_iff_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).determinesGlobalGamble
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ↔
      dlrLocalGambleDetermined M Λ X := by
  rw [
    ProjectiveLocalCredalSpec.determinesGlobalGamble_cylinder_iff_localCredal_determines_of_exact
      (S := dlrAllRegionsProjectiveSpec M) Λ
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ) X]
  exact dlrRegionCredalSet_determines_localGamble_iff_localGambleDetermined
    M Λ X

/-- With an exact global prevision adapter, strict global width of a finite-region
cylinder gamble is exactly strict DLR local-gamble width. -/
theorem dlrAllRegionsProjectiveSpec_hasStrictGlobalWidth_localGamble_iff_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)) :
    (dlrAllRegionsProjectiveSpec M).hasStrictGlobalWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ↔
      dlrLocalGambleHasStrictWidth M Λ X := by
  rw [
    ProjectiveLocalCredalSpec.hasStrictGlobalWidth_cylinder_iff_localCredal_strictWidth_of_exact
      (S := dlrAllRegionsProjectiveSpec M) Λ
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ) X]
  exact dlrRegionCredalSet_hasStrictWidth_localGamble_iff_localGambleStrictWidth
    M Λ X

/-- DLR-determined arbitrary local gambles have zero global compatible-completion
width under an exact global prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidth_eq_zero_of_localGambleDetermined_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) = 0 := by
  exact
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_cylinder_eq_zero_of_localCredal_determines_of_exact
      (S := dlrAllRegionsProjectiveSpec M)
      (dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
        M toPrecise hMarginal)
      Λ X
      (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
      (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ)
      (dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
        M Λ X hDet)

/-- Strict DLR disagreement on an arbitrary local gamble gives a nontrivial global
lower/upper compatible-completion interval under an exact global prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_globalLowerUpperEnvelope_nontrivial_of_localGambleStrictWidth_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    (dlrAllRegionsProjectiveSpec M).globalNaturalExtension
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) <
      upperEnvelope (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  exact
    ProjectiveLocalCredalSpec.globalLowerUpperEnvelope_cylinder_nontrivial_of_localCredal_strictWidth_of_exact
      (S := dlrAllRegionsProjectiveSpec M)
      ⟨toPrecise μ,
        dlrAllRegionsProjectiveSpec_mem_of_marginal_eq M toPrecise hMarginal μ⟩
      Λ X
      (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
      (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ)
      (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
        M Λ X ⟨μ, ν, hlt⟩)

/-- Strict DLR disagreement on an arbitrary local gamble gives positive global
compatible-completion width under an exact global prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidth_pos_of_localGambleStrictWidth_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    0 < (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidth
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  exact
    ProjectiveLocalCredalSpec.globalEnvelopeWidth_cylinder_pos_of_localCredal_strictWidth_of_exact
      (S := dlrAllRegionsProjectiveSpec M)
      ⟨toPrecise μ,
        dlrAllRegionsProjectiveSpec_mem_of_marginal_eq M toPrecise hMarginal μ⟩
      Λ X
      (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
      (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ)
      (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
        M Λ X ⟨μ, ν, hlt⟩)

/-- DLR-determined arbitrary local gambles have maximal global width-complement
under an exact global prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_eq_one_of_localGambleDetermined_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hDet : dlrLocalGambleDetermined M Λ X) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) = 1 := by
  exact
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement_cylinder_eq_one_of_localCredal_determines_of_exact
      (S := dlrAllRegionsProjectiveSpec M)
      (dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
        M toPrecise hMarginal)
      Λ X
      (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
      (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ)
      (dlrRegionCredalSet_determines_localGamble_of_localGambleDetermined
        M Λ X hDet)

/-- Strict DLR disagreement on an arbitrary local gamble forces the global
width-complement coordinate below one under an exact global prevision adapter. -/
theorem dlrAllRegionsProjectiveSpec_globalEnvelopeWidthComplement_lt_one_of_localGambleStrictWidth_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    (dlrAllRegionsProjectiveSpec M).globalEnvelopeWidthComplement
        ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) < 1 := by
  rcases hWidth with ⟨μ, ν, hlt⟩
  exact
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement_cylinder_lt_one_of_localCredal_strictWidth_of_exact
      (S := dlrAllRegionsProjectiveSpec M)
      ⟨toPrecise μ,
        dlrAllRegionsProjectiveSpec_mem_of_marginal_eq M toPrecise hMarginal μ⟩
      Λ X
      (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
      (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddBelow M Λ X)
      (dlrAllRegionsProjectiveSpec_cylinderLocalGamble_bddAbove M Λ X)
      (dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
        M toPrecise hMarginal Λ)
      (dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
        M Λ X ⟨μ, ν, hlt⟩)

/-- Strict DLR disagreement on an arbitrary local gamble is realized by
Walley dominating completions of the all-regions global natural extension.

The global state space is infinite, so boundedness of the projective envelope
is kept as an explicit hypothesis.  This theorem is the DLR all-regions
specialization of the generic exact-cylinder endpoint readout: once a supplied
global prevision adapter has exact finite-region marginals, local DLR
strict-width becomes global natural-extension endpoint data on the
corresponding cylinder gamble. -/
theorem dlrAllRegionsProjectiveSpec_globalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_localGamble_of_marginal_eq
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hMarginal : ∀ (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrAllRegionsCylinderSystem Atom).marginalPrevision Λ (toPrecise μ) =
        dlrCompletionRegionPrevision M μ Λ)
    (hGlobalBddBelow : ∀ Y : Gamble (InfiniteWorld Atom),
      BddBelow ((fun P : PrecisePrevision (InfiniteWorld Atom) => P Y) ''
        (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet))
    (hGlobalBddAbove : ∀ Y : Gamble (InfiniteWorld Atom),
      BddAbove ((fun P : PrecisePrevision (InfiniteWorld Atom) => P Y) ''
        (dlrAllRegionsProjectiveSpec M).projectiveLimitCredalSet))
    (Λ : Region Atom)
    [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
    (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : PrecisePrevision (InfiniteWorld Atom),
      Plo ∈ dominatingPreciseCompletions
          ((dlrAllRegionsProjectiveSpec M).globalNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
              M toPrecise hMarginal)
            hGlobalBddBelow) ∧
      ∃ Phi : PrecisePrevision (InfiniteWorld Atom),
        Phi ∈ dominatingPreciseCompletions
          ((dlrAllRegionsProjectiveSpec M).globalNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
              M toPrecise hMarginal)
            hGlobalBddBelow) ∧
        Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
          dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) <
          Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ∧
        dlrLocalGambleEnvelopeWidth M Λ X =
          Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) -
            Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) ∧
        dlrLocalGambleEnvelopeWidthComplement M Λ X =
          1 - (Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) -
            Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) ∧
        dlrLocalGambleEnvelopeMidpoint M Λ X =
          (Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) +
            Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X)) / 2 := by
  let S : ProjectiveLocalCredalSpec (Region Atom) (InfiniteWorld Atom) :=
    dlrAllRegionsProjectiveSpec M
  have hGlobalNonempty : S.hasCompatibleCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCompletion_of_marginal_eq
      M toPrecise hMarginal
  have hExact : S.localCredalExactAt Λ :=
    dlrAllRegionsProjectiveSpec_localCredalExactAt_of_marginal_eq
      M toPrecise hMarginal Λ
  have hLocalWidth : credalSetHasStrictWidth (S.localCredal Λ) X := by
    change credalSetHasStrictWidth (dlrRegionCredalSet M Λ) X
    exact dlrRegionCredalSet_hasStrictWidth_localGamble_of_localGambleStrictWidth
      M Λ X hWidth
  rcases
      ProjectiveLocalCredalSpec.globalNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_cylinder_of_localCredal_strictWidth_of_exact
        (S := S) hGlobalNonempty hGlobalBddBelow hGlobalBddAbove Λ X
        (finite_credalRange_bddBelow (dlrRegionCredalSet M Λ) X)
        (finite_credalRange_bddAbove (dlrRegionCredalSet M Λ) X)
        hExact hLocalWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  have hloDLR :
      Plo ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
        dlrLocalGambleLowerEnvelope M Λ X := by
    change Plo (S.cylinders.cylinderGamble Λ X) =
      dlrLocalGambleLowerEnvelope M Λ X
    exact hlo.trans (lowerEnvelope_dlrRegionCredalSet_localGamble_eq_lower
      M Λ X)
  have hhiDLR :
      Phi ((dlrAllRegionsProjectiveSpec M).cylinders.cylinderGamble Λ X) =
        dlrLocalGambleUpperEnvelope M Λ X := by
    change Phi (S.cylinders.cylinderGamble Λ X) =
      dlrLocalGambleUpperEnvelope M Λ X
    exact hhi.trans (upperEnvelope_dlrRegionCredalSet_localGamble_eq_upper
      M Λ X)
  refine ⟨Plo, hPlo, Phi, hPhi, hloDLR, hhiDLR, hlt, ?_, ?_, ?_⟩
  · change dlrLocalGambleEnvelopeWidth M Λ X =
      Phi (S.cylinders.cylinderGamble Λ X) -
        Plo (S.cylinders.cylinderGamble Λ X)
    exact (credalEnvelopeWidth_dlrRegionCredalSet_localGamble_eq_width
      M Λ X).symm.trans hWidthEq
  · change dlrLocalGambleEnvelopeWidthComplement M Λ X =
      1 - (Phi (S.cylinders.cylinderGamble Λ X) -
        Plo (S.cylinders.cylinderGamble Λ X))
    exact (credalEnvelopeWidthComplement_dlrRegionCredalSet_localGamble_eq_complement
      M Λ X).symm.trans hCompEq
  · change dlrLocalGambleEnvelopeMidpoint M Λ X =
      (Plo (S.cylinders.cylinderGamble Λ X) +
        Phi (S.cylinders.cylinderGamble Λ X)) / 2
    exact (credalEnvelopeMidpoint_dlrRegionCredalSet_localGamble_eq_midpoint
      M Λ X).symm.trans hMidEq

/-! ## DLR as a projective credal specialization -/

/-- Adapter from σ-additive DLR completions into the shared projective credal
abstraction.  The map to precise previsions is explicit: this file does not
claim that every measure has already been turned into an expectation functional
on all gambles. -/
structure DLRProjectiveCredalSpecialization
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Window Global : Type*) [LE Window] where
  projectiveSpec : ProjectiveLocalCredalSpec Window Global
  toPreciseCompletion : DLRCompletion M → PrecisePrevision Global
  toPreciseCompletion_compatible :
    ∀ μ : DLRCompletion M,
      toPreciseCompletion μ ∈ projectiveSpec.projectiveLimitCredalSet

namespace DLRProjectiveCredalSpecialization

variable {Window Global : Type*} [LE Window]
variable {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}

/-- Any inhabited DLR completion family that has been adapted into the shared
projective credal interface yields a nonempty compatible global credal set. -/
theorem hasCompatibleCompletion
    [Nonempty (DLRCompletion M)]
    (D : DLRProjectiveCredalSpecialization M Window Global) :
    D.projectiveSpec.hasCompatibleCompletion := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact D.projectiveSpec.projectiveLimitCredalSet_nonempty_of_completion
    (P := D.toPreciseCompletion μ)
    (by
      intro i
      exact D.toPreciseCompletion_compatible μ i)

end DLRProjectiveCredalSpecialization

/-- A supplied DLR completion, together with a supplied interpretation of DLR
measures as precise previsions, induces a concrete singleton identity
projective credal specification.  The measure-to-prevision interpretation is
explicit because the full infinite weak*/expectation adapter is a separate
functional-analysis layer. -/
def dlrCompletionSingletonProjectiveSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    ProjectiveLocalCredalSpec PUnit (InfiniteWorld Atom) :=
  singletonIdentityProjectiveSpec (toPrecise μ)

theorem dlrCompletionSingletonProjectiveSpec_hasCompatibleCompletion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : DLRCompletion M)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    (dlrCompletionSingletonProjectiveSpec M μ toPrecise).hasCompatibleCompletion :=
  singletonIdentityProjectiveSpec_hasCompatibleCompletion (toPrecise μ)

/-- The credal set of all DLR completions after a supplied interpretation of
DLR measures as precise previsions on infinite-world gambles.  The
measure-to-prevision adapter is explicit because the full weak*/expectation
construction is a separate functional-analysis layer. -/
def dlrCompletionCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    CredalPrevisionSet (InfiniteWorld Atom) :=
  {P | ∃ μ : DLRCompletion M, P = toPrecise μ}

@[simp] theorem mem_dlrCompletionCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (μ : DLRCompletion M) :
    toPrecise μ ∈ dlrCompletionCredalSet M toPrecise :=
  ⟨μ, rfl⟩

/-- If at least one DLR completion exists, every supplied DLR-to-raw-prevision
adapter has a nonempty raw credal image. -/
theorem dlrCompletionCredalSet_nonempty
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    (dlrCompletionCredalSet M toPrecise).Nonempty := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ⟩

/-- If a supplied raw DLR precise-prevision adapter restricts to the already
constructed σ-additive bounded-measurable DLR prevision, then restricting its
raw credal image gives exactly the bounded-measurable DLR carrier.

This is the explicit seam between the finite-additive Walley/projective layer
and the bounded-measurable DLR layer. -/
theorem dlrCompletionCredalSet_restrictBoundedMeasurable_eq_dlrCompletionBoundedMeasurableCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ) :
    (dlrCompletionCredalSet M toPrecise).restrictBoundedMeasurable =
      dlrCompletionBoundedMeasurableCredalSet M := by
  ext P
  constructor
  · rintro ⟨Praw, hPraw, hPrawEq⟩
    rcases hPraw with ⟨μ, rfl⟩
    refine ⟨μ, ?_⟩
    rw [← hPrawEq, hRestrict μ]
  · rintro ⟨μ, hP⟩
    refine ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ, ?_⟩
    rw [hRestrict μ]
    exact hP.symm

/-- Under a restriction-correct raw DLR adapter, the raw finite-additive lower
envelope on a finite cylinder agrees with the existing finite-region DLR lower
envelope. -/
theorem lowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower_of_restrictBoundedMeasurable
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    lowerEnvelope (dlrCompletionCredalSet M toPrecise)
        (dlrCylinderBoundedMeasurableGamble Λ X).toGamble =
      dlrLocalGambleLowerEnvelope M Λ X := by
  rw [← boundedMeasurableLowerEnvelope_restrictBoundedMeasurable_eq_lowerEnvelope
      (dlrCompletionCredalSet M toPrecise)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    dlrCompletionCredalSet_restrictBoundedMeasurable_eq_dlrCompletionBoundedMeasurableCredalSet
      M toPrecise hRestrict,
    boundedMeasurableLowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower]

/-- Under a restriction-correct raw DLR adapter, the raw finite-additive upper
envelope on a finite cylinder agrees with the existing finite-region DLR upper
envelope. -/
theorem upperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper_of_restrictBoundedMeasurable
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    upperEnvelope (dlrCompletionCredalSet M toPrecise)
        (dlrCylinderBoundedMeasurableGamble Λ X).toGamble =
      dlrLocalGambleUpperEnvelope M Λ X := by
  rw [← boundedMeasurableUpperEnvelope_restrictBoundedMeasurable_eq_upperEnvelope
      (dlrCompletionCredalSet M toPrecise)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    dlrCompletionCredalSet_restrictBoundedMeasurable_eq_dlrCompletionBoundedMeasurableCredalSet
      M toPrecise hRestrict,
    boundedMeasurableUpperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper]

/-- Under a restriction-correct raw DLR adapter, the raw finite-additive
envelope width on a finite cylinder agrees with the existing finite-region DLR
width coordinate. -/
theorem credalEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth_of_restrictBoundedMeasurable
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalEnvelopeWidth (dlrCompletionCredalSet M toPrecise)
        (dlrCylinderBoundedMeasurableGamble Λ X).toGamble =
      dlrLocalGambleEnvelopeWidth M Λ X := by
  rw [← boundedMeasurableEnvelopeWidth_restrictBoundedMeasurable_eq_credalEnvelopeWidth
      (dlrCompletionCredalSet M toPrecise)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    dlrCompletionCredalSet_restrictBoundedMeasurable_eq_dlrCompletionBoundedMeasurableCredalSet
      M toPrecise hRestrict,
    boundedMeasurableEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth]

/-- Under a restriction-correct raw DLR adapter, the raw finite-additive
width-complement coordinate on a finite cylinder agrees with the finite-region
DLR confidence-like coordinate. -/
theorem credalEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement_of_restrictBoundedMeasurable
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalEnvelopeWidthComplement (dlrCompletionCredalSet M toPrecise)
        (dlrCylinderBoundedMeasurableGamble Λ X).toGamble =
      dlrLocalGambleEnvelopeWidthComplement M Λ X := by
  rw [← boundedMeasurableEnvelopeWidthComplement_restrictBoundedMeasurable_eq_credalEnvelopeWidthComplement
      (dlrCompletionCredalSet M toPrecise)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    dlrCompletionCredalSet_restrictBoundedMeasurable_eq_dlrCompletionBoundedMeasurableCredalSet
      M toPrecise hRestrict,
    boundedMeasurableEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement]

/-- Under a restriction-correct raw DLR adapter, the raw finite-additive
midpoint coordinate on a finite cylinder agrees with the finite-region DLR
strength-like coordinate. -/
theorem credalEnvelopeMidpoint_dlrCompletionCredalSet_cylinder_eq_localGambleMidpoint_of_restrictBoundedMeasurable
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ)) :
    credalEnvelopeMidpoint (dlrCompletionCredalSet M toPrecise)
        (dlrCylinderBoundedMeasurableGamble Λ X).toGamble =
      dlrLocalGambleEnvelopeMidpoint M Λ X := by
  rw [← boundedMeasurableEnvelopeMidpoint_restrictBoundedMeasurable_eq_credalEnvelopeMidpoint
      (dlrCompletionCredalSet M toPrecise)
      (dlrCylinderBoundedMeasurableGamble Λ X),
    dlrCompletionCredalSet_restrictBoundedMeasurable_eq_dlrCompletionBoundedMeasurableCredalSet
      M toPrecise hRestrict,
    boundedMeasurableEnvelopeMidpoint_dlrCompletionCredalSet_cylinder_eq_localGambleMidpoint]

/-- Local DLR strict width, together with a restriction-correct raw
DLR-to-prevision adapter, produces Walley dominating endpoint completions for
the bounded-measurable natural extension generated by the raw DLR credal image.

This theorem composes the shared raw-to-bounded Walley bridge with the concrete
DLR finite-cylinder readout, so downstream PLN code can consume the endpoint
witnesses without duplicating the restriction/compactification argument. -/
theorem dlrCompletionCredalSet_restrictBoundedMeasurable_exists_dominatingStrictEndpointPairReadout_cylinder_of_localGambleStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (hRestrict : ∀ μ : DLRCompletion M,
      (toPrecise μ).restrictBoundedMeasurable =
        dlrCompletionBoundedMeasurablePrevision M μ)
    (Λ : Region Atom) (X : Gamble (LocalAssignment Atom Λ))
    (hWidth : dlrLocalGambleHasStrictWidth M Λ X) :
    ∃ Plo : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
      Plo ∈ boundedMeasurableDominatingPreciseCompletions
          (boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionCredalSet M toPrecise).restrictBoundedMeasurable
            (CredalPrevisionSet.restrictBoundedMeasurable_nonempty
              (dlrCompletionCredalSet_nonempty M toPrecise))) ∧
      ∃ Phi : BoundedMeasurablePrecisePrevision (InfiniteWorld Atom),
        Phi ∈ boundedMeasurableDominatingPreciseCompletions
            (boundedMeasurableNaturalExtensionPrevision
              (dlrCompletionCredalSet M toPrecise).restrictBoundedMeasurable
              (CredalPrevisionSet.restrictBoundedMeasurable_nonempty
                (dlrCompletionCredalSet_nonempty M toPrecise))) ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleLowerEnvelope M Λ X ∧
        Phi (dlrCylinderBoundedMeasurableGamble Λ X) =
          dlrLocalGambleUpperEnvelope M Λ X ∧
        Plo (dlrCylinderBoundedMeasurableGamble Λ X) <
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) ∧
        dlrLocalGambleEnvelopeWidth M Λ X =
          Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
            Plo (dlrCylinderBoundedMeasurableGamble Λ X) ∧
        dlrLocalGambleEnvelopeWidthComplement M Λ X =
          1 -
            (Phi (dlrCylinderBoundedMeasurableGamble Λ X) -
              Plo (dlrCylinderBoundedMeasurableGamble Λ X)) ∧
        dlrLocalGambleEnvelopeMidpoint M Λ X =
          (Plo (dlrCylinderBoundedMeasurableGamble Λ X) +
            Phi (dlrCylinderBoundedMeasurableGamble Λ X)) / 2 := by
  let Z : BoundedMeasurableGamble (InfiniteWorld Atom) :=
    dlrCylinderBoundedMeasurableGamble Λ X
  have hRawWidth :
      credalSetHasStrictWidth (dlrCompletionCredalSet M toPrecise)
        Z.toGamble := by
    rcases hWidth with ⟨μ, ν, hlt⟩
    refine ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ,
      toPrecise ν, mem_dlrCompletionCredalSet M toPrecise ν, ?_⟩
    have hμRestrict :=
      congrArg (fun P : BoundedMeasurablePrecisePrevision
        (InfiniteWorld Atom) => P Z) (hRestrict μ)
    have hνRestrict :=
      congrArg (fun P : BoundedMeasurablePrecisePrevision
        (InfiniteWorld Atom) => P Z) (hRestrict ν)
    have hμ :
        toPrecise μ Z.toGamble =
          dlrCompletionRegionPrevision M μ Λ X := by
      calc
        toPrecise μ Z.toGamble =
            dlrCompletionBoundedMeasurablePrevision M μ Z := by
          simpa [PrecisePrevision.restrictBoundedMeasurable_apply] using
            hμRestrict
        _ = dlrCompletionRegionPrevision M μ Λ X := by
          dsimp [Z]
          exact dlrCompletionBoundedCylinderPrevision_eq_regionPrevision
            M μ Λ X
    have hν :
        toPrecise ν Z.toGamble =
          dlrCompletionRegionPrevision M ν Λ X := by
      calc
        toPrecise ν Z.toGamble =
            dlrCompletionBoundedMeasurablePrevision M ν Z := by
          simpa [PrecisePrevision.restrictBoundedMeasurable_apply] using
            hνRestrict
        _ = dlrCompletionRegionPrevision M ν Λ X := by
          dsimp [Z]
          exact dlrCompletionBoundedCylinderPrevision_eq_regionPrevision
            M ν Λ X
    rw [hμ, hν]
    exact hlt
  rcases
      boundedMeasurableNaturalExtensionPrevision_exists_dominatingStrictEndpointPairReadout_restrictBoundedMeasurable_of_strictWidth
        (dlrCompletionCredalSet M toPrecise)
        (dlrCompletionCredalSet_nonempty M toPrecise) Z hRawWidth with
    ⟨Plo, hPlo, Phi, hPhi, hlo, hhi, hlt, hWidthEq, hCompEq, hMidEq⟩
  refine ⟨Plo, hPlo, Phi, hPhi, ?_, ?_, hlt, ?_, ?_, ?_⟩
  · dsimp [Z] at hlo ⊢
    rw [hlo,
      lowerEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleLower_of_restrictBoundedMeasurable
        M toPrecise hRestrict Λ X]
  · dsimp [Z] at hhi ⊢
    rw [hhi,
      upperEnvelope_dlrCompletionCredalSet_cylinder_eq_localGambleUpper_of_restrictBoundedMeasurable
        M toPrecise hRestrict Λ X]
  · dsimp [Z] at hWidthEq ⊢
    rw [
      credalEnvelopeWidth_dlrCompletionCredalSet_cylinder_eq_localGambleWidth_of_restrictBoundedMeasurable
        M toPrecise hRestrict Λ X] at hWidthEq
    exact hWidthEq
  · dsimp [Z] at hCompEq ⊢
    rw [
      credalEnvelopeWidthComplement_dlrCompletionCredalSet_cylinder_eq_localGambleComplement_of_restrictBoundedMeasurable
        M toPrecise hRestrict Λ X] at hCompEq
    exact hCompEq
  · dsimp [Z] at hMidEq ⊢
    rw [
      credalEnvelopeMidpoint_dlrCompletionCredalSet_cylinder_eq_localGambleMidpoint_of_restrictBoundedMeasurable
        M toPrecise hRestrict Λ X] at hMidEq
    exact hMidEq

/-- The DLR completion credal set as an identity-window projective local credal
specification. -/
def dlrCompletionIdentityProjectiveSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    ProjectiveLocalCredalSpec PUnit (InfiniteWorld Atom) :=
  identityCredalProjectiveSpec (dlrCompletionCredalSet M toPrecise)

@[simp] theorem dlrCompletionIdentityProjectiveSpec_projectiveLimitCredalSet
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    (dlrCompletionIdentityProjectiveSpec M toPrecise).projectiveLimitCredalSet =
      dlrCompletionCredalSet M toPrecise := by
  simp [dlrCompletionIdentityProjectiveSpec]

theorem dlrCompletionIdentityProjectiveSpec_hasCompatibleCompletion_of_completion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (μ : DLRCompletion M) :
    (dlrCompletionIdentityProjectiveSpec M toPrecise).hasCompatibleCompletion := by
  exact identityCredalProjectiveSpec_hasCompatibleCompletion_of_mem
    (C := dlrCompletionCredalSet M toPrecise)
    (P := toPrecise μ)
    (mem_dlrCompletionCredalSet M toPrecise μ)

theorem dlrCompletionIdentityProjectiveSpec_hasCompatibleCompletion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)) :
    (dlrCompletionIdentityProjectiveSpec M toPrecise).hasCompatibleCompletion := by
  obtain ⟨μ⟩ := (inferInstance : Nonempty (DLRCompletion M))
  exact dlrCompletionIdentityProjectiveSpec_hasCompatibleCompletion_of_completion
    M toPrecise μ

/-- DLR query determinacy transfers to projective credal determinacy for any
global gamble whose supplied precise-prevision expectations coincide with the
DLR query probabilities. -/
theorem dlrCompletionIdentityProjectiveSpec_determinesGlobalGamble_of_queryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom)
    (X : Gamble (InfiniteWorld Atom))
    (hEval : ∀ μ : DLRCompletion M,
      toPrecise μ X = dlrCompletionQueryProb M q μ)
    (hDet : dlrQueryDetermined M q) :
    (dlrCompletionIdentityProjectiveSpec M toPrecise).determinesGlobalGamble X := by
  rw [dlrCompletionIdentityProjectiveSpec,
    identityCredalProjectiveSpec_determinesGlobalGamble_iff]
  intro P hP Q hQ
  rcases hP with ⟨μ, rfl⟩
  rcases hQ with ⟨ν, rfl⟩
  rw [hEval μ, hEval ν, hDet μ ν]

/-- DLR strict query width transfers to strict projective credal width for any
global gamble whose supplied precise-prevision expectations coincide with the
DLR query probabilities. -/
theorem dlrCompletionIdentityProjectiveSpec_hasStrictGlobalWidth_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom)
    (X : Gamble (InfiniteWorld Atom))
    (hEval : ∀ μ : DLRCompletion M,
      toPrecise μ X = dlrCompletionQueryProb M q μ)
    (hWidth : dlrQueryHasStrictWidth M q) :
    (dlrCompletionIdentityProjectiveSpec M toPrecise).hasStrictGlobalWidth X := by
  rw [dlrCompletionIdentityProjectiveSpec,
    identityCredalProjectiveSpec_hasStrictGlobalWidth_iff]
  rcases hWidth with ⟨μ, ν, hlt⟩
  refine ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ,
    toPrecise ν, mem_dlrCompletionCredalSet M toPrecise ν, ?_⟩
  rw [hEval μ, hEval ν]
  exact hlt

/-- The lower/upper envelope over the DLR completion credal set is nontrivial
whenever a DLR query has strict width and the chosen gamble represents that
query under the supplied prevision adapter. -/
theorem dlrCompletionCredalSet_lowerUpperEnvelope_nontrivial_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom)
    (X : Gamble (InfiniteWorld Atom))
    (hBddBelow : BddBelow ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P X) '' dlrCompletionCredalSet M toPrecise))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P X) '' dlrCompletionCredalSet M toPrecise))
    (hEval : ∀ μ : DLRCompletion M,
      toPrecise μ X = dlrCompletionQueryProb M q μ)
    (hWidth : dlrQueryHasStrictWidth M q) :
    lowerEnvelope (dlrCompletionCredalSet M toPrecise) X <
      upperEnvelope (dlrCompletionCredalSet M toPrecise) X := by
  apply lower_upperEnvelope_nontrivial_of_strictWidth
    (C := dlrCompletionCredalSet M toPrecise) (X := X)
    hBddBelow hBddAbove
  rcases hWidth with ⟨μ, ν, hlt⟩
  refine ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ,
    toPrecise ν, mem_dlrCompletionCredalSet M toPrecise ν, ?_⟩
  rw [hEval μ, hEval ν]
  exact hlt

/-- The same DLR strict-width transfer expressed as positive envelope width of
the DLR completion credal set. -/
theorem dlrCompletionCredalSet_envelopeWidth_pos_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom)
    (X : Gamble (InfiniteWorld Atom))
    (hBddBelow : BddBelow ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P X) '' dlrCompletionCredalSet M toPrecise))
    (hBddAbove : BddAbove ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P X) '' dlrCompletionCredalSet M toPrecise))
    (hEval : ∀ μ : DLRCompletion M,
      toPrecise μ X = dlrCompletionQueryProb M q μ)
    (hWidth : dlrQueryHasStrictWidth M q) :
    0 < credalEnvelopeWidth (dlrCompletionCredalSet M toPrecise) X := by
  apply credalEnvelopeWidth_pos_of_strictWidth
    (C := dlrCompletionCredalSet M toPrecise) (X := X)
    hBddBelow hBddAbove
  rcases hWidth with ⟨μ, ν, hlt⟩
  refine ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ,
    toPrecise ν, mem_dlrCompletionCredalSet M toPrecise ν, ?_⟩
  rw [hEval μ, hEval ν]
  exact hlt

/-- Any DLR-completion credal set evaluates a query-indicator gamble in a
bounded interval.  This discharges the lower-envelope boundedness side
condition for query indicators without invoking the full weak* theory. -/
theorem dlrCompletionCredalSet_queryIndicator_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom) :
    BddBelow ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P (infiniteQueryIndicatorGamble q)) '' dlrCompletionCredalSet M toPrecise) := by
  refine ⟨0, ?_⟩
  rintro x ⟨P, _hP, rfl⟩
  exact precisePrevision_infiniteQueryIndicatorGamble_nonneg P q

/-- Any DLR-completion credal set evaluates a query-indicator gamble at most
one.  This discharges the upper-envelope boundedness side condition for query
indicators without invoking the full weak* theory. -/
theorem dlrCompletionCredalSet_queryIndicator_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom) :
    BddAbove ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P (infiniteQueryIndicatorGamble q)) '' dlrCompletionCredalSet M toPrecise) := by
  refine ⟨1, ?_⟩
  rintro x ⟨P, _hP, rfl⟩
  exact precisePrevision_infiniteQueryIndicatorGamble_le_one P q

/-- If an adapter evaluates query indicators as DLR query probabilities, the
query-indicator value set of its credal image is exactly the scalar range of
DLR query probabilities. -/
theorem dlrCompletionCredalSet_queryIndicator_value_image_eq_range
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
    (q : ConstraintQuery Atom)
    (hEval : ∀ μ : DLRCompletion M,
      toPrecise μ (infiniteQueryIndicatorGamble q) =
        dlrCompletionQueryProb M q μ) :
    ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
      P (infiniteQueryIndicatorGamble q)) '' dlrCompletionCredalSet M toPrecise) =
      Set.range (dlrCompletionQueryProb M q) := by
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    rcases hP with ⟨μ, rfl⟩
    exact ⟨μ, (hEval μ).symm⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨toPrecise μ, mem_dlrCompletionCredalSet M toPrecise μ, hEval μ⟩

/-- A query-indicator prevision adapter is the exact finite-query part of the
future full measure-to-prevision construction: it interprets each DLR
completion as a precise prevision, and it proves that query indicators evaluate
to the DLR query probabilities.

This is intentionally weaker than a full weak*/expectation adapter for all
bounded measurable gambles. -/
structure DLRQueryIndicatorPrevisionAdapter
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)
  queryIndicatorEval :
    ∀ (μ : DLRCompletion M) (q : ConstraintQuery Atom),
      toPrecise μ (infiniteQueryIndicatorGamble q) =
        dlrCompletionQueryProb M q μ

namespace DLRQueryIndicatorPrevisionAdapter

/-- The projective identity specification induced by a query-indicator adapter. -/
def identityProjectiveSpec
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M) :
    ProjectiveLocalCredalSpec PUnit (InfiniteWorld Atom) :=
  dlrCompletionIdentityProjectiveSpec M A.toPrecise

theorem determinesQueryIndicator_of_queryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom)
    (hDet : dlrQueryDetermined M q) :
    (A.identityProjectiveSpec M).determinesGlobalGamble
      (infiniteQueryIndicatorGamble q) :=
  dlrCompletionIdentityProjectiveSpec_determinesGlobalGamble_of_queryDetermined
    M A.toPrecise q (infiniteQueryIndicatorGamble q)
    (fun μ => A.queryIndicatorEval μ q) hDet

theorem hasStrictQueryIndicatorWidth_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    (A.identityProjectiveSpec M).hasStrictGlobalWidth
      (infiniteQueryIndicatorGamble q) :=
  dlrCompletionIdentityProjectiveSpec_hasStrictGlobalWidth_of_queryStrictWidth
    M A.toPrecise q (infiniteQueryIndicatorGamble q)
    (fun μ => A.queryIndicatorEval μ q) hWidth

theorem lowerUpperEnvelope_nontrivial_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    lowerEnvelope (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) <
      upperEnvelope (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) :=
  dlrCompletionCredalSet_lowerUpperEnvelope_nontrivial_of_queryStrictWidth
    M A.toPrecise q (infiniteQueryIndicatorGamble q)
    (dlrCompletionCredalSet_queryIndicator_bddBelow M A.toPrecise q)
    (dlrCompletionCredalSet_queryIndicator_bddAbove M A.toPrecise q)
    (fun μ => A.queryIndicatorEval μ q) hWidth

theorem envelopeWidth_pos_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    0 < credalEnvelopeWidth (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) :=
  dlrCompletionCredalSet_envelopeWidth_pos_of_queryStrictWidth
    M A.toPrecise q (infiniteQueryIndicatorGamble q)
    (dlrCompletionCredalSet_queryIndicator_bddBelow M A.toPrecise q)
    (dlrCompletionCredalSet_queryIndicator_bddAbove M A.toPrecise q)
    (fun μ => A.queryIndicatorEval μ q) hWidth

end DLRQueryIndicatorPrevisionAdapter

/-- The Walley-style lower envelope over all DLR completions. -/
noncomputable def infiniteMLNLowerQueryEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : ℝ :=
  sInf (Set.range (dlrCompletionQueryProb M q))

/-- The dual upper envelope over all DLR completions. -/
noncomputable def infiniteMLNUpperQueryEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : ℝ :=
  sSup (Set.range (dlrCompletionQueryProb M q))

/-- The width of the lower/upper DLR query envelope. -/
noncomputable def infiniteMLNQueryEnvelopeWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : ℝ :=
  infiniteMLNUpperQueryEnvelope M q - infiniteMLNLowerQueryEnvelope M q

/-- Width-complement of the DLR lower/upper query envelope.  This is the
Walley-style confidence coordinate associated to the scalar DLR query
projection. -/
noncomputable def infiniteMLNQueryEnvelopeWidthComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : ℝ :=
  1 - infiniteMLNQueryEnvelopeWidth M q

/-- Midpoint of the DLR lower/upper query envelope.  This is the scalar
strength coordinate associated to the DLR query projection. -/
noncomputable def infiniteMLNQueryEnvelopeMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) : ℝ :=
  (infiniteMLNLowerQueryEnvelope M q + infiniteMLNUpperQueryEnvelope M q) / 2

namespace DLRQueryIndicatorPrevisionAdapter

/-- The adapter's lower envelope on the global query-indicator gamble is
exactly the scalar DLR lower query envelope. -/
theorem lowerEnvelope_queryIndicator_eq_infiniteMLNLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    lowerEnvelope (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNLowerQueryEnvelope M q := by
  unfold lowerEnvelope infiniteMLNLowerQueryEnvelope
  rw [dlrCompletionCredalSet_queryIndicator_value_image_eq_range
    M A.toPrecise q (fun μ => A.queryIndicatorEval μ q)]

/-- The adapter's upper envelope on the global query-indicator gamble is
exactly the scalar DLR upper query envelope. -/
theorem upperEnvelope_queryIndicator_eq_infiniteMLNUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    upperEnvelope (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNUpperQueryEnvelope M q := by
  unfold upperEnvelope infiniteMLNUpperQueryEnvelope
  rw [dlrCompletionCredalSet_queryIndicator_value_image_eq_range
    M A.toPrecise q (fun μ => A.queryIndicatorEval μ q)]

/-- The adapter's credal width on the global query-indicator gamble is exactly
the scalar DLR query-envelope width. -/
theorem envelopeWidth_queryIndicator_eq_infiniteMLNWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    credalEnvelopeWidth (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNQueryEnvelopeWidth M q := by
  unfold credalEnvelopeWidth infiniteMLNQueryEnvelopeWidth
  rw [lowerEnvelope_queryIndicator_eq_infiniteMLNLower,
    upperEnvelope_queryIndicator_eq_infiniteMLNUpper]

/-- The adapter's width-complement on the global query-indicator gamble is
exactly the scalar DLR query-envelope width-complement. -/
theorem envelopeWidthComplement_queryIndicator_eq_infiniteMLNComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    credalEnvelopeWidthComplement (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNQueryEnvelopeWidthComplement M q := by
  unfold credalEnvelopeWidthComplement infiniteMLNQueryEnvelopeWidthComplement
  rw [envelopeWidth_queryIndicator_eq_infiniteMLNWidth]

/-- The adapter's midpoint on the global query-indicator gamble is exactly the
scalar DLR query-envelope midpoint. -/
theorem envelopeMidpoint_queryIndicator_eq_infiniteMLNMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    credalEnvelopeMidpoint (dlrCompletionCredalSet M A.toPrecise)
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNQueryEnvelopeMidpoint M q := by
  unfold credalEnvelopeMidpoint infiniteMLNQueryEnvelopeMidpoint
  rw [lowerEnvelope_queryIndicator_eq_infiniteMLNLower,
    upperEnvelope_queryIndicator_eq_infiniteMLNUpper]

/-- The identity projective spec induced by the adapter has global natural
extension equal to the scalar DLR lower query envelope. -/
theorem globalNaturalExtension_queryIndicator_eq_infiniteMLNLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    (A.identityProjectiveSpec M).globalNaturalExtension
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNLowerQueryEnvelope M q := by
  simp [identityProjectiveSpec, dlrCompletionIdentityProjectiveSpec,
    ProjectiveLocalCredalSpec.globalNaturalExtension,
    lowerEnvelope_queryIndicator_eq_infiniteMLNLower]

/-- The identity projective spec induced by the adapter has upper envelope
equal to the scalar DLR upper query envelope. -/
theorem globalUpperEnvelope_queryIndicator_eq_infiniteMLNUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    upperEnvelope (A.identityProjectiveSpec M).projectiveLimitCredalSet
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNUpperQueryEnvelope M q := by
  simp [identityProjectiveSpec, dlrCompletionIdentityProjectiveSpec,
    upperEnvelope_queryIndicator_eq_infiniteMLNUpper]

/-- The identity projective spec induced by the adapter has global envelope
width equal to the scalar DLR query-envelope width. -/
theorem globalEnvelopeWidth_queryIndicator_eq_infiniteMLNWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    (A.identityProjectiveSpec M).globalEnvelopeWidth
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNQueryEnvelopeWidth M q := by
  simp [identityProjectiveSpec, dlrCompletionIdentityProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    envelopeWidth_queryIndicator_eq_infiniteMLNWidth]

/-- The identity projective spec induced by the adapter has global
width-complement equal to the scalar DLR query-envelope width-complement. -/
theorem globalEnvelopeWidthComplement_queryIndicator_eq_infiniteMLNComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    (A.identityProjectiveSpec M).globalEnvelopeWidthComplement
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNQueryEnvelopeWidthComplement M q := by
  simp [identityProjectiveSpec, dlrCompletionIdentityProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement,
    envelopeWidthComplement_queryIndicator_eq_infiniteMLNComplement]

/-- The identity projective spec induced by the adapter has global midpoint
equal to the scalar DLR query-envelope midpoint. -/
theorem globalEnvelopeMidpoint_queryIndicator_eq_infiniteMLNMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (A : DLRQueryIndicatorPrevisionAdapter M)
    (q : ConstraintQuery Atom) :
    (A.identityProjectiveSpec M).globalEnvelopeMidpoint
        (infiniteQueryIndicatorGamble q) =
      infiniteMLNQueryEnvelopeMidpoint M q := by
  simp [identityProjectiveSpec, dlrCompletionIdentityProjectiveSpec,
    ProjectiveLocalCredalSpec.globalEnvelopeMidpoint,
    envelopeMidpoint_queryIndicator_eq_infiniteMLNMidpoint]

end DLRQueryIndicatorPrevisionAdapter

/-- The lower envelope of the concrete binary query-outcome credal projection
is the DLR lower query envelope. -/
theorem lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    lowerEnvelope (dlrQueryOutcomeCredalSet M q)
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNLowerQueryEnvelope M q := by
  unfold lowerEnvelope infiniteMLNLowerQueryEnvelope
  rw [dlrQueryOutcomeCredalSet_true_atom_value_image_eq_range]

/-- The DLR lower query envelope is below every DLR completion's query
probability. -/
theorem infiniteMLNLowerQueryEnvelope_le_completionProb
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    infiniteMLNLowerQueryEnvelope M q ≤ dlrCompletionQueryProb M q μ := by
  rw [← lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower]
  have hle := dlrQueryOutcomeLowerEnvelope_le_completion M q μ
    (PrecisePrevision.FiniteWeights.atomGamble true)
  rw [dlrQueryOutcomePrevision_true_atom] at hle
  exact hle

/-- The DLR lower query envelope is the greatest scalar lower bound of all DLR
completion query probabilities. -/
theorem infiniteMLNLowerQueryEnvelope_greatest_lower_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) (r : ℝ)
    (hr : ∀ μ : DLRCompletion M, r ≤ dlrCompletionQueryProb M q μ) :
    r ≤ infiniteMLNLowerQueryEnvelope M q := by
  rw [← lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower]
  exact
    le_lowerEnvelope_of_forall_le (dlrQueryOutcomeCredalSet M q)
      (dlrQueryOutcomeCredalSet_nonempty M q)
      (PrecisePrevision.FiniteWeights.atomGamble true)
      (by
        intro P hP
        rcases hP with ⟨μ, rfl⟩
        rw [dlrQueryOutcomePrevision_true_atom]
        exact hr μ)

/-- The upper envelope of the concrete binary query-outcome credal projection
is the DLR upper query envelope. -/
theorem upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    upperEnvelope (dlrQueryOutcomeCredalSet M q)
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNUpperQueryEnvelope M q := by
  unfold upperEnvelope infiniteMLNUpperQueryEnvelope
  rw [dlrQueryOutcomeCredalSet_true_atom_value_image_eq_range]

/-- Every DLR completion's query probability is below the DLR upper query
envelope. -/
theorem dlrCompletionQueryProb_le_infiniteMLNUpperQueryEnvelope
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) :
    dlrCompletionQueryProb M q μ ≤ infiniteMLNUpperQueryEnvelope M q := by
  rw [← upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper]
  have hle := dlrQueryOutcomeCompletion_le_upperEnvelope M q μ
    (PrecisePrevision.FiniteWeights.atomGamble true)
  rw [dlrQueryOutcomePrevision_true_atom] at hle
  exact hle

/-- The DLR upper query envelope is the least scalar upper bound of all DLR
completion query probabilities. -/
theorem infiniteMLNUpperQueryEnvelope_least_upper_bound
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) (r : ℝ)
    (hr : ∀ μ : DLRCompletion M, dlrCompletionQueryProb M q μ ≤ r) :
    infiniteMLNUpperQueryEnvelope M q ≤ r := by
  rw [← upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper]
  exact
    upperEnvelope_le_of_forall_le (dlrQueryOutcomeCredalSet M q)
      (dlrQueryOutcomeCredalSet_nonempty M q)
      (PrecisePrevision.FiniteWeights.atomGamble true)
      (by
        intro P hP
        rcases hP with ⟨μ, rfl⟩
        rw [dlrQueryOutcomePrevision_true_atom]
        exact hr μ)

/-- The concrete binary query-outcome credal width is exactly the DLR query
envelope width. -/
theorem credalEnvelopeWidth_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    credalEnvelopeWidth (dlrQueryOutcomeCredalSet M q)
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNQueryEnvelopeWidth M q := by
  unfold credalEnvelopeWidth infiniteMLNQueryEnvelopeWidth
  rw [lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower,
    upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper]

/-- The concrete binary query-outcome credal width-complement is exactly the
DLR query-envelope width-complement. -/
theorem credalEnvelopeWidthComplement_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNComplement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    credalEnvelopeWidthComplement (dlrQueryOutcomeCredalSet M q)
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNQueryEnvelopeWidthComplement M q := by
  unfold credalEnvelopeWidthComplement infiniteMLNQueryEnvelopeWidthComplement
  rw [credalEnvelopeWidth_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNWidth]

/-- The concrete binary query-outcome credal midpoint is exactly the DLR
query-envelope midpoint. -/
theorem credalEnvelopeMidpoint_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNMidpoint
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    credalEnvelopeMidpoint (dlrQueryOutcomeCredalSet M q)
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNQueryEnvelopeMidpoint M q := by
  unfold credalEnvelopeMidpoint infiniteMLNQueryEnvelopeMidpoint
  rw [lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower,
    upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper]

/-- The one-window projective DLR query-outcome specification has global
natural extension equal to the DLR lower query envelope. -/
theorem dlrQueryOutcomeProjectiveSpec_globalNaturalExtension_true_atom_eq_infiniteMLNLower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeProjectiveSpec M q).globalNaturalExtension
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNLowerQueryEnvelope M q := by
  simp [ProjectiveLocalCredalSpec.globalNaturalExtension,
    lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower]

/-- The upper envelope of the one-window projective DLR query-outcome
specification is the DLR upper query envelope. -/
theorem dlrQueryOutcomeProjectiveSpec_upperEnvelope_true_atom_eq_infiniteMLNUpper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    upperEnvelope (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNUpperQueryEnvelope M q := by
  simp [upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper]

/-- The projective global envelope width of the DLR query-outcome
specification is exactly the DLR query-envelope width. -/
theorem dlrQueryOutcomeProjectiveSpec_globalEnvelopeWidth_true_atom_eq_infiniteMLNWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeProjectiveSpec M q).globalEnvelopeWidth
        (PrecisePrevision.FiniteWeights.atomGamble true) =
      infiniteMLNQueryEnvelopeWidth M q := by
  simp [ProjectiveLocalCredalSpec.globalEnvelopeWidth,
    credalEnvelopeWidth_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNWidth]

/-- DLR query-probability ranges are bounded below by `0`. -/
theorem dlrCompletionQueryProb_range_bddBelow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    BddBelow (Set.range (dlrCompletionQueryProb M q)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨μ, rfl⟩
  exact dlrCompletionQueryProb_nonneg M q μ

/-- DLR query-probability ranges are bounded above by `1`. -/
theorem dlrCompletionQueryProb_range_bddAbove
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) :
    BddAbove (Set.range (dlrCompletionQueryProb M q)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨μ, rfl⟩
  exact dlrCompletionQueryProb_le_one M q μ

/-- Dobrushin uniqueness says every DLR completion gives the same finite-query
probability. -/
theorem dlrCompletionQueryProb_eq_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) (μ ν : DLRCompletion M) :
    dlrCompletionQueryProb M q μ = dlrCompletionQueryProb M q ν := by
  unfold dlrCompletionQueryProb
  exact congrArg ENNReal.toReal
    (infiniteMLN_queryStrength_unique_of_uniform
      (Atom := Atom) (ClauseId := ClauseId) M hM μ.1 ν.1 μ.2 ν.2 q)

/-- Dobrushin uniqueness is precisely the query-determined case for every
finite MLN query. -/
theorem dlrQueryDetermined_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) :
    dlrQueryDetermined M q := by
  intro μ ν
  exact dlrCompletionQueryProb_eq_of_uniform M hM q μ ν

/-- Strict query width rules out DLR-determination. -/
theorem not_dlrQueryDetermined_of_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    ¬ dlrQueryDetermined M q := by
  intro hDet
  rcases hWidth with ⟨μ, ν, hμν⟩
  exact (ne_of_lt hμν) (hDet μ ν)

/-- If all DLR completions agree on a query, the lower and upper DLR envelopes
collapse to a point, provided the completion family is inhabited. -/
theorem infiniteMLN_queryEnvelope_precise_of_dlrQueryDetermined
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom)
    (hDet : dlrQueryDetermined M q) :
    infiniteMLNLowerQueryEnvelope M q =
      infiniteMLNUpperQueryEnvelope M q := by
  classical
  obtain ⟨μ₀⟩ := (inferInstance : Nonempty (DLRCompletion M))
  have hRange :
      Set.range (dlrCompletionQueryProb M q) =
        ({dlrCompletionQueryProb M q μ₀} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨μ, rfl⟩
      exact by
        rw [hDet μ μ₀]
        simp
    · intro hx
      have hx' : x = dlrCompletionQueryProb M q μ₀ := by simpa using hx
      exact ⟨μ₀, hx'.symm⟩
  unfold infiniteMLNLowerQueryEnvelope infiniteMLNUpperQueryEnvelope
  rw [hRange, csInf_singleton, csSup_singleton]

/-- Under Dobrushin uniqueness, the DLR credal envelope is precise for every
finite query, provided at least one DLR completion exists. -/
theorem infiniteMLN_queryEnvelope_precise_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) :
    infiniteMLNLowerQueryEnvelope M q =
      infiniteMLNUpperQueryEnvelope M q := by
  exact infiniteMLN_queryEnvelope_precise_of_dlrQueryDetermined M q
    (dlrQueryDetermined_of_uniform M hM q)

/-- If two DLR completions disagree on a query, the lower/upper query envelope
is nontrivial.  This is the formal "phase transition creates imprecision"
canary; boundedness is explicit rather than hidden. -/
theorem infiniteMLN_queryEnvelope_nontrivial_of_disagreement
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hBddBelow : BddBelow (Set.range (dlrCompletionQueryProb M q)))
    (hBddAbove : BddAbove (Set.range (dlrCompletionQueryProb M q)))
    (μ ν : DLRCompletion M)
    (hμν : dlrCompletionQueryProb M q μ <
      dlrCompletionQueryProb M q ν) :
    infiniteMLNLowerQueryEnvelope M q <
      infiniteMLNUpperQueryEnvelope M q := by
  unfold infiniteMLNLowerQueryEnvelope infiniteMLNUpperQueryEnvelope
  calc
    sInf (Set.range (dlrCompletionQueryProb M q))
        ≤ dlrCompletionQueryProb M q μ :=
          csInf_le hBddBelow ⟨μ, rfl⟩
    _ < dlrCompletionQueryProb M q ν := hμν
    _ ≤ sSup (Set.range (dlrCompletionQueryProb M q)) :=
          le_csSup hBddAbove ⟨ν, rfl⟩

/-- Strict DLR query-width is the reusable version of the phase-transition
canary: any two disagreeing completions force a nontrivial Walley envelope. -/
theorem infiniteMLN_queryEnvelope_nontrivial_of_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hBddBelow : BddBelow (Set.range (dlrCompletionQueryProb M q)))
    (hBddAbove : BddAbove (Set.range (dlrCompletionQueryProb M q)))
    (hWidth : dlrQueryHasStrictWidth M q) :
    infiniteMLNLowerQueryEnvelope M q <
      infiniteMLNUpperQueryEnvelope M q := by
  rcases hWidth with ⟨μ, ν, hμν⟩
  exact infiniteMLN_queryEnvelope_nontrivial_of_disagreement
    M q hBddBelow hBddAbove μ ν hμν

/-- Strict DLR query-width gives a nontrivial query envelope; boundedness is
automatic because DLR query probabilities lie in `[0,1]`. -/
theorem infiniteMLN_queryEnvelope_nontrivial_of_strictWidth_bounded
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    infiniteMLNLowerQueryEnvelope M q <
      infiniteMLNUpperQueryEnvelope M q :=
  infiniteMLN_queryEnvelope_nontrivial_of_strictWidth M q
    (dlrCompletionQueryProb_range_bddBelow M q)
    (dlrCompletionQueryProb_range_bddAbove M q)
    hWidth

/-- Strict DLR query-width gives positive DLR query-envelope width. -/
theorem infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    0 < infiniteMLNQueryEnvelopeWidth M q := by
  have hlt := infiniteMLN_queryEnvelope_nontrivial_of_strictWidth_bounded M q hWidth
  unfold infiniteMLNQueryEnvelopeWidth
  linarith

/-- Strict DLR query-width gives positive width in the concrete binary
query-outcome credal projection. -/
theorem dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    0 < credalEnvelopeWidth (dlrQueryOutcomeCredalSet M q)
        (PrecisePrevision.FiniteWeights.atomGamble true) := by
  rw [credalEnvelopeWidth_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNWidth]
  exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth M q hWidth

set_option linter.unusedSectionVars false in
/-- A countable projective family constructed by the infinite-MLN projective
limit theorem gives query probabilities by its finite-dimensional marginals.
This is the precise σ-additive face that the credal bridge envelops when
multiple completions are possible. -/
theorem projectiveLimitMeasure_queryEnvelope_value
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom,
      Measure (∀ i : I,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.globalMeasureMassSemantics
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure
        e P hP) Λ).queryProb q =
        P Λ (localConstraintSet Λ q) :=
  Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure_queryProb_eq_family
    (Atom := Atom) e P hP Λ q

/-- The existing projective-limit DLR theorem supplies an actual DLR completion
for the credal bridge whenever a limiting finite-dimensional family is obtained
as the pointwise limit of finite-volume stage marginals. -/
noncomputable def projectiveLimitDLRCompletion_of_stageMarginal_tendsto
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (ξ : BoundaryCondition Atom)
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom,
      Measure (∀ i : I,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (hconv : ∀ (I : Finset Atom) (S : Set (∀ i : I,
        Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i)),
        MeasurableSet S →
          Tendsto
            (fun n =>
              Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                E M.toStrictlyPositiveInfiniteGroundMLNSpec ξ n I S)
            atTop (nhds (P I S))) :
    DLRCompletion M := by
  let μ : Measure (InfiniteWorld Atom) :=
    Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure
      e P hP
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  refine ⟨⟨μ, inferInstance⟩, ?_⟩
  dsimp [μ]
  exact
    Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.RegionExhaustion.projectiveLimitMeasure_fixedRegionDLR_of_stageMarginal_tendsto
      (E := E) (M := M.toStrictlyPositiveInfiniteGroundMLNSpec) (ξ := ξ)
      e P hP hconv

/-! ## Profile surface -/

/-- Proof-carrying profile for the σ-additive infinite-MLN face of the
projective credal abstraction. -/
structure InfiniteMLNCredalBridgeProfile where
  queryEventMeasurable :
    ∀ {Atom : Type*} (q : ConstraintQuery Atom),
      MeasurableSet (infiniteQueryEvent q)
  dlrCompletionQueryProbIsEventMeasure :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M),
      dlrCompletionQueryProb M q μ =
        ENNReal.toReal
          ((μ.1 : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q))
  dlrCompletionQueryProbInUnit :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M),
      dlrCompletionQueryProb M q μ ∈ Set.Icc (0 : ℝ) 1
  queryOutcomePrevisionIsPrecise :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M),
      (dlrQueryOutcomePrevision M q μ).toLowerPrevision.isPrecise
  queryOutcomePrevisionTrueAtom :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M),
      dlrQueryOutcomePrevision M q μ
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        dlrCompletionQueryProb M q μ
  queryOutcomeCredalSetDeterminesOfQueryDetermined :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryDetermined M q →
        credalSetDetermines (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeCredalSetStrictWidthOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        credalSetHasStrictWidth (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeCredalSetNotDeterminesOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        ¬ credalSetDetermines (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeValueImageEqQueryRange :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      ((fun P : PrecisePrevision Bool =>
        P (PrecisePrevision.FiniteWeights.atomGamble true)) ''
          dlrQueryOutcomeCredalSet M q) =
        Set.range (dlrCompletionQueryProb M q)
  queryOutcomeLowerEnvelopeEqQueryLower :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      lowerEnvelope (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNLowerQueryEnvelope M q
  queryOutcomeLowerEnvelopeLeCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M) (X : Gamble Bool),
      lowerEnvelope (dlrQueryOutcomeCredalSet M q) X ≤
        dlrQueryOutcomePrevision M q μ X
  queryOutcomeLowerEnvelopeGreatestLowerBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom) (L : LowerPrevision Bool),
      (∀ μ : DLRCompletion M, ∀ X : Gamble Bool,
        L X ≤ dlrQueryOutcomePrevision M q μ X) →
      ∀ X : Gamble Bool,
        L X ≤ lowerEnvelope (dlrQueryOutcomeCredalSet M q) X
  queryLowerEnvelopeLeCompletionProb :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M),
      infiniteMLNLowerQueryEnvelope M q ≤ dlrCompletionQueryProb M q μ
  queryLowerEnvelopeGreatestLowerBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom) (r : ℝ),
      (∀ μ : DLRCompletion M, r ≤ dlrCompletionQueryProb M q μ) →
        r ≤ infiniteMLNLowerQueryEnvelope M q
  queryOutcomeUpperEnvelopeEqQueryUpper :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      upperEnvelope (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNUpperQueryEnvelope M q
  queryOutcomeCompletionLeUpperEnvelope :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M) (X : Gamble Bool),
      dlrQueryOutcomePrevision M q μ X ≤
        upperEnvelope (dlrQueryOutcomeCredalSet M q) X
  queryOutcomeUpperEnvelopeLeastUpperBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom) (U : UpperPrevision Bool),
      (∀ μ : DLRCompletion M, ∀ X : Gamble Bool,
        dlrQueryOutcomePrevision M q μ X ≤ U X) →
      ∀ X : Gamble Bool,
        upperEnvelope (dlrQueryOutcomeCredalSet M q) X ≤ U X
  queryCompletionProbLeUpperEnvelope :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom) (μ : DLRCompletion M),
      dlrCompletionQueryProb M q μ ≤ infiniteMLNUpperQueryEnvelope M q
  queryUpperEnvelopeLeastUpperBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom) (r : ℝ),
      (∀ μ : DLRCompletion M, dlrCompletionQueryProb M q μ ≤ r) →
        infiniteMLNUpperQueryEnvelope M q ≤ r
  queryOutcomeWidthEqQueryEnvelopeWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      credalEnvelopeWidth (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNQueryEnvelopeWidth M q
  queryEnvelopeNontrivialOfStrictWidthBounded :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        infiniteMLNLowerQueryEnvelope M q <
          infiniteMLNUpperQueryEnvelope M q
  queryEnvelopeWidthPositiveOfStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        0 < infiniteMLNQueryEnvelopeWidth M q
  queryOutcomeCredalSetWidthPositiveOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        0 < credalEnvelopeWidth (dlrQueryOutcomeCredalSet M q)
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeProjectiveSpecLimitSet :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet =
        dlrQueryOutcomeCredalSet M q
  queryOutcomeProjectiveSpecHasCompatibleCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeProjectiveSpec M q).hasCompatibleCompletion
  queryOutcomeProjectiveSpecDeterminesOfQueryDetermined :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryDetermined M q →
        (dlrQueryOutcomeProjectiveSpec M q).determinesGlobalGamble
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeProjectiveSpecStrictWidthOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        (dlrQueryOutcomeProjectiveSpec M q).hasStrictGlobalWidth
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeProjectiveSpecNotDeterminesOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        ¬ (dlrQueryOutcomeProjectiveSpec M q).determinesGlobalGamble
          (PrecisePrevision.FiniteWeights.atomGamble true)
  queryOutcomeProjectiveSpecLowerEqQueryLower :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeProjectiveSpec M q).globalNaturalExtension
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNLowerQueryEnvelope M q
  queryOutcomeProjectiveSpecUpperEqQueryUpper :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      upperEnvelope (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNUpperQueryEnvelope M q
  queryOutcomeProjectiveSpecWidthEqQueryEnvelopeWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeProjectiveSpec M q).globalEnvelopeWidth
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNQueryEnvelopeWidth M q
  queryIndicatorBounded :
    ∀ {Atom : Type*}
      (q : ConstraintQuery Atom) (ω : InfiniteWorld Atom),
      infiniteQueryIndicatorGamble q ω ∈ Set.Icc (0 : ℝ) 1
  queryIndicatorAdapterDeterminesOfQueryDetermined :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
      dlrQueryDetermined M q →
        (_A.identityProjectiveSpec M).determinesGlobalGamble
          (infiniteQueryIndicatorGamble q)
  queryIndicatorAdapterStrictWidthOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        (_A.identityProjectiveSpec M).hasStrictGlobalWidth
          (infiniteQueryIndicatorGamble q)
  queryIndicatorAdapterEnvelopeNontrivialOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        lowerEnvelope (dlrCompletionCredalSet M _A.toPrecise)
            (infiniteQueryIndicatorGamble q) <
          upperEnvelope (dlrCompletionCredalSet M _A.toPrecise)
            (infiniteQueryIndicatorGamble q)
  queryIndicatorAdapterWidthPositiveOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        0 < credalEnvelopeWidth (dlrCompletionCredalSet M _A.toPrecise)
          (infiniteQueryIndicatorGamble q)
  queryIndicatorAdapterLowerEqQueryLower :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
        (_A.identityProjectiveSpec M).globalNaturalExtension
          (infiniteQueryIndicatorGamble q) =
        infiniteMLNLowerQueryEnvelope M q
  queryIndicatorAdapterUpperEqQueryUpper :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
        upperEnvelope (_A.identityProjectiveSpec M).projectiveLimitCredalSet
          (infiniteQueryIndicatorGamble q) =
        infiniteMLNUpperQueryEnvelope M q
  queryIndicatorAdapterWidthEqQueryWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
        (_A.identityProjectiveSpec M).globalEnvelopeWidth
          (infiniteQueryIndicatorGamble q) =
        infiniteMLNQueryEnvelopeWidth M q
  queryIndicatorAdapterWidthComplementEqQueryWidthComplement :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
        (_A.identityProjectiveSpec M).globalEnvelopeWidthComplement
          (infiniteQueryIndicatorGamble q) =
        infiniteMLNQueryEnvelopeWidthComplement M q
  queryIndicatorAdapterMidpointEqQueryMidpoint :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_A : DLRQueryIndicatorPrevisionAdapter M)
      (q : ConstraintQuery Atom),
        (_A.identityProjectiveSpec M).globalEnvelopeMidpoint
          (infiniteQueryIndicatorGamble q) =
        infiniteMLNQueryEnvelopeMidpoint M q
  finiteVolumeAssignmentPrevisionIsPrecise :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : InfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom) (ξ : BoundaryCondition Atom)
      (_hZ : M.finiteVolumePartition Λ ξ ≠ 0),
      (finiteVolumeAssignmentPrevision M Λ ξ _hZ).toLowerPrevision.isPrecise
  finiteVolumeAssignmentMeasurePrevisionIsPrecise :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : InfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom) (ξ : BoundaryCondition Atom)
      (_hZ : M.finiteVolumePartition Λ ξ ≠ 0),
      (finiteVolumeAssignmentMeasurePrevision M Λ ξ _hZ).toLowerPrevision.isPrecise
  dlrCompletionRegionPrevisionIsPrecise :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (μ : DLRCompletion M) (Λ : Region Atom),
      (dlrCompletionRegionPrevision M μ Λ).toLowerPrevision.isPrecise
  dlrCompletionRegionPrevisionLocalQueryIndicator :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (μ : DLRCompletion M) (Λ : Region Atom)
      (q : LocalConstraintQuery Atom Λ),
      dlrCompletionRegionPrevision M μ Λ (localQueryIndicatorGamble Λ q) =
        ENNReal.toReal
          ((μ.1 : Measure (InfiniteWorld Atom)) (localQueryEvent Λ q))
  dlrLocalGambleLowerEnvelopeLeCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom) (μ : DLRCompletion M)
      (X : Gamble (LocalAssignment Atom Λ)),
      dlrLocalGambleLowerEnvelope M Λ X ≤
        dlrCompletionRegionPrevision M μ Λ X
  dlrLocalGambleLowerEnvelopeGreatestLowerBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      (L : LowerPrevision (LocalAssignment Atom Λ)),
      (∀ μ : DLRCompletion M,
        ∀ X : Gamble (LocalAssignment Atom Λ),
          L X ≤ dlrCompletionRegionPrevision M μ Λ X) →
      ∀ X : Gamble (LocalAssignment Atom Λ),
        L X ≤ dlrLocalGambleLowerEnvelope M Λ X
  dlrCompletionLeLocalGambleUpperEnvelope :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom) (μ : DLRCompletion M)
      (X : Gamble (LocalAssignment Atom Λ)),
      dlrCompletionRegionPrevision M μ Λ X ≤
        dlrLocalGambleUpperEnvelope M Λ X
  dlrLocalGambleUpperEnvelopeLeastUpperBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      (U : UpperPrevision (LocalAssignment Atom Λ)),
      (∀ μ : DLRCompletion M,
        ∀ X : Gamble (LocalAssignment Atom Λ),
          dlrCompletionRegionPrevision M μ Λ X ≤ U X) →
      ∀ X : Gamble (LocalAssignment Atom Λ),
        dlrLocalGambleUpperEnvelope M Λ X ≤ U X
  dlrAllRegionsHasCompatibleCylinderCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)],
      (dlrAllRegionsProjectiveSpec M).hasCompatibleCylinderCompletion
  dlrAllRegionsLocalCylinderCredalExactAt :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom),
      (dlrAllRegionsProjectiveSpec M).localCylinderCredalExactAt Λ
  dlrAllRegionsCylinderNaturalExtensionLocalGambleEqLower :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (dlrAllRegionsProjectiveSpec M).cylinderNaturalExtension Λ X =
        dlrLocalGambleLowerEnvelope M Λ X
  dlrAllRegionsCylinderUpperEnvelopeLocalGambleEqUpper :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (dlrAllRegionsProjectiveSpec M).cylinderUpperEnvelope Λ X =
        dlrLocalGambleUpperEnvelope M Λ X
  dlrAllRegionsCylinderWidthComplementIffLocalGambleStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidthComplement Λ X < 1 ↔
        dlrLocalGambleHasStrictWidth M Λ X
  dlrAllRegionsCylinderWidthPositiveOfCompletionDisagreement :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ))
      (μ ν : DLRCompletion M),
      dlrCompletionRegionPrevision M μ Λ X <
        dlrCompletionRegionPrevision M ν Λ X →
        0 < (dlrAllRegionsProjectiveSpec M).cylinderEnvelopeWidth Λ X
  dlrAllRegionsFiniteCylinderNaturalExtensionLeCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (μ : DLRCompletion M)
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
        (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X ≤
          dlrCompletionRegionPrevision M μ Λ X
  dlrAllRegionsFiniteCylinderNaturalExtensionGreatestLowerBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (L : LowerPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (∀ μ : DLRCompletion M,
        ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
          L X ≤ dlrCompletionRegionPrevision M μ Λ X) →
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        L X ≤
          ((dlrAllRegionsProjectiveSpec M).finiteCylinderNaturalExtensionPrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X
  dlrAllRegionsCompletionLeFiniteCylinderUpperEnvelope :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (μ : DLRCompletion M)
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      dlrCompletionRegionPrevision M μ Λ X ≤
        ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
          (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X
  dlrAllRegionsFiniteCylinderUpperEnvelopeLeastUpperBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (U : UpperPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (∀ μ : DLRCompletion M,
        ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
          dlrCompletionRegionPrevision M μ Λ X ≤ U X) →
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        ((dlrAllRegionsProjectiveSpec M).finiteCylinderUpperEnvelopePrevision
            (dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion M) Λ) X ≤
          U X
  dlrCompactBoundedFiniteCylinderNaturalExtensionLeCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (μ : DLRCompletion M)
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCompactCredalSet M)
          (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
          (dlrCylinderBoundedMeasurableGamble Λ X) ≤
        dlrCompletionRegionPrevision M μ Λ X
  dlrCompactBoundedFiniteCylinderNaturalExtensionGreatestLowerBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (L : LowerPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (∀ μ : DLRCompletion M,
        ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
          L X ≤ dlrCompletionRegionPrevision M μ Λ X) →
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        L X ≤
          boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionBoundedMeasurableCompactCredalSet M)
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
            (dlrCylinderBoundedMeasurableGamble Λ X)
  dlrCompactBoundedCompletionLeFiniteCylinderUpperEnvelope :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (μ : DLRCompletion M)
      (X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      dlrCompletionRegionPrevision M μ Λ X ≤
        boundedMeasurableNaturalUpperEnvelopePrevision
          (dlrCompletionBoundedMeasurableCompactCredalSet M)
          (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
          (dlrCylinderBoundedMeasurableGamble Λ X)
  dlrCompactBoundedFiniteCylinderUpperEnvelopeLeastUpperBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (Λ : Region Atom)
      [Fintype ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      [Nonempty ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)]
      (U : UpperPrevision ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ)),
      (∀ μ : DLRCompletion M,
        ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
          dlrCompletionRegionPrevision M μ Λ X ≤ U X) →
      ∀ X : Gamble ((dlrAllRegionsProjectiveSpec M).cylinders.Local Λ),
        boundedMeasurableNaturalUpperEnvelopePrevision
            (dlrCompletionBoundedMeasurableCompactCredalSet M)
            (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M)
            (dlrCylinderBoundedMeasurableGamble Λ X) ≤
          U X
  dlrBoundedNaturalExtensionLeCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (μ : DLRCompletion M)
      (X : BoundedMeasurableGamble (InfiniteWorld Atom)),
      boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCredalSet M)
          (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X ≤
        dlrCompletionBoundedMeasurablePrevision M μ X
  dlrBoundedNaturalExtensionGreatestLowerBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (L : BoundedMeasurableLowerPrevision (InfiniteWorld Atom)),
      (∀ μ : DLRCompletion M,
        ∀ X : BoundedMeasurableGamble (InfiniteWorld Atom),
          L X ≤ dlrCompletionBoundedMeasurablePrevision M μ X) →
      ∀ X : BoundedMeasurableGamble (InfiniteWorld Atom),
        L X ≤
          boundedMeasurableNaturalExtensionPrevision
            (dlrCompletionBoundedMeasurableCredalSet M)
            (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X
  dlrBoundedNaturalUpperEnvelopeCompletionLe :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (μ : DLRCompletion M)
      (X : BoundedMeasurableGamble (InfiniteWorld Atom)),
      dlrCompletionBoundedMeasurablePrevision M μ X ≤
        boundedMeasurableNaturalUpperEnvelopePrevision
          (dlrCompletionBoundedMeasurableCredalSet M)
          (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X
  dlrBoundedNaturalUpperEnvelopeLeastUpperBound :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (U : BoundedMeasurableUpperPrevision (InfiniteWorld Atom)),
      (∀ μ : DLRCompletion M,
        ∀ X : BoundedMeasurableGamble (InfiniteWorld Atom),
          dlrCompletionBoundedMeasurablePrevision M μ X ≤ U X) →
      ∀ X : BoundedMeasurableGamble (InfiniteWorld Atom),
        boundedMeasurableNaturalUpperEnvelopePrevision
            (dlrCompletionBoundedMeasurableCredalSet M)
            (dlrCompletionBoundedMeasurableCredalSet_nonempty M) X ≤
          U X
  dlrCompactBoundedNaturalExtensionLeCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (μ : DLRCompletion M)
      (X : BoundedMeasurableGamble (InfiniteWorld Atom)),
      boundedMeasurableNaturalExtensionPrevision
          (dlrCompletionBoundedMeasurableCompactCredalSet M)
          (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) X ≤
        dlrCompletionBoundedMeasurablePrevision M μ X
  dlrCompactBoundedNaturalUpperEnvelopeCompletionLe :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (μ : DLRCompletion M)
      (X : BoundedMeasurableGamble (InfiniteWorld Atom)),
      dlrCompletionBoundedMeasurablePrevision M μ X ≤
        boundedMeasurableNaturalUpperEnvelopePrevision
          (dlrCompletionBoundedMeasurableCompactCredalSet M)
          (dlrCompletionBoundedMeasurableCompactCredalSet_nonempty M) X
  queryEnvelopePreciseOfUniform :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (_hM : M.PaperUniformSmallTotalInfluence)
      (q : ConstraintQuery Atom),
      infiniteMLNLowerQueryEnvelope M q =
        infiniteMLNUpperQueryEnvelope M q
  queryDeterminedOfUniform :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_hM : M.PaperUniformSmallTotalInfluence)
      (q : ConstraintQuery Atom),
      dlrQueryDetermined M q
  queryEnvelopePreciseOfDetermined :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      dlrQueryDetermined M q →
        infiniteMLNLowerQueryEnvelope M q =
          infiniteMLNUpperQueryEnvelope M q
  queryEnvelopeNontrivialOfDisagreement :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom)
      (_hBddBelow : BddBelow (Set.range (dlrCompletionQueryProb M q)))
      (_hBddAbove : BddAbove (Set.range (dlrCompletionQueryProb M q)))
      (μ ν : DLRCompletion M),
      dlrCompletionQueryProb M q μ < dlrCompletionQueryProb M q ν →
        infiniteMLNLowerQueryEnvelope M q <
          infiniteMLNUpperQueryEnvelope M q
  queryEnvelopeNontrivialOfStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom)
      (_hBddBelow : BddBelow (Set.range (dlrCompletionQueryProb M q)))
      (_hBddAbove : BddAbove (Set.range (dlrCompletionQueryProb M q))),
      dlrQueryHasStrictWidth M q →
        infiniteMLNLowerQueryEnvelope M q <
          infiniteMLNUpperQueryEnvelope M q
  strictWidthRefutesQueryDetermined :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q → ¬ dlrQueryDetermined M q
  projectiveLimitQueryValue :
    ∀ {Atom : Type*} [DecidableEq Atom]
      (e : ℕ ≃ Atom)
      (P : ∀ I : Finset Atom,
        Measure (∀ i : I,
          Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
      [∀ I, IsProbabilityMeasure (P I)]
      (hP : MeasureTheory.IsProjectiveMeasureFamily P)
      (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ),
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.globalMeasureMassSemantics
        (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.projectiveLimitMeasure
          e P hP) Λ).queryProb q =
          P Λ (localConstraintSet Λ q)
  projectiveLimitDLRCompletionOfStageMarginalTendsto :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
      (ξ : BoundaryCondition Atom)
      (_e : ℕ ≃ Atom)
      (P : ∀ I : Finset Atom,
        Measure (∀ i : I,
          Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i))
      [∀ I, IsProbabilityMeasure (P I)]
      (_hP : MeasureTheory.IsProjectiveMeasureFamily P)
      (_hconv : ∀ (I : Finset Atom) (S : Set (∀ i : I,
          Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.BoolCoord Atom i)),
          MeasurableSet S →
            Tendsto
              (fun n =>
                Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
                  E M.toStrictlyPositiveInfiniteGroundMLNSpec ξ n I S)
              atTop (nhds (P I S))),
      DLRCompletion M
  dlrCompletionSingletonSpecHasCompatibleCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (μ : DLRCompletion M)
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)),
      (dlrCompletionSingletonProjectiveSpec M μ _toPrecise).hasCompatibleCompletion
  dlrCompletionIdentityProjectiveLimitSet :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)),
      (dlrCompletionIdentityProjectiveSpec M _toPrecise).projectiveLimitCredalSet =
        dlrCompletionCredalSet M _toPrecise
  dlrCompletionIdentitySpecHasCompatibleCompletion :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom)),
      (dlrCompletionIdentityProjectiveSpec M _toPrecise).hasCompatibleCompletion
  dlrCompletionIdentitySpecDeterminesOfQueryDetermined :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
      (q : ConstraintQuery Atom)
      (X : Gamble (InfiniteWorld Atom)),
      (∀ μ : DLRCompletion M,
        _toPrecise μ X = dlrCompletionQueryProb M q μ) →
      dlrQueryDetermined M q →
        (dlrCompletionIdentityProjectiveSpec M _toPrecise).determinesGlobalGamble X
  dlrCompletionIdentitySpecStrictWidthOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
      (q : ConstraintQuery Atom)
      (X : Gamble (InfiniteWorld Atom)),
      (∀ μ : DLRCompletion M,
        _toPrecise μ X = dlrCompletionQueryProb M q μ) →
      dlrQueryHasStrictWidth M q →
        (dlrCompletionIdentityProjectiveSpec M _toPrecise).hasStrictGlobalWidth X
  dlrCompletionCredalSetEnvelopeNontrivialOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
      (q : ConstraintQuery Atom)
      (X : Gamble (InfiniteWorld Atom))
      (_hBddBelow : BddBelow ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P X) '' dlrCompletionCredalSet M _toPrecise))
      (_hBddAbove : BddAbove ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P X) '' dlrCompletionCredalSet M _toPrecise)),
      (∀ μ : DLRCompletion M,
        _toPrecise μ X = dlrCompletionQueryProb M q μ) →
      dlrQueryHasStrictWidth M q →
        lowerEnvelope (dlrCompletionCredalSet M _toPrecise) X <
          upperEnvelope (dlrCompletionCredalSet M _toPrecise) X
  dlrCompletionCredalSetWidthPositiveOfQueryStrictWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      (_toPrecise : DLRCompletion M → PrecisePrevision (InfiniteWorld Atom))
      (q : ConstraintQuery Atom)
      (X : Gamble (InfiniteWorld Atom))
      (_hBddBelow : BddBelow ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P X) '' dlrCompletionCredalSet M _toPrecise))
      (_hBddAbove : BddAbove ((fun P : PrecisePrevision (InfiniteWorld Atom) =>
        P X) '' dlrCompletionCredalSet M _toPrecise)),
      (∀ μ : DLRCompletion M,
        _toPrecise μ X = dlrCompletionQueryProb M q μ) →
      dlrQueryHasStrictWidth M q →
        0 < credalEnvelopeWidth (dlrCompletionCredalSet M _toPrecise) X
  dlrSpecializationHasCompatibleCompletion :
    ∀ {Atom ClauseId Window Global : Type*}
      [DecidableEq Atom] [DecidableEq ClauseId] [LE Window]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (_D : DLRProjectiveCredalSpecialization M Window Global),
      _D.projectiveSpec.hasCompatibleCompletion

/-- Current infinite-MLN credal bridge profile. -/
noncomputable def infiniteMLNCredalBridgeProfile :
    InfiniteMLNCredalBridgeProfile where
  queryEventMeasurable :=
    measurableSet_infiniteQueryEvent
  dlrCompletionQueryProbIsEventMeasure :=
    dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent
  dlrCompletionQueryProbInUnit :=
    dlrCompletionQueryProb_mem_Icc
  queryOutcomePrevisionIsPrecise :=
    dlrQueryOutcomePrevision_precise
  queryOutcomePrevisionTrueAtom :=
    dlrQueryOutcomePrevision_true_atom
  queryOutcomeCredalSetDeterminesOfQueryDetermined :=
    dlrQueryOutcomeCredalSet_determines_true_atom_of_queryDetermined
  queryOutcomeCredalSetStrictWidthOfQueryStrictWidth :=
    dlrQueryOutcomeCredalSet_hasStrictWidth_true_atom_of_queryStrictWidth
  queryOutcomeCredalSetNotDeterminesOfQueryStrictWidth :=
    dlrQueryOutcomeCredalSet_not_determines_true_atom_of_queryStrictWidth
  queryOutcomeValueImageEqQueryRange :=
    dlrQueryOutcomeCredalSet_true_atom_value_image_eq_range
  queryOutcomeLowerEnvelopeEqQueryLower :=
    lowerEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNLower
  queryOutcomeLowerEnvelopeLeCompletion :=
    dlrQueryOutcomeLowerEnvelope_le_completion
  queryOutcomeLowerEnvelopeGreatestLowerBound :=
    dlrQueryOutcomeLowerEnvelope_greatest_lower_bound
  queryLowerEnvelopeLeCompletionProb :=
    infiniteMLNLowerQueryEnvelope_le_completionProb
  queryLowerEnvelopeGreatestLowerBound :=
    infiniteMLNLowerQueryEnvelope_greatest_lower_bound
  queryOutcomeUpperEnvelopeEqQueryUpper :=
    upperEnvelope_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNUpper
  queryOutcomeCompletionLeUpperEnvelope :=
    dlrQueryOutcomeCompletion_le_upperEnvelope
  queryOutcomeUpperEnvelopeLeastUpperBound :=
    dlrQueryOutcomeUpperEnvelope_least_upper_bound
  queryCompletionProbLeUpperEnvelope :=
    dlrCompletionQueryProb_le_infiniteMLNUpperQueryEnvelope
  queryUpperEnvelopeLeastUpperBound :=
    infiniteMLNUpperQueryEnvelope_least_upper_bound
  queryOutcomeWidthEqQueryEnvelopeWidth :=
    credalEnvelopeWidth_dlrQueryOutcomeCredalSet_true_atom_eq_infiniteMLNWidth
  queryEnvelopeNontrivialOfStrictWidthBounded :=
    infiniteMLN_queryEnvelope_nontrivial_of_strictWidth_bounded
  queryEnvelopeWidthPositiveOfStrictWidth :=
    infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
  queryOutcomeCredalSetWidthPositiveOfQueryStrictWidth :=
    dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
  queryOutcomeProjectiveSpecLimitSet :=
    dlrQueryOutcomeProjectiveSpec_projectiveLimitCredalSet
  queryOutcomeProjectiveSpecHasCompatibleCompletion :=
    dlrQueryOutcomeProjectiveSpec_hasCompatibleCompletion
  queryOutcomeProjectiveSpecDeterminesOfQueryDetermined :=
    dlrQueryOutcomeProjectiveSpec_determines_true_atom_of_queryDetermined
  queryOutcomeProjectiveSpecStrictWidthOfQueryStrictWidth :=
    dlrQueryOutcomeProjectiveSpec_hasStrictWidth_true_atom_of_queryStrictWidth
  queryOutcomeProjectiveSpecNotDeterminesOfQueryStrictWidth :=
    dlrQueryOutcomeProjectiveSpec_not_determines_true_atom_of_queryStrictWidth
  queryOutcomeProjectiveSpecLowerEqQueryLower :=
    dlrQueryOutcomeProjectiveSpec_globalNaturalExtension_true_atom_eq_infiniteMLNLower
  queryOutcomeProjectiveSpecUpperEqQueryUpper :=
    dlrQueryOutcomeProjectiveSpec_upperEnvelope_true_atom_eq_infiniteMLNUpper
  queryOutcomeProjectiveSpecWidthEqQueryEnvelopeWidth :=
    dlrQueryOutcomeProjectiveSpec_globalEnvelopeWidth_true_atom_eq_infiniteMLNWidth
  queryIndicatorBounded :=
    infiniteQueryIndicatorGamble_mem_Icc
  queryIndicatorAdapterDeterminesOfQueryDetermined :=
    DLRQueryIndicatorPrevisionAdapter.determinesQueryIndicator_of_queryDetermined
  queryIndicatorAdapterStrictWidthOfQueryStrictWidth :=
    DLRQueryIndicatorPrevisionAdapter.hasStrictQueryIndicatorWidth_of_queryStrictWidth
  queryIndicatorAdapterEnvelopeNontrivialOfQueryStrictWidth :=
    DLRQueryIndicatorPrevisionAdapter.lowerUpperEnvelope_nontrivial_of_queryStrictWidth
  queryIndicatorAdapterWidthPositiveOfQueryStrictWidth :=
    DLRQueryIndicatorPrevisionAdapter.envelopeWidth_pos_of_queryStrictWidth
  queryIndicatorAdapterLowerEqQueryLower :=
    DLRQueryIndicatorPrevisionAdapter.globalNaturalExtension_queryIndicator_eq_infiniteMLNLower
  queryIndicatorAdapterUpperEqQueryUpper :=
    DLRQueryIndicatorPrevisionAdapter.globalUpperEnvelope_queryIndicator_eq_infiniteMLNUpper
  queryIndicatorAdapterWidthEqQueryWidth :=
    DLRQueryIndicatorPrevisionAdapter.globalEnvelopeWidth_queryIndicator_eq_infiniteMLNWidth
  queryIndicatorAdapterWidthComplementEqQueryWidthComplement :=
    DLRQueryIndicatorPrevisionAdapter.globalEnvelopeWidthComplement_queryIndicator_eq_infiniteMLNComplement
  queryIndicatorAdapterMidpointEqQueryMidpoint :=
    DLRQueryIndicatorPrevisionAdapter.globalEnvelopeMidpoint_queryIndicator_eq_infiniteMLNMidpoint
  finiteVolumeAssignmentPrevisionIsPrecise :=
    finiteVolumeAssignmentPrevision_precise
  finiteVolumeAssignmentMeasurePrevisionIsPrecise :=
    finiteVolumeAssignmentMeasurePrevision_precise
  dlrCompletionRegionPrevisionIsPrecise :=
    dlrCompletionRegionPrevision_precise
  dlrCompletionRegionPrevisionLocalQueryIndicator :=
    dlrCompletionRegionPrevision_localQueryIndicator
  dlrLocalGambleLowerEnvelopeLeCompletion :=
    dlrLocalGambleLowerEnvelope_le_completion
  dlrLocalGambleLowerEnvelopeGreatestLowerBound :=
    dlrLocalGambleLowerEnvelope_greatest_lower_bound
  dlrCompletionLeLocalGambleUpperEnvelope :=
    dlrCompletion_le_localGambleUpperEnvelope
  dlrLocalGambleUpperEnvelopeLeastUpperBound :=
    dlrLocalGambleUpperEnvelope_least_upper_bound
  dlrAllRegionsHasCompatibleCylinderCompletion :=
    dlrAllRegionsProjectiveSpec_hasCompatibleCylinderCompletion
  dlrAllRegionsLocalCylinderCredalExactAt :=
    dlrAllRegionsProjectiveSpec_localCylinderCredalExactAt
  dlrAllRegionsCylinderNaturalExtensionLocalGambleEqLower :=
    dlrAllRegionsProjectiveSpec_cylinderNaturalExtension_localGamble_eq_localGambleLowerEnvelope
  dlrAllRegionsCylinderUpperEnvelopeLocalGambleEqUpper :=
    dlrAllRegionsProjectiveSpec_cylinderUpperEnvelope_localGamble_eq_localGambleUpperEnvelope
  dlrAllRegionsCylinderWidthComplementIffLocalGambleStrictWidth :=
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidthComplement_lt_one_iff_localGambleStrictWidth
  dlrAllRegionsCylinderWidthPositiveOfCompletionDisagreement :=
    dlrAllRegionsProjectiveSpec_cylinderEnvelopeWidth_pos_of_completionDisagreement
  dlrAllRegionsFiniteCylinderNaturalExtensionLeCompletion :=
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_le_completion_localGamble
  dlrAllRegionsFiniteCylinderNaturalExtensionGreatestLowerBound :=
    dlrAllRegionsProjectiveSpec_finiteCylinderNaturalExtensionPrevision_greatest_lower_bound_localGamble
  dlrAllRegionsCompletionLeFiniteCylinderUpperEnvelope :=
    dlrAllRegionsProjectiveSpec_completion_le_finiteCylinderUpperEnvelopePrevision_localGamble
  dlrAllRegionsFiniteCylinderUpperEnvelopeLeastUpperBound :=
    dlrAllRegionsProjectiveSpec_finiteCylinderUpperEnvelopePrevision_least_upper_bound_localGamble
  dlrCompactBoundedFiniteCylinderNaturalExtensionLeCompletion :=
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_le_completionRegionPrevision
  dlrCompactBoundedFiniteCylinderNaturalExtensionGreatestLowerBound :=
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_cylinder_greatest_lower_bound_localGamble
  dlrCompactBoundedCompletionLeFiniteCylinderUpperEnvelope :=
    dlrCompletionRegionPrevision_le_boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder
  dlrCompactBoundedFiniteCylinderUpperEnvelopeLeastUpperBound :=
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_cylinder_least_upper_bound_localGamble
  dlrBoundedNaturalExtensionLeCompletion :=
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_le_completion
  dlrBoundedNaturalExtensionGreatestLowerBound :=
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCredalSet_greatest_lower_bound
  dlrBoundedNaturalUpperEnvelopeCompletionLe :=
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCredalSet_completion_le
  dlrBoundedNaturalUpperEnvelopeLeastUpperBound :=
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCredalSet_least_upper_bound
  dlrCompactBoundedNaturalExtensionLeCompletion :=
    boundedMeasurableNaturalExtensionPrevision_dlrCompletionCompactCredalSet_le_completion
  dlrCompactBoundedNaturalUpperEnvelopeCompletionLe :=
    boundedMeasurableNaturalUpperEnvelopePrevision_dlrCompletionCompactCredalSet_completion_le
  queryEnvelopePreciseOfUniform :=
    infiniteMLN_queryEnvelope_precise_of_uniform
  queryDeterminedOfUniform :=
    dlrQueryDetermined_of_uniform
  queryEnvelopePreciseOfDetermined :=
    infiniteMLN_queryEnvelope_precise_of_dlrQueryDetermined
  queryEnvelopeNontrivialOfDisagreement :=
    infiniteMLN_queryEnvelope_nontrivial_of_disagreement
  queryEnvelopeNontrivialOfStrictWidth :=
    infiniteMLN_queryEnvelope_nontrivial_of_strictWidth
  strictWidthRefutesQueryDetermined :=
    not_dlrQueryDetermined_of_strictWidth
  projectiveLimitQueryValue :=
    projectiveLimitMeasure_queryEnvelope_value
  projectiveLimitDLRCompletionOfStageMarginalTendsto :=
    projectiveLimitDLRCompletion_of_stageMarginal_tendsto
  dlrCompletionSingletonSpecHasCompatibleCompletion :=
    dlrCompletionSingletonProjectiveSpec_hasCompatibleCompletion
  dlrCompletionIdentityProjectiveLimitSet :=
    dlrCompletionIdentityProjectiveSpec_projectiveLimitCredalSet
  dlrCompletionIdentitySpecHasCompatibleCompletion :=
    dlrCompletionIdentityProjectiveSpec_hasCompatibleCompletion
  dlrCompletionIdentitySpecDeterminesOfQueryDetermined :=
    dlrCompletionIdentityProjectiveSpec_determinesGlobalGamble_of_queryDetermined
  dlrCompletionIdentitySpecStrictWidthOfQueryStrictWidth :=
    dlrCompletionIdentityProjectiveSpec_hasStrictGlobalWidth_of_queryStrictWidth
  dlrCompletionCredalSetEnvelopeNontrivialOfQueryStrictWidth :=
    dlrCompletionCredalSet_lowerUpperEnvelope_nontrivial_of_queryStrictWidth
  dlrCompletionCredalSetWidthPositiveOfQueryStrictWidth :=
    dlrCompletionCredalSet_envelopeWidth_pos_of_queryStrictWidth
  dlrSpecializationHasCompatibleCompletion :=
    by
      intro Atom ClauseId Window Global instAtom instClause instLE M instNonempty D
      exact DLRProjectiveCredalSpecialization.hasCompatibleCompletion D

end Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
