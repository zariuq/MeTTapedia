import Mettapedia.Logic.MarkovLogicInfiniteWorldModel
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

/-- Query probability supplied by one DLR completion, converted to a real
number for lower/upper-envelope comparisons. -/
noncomputable def dlrCompletionQueryProb
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (q : ConstraintQuery Atom) (μ : DLRCompletion M) : ℝ :=
  ENNReal.toReal
    ((infiniteMLNMassSemantics M μ.1 μ.2).queryProb q)

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

/-- Under Dobrushin uniqueness, the DLR credal envelope is precise for every
finite query, provided at least one DLR completion exists. -/
theorem infiniteMLN_queryEnvelope_precise_of_uniform
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (hM : M.PaperUniformSmallTotalInfluence)
    (q : ConstraintQuery Atom) :
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
        rw [dlrCompletionQueryProb_eq_of_uniform M hM q μ μ₀]
        simp
    · intro hx
      have hx' : x = dlrCompletionQueryProb M q μ₀ := by simpa using hx
      exact ⟨μ₀, hx'.symm⟩
  unfold infiniteMLNLowerQueryEnvelope infiniteMLNUpperQueryEnvelope
  rw [hRange, csInf_singleton, csSup_singleton]

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

/-! ## Profile surface -/

/-- Proof-carrying profile for the σ-additive infinite-MLN face of the
projective credal abstraction. -/
structure InfiniteMLNCredalBridgeProfile where
  finiteVolumeAssignmentPrevisionIsPrecise :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : InfiniteGroundMLNSpec Atom ClauseId)
      (Λ : Region Atom) (ξ : BoundaryCondition Atom)
      (_hZ : M.finiteVolumePartition Λ ξ ≠ 0),
      (finiteVolumeAssignmentPrevision M Λ ξ _hZ).toLowerPrevision.isPrecise
  queryEnvelopePreciseOfUniform :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (_hM : M.PaperUniformSmallTotalInfluence)
      (q : ConstraintQuery Atom),
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
  finiteVolumeAssignmentPrevisionIsPrecise :=
    finiteVolumeAssignmentPrevision_precise
  queryEnvelopePreciseOfUniform :=
    infiniteMLN_queryEnvelope_precise_of_uniform
  queryEnvelopeNontrivialOfDisagreement :=
    infiniteMLN_queryEnvelope_nontrivial_of_disagreement
  projectiveLimitQueryValue :=
    projectiveLimitMeasure_queryEnvelope_value
  dlrSpecializationHasCompatibleCompletion :=
    by
      intro Atom ClauseId Window Global instAtom instClause instLE M instNonempty D
      exact DLRProjectiveCredalSpecialization.hasCompatibleCompletion D

end Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
