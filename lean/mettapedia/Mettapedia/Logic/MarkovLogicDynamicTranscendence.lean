import Mettapedia.Logic.MarkovLogicIndividuation
import Mettapedia.Logic.MarkovLogicSelfTranscendence
import Mettapedia.Logic.MarkovLogicFiniteVolumeContraction
import Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
import Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
import Mettapedia.Logic.MarkovLogicInfiniteCylinders
import Mettapedia.Logic.MarkovLogicInfinitePositive

/-!
# Dynamic Self-Transcendence: Approximate Preservation Under Rewriting

Static self-transcendence (in `MarkovLogicSelfTranscendence`) gives exact
preservation when old clauses are preserved and new ones are added outside.

This module addresses the harder case: what happens when old clauses are
**rewritten** (changed, not just extended)?  Exact preservation fails, but
approximate preservation holds: the truth-value discrepancy decays
geometrically with the interaction distance from the rewritten clauses
to the query.

The key theorem: if two specs M₁, M₂ agree on the n-th interaction shell
around a query region Γ (i.e., on `iterExpandRegion M₁ Γ n`), then their
DLR measures disagree on Γ-queries by at most `2|Γ| · C^n` via the present
shell comparison argument.

This captures Weinbaum's dynamic self-transcendence: a system can change
its mind about distant concepts while barely affecting local beliefs.
The Dobrushin budget controls how much the change propagates.

## References

- D. R. Weinbaum & V. Veitas, *Open-Ended Intelligence*, 2015.
- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, Theorem 8.7.
-/

namespace Mettapedia.Logic.MarkovLogicDynamicTranscendence

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicFiniteVolumeContraction
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.MarkovLogicSelfTranscendence
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A **dynamic transcendence step**: two specs that may differ on the
    old core (clause rewriting), but agree on a shell of depth n around
    the query region.  Unlike `TranscendenceStep`, this does NOT require
    agreement on the core itself — the system may have "changed its mind."

    The key hypothesis: the specs agree on `iterExpandRegion M₁ Γ n`,
    the n-th interaction-neighborhood expansion of Γ.  Clauses OUTSIDE
    this shell may be completely different between the two specs.

    Under this hypothesis, queries on Γ differ by at most `2|Γ| · C^n`
    in the current formalization. -/
structure DynamicTranscendenceStep
    (M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  /-- The query region. -/
  queryRegion : Region Atom
  /-- The shell depth: how many interaction layers separate the query
      from the first disagreement between the specs. -/
  shellDepth : ℕ
  /-- The specs agree on the shell around the query. -/
  shell_agreement : SpecAgreesOnRegion M₁ M₂
    (M₁.iterExpandRegion queryRegion shellDepth)
  /-- Dobrushin budgets. -/
  budget₁ : M₁.PaperUniformSmallTotalInfluence
  budget₂ : M₂.PaperUniformSmallTotalInfluence

private theorem classicalRegionSupport_mono
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Λ Δ : Region Atom}
    (hΛΔ : Λ ⊆ Δ) :
    M.regionSupport Λ ⊆ M.regionSupport Δ := by
  intro j hj
  exact M.regionSupport_complete
    (clauseTouchesRegion_mono (C := M.clause j) hΛΔ (M.regionSupport_sound hj))

private theorem atomInteractionNeighborhood_eq_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Ω : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Ω)
    {a : Atom}
    (haΩ : a ∈ Ω) :
    M₁.atomInteractionNeighborhood a = M₂.atomInteractionNeighborhood a := by
  ext b
  constructor
  · intro hb
    rcases (M₁.mem_atomInteractionNeighborhood_iff a b).1 hb with ⟨j, hj₁, hb₁⟩
    have hsingleton_subset : ({a} : Region Atom) ⊆ Ω := by
      intro x hx
      have hx' : x = a := by simpa using hx
      rw [hx']
      exact haΩ
    have hsupp :
        M₁.regionSupport ({a} : Region Atom) = M₂.regionSupport ({a} : Region Atom) :=
      hagree.regionSupport_eq ({a} : Region Atom) hsingleton_subset ⟨a, by simp⟩
    have hj₂ : j ∈ M₂.regionSupport ({a} : Region Atom) := by
      simpa [hsupp] using hj₁
    have hjΩ : j ∈ M₁.regionSupport Ω :=
      classicalRegionSupport_mono M₁ hsingleton_subset hj₁
    have hclause : M₁.clause j = M₂.clause j := hagree.clause_eq j hjΩ
    have hb₂ : b ∈ (M₂.clause j).atoms.erase a := by
      simpa [hclause] using hb₁
    exact (M₂.mem_atomInteractionNeighborhood_iff a b).2 ⟨j, hj₂, hb₂⟩
  · intro hb
    rcases (M₂.mem_atomInteractionNeighborhood_iff a b).1 hb with ⟨j, hj₂, hb₂⟩
    have hsingleton_subset : ({a} : Region Atom) ⊆ Ω := by
      intro x hx
      have hx' : x = a := by simpa using hx
      rw [hx']
      exact haΩ
    have hsupp :
        M₁.regionSupport ({a} : Region Atom) = M₂.regionSupport ({a} : Region Atom) :=
      hagree.regionSupport_eq ({a} : Region Atom) hsingleton_subset ⟨a, by simp⟩
    have hj₁ : j ∈ M₁.regionSupport ({a} : Region Atom) := by
      simpa [hsupp] using hj₂
    have hjΩ : j ∈ M₁.regionSupport Ω :=
      classicalRegionSupport_mono M₁ hsingleton_subset hj₁
    have hclause : M₁.clause j = M₂.clause j := hagree.clause_eq j hjΩ
    have hb₁ : b ∈ (M₁.clause j).atoms.erase a := by
      simpa [hclause] using hb₂
    exact (M₁.mem_atomInteractionNeighborhood_iff a b).2 ⟨j, hj₁, hb₁⟩

private theorem expandRegion_eq_of_atomInteractionNeighborhood_eq_on
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Λ : Region Atom}
    (hnbhd : ∀ a ∈ Λ, M₁.atomInteractionNeighborhood a = M₂.atomInteractionNeighborhood a) :
    M₁.expandRegion Λ = M₂.expandRegion Λ := by
  ext b
  simp only [ClassicalInfiniteGroundMLNSpec.expandRegion, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (hb | ⟨a, ha, hb⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨a, ha, by simpa [hnbhd a ha] using hb⟩
  · rintro (hb | ⟨a, ha, hb⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨a, ha, by simpa [hnbhd a ha] using hb⟩

private theorem iterExpandRegion_mono
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Γ : Region Atom)
    {k n : ℕ}
    (hkn : k ≤ n) :
    M.iterExpandRegion Γ k ⊆ M.iterExpandRegion Γ n := by
  induction hkn with
  | refl =>
      intro a ha
      exact ha
  | @step n hkn ih =>
      intro a ha
      exact M.subset_iterExpandRegion_succ Γ n (ih ha)

private theorem iterExpandRegion_eq_of_specAgreesOnRegion_prefix
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ Ω : Region Atom}
    {n : ℕ}
    (hagree : SpecAgreesOnRegion M₁ M₂ Ω)
    (hΩ : M₁.iterExpandRegion Γ n ⊆ Ω) :
    ∀ k ≤ n, M₂.iterExpandRegion Γ k = M₁.iterExpandRegion Γ k
  | 0, _ => rfl
  | k + 1, hk => by
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hk_eq : M₂.iterExpandRegion Γ k = M₁.iterExpandRegion Γ k :=
        iterExpandRegion_eq_of_specAgreesOnRegion_prefix hagree hΩ k hk'
      have hsubset :
          M₁.iterExpandRegion Γ k ⊆ Ω := by
        exact fun a ha => hΩ (iterExpandRegion_mono M₁ Γ hk' ha)
      have hnbhd :
          ∀ a ∈ M₁.iterExpandRegion Γ k,
            M₁.atomInteractionNeighborhood a = M₂.atomInteractionNeighborhood a := by
        intro a ha
        exact atomInteractionNeighborhood_eq_of_specAgreesOnRegion hagree (hsubset ha)
      calc
        M₂.iterExpandRegion Γ (k + 1)
            = M₂.expandRegion (M₂.iterExpandRegion Γ k) := by
                simp [ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
        _ = M₂.expandRegion (M₁.iterExpandRegion Γ k) := by
              rw [hk_eq]
        _ = M₁.expandRegion (M₁.iterExpandRegion Γ k) := by
              symm
              exact expandRegion_eq_of_atomInteractionNeighborhood_eq_on hnbhd
        _ = M₁.iterExpandRegion Γ (k + 1) := by
              simp [ClassicalInfiniteGroundMLNSpec.iterExpandRegion]

private theorem infiniteQueryEvent_eq_localQueryEvent_restrictQueryToRegion
    {Γ : Region Atom}
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    infiniteQueryEvent q =
      localQueryEvent Γ (restrictQueryToRegion Γ q hq) := by
  ext ω
  have hpatch : patch Γ (Finset.restrict Γ ω) ω = ω := by
    funext a
    by_cases ha : a ∈ Γ
    · simp [patch, ha]
    · simp [patch, ha]
  have hiff :=
    satisfiesConstraints_restrictQueryToRegion_iff Γ (Finset.restrict Γ ω) q hq ω
  simpa [infiniteQueryEvent, localQueryEvent, InfiniteGroundMLNSpec.infiniteConstraintQueryHolds, hpatch]
    using hiff.symm

private lemma infiniteMLNMassSemantics_queryProb_empty_eq_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (μ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ : FixedRegionCylinderDLR M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom))) :
    (infiniteMLNMassSemantics M μ hμ).queryProb [] = 1 := by
  simp only [MassSemantics.queryProb, infiniteMLNMassSemantics]
  rw [if_neg (by simp : (1 : ENNReal) ≠ 0)]
  have huniv : infiniteQueryEvent ([] : ConstraintQuery Atom) = Set.univ := by
    ext ω
    simp [infiniteQueryEvent, satisfiesConstraints]
  rw [huniv]
  simp [MeasureTheory.measure_univ (μ := (μ : Measure (InfiniteWorld Atom)))]

private theorem limitMarginal_toPMF_finiteVolumeWorldMeasure_eq_finiteVolumeAssignmentPMF
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Ω : Region Atom)
    (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Ω ξ ≠ 0) :
    (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
      (finiteVolumeWorldMeasure M Ω ξ hZ) Ω).toPMF =
      finiteVolumeAssignmentPMF M Ω ξ hZ := by
  let p := finiteVolumeAssignmentPMF M Ω ξ hZ
  have hmeasure :
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (finiteVolumeWorldMeasure M Ω ξ hZ) Ω =
        p.toMeasure := by
    unfold Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
    have hworld :
        finiteVolumeWorldMeasure M Ω ξ hZ =
          p.toMeasure.map (fun x => patch Ω x ξ) := by
      unfold p
      unfold MarkovLogicInfiniteWorldMeasures.finiteVolumeWorldMeasure
      unfold MarkovLogicInfiniteWorldMeasures.finiteVolumeWorldPMF
      symm
      simpa using
        (PMF.toMeasure_map (p := finiteVolumeAssignmentPMF M Ω ξ hZ)
          (f := fun x => patch Ω x ξ)
          (hf := measurable_patch Ω ξ))
    rw [hworld]
    rw [Measure.map_map (Finset.measurable_restrict Ω) (measurable_patch Ω ξ)]
    have hcomp : (fun x : LocalAssignment Atom Ω => Finset.restrict Ω (patch Ω x ξ)) = id := by
      funext x
      ext a
      simp [patch]
    change Measure.map (fun x : LocalAssignment Atom Ω => Finset.restrict Ω (patch Ω x ξ)) p.toMeasure =
      p.toMeasure
    rw [hcomp]
    simp [p]
  apply PMF.ext
  intro x
  have hsingleton :=
    congrArg (fun ρ : Measure (LocalAssignment Atom Ω) => ρ ({x} : Set (LocalAssignment Atom Ω))) hmeasure
  simpa [p] using hsingleton

private theorem finiteVolumeAssignmentPMF_eq_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Ω : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Ω)
    (hΩne : Ω.Nonempty)
    (ξ : BoundaryCondition Atom) :
    let N₁ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    let N₂ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    finiteVolumeAssignmentPMF N₁ Ω ξ
        (M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ) =
      finiteVolumeAssignmentPMF N₂ Ω ξ
        (M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ) := by
  classical
  let N₁ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let N₂ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  have hsupport : N₁.regionSupport Ω = N₂.regionSupport Ω := by
    simpa [N₁, N₂] using hagree.regionSupport_eq Ω (by intro a ha; exact ha) hΩne
  have hweight :
      ∀ x : LocalAssignment Atom Ω,
        N₁.finiteVolumeWeight Ω x ξ = N₂.finiteVolumeWeight Ω x ξ := by
    intro x
    unfold InfiniteGroundMLNSpec.finiteVolumeWeight
    rw [hsupport]
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hjN₁ : j ∈ N₁.regionSupport Ω := by
      rw [hsupport]
      exact hj
    have hj' : j ∈ M₁.regionSupport Ω := by
      simpa [N₁] using hjN₁
    have hwc := classicalWeightedClause_eq_of_specAgreesOnRegion hagree hj'
    simpa [N₁, N₂, ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec]
      using congrArg (fun wc => wc.eval (patch Ω x ξ)) hwc
  have hpartition :
      N₁.finiteVolumePartition Ω ξ = N₂.finiteVolumePartition Ω ξ := by
    unfold InfiniteGroundMLNSpec.finiteVolumePartition
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact hweight x
  apply PMF.ext
  intro x
  rw [MarkovLogicInfiniteWorldMeasures.finiteVolumeAssignmentPMF_apply]
  rw [MarkovLogicInfiniteWorldMeasures.finiteVolumeAssignmentPMF_apply]
  rw [hweight x, hpartition]

private theorem finiteVolume_localQueryDiscrepancy_eq_zero_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ Ω : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Ω)
    (hΓΩ : Γ ⊆ Ω)
    (hΩne : Ω.Nonempty)
    (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Γ) :
    let N₁ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    let N₂ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    let ν₁ : ProbabilityMeasure (InfiniteWorld Atom) :=
      ⟨finiteVolumeWorldMeasure N₁ Ω ξ
        (M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ), inferInstance⟩
    let ν₂ : ProbabilityMeasure (InfiniteWorld Atom) :=
      ⟨finiteVolumeWorldMeasure N₂ Ω ξ
        (M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ), inferInstance⟩
    M₁.finiteRegionLocalQueryDiscrepancy ν₁ ν₂ Γ q = 0 := by
  classical
  let N₁ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let N₂ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let hZ₁ :=
    M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ
  let hZ₂ :=
    M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ
  let ν₁ : ProbabilityMeasure (InfiniteWorld Atom) := ⟨finiteVolumeWorldMeasure N₁ Ω ξ hZ₁, inferInstance⟩
  let ν₂ : ProbabilityMeasure (InfiniteWorld Atom) := ⟨finiteVolumeWorldMeasure N₂ Ω ξ hZ₂, inferInstance⟩
  have hpmfΩ :
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₁ : Measure (InfiniteWorld Atom)) Ω).toPMF =
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₂ : Measure (InfiniteWorld Atom)) Ω).toPMF := by
    calc
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₁ : Measure (InfiniteWorld Atom)) Ω).toPMF
          = finiteVolumeAssignmentPMF N₁ Ω ξ hZ₁ := by
              simpa [ν₁, N₁, hZ₁] using
                limitMarginal_toPMF_finiteVolumeWorldMeasure_eq_finiteVolumeAssignmentPMF
                  N₁ Ω ξ hZ₁
      _ = finiteVolumeAssignmentPMF N₂ Ω ξ hZ₂ := by
            simpa [N₁, N₂, hZ₁, hZ₂] using
              finiteVolumeAssignmentPMF_eq_of_specAgreesOnRegion
                hagree hΩne ξ
      _ = (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
            (ν₂ : Measure (InfiniteWorld Atom)) Ω).toPMF := by
            symm
            simpa [ν₂, N₂, hZ₂] using
              limitMarginal_toPMF_finiteVolumeWorldMeasure_eq_finiteVolumeAssignmentPMF
                N₂ Ω ξ hZ₂
  have hpmfΓ :
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₁ : Measure (InfiniteWorld Atom)) Γ).toPMF =
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₂ : Measure (InfiniteWorld Atom)) Γ).toPMF := by
    calc
      (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₁ : Measure (InfiniteWorld Atom)) Γ).toPMF
          =
        ((Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν₁ : Measure (InfiniteWorld Atom)) Ω).toPMF).map
          (Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec.restrictAssignment hΓΩ) := by
            symm
            exact limitMarginal_toPMF_map_restrictAssignment (Atom := Atom) (μ := ν₁) hΓΩ
      _ =
        ((Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν₂ : Measure (InfiniteWorld Atom)) Ω).toPMF).map
          (Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec.restrictAssignment hΓΩ) := by
            rw [hpmfΩ]
      _ =
        (Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
          (ν₂ : Measure (InfiniteWorld Atom)) Γ).toPMF := by
            exact limitMarginal_toPMF_map_restrictAssignment (Atom := Atom) (μ := ν₂) hΓΩ
  have hlim :
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₁ : Measure (InfiniteWorld Atom)) Γ =
      Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        (ν₂ : Measure (InfiniteWorld Atom)) Γ := by
    simpa [MeasureTheory.Measure.toPMF_toMeasure] using congrArg PMF.toMeasure hpmfΓ
  unfold ClassicalInfiniteGroundMLNSpec.finiteRegionLocalQueryDiscrepancy
  have hquery :=
    congrArg
      (fun ρ : Measure (LocalAssignment Atom Γ) =>
        ENNReal.toReal (ρ (localConstraintSet Γ q))) hlim
  have hquery' :
      ((ν₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ q)).toReal =
        ((ν₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ q)).toReal := by
    simpa [Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal_apply_localConstraintSet]
      using hquery
  rw [abs_eq_zero]
  exact sub_eq_zero.mpr hquery'

/-- Explicit-constant version of approximate preservation under rewriting.

If the two specifications agree on the `n`-shell around `Γ`, and both admit the
same uniform Dobrushin bound `C`, then a `Γ`-query can drift only by the
geometric tail coming from the unresolved exterior.  This first theorem uses a
    shell comparison through a shared finite-volume shell, so the constant is
`2 * |Γ| * C^n`. -/
theorem DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicTranscendenceStep M₁ M₂)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound₁ : ∀ Δ : Region Atom, M₁.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (hC_bound₂ : ∀ Δ : Region Atom, M₂.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.queryRegion) :
    |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
      ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
        2 * (step.queryRegion.card : ℝ) * C ^ step.shellDepth := by
  let Γ := step.queryRegion
  let n := step.shellDepth
  by_cases hΓ : step.queryRegion.card = 0
  · -- Empty query region ⟹ q = [] ⟹ both probabilities = 1
    have hq_nil : q = [] := by
      by_contra h
      rcases List.exists_mem_of_ne_nil q h with ⟨p, hp⟩
      have hmem := hq p hp
      rw [Finset.card_eq_zero.mp hΓ] at hmem
      simp at hmem
    rw [hq_nil]
    rw [show ((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb []) = 1 from
      infiniteMLNMassSemantics_queryProb_empty_eq_one M₁ μ₁ hμ₁]
    rw [show ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb []) = 1 from
      infiniteMLNMassSemantics_queryProb_empty_eq_one M₂ μ₂ hμ₂]
    simp [hΓ]
  · have hΓne : Γ.Nonempty := by
      rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hΓ) with ⟨a, ha⟩
      exact ⟨a, ha⟩
    let Ω := M₁.iterExpandRegion Γ n
    let qΓ : LocalConstraintQuery Atom Γ := restrictQueryToRegion Γ q hq
    let ξ₀ : BoundaryCondition Atom := fun _ => false
    let N₁ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    let N₂ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
    let hZ₁ :=
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ₀
    let hZ₂ :=
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Ω ξ₀
    let ν₁ : ProbabilityMeasure (InfiniteWorld Atom) := ⟨finiteVolumeWorldMeasure N₁ Ω ξ₀ hZ₁, inferInstance⟩
    let ν₂ : ProbabilityMeasure (InfiniteWorld Atom) := ⟨finiteVolumeWorldMeasure N₂ Ω ξ₀ hZ₂, inferInstance⟩
    have hΓΩ : Γ ⊆ Ω := by
      intro a ha
      exact iterExpandRegion_mono M₁ Γ (show 0 ≤ n by exact Nat.zero_le _) ha
    have hΩeq :
        M₂.iterExpandRegion Γ n = Ω := by
      simpa [Ω] using
        (iterExpandRegion_eq_of_specAgreesOnRegion_prefix
          step.shell_agreement (by intro a ha; exact ha) n le_rfl)
    have hμ₁_on :
        FixedRegionCylinderDLR_on M₁.toStrictlyPositiveInfiniteGroundMLNSpec
          (μ₁ : Measure (InfiniteWorld Atom)) Ω :=
      FixedRegionCylinderDLR_on_of_full _ _ hμ₁ Ω
    have hμ₂_on :
        FixedRegionCylinderDLR_on M₂.toStrictlyPositiveInfiniteGroundMLNSpec
          (μ₂ : Measure (InfiniteWorld Atom)) Ω :=
      FixedRegionCylinderDLR_on_of_full _ _ hμ₂ Ω
    have hν₁_on :
        FixedRegionCylinderDLR_on M₁.toStrictlyPositiveInfiniteGroundMLNSpec
          (ν₁ : Measure (InfiniteWorld Atom)) Ω := by
      simpa [ν₁, N₁, hZ₁] using
        finiteVolumeWorldMeasure_fixedRegionCylinderDLR_on
          M₁.toStrictlyPositiveInfiniteGroundMLNSpec Ω ξ₀
    have hν₂_on :
        FixedRegionCylinderDLR_on M₂.toStrictlyPositiveInfiniteGroundMLNSpec
          (ν₂ : Measure (InfiniteWorld Atom)) Ω := by
      simpa [ν₂, N₂, hZ₂] using
        finiteVolumeWorldMeasure_fixedRegionCylinderDLR_on
          M₂.toStrictlyPositiveInfiniteGroundMLNSpec Ω ξ₀
    have hleft :
        M₁.finiteRegionLocalQueryDiscrepancy μ₁ ν₁ Γ qΓ ≤
          (Γ.card : ℝ) * C ^ n := by
      exact localQueryDiscrepancy_le_card_mul_pow_on
        (M := M₁) hC_nonneg hC_lt_one hC_bound₁ μ₁ ν₁ hμ₁_on hν₁_on Γ qΓ n
        (by intro a ha; exact ha)
    have hright :
        M₂.finiteRegionLocalQueryDiscrepancy μ₂ ν₂ Γ qΓ ≤
          (Γ.card : ℝ) * C ^ n := by
      exact localQueryDiscrepancy_le_card_mul_pow_on
        (M := M₂) hC_nonneg hC_lt_one hC_bound₂ μ₂ ν₂ hμ₂_on hν₂_on Γ qΓ n
        (by
          intro a ha
          simpa [Ω, hΩeq] using ha)
    have hmid :
        M₁.finiteRegionLocalQueryDiscrepancy ν₁ ν₂ Γ qΓ = 0 := by
      simpa [Ω, N₁, N₂, ν₁, ν₂, hZ₁, hZ₂] using
        finiteVolume_localQueryDiscrepancy_eq_zero_of_specAgreesOnRegion
          step.shell_agreement hΓΩ
          (show Ω.Nonempty from ⟨hΓne.choose, hΓΩ hΓne.choose_spec⟩)
          ξ₀ qΓ
    have hEvent :
        infiniteQueryEvent q = localQueryEvent Γ qΓ := by
      simpa [Γ, qΓ] using
        infiniteQueryEvent_eq_localQueryEvent_restrictQueryToRegion q hq
    have hp₁ :
        ((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal =
          ((μ₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ)).toReal := by
      unfold MassSemantics.queryProb infiniteMLNMassSemantics
      rw [if_neg (by simp), div_one]
      have hmeasureEvent :
          (μ₁ : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q) =
            (μ₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) := by
        exact congrArg (fun S => (μ₁ : Measure (InfiniteWorld Atom)) S) hEvent
      exact congrArg ENNReal.toReal hmeasureEvent
    have hp₂ :
        ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal =
          ((μ₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ)).toReal := by
      unfold MassSemantics.queryProb infiniteMLNMassSemantics
      rw [if_neg (by simp), div_one]
      have hmeasureEvent :
          (μ₂ : Measure (InfiniteWorld Atom)) (infiniteQueryEvent q) =
            (μ₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) := by
        exact congrArg (fun S => (μ₂ : Measure (InfiniteWorld Atom)) S) hEvent
      exact congrArg ENNReal.toReal hmeasureEvent
    let a : ℝ := ((μ₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ)).toReal
    let b : ℝ := ((ν₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ)).toReal
    let c : ℝ := ((ν₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ)).toReal
    let d : ℝ := ((μ₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ)).toReal
    have hab : |a - b| ≤ (Γ.card : ℝ) * C ^ n := by
      simpa [a, b, ν₁, ClassicalInfiniteGroundMLNSpec.finiteRegionLocalQueryDiscrepancy]
        using hleft
    have hbc : |b - c| = 0 := by
      simpa [b, c, ν₁, ν₂, ClassicalInfiniteGroundMLNSpec.finiteRegionLocalQueryDiscrepancy]
        using hmid
    have hcd : |c - d| ≤ (Γ.card : ℝ) * C ^ n := by
      simpa [c, d, ν₂, ClassicalInfiniteGroundMLNSpec.finiteRegionLocalQueryDiscrepancy,
        abs_sub_comm]
        using hright
    have htri₁ : |a - d| ≤ |a - b| + |b - d| := by
      calc
        |a - d| = |(a - b) + (b - d)| := by ring_nf
        _ ≤ |a - b| + |b - d| := abs_add_le _ _
    have htri₂ : |b - d| ≤ |b - c| + |c - d| := by
      calc
        |b - d| = |(b - c) + (c - d)| := by ring_nf
        _ ≤ |b - c| + |c - d| := abs_add_le _ _
    rw [hp₁, hp₂]
    have hbound :
        |a - d| ≤ ((Γ.card : ℝ) * C ^ n) + (0 + ((Γ.card : ℝ) * C ^ n)) := by
      linarith [htri₁, htri₂, hab, hbc, hcd]
    calc
      |a - d| ≤ ((Γ.card : ℝ) * C ^ n) + (0 + ((Γ.card : ℝ) * C ^ n)) := hbound
      _ = 2 * (Γ.card : ℝ) * C ^ n := by ring

/-- Budget-packaged dynamic self-transcendence theorem. -/
theorem DynamicTranscendenceStep.queryProb_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicTranscendenceStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.queryRegion) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
        ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
          2 * (step.queryRegion.card : ℝ) * C ^ step.shellDepth := by
  rcases M₁.finiteRegionPairwiseDobrushinConstant_le_uniform step.budget₁ with
    ⟨C₁, hC₁_nonneg, hC₁_lt_one, hC₁_bound⟩
  rcases M₂.finiteRegionPairwiseDobrushinConstant_le_uniform step.budget₂ with
    ⟨C₂, hC₂_nonneg, hC₂_lt_one, hC₂_bound⟩
  refine ⟨max C₁ C₂, le_trans hC₁_nonneg (le_max_left _ _), ?_, ?_⟩
  · exact max_lt_iff.mpr ⟨hC₁_lt_one, hC₂_lt_one⟩
  · exact DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
      (step := step)
      (C := max C₁ C₂)
      (hC_nonneg := le_trans hC₁_nonneg (le_max_left _ _))
      (hC_lt_one := max_lt_iff.mpr ⟨hC₁_lt_one, hC₂_lt_one⟩)
      (hC_bound₁ := by
        intro Δ
        exact le_trans (hC₁_bound Δ) (le_max_left _ _))
      (hC_bound₂ := by
        intro Δ
        exact le_trans (hC₂_bound Δ) (le_max_right _ _))
      μ₁ μ₂ hμ₁ hμ₂ q hq

end Mettapedia.Logic.MarkovLogicDynamicTranscendence
