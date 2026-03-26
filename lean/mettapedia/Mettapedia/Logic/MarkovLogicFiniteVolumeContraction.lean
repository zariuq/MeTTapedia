import Mettapedia.Logic.MarkovLogicInfiniteUniqueness

/-!
# Finite-Volume Contraction (Restricted DLR Coupling)

The coupling descent in `MarkovLogicInfiniteUniqueness` proves that any two
DLR measures of the same spec have geometrically decaying marginal disagreement.
That proof requires `FixedRegionCylinderDLR`, which is universally quantified
over ALL finite regions.

This module provides a **restricted** version: the DLR equation need only hold
for kernel regions `Λ ⊆ Ω` (a fixed bounding region).  The key application is
to finite-volume world measures, which satisfy the DLR equation on subregions
(by `finiteVolumeWorldMeasure_subregion_cylinder_dlr`) but NOT on regions
extending beyond their support.

The main result is an assignment total-variation bound for the finite-volume
Gibbs kernel: changing the boundary condition at distance `n` from a query
region `Γ` shifts the Γ-marginal TV by at most `|Γ| · C^n`.  The standard
event-disagreement coupling bridge then gives query oscillation
`≤ |Γ| · C^n`.
-/

namespace Mettapedia.Logic.MarkovLogicFiniteVolumeContraction

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteLimitFamily.RegionExhaustion
open MeasureTheory
open scoped ENNReal

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Restricted DLR: the DLR equation holds for kernel regions `Λ ⊆ Ω`. -/
def FixedRegionCylinderDLR_on
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ]
    (Ω : Region Atom) : Prop :=
  ∀ (Λ I : Region Atom), Λ ⊆ Ω →
    ∀ (S : Set (LocalAssignment Atom I)),
    MeasurableSet S →
      ∫⁻ ω, M.finiteVolumeWorldMeasure Λ ω (MeasureTheory.cylinder I S) ∂ μ =
        μ (MeasureTheory.cylinder I S)

/-- The full DLR implies the restricted DLR. -/
theorem FixedRegionCylinderDLR_on_of_full
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ]
    (hμ : FixedRegionCylinderDLR M μ)
    (Ω : Region Atom) :
    FixedRegionCylinderDLR_on M μ Ω := by
  intro Λ I _ S hS
  exact hμ Λ I S hS

/-- The finite-volume world measure satisfies the restricted DLR on subregions. -/
theorem finiteVolumeWorldMeasure_fixedRegionCylinderDLR_on
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (Ω : Region Atom) (ξ : BoundaryCondition Atom) :
    FixedRegionCylinderDLR_on M (M.finiteVolumeWorldMeasure Ω ξ) Ω := by
  intro Λ I hΛΩ S hS
  exact finiteVolumeWorldMeasure_subregion_cylinder_dlr M hΛΩ ξ I S hS

/-- Single-site heat-bath fixed point under restricted DLR.

    This is the restricted version of
    `limitMarginal_toPMF_singleSiteHeatBathUpdatePMF_eq_of_interior`:
    the DLR equation need only hold for the singleton `{i.1}` as
    kernel region, which is guaranteed by `FixedRegionCylinderDLR_on`
    when `{i.1} ⊆ Ω`. -/
theorem limitMarginal_toPMF_singleSiteHeatBathUpdatePMF_eq_of_interior_on
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (i : RegionAtom Atom Δ)
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom))
    [hprob : IsProbabilityMeasure μ]
    {Ω : Region Atom}
    (hμ : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec μ Ω)
    (hi_in_Ω : ({i.1} : Region Atom) ⊆ Ω)
    (hi_nbhd : M.atomInteractionNeighborhood i.1 ⊆ Δ) :
    M.singleSiteHeatBathUpdatePMF i ξ (limitMarginal μ Δ).toPMF =
      (limitMarginal μ Δ).toPMF := by
  -- The proof is identical to the original except we use hμ restricted to {i.1}
  let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
  let pμ := (limitMarginal μ Δ).toPMF
  ext y
  have hsingleton : MeasurableSet ({y} : Set (LocalAssignment Atom Δ)) :=
    MeasurableSet.singleton y
  have hupdate :=
    M.singleSiteHeatBathUpdatePMF_toMeasure_apply i ξ pμ ({y} : Set (LocalAssignment Atom Δ))
      hsingleton
  rw [tsum_fintype] at hupdate
  -- The restricted DLR equation for {i.1} ⊆ Ω
  have hdlr :
      ∫⁻ ω,
        M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) ω
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
        ∂ μ =
        μ (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) :=
    hμ ({i.1} : Region Atom) Δ hi_in_Ω
      ({y} : Set (LocalAssignment Atom Δ)) hsingleton
  -- The rest is identical to the original proof
  have hdlr_sum :
      ∑ b, pμ b *
        (M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) (patch Δ b ξ))
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) =
        pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) := by
    let f : LocalAssignment Atom Δ → ENNReal := fun b =>
      (M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) (patch Δ b ξ))
        (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
    let J : Region Atom :=
      cylinderBoundarySupportRegion M'.toInfiniteGroundMLNSpec ({i.1} : Region Atom) Δ
    have hsum_as_lintegral :
        ∑ b, pμ b * f b = ∫⁻ b, f b ∂ pμ.toMeasure := by
      calc
        ∑ b, pμ b * f b
            = ∑ b, f b * pμ.toMeasure ({b} : Set (LocalAssignment Atom Δ)) := by
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
        _ = ∫⁻ b, f b ∂ pμ.toMeasure := by
                symm
                exact MeasureTheory.lintegral_fintype (μ := pμ.toMeasure) f
    have hboundaryEq :
        boundaryClauseSupportRegion M'.toInfiniteGroundMLNSpec ({i.1} : Region Atom) =
          M.atomInteractionNeighborhood i.1 := by
      simpa [M'] using
        M.boundaryClauseSupportRegion_singleton_eq_atomInteractionNeighborhood i.1
    have hJsubset : J ⊆ Δ := by
      intro a ha
      have ha' :
          a ∈ M.atomInteractionNeighborhood i.1 ∪ outsideRegion ({i.1} : Region Atom) Δ := by
        simpa [J, cylinderBoundarySupportRegion, hboundaryEq] using ha
      rcases Finset.mem_union.mp ha' with ha_nbhd | ha_out
      · exact hi_nbhd ha_nbhd
      · have ha_out' : a ∈ Δ \ ({i.1} : Region Atom) := by
          simpa [outsideRegion] using ha_out
        exact (Finset.mem_sdiff.mp ha_out').1
    have hrestrict_patch :
        ∀ ω : InfiniteWorld Atom,
          Finset.restrict J (patch Δ (Finset.restrict Δ ω) ξ) =
            Finset.restrict J ω := by
      intro ω
      funext a
      have haΔ : a.1 ∈ Δ := hJsubset a.2
      simp [J, patch, haΔ]
    have hboundary :
        ∀ ω : InfiniteWorld Atom,
          f (Finset.restrict Δ ω) =
            M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) ω
              (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
      intro ω
      show f (Finset.restrict Δ ω) = _
      dsimp only [f]
      exact
        (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure_cylinder_eq_of_restrict_cylinderBoundarySupportRegion_eq'
            (M := M') (Λ := ({i.1} : Region Atom)) (I := Δ)
            (S := ({y} : Set (LocalAssignment Atom Δ))) hsingleton
            (ξ₁ := patch Δ (Finset.restrict Δ ω) ξ) (ξ₂ := ω)
            (by simpa [J] using hrestrict_patch ω))
    have hrhs :
        pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) =
          μ (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
      calc
        pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ))
            = (limitMarginal μ Δ) ({y} : Set (LocalAssignment Atom Δ)) := by
              simp [pμ, MeasureTheory.Measure.toPMF_toMeasure]
        _ = μ ((Finset.restrict Δ) ⁻¹' ({y} : Set (LocalAssignment Atom Δ))) := by
              rw [limitMarginal]
              rw [MeasureTheory.Measure.map_apply (Finset.measurable_restrict Δ) hsingleton]
        _ = μ (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := by
              congr 1
    calc
      ∑ b, pμ b *
        (M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) (patch Δ b ξ))
          (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
          = ∫⁻ b, f b ∂ pμ.toMeasure := by
              simpa [f] using hsum_as_lintegral
      _ =
        ∫⁻ b, f b
          ∂ (limitMarginal μ Δ) := by
              simp [pμ, MeasureTheory.Measure.toPMF_toMeasure]
      _ =
        ∫⁻ ω, f (Finset.restrict Δ ω) ∂ μ := by
              simpa [limitMarginal] using
                (MeasureTheory.lintegral_map
                  (μ := μ)
                  (f := f)
                  (g := Finset.restrict Δ)
                  (Measurable.of_discrete)
                  (Finset.measurable_restrict Δ))
      _ =
        ∫⁻ ω,
          M'.finiteVolumeWorldMeasure ({i.1} : Region Atom) ω
            (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ)))
          ∂ μ := by
              exact MeasureTheory.lintegral_congr (fun ω => hboundary ω)
      _ = μ (MeasureTheory.cylinder Δ ({y} : Set (LocalAssignment Atom Δ))) := hdlr
      _ = pμ.toMeasure ({y} : Set (LocalAssignment Atom Δ)) := hrhs.symm
  rw [hdlr_sum] at hupdate
  simpa [pμ, PMF.toMeasure_apply_singleton] using hupdate

/-- Partial heat-bath sweep preserves the limit marginal under restricted DLR. -/
theorem limitMarginal_toPMF_partialHeatBathSweepPMF_eq_of_interiorList_on
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Δ : Region Atom}
    (l : List (RegionAtom Atom Δ))
    (ξ : BoundaryCondition Atom)
    (μ : Measure (InfiniteWorld Atom))
    [IsProbabilityMeasure μ]
    {Ω : Region Atom}
    (hμ : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec μ Ω)
    (hl : ∀ i ∈ l, M.atomInteractionNeighborhood i.1 ⊆ Δ)
    (hl_Ω : ∀ i ∈ l, ({i.1} : Region Atom) ⊆ Ω) :
    l.foldl (fun r i => M.singleSiteHeatBathUpdatePMF i ξ r)
      (limitMarginal μ Δ).toPMF =
      (limitMarginal μ Δ).toPMF := by
  induction l with
  | nil => rfl
  | cons i is ih =>
      have hi_nbhd : M.atomInteractionNeighborhood i.1 ⊆ Δ := by
        exact hl i (by simp)
      have hi_Ω : ({i.1} : Region Atom) ⊆ Ω := hl_Ω i (by simp)
      have his : ∀ j ∈ is, M.atomInteractionNeighborhood j.1 ⊆ Δ := by
        intro j hj; exact hl j (by simp [hj])
      have his_Ω : ∀ j ∈ is, ({j.1} : Region Atom) ⊆ Ω := by
        intro j hj; exact hl_Ω j (by simp [hj])
      simp [List.foldl]
      rw [limitMarginal_toPMF_singleSiteHeatBathUpdatePMF_eq_of_interior_on
        M i ξ μ hμ hi_Ω hi_nbhd]
      simpa using ih his his_Ω

private theorem iterExpandRegion_expandRegion_comm
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (n : ℕ) :
    M.iterExpandRegion (M.expandRegion Λ) n = M.iterExpandRegion Λ (n + 1) := by
  induction n with
  | zero => simp [iterExpandRegion]
  | succ n ih => simp [iterExpandRegion, ih]

private theorem subset_iterExpandRegion
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (n : ℕ) :
    Λ ⊆ M.iterExpandRegion Λ n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
      calc Λ ⊆ M.iterExpandRegion Λ n := ih
        _ ⊆ M.expandRegion (M.iterExpandRegion Λ n) := M.subset_expandRegion _
        _ = M.iterExpandRegion Λ (n + 1) := by simp [iterExpandRegion]

/-- Descending-shell coupling bound under restricted DLR.

    This is the restricted version of
    `exists_limitMarginalCoupling_sup_le_pow_of_uniformConstant`:
    the DLR equation need only hold on subregions of `Ω`, sufficient
    for finite-volume world measures. The extra hypothesis
    `iterExpandRegion Λ n ⊆ Ω` ensures all swept sites are in `Ω`. -/
theorem exists_limitMarginalCoupling_sup_le_pow_on
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    {Ω : Region Atom}
    (hμ : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)) Ω)
    (hν : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)) Ω)
    (ξ : BoundaryCondition Atom) :
    ∀ n : ℕ, ∀ Λ : Region Atom, M.iterExpandRegion Λ n ⊆ Ω →
      ∃ q : PMF (LocalAssignment Atom Λ × LocalAssignment Atom Λ),
        q.map Prod.fst =
            (limitMarginal (μ : Measure (InfiniteWorld Atom)) Λ).toPMF ∧
          q.map Prod.snd =
            (limitMarginal (ν : Measure (InfiniteWorld Atom)) Λ).toPMF ∧
          finiteRegionSupSeminorm Λ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) ≤ C ^ n := by
  intro n
  induction n with
  | zero =>
      intro Λ _
      let pμ := (limitMarginal (μ : Measure (InfiniteWorld Atom)) Λ).toPMF
      let pν := (limitMarginal (ν : Measure (InfiniteWorld Atom)) Λ).toPMF
      refine ⟨pmfMaximalCoupling pμ pν, ?_, ?_, ?_⟩
      · exact pmfMaximalCoupling_map_fst pμ pν
      · exact pmfMaximalCoupling_map_snd pμ pν
      · calc
          finiteRegionSupSeminorm Λ
              (finiteRegionCouplingExpectedDisagreement (Atom := Atom)
                (pmfMaximalCoupling pμ pν))
            ≤ finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom)
                (pmfMaximalCoupling pμ pν) := by
                  exact
                    finiteRegionSupSeminorm_finiteRegionCouplingExpectedDisagreement_le_assignmentDisagreementProbability
                      (Atom := Atom) (pmfMaximalCoupling pμ pν)
          _ = pmfTotalVariation pμ pν := by
                unfold finiteRegionCouplingAssignmentDisagreementProbability
                simpa using pmfMaximalCoupling_disagreementProbability_eq_totalVariation pμ pν
          _ ≤ 1 := pmfTotalVariation_le_one pμ pν
          _ = C ^ 0 := by simp
  | succ n ih =>
      intro Λ hΛΩ
      let Δ := M.expandRegion Λ
      let hΛΔ : Λ ⊆ Δ := M.subset_expandRegion Λ
      -- iterExpandRegion Λ (n+1) = iterExpandRegion (expandRegion Λ) n
      have hΔΩ : M.iterExpandRegion Δ n ⊆ Ω := by
        calc M.iterExpandRegion Δ n
            = M.iterExpandRegion Λ (n + 1) :=
                iterExpandRegion_expandRegion_comm M Λ n
          _ ⊆ Ω := hΛΩ
      rcases ih Δ hΔΩ with ⟨qΔ, hqfstΔ, hqsndΔ, hsupΔ⟩
      let emb : RegionAtom Atom Λ → RegionAtom Atom Δ := fun a => ⟨a.1, hΛΔ a.2⟩
      let lset : Finset (RegionAtom Atom Δ) := Λ.attach.image emb
      let l : List (RegionAtom Atom Δ) := lset.toList
      have hNodup : l.Nodup := by
        simpa [l] using lset.nodup_toList
      have hl_interior : ∀ i ∈ l, M.atomInteractionNeighborhood i.1 ⊆ Δ := by
        intro i hi
        have hi' : i ∈ lset := by simpa [l] using hi
        rcases Finset.mem_image.mp hi' with ⟨a, ha, rfl⟩
        simpa [Δ, iterExpandRegion] using
          (M.atomInteractionNeighborhood_subset_iterExpandRegion_succ
            (Λ := Λ) (n := 0) a.2)
      -- Sites swept are in Λ ⊆ iterExpandRegion Λ (n+1) ⊆ Ω
      have hl_Ω : ∀ i ∈ l, ({i.1} : Region Atom) ⊆ Ω := by
        intro i hi
        have hi' : i ∈ lset := by simpa [l] using hi
        rcases Finset.mem_image.mp hi' with ⟨a, _, rfl⟩
        intro x hx
        simp at hx
        rw [hx]
        exact hΛΩ (subset_iterExpandRegion M Λ (n + 1) a.2)
      let qs := M.partialHeatBathSweepCouplingPMF l ξ qΔ
      let qΛ := projectCouplingToSubregion hΛΔ qs
      have hfst_qs :
          qs.map Prod.fst =
            (limitMarginal (μ : Measure (InfiniteWorld Atom)) Δ).toPMF := by
        dsimp [qs]
        rw [M.partialHeatBathSweepCouplingPMF_map_fst]
        rw [hqfstΔ]
        exact limitMarginal_toPMF_partialHeatBathSweepPMF_eq_of_interiorList_on
          M l ξ (μ : Measure _) hμ hl_interior hl_Ω
      have hsnd_qs :
          qs.map Prod.snd =
            (limitMarginal (ν : Measure (InfiniteWorld Atom)) Δ).toPMF := by
        dsimp [qs]
        rw [M.partialHeatBathSweepCouplingPMF_map_snd]
        rw [hqsndΔ]
        exact limitMarginal_toPMF_partialHeatBathSweepPMF_eq_of_interiorList_on
          M l ξ (ν : Measure _) hν hl_interior hl_Ω
      have hfst_qΛ :
          qΛ.map Prod.fst =
            (limitMarginal (μ : Measure (InfiniteWorld Atom)) Λ).toPMF := by
        dsimp [qΛ]
        rw [projectCouplingToSubregion_map_fst]
        rw [hfst_qs]
        exact limitMarginal_toPMF_map_restrictAssignment (Atom := Atom) μ hΛΔ
      have hsnd_qΛ :
          qΛ.map Prod.snd =
            (limitMarginal (ν : Measure (InfiniteWorld Atom)) Λ).toPMF := by
        dsimp [qΛ]
        rw [projectCouplingToSubregion_map_snd]
        rw [hsnd_qs]
        exact limitMarginal_toPMF_map_restrictAssignment (Atom := Atom) ν hΛΔ
      have hs_nonneg : 0 ≤ C ^ n := by exact pow_nonneg hC_nonneg n
      have hs : ∀ a ∈ Δ,
          finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΔ a ≤ C ^ n := by
        intro a ha
        exact le_trans
          (le_finiteRegionSupSeminorm
            (Λ := Δ)
            (d := finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΔ) ha)
          hsupΔ
      have hconst_le_one : M.finiteRegionPairwiseDobrushinConstant Δ ≤ 1 := by
        exact le_trans (hC_bound Δ) (le_of_lt hC_lt_one)
      have hcontrol :=
        M.finiteRegionCouplingExpectedDisagreement_foldl_singleSiteHeatBathUpdateCoupling_control
          (Δ := Δ) (l := l) hNodup ξ qΔ (C ^ n) hs_nonneg hs hconst_le_one
      rcases hcontrol with ⟨_, hupdated, _⟩
      have hsup_qΛ :
          finiteRegionSupSeminorm Λ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΛ) ≤ C ^ (n + 1) := by
        refine finiteRegionSupSeminorm_le_of_bound
          (c := C ^ (n + 1))
          (pow_nonneg hC_nonneg (n + 1)) ?_
        intro a ha
        let aΛ : RegionAtom Atom Λ := ⟨a, ha⟩
        let aΔ : RegionAtom Atom Δ := emb aΛ
        have ha_mem_lset : aΔ ∈ lset := by
          refine Finset.mem_image.mpr ?_
          exact ⟨aΛ, by simp [aΔ, emb]⟩
        have ha_mem_l : aΔ ∈ l := by
          simpa [l] using ha_mem_lset
        calc
          finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΛ a
            = finiteRegionCouplingExpectedDisagreement (Atom := Atom) qs a := by
                simpa [qΛ, qs] using
                  (finiteRegionCouplingExpectedDisagreement_projectCoupling_eq
                    (Atom := Atom) hΛΔ qs a ha)
          _ ≤ M.finiteRegionPairwiseDobrushinConstant Δ * C ^ n := by
                simpa [qs] using hupdated aΔ ha_mem_l
          _ ≤ C * C ^ n := by
                exact mul_le_mul_of_nonneg_right (hC_bound Δ) hs_nonneg
          _ = C ^ (n + 1) := by
                simp [pow_succ, mul_comm]
      exact ⟨qΛ, hfst_qΛ, hsnd_qΛ, hsup_qΛ⟩

/-- Finite-volume TV bound: two finite-volume measures on `Ω` with different
    boundary conditions have Γ-marginal assignment TV ≤ |Γ|·C^n, where
    Γ is n shells deep in Ω = iterExpandRegion Γ n. -/
theorem finiteVolume_assignmentTotalVariation_le_card_mul_pow
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (Γ : Region Atom)
    (n : ℕ)
    (ξ₁ ξ₂ : BoundaryCondition Atom) :
    let Ω := M.iterExpandRegion Γ n
    let M' := M.toStrictlyPositiveInfiniteGroundMLNSpec
    M.finiteRegionAssignmentTotalVariation
      ⟨M'.finiteVolumeWorldMeasure Ω ξ₁, inferInstance⟩
      ⟨M'.finiteVolumeWorldMeasure Ω ξ₂, inferInstance⟩
      Γ ≤ (Γ.card : ℝ) * C ^ n := by
  intro Ω M'
  have hμ := finiteVolumeWorldMeasure_fixedRegionCylinderDLR_on
    M' Ω ξ₁
  have hν := finiteVolumeWorldMeasure_fixedRegionCylinderDLR_on
    M' Ω ξ₂
  rcases exists_limitMarginalCoupling_sup_le_pow_on M hC_nonneg hC_lt_one hC_bound
    ⟨M'.finiteVolumeWorldMeasure Ω ξ₁, inferInstance⟩
    ⟨M'.finiteVolumeWorldMeasure Ω ξ₂, inferInstance⟩
    hμ hν (fun _ => false) n Γ (Finset.Subset.refl _) with
    ⟨q, hqfst, hqsnd, hsup⟩
  calc
    M.finiteRegionAssignmentTotalVariation
      ⟨M'.finiteVolumeWorldMeasure Ω ξ₁, inferInstance⟩
      ⟨M'.finiteVolumeWorldMeasure Ω ξ₂, inferInstance⟩ Γ
      ≤ (Γ.card : ℝ) *
          finiteRegionSupSeminorm Γ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
            exact M.finiteRegionAssignmentTotalVariation_le_card_mul_sup_of_limitMarginalCoupling
              ⟨_, inferInstance⟩ ⟨_, inferInstance⟩ Γ q hqfst hqsnd
    _ ≤ (Γ.card : ℝ) * C ^ n := by
          exact mul_le_mul_of_nonneg_left hsup (by positivity)

/-- Restricted-DLR shell bound for arbitrary measures on a common bounding
region `Ω`.  This is the reusable finite-volume comparison interface needed
to compare an infinite DLR measure with a finite-volume Gibbs measure on the
same shell. -/
theorem assignmentTotalVariation_le_card_mul_pow_on
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    {Ω : Region Atom}
    (hμ : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)) Ω)
    (hν : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)) Ω)
    (Γ : Region Atom)
    (n : ℕ)
    (hΓΩ : M.iterExpandRegion Γ n ⊆ Ω) :
    M.finiteRegionAssignmentTotalVariation μ ν Γ ≤ (Γ.card : ℝ) * C ^ n := by
  rcases exists_limitMarginalCoupling_sup_le_pow_on M hC_nonneg hC_lt_one hC_bound
    μ ν hμ hν (fun _ => false) n Γ hΓΩ with
    ⟨q, hqfst, hqsnd, hsup⟩
  calc
    M.finiteRegionAssignmentTotalVariation μ ν Γ
      ≤ (Γ.card : ℝ) *
          finiteRegionSupSeminorm Γ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) q) := by
            exact M.finiteRegionAssignmentTotalVariation_le_card_mul_sup_of_limitMarginalCoupling
              μ ν Γ q hqfst hqsnd
    _ ≤ (Γ.card : ℝ) * C ^ n := by
          exact mul_le_mul_of_nonneg_left hsup (by positivity)

/-- Restricted-DLR shell bound for local queries on a common bounding region
`Ω`. -/
theorem localQueryDiscrepancy_le_card_mul_pow_on
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    {Ω : Region Atom}
    (hμ : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)) Ω)
    (hν : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)) Ω)
    (Γ : Region Atom)
    (q : LocalConstraintQuery Atom Γ)
    (n : ℕ)
    (hΓΩ : M.iterExpandRegion Γ n ⊆ Ω) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Γ q ≤ (Γ.card : ℝ) * C ^ n := by
  rcases exists_limitMarginalCoupling_sup_le_pow_on M hC_nonneg hC_lt_one hC_bound
    μ ν hμ hν (fun _ => false) n Γ hΓΩ with
    ⟨qΓ, hqfst, hqsnd, hsup⟩
  calc
    M.finiteRegionLocalQueryDiscrepancy μ ν Γ q
      ≤ finiteRegionCouplingAssignmentDisagreementProbability (Atom := Atom) qΓ := by
          exact
            M.finiteRegionLocalQueryDiscrepancy_le_couplingAssignmentDisagreementProbability
              μ ν Γ q qΓ hqfst hqsnd
    _ ≤ finiteRegionCouplingExpectedHammingDisagreement (Atom := Atom) qΓ := by
          exact finiteRegionCouplingAssignmentDisagreementProbability_le_expectedHamming
            (Atom := Atom) qΓ
    _ ≤ (Γ.card : ℝ) *
          finiteRegionSupSeminorm Γ
            (finiteRegionCouplingExpectedDisagreement (Atom := Atom) qΓ) := by
          exact finiteRegionCouplingExpectedHammingDisagreement_le_card_mul_sup
            (Atom := Atom) qΓ
    _ ≤ (Γ.card : ℝ) * C ^ n := by
          exact mul_le_mul_of_nonneg_left hsup (by positivity)

/-- Coarser restricted-DLR shell bound retained for compatibility. -/
theorem localQueryDiscrepancy_le_two_mul_card_mul_pow_on
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC_lt_one : C < 1)
    (hC_bound : ∀ Δ : Region Atom, M.finiteRegionPairwiseDobrushinConstant Δ ≤ C)
    (μ ν : ProbabilityMeasure (InfiniteWorld Atom))
    {Ω : Region Atom}
    (hμ : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld Atom)) Ω)
    (hν : FixedRegionCylinderDLR_on M.toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld Atom)) Ω)
    (Γ : Region Atom)
    (q : LocalConstraintQuery Atom Γ)
    (n : ℕ)
    (hΓΩ : M.iterExpandRegion Γ n ⊆ Ω) :
    M.finiteRegionLocalQueryDiscrepancy μ ν Γ q ≤ 2 * (Γ.card : ℝ) * C ^ n := by
  calc
    M.finiteRegionLocalQueryDiscrepancy μ ν Γ q
      ≤ (Γ.card : ℝ) * C ^ n := by
          exact localQueryDiscrepancy_le_card_mul_pow_on
            (M := M) hC_nonneg hC_lt_one hC_bound μ ν hμ hν Γ q n hΓΩ
    _ ≤ 2 * (Γ.card : ℝ) * C ^ n := by
          nlinarith [show 0 ≤ (Γ.card : ℝ) * C ^ n by positivity]

end Mettapedia.Logic.MarkovLogicFiniteVolumeContraction
