import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification

/-!
# Infinite MLN Finite-Volume Query Locality

This module records the first theorem-level facts for the infinite MLN lane:
finite constraint queries are local.  In particular, if all queried atoms lie in
a finite region `Λ`, then evaluating the query on a patched world depends only
on the local assignment on `Λ`, not on the boundary condition outside `Λ`.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume

open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicAbstract
open scoped ENNReal

/-- Local finite constraint queries over a fixed region. -/
abbrev LocalConstraintQuery (Atom : Type*) (Λ : Region Atom) :=
  ConstraintQuery (RegionAtom Atom Λ)

/-- The finite atom support of a finite constraint query. -/
def queryAtoms {Atom : Type*} [DecidableEq Atom]
    (q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom) : Finset Atom :=
  (q.toFinset.image Sigma.fst)

/-- Two infinite worlds agree on a finite atom set. -/
def agreesOnAtoms {Atom : Type*} (S : Finset Atom)
    (ω ξ : InfiniteWorld Atom) : Prop :=
  ∀ a, a ∈ S → ω a = ξ a

theorem infiniteConstraintQueryHolds_congr_of_agreesOnAtoms
    {Atom : Type*} [DecidableEq Atom]
    {q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom}
    {ω ξ : InfiniteWorld Atom}
    (hag : agreesOnAtoms (queryAtoms q) ω ξ) :
    InfiniteGroundMLNSpec.infiniteConstraintQueryHolds q ω ↔
      InfiniteGroundMLNSpec.infiniteConstraintQueryHolds q ξ := by
  unfold InfiniteGroundMLNSpec.infiniteConstraintQueryHolds
  unfold constraintQueryHolds satisfiesConstraints
  constructor
  · intro h c hc
    have hcAtoms : c.1 ∈ queryAtoms q := by
      exact Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hc, rfl⟩
    calc
      ξ c.1 = ω c.1 := (hag c.1 hcAtoms).symm
      _ = c.2 := h c hc
  · intro h c hc
    have hcAtoms : c.1 ∈ queryAtoms q := by
      exact Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hc, rfl⟩
    calc
      ω c.1 = ξ c.1 := hag c.1 hcAtoms
      _ = c.2 := h c hc

theorem infiniteConstraintQueryHolds_patch_boundary_irrelevant
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom)
    (x : LocalAssignment Atom Λ)
    (ξ₁ ξ₂ : BoundaryCondition Atom)
    (q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom)
    (hq : ∀ c ∈ q, c.1 ∈ Λ) :
    InfiniteGroundMLNSpec.infiniteConstraintQueryHolds q (patch Λ x ξ₁) ↔
      InfiniteGroundMLNSpec.infiniteConstraintQueryHolds q (patch Λ x ξ₂) := by
  apply infiniteConstraintQueryHolds_congr_of_agreesOnAtoms
  intro a ha
  obtain ⟨c, hc, hfst⟩ := Finset.mem_image.mp ha
  have hcΛ : c.1 ∈ Λ := hq c (List.mem_toFinset.mp hc)
  subst hfst
  simp [patch, hcΛ]

/-- Restrict an infinite query to a fixed region when all queried atoms lie in
that region. -/
def restrictQueryToRegion
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom)
    (q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom)
    (hq : ∀ c ∈ q, c.1 ∈ Λ) :
    LocalConstraintQuery Atom Λ :=
  q.pmap (fun c hc => ⟨⟨c.1, hc⟩, c.2⟩) (by
    intro c hc
    exact hq c hc)

theorem satisfiesConstraints_restrictQueryToRegion_iff
    {Atom : Type*} [DecidableEq Atom]
    (Λ : Region Atom)
    (x : LocalAssignment Atom Λ)
    (q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom)
    (hq : ∀ c ∈ q, c.1 ∈ Λ)
    (ξ : BoundaryCondition Atom) :
    satisfiesConstraints x (restrictQueryToRegion Λ q hq) ↔
      InfiniteGroundMLNSpec.infiniteConstraintQueryHolds q (patch Λ x ξ) := by
  unfold InfiniteGroundMLNSpec.infiniteConstraintQueryHolds
  unfold satisfiesConstraints constraintQueryHolds restrictQueryToRegion
  constructor
  · intro hx c hc
    have hmem :
        (Sigma.mk ⟨c.1, hq c hc⟩ c.2 : Sigma (fun _ : RegionAtom Atom Λ => Bool)) ∈
          List.pmap (fun c hc => (Sigma.mk ⟨c.1, hc⟩ c.2 : Sigma (fun _ : RegionAtom Atom Λ => Bool))) q (by
        intro c hc
        exact hq c hc) := by
      exact List.mem_pmap.mpr ⟨c, hc, rfl⟩
    have hx' : x ⟨c.1, hq c hc⟩ = c.2 := hx _ hmem
    simpa [patch, hq c hc] using hx'
  · intro hx c hc
    obtain ⟨c', hc', heq⟩ := List.mem_pmap.mp hc
    cases c' with
    | mk a b =>
        cases heq
        simpa [patch, hq ⟨a, b⟩ hc'] using hx ⟨a, b⟩ hc'

/-- Unnormalized finite-volume mass of a local query. -/
noncomputable def finiteVolumeQueryMass
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Λ) : ENNReal :=
  by
    classical
    exact Finset.sum Finset.univ
      (fun x =>
        if satisfiesConstraints x q then
          M.finiteVolumeWeight Λ x ξ
        else 0)

theorem finiteVolumeQueryMass_le_partition
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Λ) :
    finiteVolumeQueryMass M Λ ξ q ≤ M.finiteVolumePartition Λ ξ := by
  classical
  unfold finiteVolumeQueryMass InfiniteGroundMLNSpec.finiteVolumePartition
  refine Finset.sum_le_sum ?_
  intro x hx
  by_cases hsat : satisfiesConstraints x q
  · simp [hsat]
  · simp [hsat]

theorem finiteVolumePartition_ne_top
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    M.finiteVolumePartition Λ ξ ≠ ⊤ := by
  classical
  unfold InfiniteGroundMLNSpec.finiteVolumePartition
  exact (ENNReal.sum_ne_top).2 (by
    intro x hx
    exact M.finiteVolumeWeight_ne_top Λ x ξ)

/-- Local finite-volume probabilities packaged as `MassSemantics`. -/
noncomputable def finiteVolumeMassSemantics
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    MassSemantics (LocalConstraintQuery Atom Λ) where
  queryMass := finiteVolumeQueryMass M Λ ξ
  totalMass := M.finiteVolumePartition Λ ξ
  queryMass_le_total := finiteVolumeQueryMass_le_partition M Λ ξ
  totalMass_ne_top := finiteVolumePartition_ne_top M Λ ξ

end Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume
