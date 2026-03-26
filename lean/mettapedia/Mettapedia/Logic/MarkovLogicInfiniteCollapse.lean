import Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
import Mettapedia.Logic.MarkovLogicClauseFactorGraph
import Mettapedia.ProbabilityTheory.BayesianNetworks.VEBridge

/-!
# Infinite MLN Finite-Volume Collapse into Finite Factor-Graph Semantics

For a fixed finite region `Λ` and a fixed boundary condition `ξ`, an infinite
MLN induces a finite factor graph over the region atoms.  This file proves that
the resulting finite factor-graph semantics computes exactly the same local
partition function and query masses as the direct finite-volume definitions.

This is the key compatibility doorway from the infinite-domain literature lane
back into the project's existing finite graphical-model machinery.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteCollapse

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.ProbabilityTheory.BayesianNetworks

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Boundary-conditioned finite factor graph over the atoms of `Λ`.

Every active infinite-MLN clause touching `Λ` becomes one factor.  The factor
looks at the full region assignment and evaluates the original clause after
patching the assignment into the boundary condition `ξ`.  The scope is taken to
be all of `Λ`; this is semantically exact, though later we may refine it to the
smaller true clause scope for efficiency.
-/
noncomputable def regionFactorGraph
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    FactorGraph (RegionAtom Atom Λ) ENNReal where
  stateSpace _ := Bool
  factors := {j // j ∈ M.regionSupport Λ}
  scope _ := Finset.univ
  potential j x := (M.clauseData j.1).eval (patch Λ (fun a => x a (by simp)) ξ)

private instance regionFactorGraphFactorsFintype
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    Fintype (regionFactorGraph M Λ ξ).factors := by
  dsimp [regionFactorGraph]
  infer_instance

private instance regionFactorGraphStateFintype
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (a : RegionAtom Atom Λ) :
    Fintype ((regionFactorGraph M Λ ξ).stateSpace a) := by
  dsimp [regionFactorGraph]
  infer_instance

private instance regionFactorGraphStateDecidableEq
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (a : RegionAtom Atom Λ) :
    DecidableEq ((regionFactorGraph M Λ ξ).stateSpace a) := by
  dsimp [regionFactorGraph]
  infer_instance

theorem regionFactorGraph_unnormalizedJoint_eq_finiteVolumeWeight
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (x : LocalAssignment Atom Λ) :
    (regionFactorGraph M Λ ξ).unnormalizedJoint x =
      M.finiteVolumeWeight Λ x ξ := by
  classical
  unfold FactorGraph.unnormalizedJoint
  unfold InfiniteGroundMLNSpec.finiteVolumeWeight
  change (∏ i : M.regionSupport Λ, (M.clauseData i.1).eval (patch Λ x ξ)) =
      ∏ j ∈ M.regionSupport Λ, (M.clauseData j).eval (patch Λ x ξ)
  calc
    ∏ i : M.regionSupport Λ, (M.clauseData i.1).eval (patch Λ x ξ) =
        ∏ i ∈ (M.regionSupport Λ).attach, (M.clauseData i.1).eval (patch Λ x ξ) := by
          rw [Finset.prod_coe_sort_eq_attach (s := M.regionSupport Λ)
            (f := fun i : M.regionSupport Λ => (M.clauseData i.1).eval (patch Λ x ξ))]
    _ = ∏ j ∈ M.regionSupport Λ, (M.clauseData j).eval (patch Λ x ξ) := by
          rw [Finset.prod_attach (s := M.regionSupport Λ)
            (f := fun j => (M.clauseData j).eval (patch Λ x ξ))]

lemma regionFactorGraph_weightOfConstraints_eq_queryMass
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Λ) :
    VariableElimination.weightOfConstraints (fg := regionFactorGraph M Λ ξ) q =
      finiteVolumeQueryMass M Λ ξ q := by
  classical
  have hpot : ∀ x : LocalAssignment Atom Λ,
      (VariableElimination.combineAll (fg := regionFactorGraph M Λ ξ)
        (VariableElimination.factorsOfGraph (fg := regionFactorGraph M Λ ξ))).potential
        (VariableElimination.FactorGraph.fullAssign (fg := regionFactorGraph M Λ ξ) x
          (VariableElimination.combineAll (fg := regionFactorGraph M Λ ξ)
            (VariableElimination.factorsOfGraph (fg := regionFactorGraph M Λ ξ))).scope) =
        M.finiteVolumeWeight Λ x ξ := by
    intro x
    have h :=
      VariableElimination.combineAll_factorsOfGraph_potential_eq_unnormalizedJoint
        (fg := regionFactorGraph M Λ ξ) (x := x)
    simpa [regionFactorGraph_unnormalizedJoint_eq_finiteVolumeWeight] using h
  unfold VariableElimination.weightOfConstraints finiteVolumeQueryMass
  simp only [VariableElimination.weightOfConstraintsList, satisfiesConstraints]
  refine Finset.sum_congr rfl ?_
  intro x _
  split_ifs
  · exact hpot x
  · contradiction
  · contradiction
  · rfl

theorem regionFactorGraph_partitionFunction_eq_finiteVolumePartition
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    (regionFactorGraph M Λ ξ).partitionFunction =
      M.finiteVolumePartition Λ ξ := by
  classical
  unfold FactorGraph.partitionFunction InfiniteGroundMLNSpec.finiteVolumePartition
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl ?_
  intro x _
  exact regionFactorGraph_unnormalizedJoint_eq_finiteVolumeWeight M Λ ξ x

/-- The finite-volume probability object seen through the finite factor-graph
machinery. -/
noncomputable def regionFactorGraphMassSemantics
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom) :
    MassSemantics (LocalConstraintQuery Atom Λ) where
  queryMass := fun q => VariableElimination.weightOfConstraints (fg := regionFactorGraph M Λ ξ) q
  totalMass := (regionFactorGraph M Λ ξ).partitionFunction
  queryMass_le_total := by
    intro q
    rw [regionFactorGraph_weightOfConstraints_eq_queryMass]
    rw [regionFactorGraph_partitionFunction_eq_finiteVolumePartition]
    exact finiteVolumeQueryMass_le_partition M Λ ξ q
  totalMass_ne_top := by
    rw [regionFactorGraph_partitionFunction_eq_finiteVolumePartition]
    exact finiteVolumePartition_ne_top M Λ ξ

theorem regionFactorGraph_queryProb_eq_finiteVolume_queryProb
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Λ) :
    (regionFactorGraphMassSemantics M Λ ξ).queryProb q =
      (finiteVolumeMassSemantics M Λ ξ).queryProb q := by
  simp [regionFactorGraphMassSemantics, finiteVolumeMassSemantics,
    MassSemantics.queryProb,
    regionFactorGraph_weightOfConstraints_eq_queryMass,
    regionFactorGraph_partitionFunction_eq_finiteVolumePartition]

end Mettapedia.Logic.MarkovLogicInfiniteCollapse
