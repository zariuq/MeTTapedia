import Mathlib.MeasureTheory.Measure.Portmanteau
import Mettapedia.Logic.MarkovLogicInfiniteCompactness
import Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR

/-!
# Infinite MLN Existence Packaging

This module closes the main remaining compactness-to-existence gap for the
current infinite-MLN theorem layer.

The preceding files already provide:

- finite-volume kernels and their finite-dimensional marginals;
- compactness extraction of a convergent subsequence of the stage marginal
  families;
- projectivity of the subsequential limit family;
- fixed-region cylinder DLR for any projective family that is the pointwise
  measurable limit of the stage marginals.

The new ingredient here is that convergence of the packaged
`StageProbabilityFamily` in the product topology implies pointwise convergence
of the corresponding finite-dimensional marginals on all measurable sets.
Because finite Boolean assignment spaces are discrete, every set is clopen, so
Portmanteau gives setwise convergence directly.

This yields the first paper-shaped existence theorem at the current honest
abstraction layer:

`ℕ ≃ Atom -> ∃ μ, IsProbabilityMeasure μ ∧ FixedRegionCylinderDLR M μ`.

This is still weaker than the full Singla--Domingos stack, because uniqueness,
tail/extremal Gibbs structure, and regular-conditional packaging remain future
work.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteExistence

open Filter
open MeasureTheory
open scoped Topology
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteProjective
open Mettapedia.Logic.MarkovLogicInfiniteCompactness
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteCompactness.RegionExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR.RegionExhaustion

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Convergence of the packaged `StageProbabilityFamily` implies convergence of
the corresponding finite-dimensional marginals on every measurable set.  Since
the local assignment space is discrete, every set is clopen, so Portmanteau
applies directly. -/
theorem tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {P : StageProbabilityFamily Atom}
    {φ : ℕ → ℕ}
    (hφ : Tendsto (fun n => stageProbabilityFamily E M ξ (φ n)) atTop (𝓝 P))
    (I : Finset Atom)
    (S : Set (LocalAssignment Atom I)) :
    Tendsto (fun n => stageMarginal E M ξ (φ n) I S) atTop
      (𝓝 (((P I : ProbabilityMeasure (LocalAssignment Atom I)) :
        Measure (LocalAssignment Atom I)) S)) := by
  have hI :
      Tendsto (fun n => stageProbabilityFamily E M ξ (φ n) I) atTop (𝓝 (P I)) :=
    (continuous_apply I).continuousAt.tendsto.comp hφ
  have hSclopen : IsClopen S := by
    classical
    exact isClopen_discrete S
  have hfrontier :
      (((P I : ProbabilityMeasure (LocalAssignment Atom I)) :
        Measure (LocalAssignment Atom I)) (frontier S)) = 0 := by
    rw [hSclopen.frontier_eq]
    simp
  simpa [stageProbabilityFamily] using
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (μs_lim := hI) hfrontier)

/-- Once a subsequence of the packaged stage marginal families converges, the
existing fixed-region DLR packaging applies to the reindexed exhaustion. -/
theorem exists_fixedRegionCylinderDLR_of_tendsto_stageProbabilityFamily
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    (e : ℕ ≃ Atom)
    (P : StageProbabilityFamily Atom)
    (φ : ℕ → ℕ)
    (hmono : StrictMono φ)
    (hφ : Tendsto (fun n => stageProbabilityFamily E M ξ (φ n)) atTop (𝓝 P)) :
    ∃ μ : Measure (InfiniteWorld Atom),
      ∃ _ : IsProbabilityMeasure μ, FixedRegionCylinderDLR M μ := by
  let Q : ∀ I : Finset Atom, Measure (LocalAssignment Atom I) :=
    fun I => ((P I : ProbabilityMeasure (LocalAssignment Atom I)) :
      Measure (LocalAssignment Atom I))
  haveI hQprob : ∀ I : Finset Atom, IsProbabilityMeasure (Q I) := by
    intro I
    dsimp [Q]
    infer_instance
  have hQ :
      MeasureTheory.IsProjectiveMeasureFamily
        (ι := Atom)
        (α :=
          Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom)
        Q := by
    simpa [Q] using
      (isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
        (E := E) (M := M) (ξ := ξ) (P := P) (φ := φ) hφ)
  let E' := E.reindex φ hmono
  have hconv :
      ∀ (I : Finset Atom) (S : Set (LocalAssignment Atom I)),
        MeasurableSet S →
          Tendsto (fun n => stageMarginal E' M ξ n I S) atTop (nhds (Q I S)) := by
    intro I S _hS
    simpa [E', Q, stageMarginal_reindex] using
      (tendsto_stageMarginal_apply_of_tendsto_stageProbabilityFamily
        (E := E) (M := M) (ξ := ξ) (P := P) (φ := φ) hφ I S)
  exact exists_fixedRegionCylinderDLR_of_stageMarginal_tendsto
    (E := E') (M := M) (ξ := ξ) (e := e) (P := Q) hQ hconv

/-- Paper-shaped existence theorem at the current theorem frontier: for a
countably infinite atom type presented by `ℕ ≃ Atom`, compactness extraction
produces a global measure satisfying fixed-region cylinder DLR. -/
theorem exists_fixedRegionCylinderDLR_of_equiv
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (e : ℕ ≃ Atom) :
    ∃ μ : Measure (InfiniteWorld Atom),
      ∃ _ : IsProbabilityMeasure μ, FixedRegionCylinderDLR M μ := by
  rcases exists_stageProbabilityFamily_tendsto_subseq_of_equiv
      (E := E) (M := M) (ξ := ξ) e with
    ⟨P, φ, hmono, hφ⟩
  exact exists_fixedRegionCylinderDLR_of_tendsto_stageProbabilityFamily
    (E := E) (M := M) (ξ := ξ) e P φ hmono hφ

end RegionExhaustion

end Mettapedia.Logic.MarkovLogicInfiniteExistence
