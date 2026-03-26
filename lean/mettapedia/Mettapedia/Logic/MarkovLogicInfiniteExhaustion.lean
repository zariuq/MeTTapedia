import Mettapedia.Logic.MarkovLogicInfinitePositive

/-!
# Infinite MLN Exhaustions and Finite-Volume Kernel Sequences

This module packages the next literature-facing layer for the infinite MLN
development: countable-region exhaustions and the resulting sequence of
finite-volume kernels along an exhaustion.

At this stage we do not yet construct a global Gibbs measure. Instead we make
explicit the approximation family that the existence step will quantify over:

- an increasing exhaustion `Λ₀ ⊆ Λ₁ ⊆ ...` of the atom space,
- eventual containment of every finite query support,
- the corresponding sequence of boundary-conditioned finite-volume measures,
- the induced sequence of local `MassSemantics` objects.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteExhaustion

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteDLR
open Mettapedia.Logic.MarkovLogicAbstract

/-- A countable exhaustion of an infinite atom space by finite regions. -/
structure RegionExhaustion (Atom : Type*) where
  region : ℕ → Region Atom
  monotone : Monotone region
  exhaustive : ∀ a : Atom, ∃ n, a ∈ region n

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Reindex an exhaustion along a strictly monotone subsequence. -/
def reindex
    (E : RegionExhaustion Atom)
    (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    RegionExhaustion Atom where
  region := fun n => E.region (φ n)
  monotone := fun a b hab => E.monotone (hφ.monotone hab)
  exhaustive := by
    intro a
    rcases E.exhaustive a with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    exact E.monotone (hφ.id_le N) hN

omit [DecidableEq Atom] in
@[simp] theorem reindex_region
    (E : RegionExhaustion Atom)
    (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (n : ℕ) :
    (E.reindex φ hφ).region n = E.region (φ n) :=
  rfl

/-- Every finite atom set is eventually contained in some stage of an
exhaustion. -/
theorem exists_stage_subset
    (E : RegionExhaustion Atom) (S : Finset Atom) :
    ∃ N, S ⊆ E.region N := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨0, Finset.empty_subset _⟩
  · intro a S ha hS
    rcases hS with ⟨NS, hNS⟩
    rcases E.exhaustive a with ⟨Na, haNa⟩
    refine ⟨max Na NS, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact E.monotone (Nat.le_max_left _ _) haNa
    · exact E.monotone (Nat.le_max_right _ _) (hNS hxS)

/-- Every finite constraint query is eventually supported inside some
exhaustion stage. -/
theorem exists_stage_queryAtoms_subset
    (E : RegionExhaustion Atom)
    (q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom) :
    ∃ N, queryAtoms q ⊆ E.region N :=
  exists_stage_subset E (queryAtoms q)

/-- Eventual support containment restated in pointwise query form. -/
theorem exists_stage_supports_query
    (E : RegionExhaustion Atom)
    (q : InfiniteGroundMLNSpec.InfiniteConstraintQuery Atom) :
    ∃ N, ∀ c ∈ q, c.1 ∈ E.region N := by
  rcases exists_stage_queryAtoms_subset E q with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro c hc
  exact hN <| Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hc, rfl⟩

/-- The sequence of boundary-conditioned finite-volume world measures along an
exhaustion. -/
noncomputable def finiteVolumeKernelSequence
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) :
    ℕ → Measure (InfiniteWorld Atom) :=
  fun n =>
    StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
      M (E.region n) ξ

@[simp] theorem finiteVolumeKernelSequence_reindex
    (E : RegionExhaustion Atom)
    (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (n : ℕ) :
    finiteVolumeKernelSequence (E.reindex φ hφ) M ξ n =
      finiteVolumeKernelSequence E M ξ (φ n) := by
  simp [finiteVolumeKernelSequence, reindex]

instance finiteVolumeKernelSequence_isProbability
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ) :
    IsProbabilityMeasure (finiteVolumeKernelSequence E M ξ n) := by
  unfold finiteVolumeKernelSequence
  infer_instance

/-- The local `MassSemantics` induced by the finite-volume kernels along an
exhaustion. -/
noncomputable def massSemanticsSequence
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) :
    (n : ℕ) → MassSemantics (LocalConstraintQuery Atom (E.region n)) :=
  fun n =>
    (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeSpecification M).kernelMassSemantics
      (E.region n) ξ
      (StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero M (E.region n) ξ)

theorem massSemanticsSequence_queryProb_eq_finiteVolume
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (n : ℕ) (q : LocalConstraintQuery Atom (E.region n)) :
    (massSemanticsSequence E M ξ n).queryProb q =
      (finiteVolumeMassSemantics M.toInfiniteGroundMLNSpec (E.region n) ξ).queryProb q := by
  exact StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeSpecification_queryProb_eq_finiteVolume
    M (E.region n) ξ q

theorem massSemanticsSequence_queryStrength_eq_finiteVolume
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (n : ℕ) (q : LocalConstraintQuery Atom (E.region n)) :
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
      ({massSemanticsSequence E M ξ n} :
        MassState (LocalConstraintQuery Atom (E.region n))) q =
      (finiteVolumeMassSemantics M.toInfiniteGroundMLNSpec (E.region n) ξ).queryProb q := by
  rw [MassState.queryStrength_singleton_eq_queryProb]
  exact massSemanticsSequence_queryProb_eq_finiteVolume E M ξ n q

end RegionExhaustion

end Mettapedia.Logic.MarkovLogicInfiniteExhaustion
