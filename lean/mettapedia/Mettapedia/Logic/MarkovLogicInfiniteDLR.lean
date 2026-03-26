import Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures

/-!
# Infinite MLN Gibbsian Specification Kernel

This module packages the boundary-conditioned finite-volume world measures into
the specification-kernel object that underlies DLR/Gibbs semantics.

At this stage we do **not** yet formalize regular conditional probabilities or
global DLR-consistent measures. Instead we isolate the load-bearing object that
the next step will quantify over:

- for each finite region `Λ`,
- for each boundary condition `ξ`,
- provided the local partition function is nonzero,
- we have a probability measure on full infinite worlds,
- whose local query probabilities agree with the already established
  finite-volume semantics.

This is the honest doorstep of the global infinite-MLN theory.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteDLR

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicAbstract

/-- A Gibbsian specification kernel for an infinite MLN.

For each finite region and boundary condition, it returns the corresponding
finite-volume probability measure on full infinite worlds, together with the
local query law that characterizes the kernel on cylinder events.
-/
structure GibbsianSpecification
    (Atom ClauseId : Type*) [DecidableEq Atom] [DecidableEq ClauseId]
    (M : InfiniteGroundMLNSpec Atom ClauseId) where
  kernel :
    (Λ : Region Atom) →
    (ξ : BoundaryCondition Atom) →
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) →
    Measure (InfiniteWorld Atom)
  kernel_isProbability :
    ∀ Λ ξ hZ, IsProbabilityMeasure (kernel Λ ξ hZ)
  kernel_localQuery :
    ∀ Λ ξ hZ (q : LocalConstraintQuery Atom Λ),
      kernel Λ ξ hZ (localQueryEvent Λ q) =
        (finiteVolumeMassSemantics M Λ ξ).queryProb q

namespace GibbsianSpecification

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
variable {M : InfiniteGroundMLNSpec Atom ClauseId}

/-- Each finite-volume kernel induces a `MassSemantics` object on local queries. -/
noncomputable def kernelMassSemantics
    (S : GibbsianSpecification Atom ClauseId M)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0) :
    MassSemantics (LocalConstraintQuery Atom Λ) where
  queryMass := fun q => S.kernel Λ ξ hZ (localQueryEvent Λ q)
  totalMass := 1
  queryMass_le_total := by
    intro q
    letI := S.kernel_isProbability Λ ξ hZ
    have hmono :
        S.kernel Λ ξ hZ (localQueryEvent (Atom := Atom) Λ q) ≤
          S.kernel Λ ξ hZ Set.univ :=
      measure_mono (Set.subset_univ (localQueryEvent (Atom := Atom) Λ q))
    simpa using hmono
  totalMass_ne_top := ENNReal.one_ne_top

theorem kernelMassSemantics_queryProb
    (S : GibbsianSpecification Atom ClauseId M)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (q : LocalConstraintQuery Atom Λ) :
    (S.kernelMassSemantics Λ ξ hZ).queryProb q =
      S.kernel Λ ξ hZ (localQueryEvent Λ q) := by
  simp [kernelMassSemantics, MassSemantics.queryProb]

end GibbsianSpecification

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- The canonical Gibbsian specification associated to an infinite MLN:
the kernel is exactly the normalized finite-volume world measure. -/
noncomputable def finiteVolumeSpecification
    (M : InfiniteGroundMLNSpec Atom ClauseId) :
    GibbsianSpecification Atom ClauseId M where
  kernel := fun Λ ξ hZ => finiteVolumeWorldMeasure M Λ ξ hZ
  kernel_isProbability := fun Λ ξ hZ => finiteVolumeWorldMeasure_isProbability M Λ ξ hZ
  kernel_localQuery := fun Λ ξ hZ q =>
    finiteVolumeWorldMeasure_localQueryEvent M Λ ξ hZ q

theorem finiteVolumeSpecification_queryProb_eq_finiteVolume
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (q : LocalConstraintQuery Atom Λ) :
    ((finiteVolumeSpecification M).kernelMassSemantics Λ ξ hZ).queryProb q =
      (finiteVolumeMassSemantics M Λ ξ).queryProb q := by
  rw [GibbsianSpecification.kernelMassSemantics_queryProb]
  exact finiteVolumeWorldMeasure_localQueryEvent M Λ ξ hZ q

theorem finiteVolumeSpecification_queryStrength_eq_finiteVolume
    (M : InfiniteGroundMLNSpec Atom ClauseId)
    (Λ : Region Atom) (ξ : BoundaryCondition Atom)
    (hZ : M.finiteVolumePartition Λ ξ ≠ 0)
    (q : LocalConstraintQuery Atom Λ) :
    Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
      ({(finiteVolumeSpecification M).kernelMassSemantics Λ ξ hZ} :
        MassState (LocalConstraintQuery Atom Λ)) q =
      (finiteVolumeMassSemantics M Λ ξ).queryProb q := by
  rw [MassState.queryStrength_singleton_eq_queryProb]
  exact finiteVolumeSpecification_queryProb_eq_finiteVolume M Λ ξ hZ q

end Mettapedia.Logic.MarkovLogicInfiniteDLR
