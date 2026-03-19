import Mathlib.MeasureTheory.Constructions.Projective
import Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion

/-!
# Infinite MLN Stagewise Projective Families

This module packages each exhaustion stage of the infinite MLN construction as
a projective family of finite-dimensional marginals.

Concretely, for a fixed boundary-conditioned finite-volume world measure
`μₙ` on `Atom → Bool`, we define:

- its marginal on any finite atom set `I`,
- the proof that these marginals form a projective family,
- the proof that `μₙ` itself is the projective limit of that family.

This does not yet produce the *global* infinite-MLN measure, but it isolates
the exact finite-dimensional object that the next consistency/existence step
must stabilize and extend.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteProjective

open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive
open Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- The constant Bool-valued coordinate family used for finite-dimensional
marginals on infinite Boolean worlds. -/
abbrev BoolCoord (Atom : Type*) (_ : Atom) := Bool

/-- The marginal of stage `n` on a finite atom set `I`. -/
noncomputable def stageMarginal
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (I : Finset Atom) : Measure (∀ i : I, BoolCoord Atom i) :=
  (Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence
    E M ξ n).map I.restrict

instance stageMarginal_isProbability
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (I : Finset Atom) :
    IsProbabilityMeasure (stageMarginal E M ξ n I) := by
  constructor
  rw [stageMarginal, Measure.map_apply (Finset.measurable_restrict I) MeasurableSet.univ]
  simp

/-- The finite-dimensional marginals of a fixed stage form a projective
measure family. -/
theorem isProjectiveMeasureFamily_stageMarginal
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ) :
    MeasureTheory.IsProjectiveMeasureFamily
      (ι := Atom) (α := BoolCoord Atom) (stageMarginal E M ξ n) := by
  intro I J hJI
  unfold stageMarginal
  change Measure.map J.restrict (E.finiteVolumeKernelSequence M ξ n) =
    ((E.finiteVolumeKernelSequence M ξ n).map I.restrict).map
      (Finset.restrict₂ (π := BoolCoord Atom) hJI)
  rw [Measure.map_map
    (Finset.measurable_restrict₂ (X := BoolCoord Atom) hJI)
    (Finset.measurable_restrict I)]
  congr 1

/-- The stage `n` finite-volume world measure is the projective limit of its
finite-dimensional marginals. -/
theorem isProjectiveLimit_stageMarginal
    (E : RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ) :
    MeasureTheory.IsProjectiveLimit
      (ι := Atom) (α := BoolCoord Atom)
      (Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion.finiteVolumeKernelSequence
        E M ξ n)
      (stageMarginal E M ξ n) := by
  intro I
  rfl

end RegionExhaustion

end Mettapedia.Logic.PLNMarkovLogicInfiniteProjective
