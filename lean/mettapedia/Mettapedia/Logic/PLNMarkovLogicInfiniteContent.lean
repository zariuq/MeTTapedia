import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily

/-!
# Infinite MLN Cylinder Content from Finite-Dimensional Families

This module packages the finite-dimensional families arising in the infinite-MLN
development as additive contents on measurable cylinders.

The key point is that once we have a projective family `P` on finite atom sets,
Mathlib already gives an additive content `projectiveFamilyContent hP` on
measurable cylinders.  Here we specialize that construction to the Boolean
worlds of the infinite-MLN lane and record the exact local-query formula we
need later:

`content (localQueryEvent Λ q) = P Λ (localConstraintSet Λ q)`.
-/

namespace Mettapedia.Logic.PLNMarkovLogicInfiniteContent

open MeasureTheory
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicInfiniteSpecification
open Mettapedia.Logic.PLNMarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.PLNMarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.PLNMarkovLogicInfiniteProjective
open Mettapedia.Logic.PLNMarkovLogicInfiniteCylinders
open Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion
open Mettapedia.Logic.PLNMarkovLogicInfinitePositive
open Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily

namespace RegionExhaustion

variable {Atom : Type*} [DecidableEq Atom]

abbrev BoolCoord (Atom : Type*) (i : Atom) :=
  Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i

/-- The additive content on measurable cylinders induced by a projective family
of finite-dimensional marginals. -/
noncomputable def familyContent
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :=
  MeasureTheory.projectiveFamilyContent hP

/-- On a local query event, the induced content is exactly the corresponding
finite-dimensional mass. -/
theorem familyContent_localQueryEvent
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    familyContent P hP (localQueryEvent Λ q) =
      P Λ (localConstraintSet Λ q) := by
  simpa [familyContent, localQueryEvent_eq_cylinder Λ q] using
    (MeasureTheory.projectiveFamilyContent_cylinder
      (P := P) (I := Λ) (S := localConstraintSet Λ q) hP
      (measurableSet_localConstraintSet Λ q))

/-- The cylinder content induced by a candidate global limit measure via its
finite-dimensional marginals. -/
noncomputable def limitContent
    (μ : Measure (InfiniteWorld Atom)) :=
  familyContent
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal μ)
    (Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.isProjectiveMeasureFamily_limitMarginal μ)

theorem limitContent_localQueryEvent
    (μ : Measure (InfiniteWorld Atom))
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    limitContent μ (localQueryEvent Λ q) =
      Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal
        μ Λ (localConstraintSet Λ q) :=
  familyContent_localQueryEvent
    (P := Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.limitMarginal μ)
    (hP := Mettapedia.Logic.PLNMarkovLogicInfiniteLimitFamily.RegionExhaustion.isProjectiveMeasureFamily_limitMarginal μ)
    Λ q

/-- The cylinder content induced by a single exhaustion stage. -/
noncomputable def stageContent
    {ClauseId : Type*} [DecidableEq ClauseId]
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ) :=
  familyContent
    (Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
      E M ξ n)
    (Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.isProjectiveMeasureFamily_stageMarginal
      E M ξ n)

theorem stageContent_localQueryEvent
    {ClauseId : Type*} [DecidableEq ClauseId]
    (E : Mettapedia.Logic.PLNMarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) (n : ℕ)
    (Λ : Region Atom) (q : LocalConstraintQuery Atom Λ) :
    stageContent E M ξ n (localQueryEvent Λ q) =
      Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
        E M ξ n Λ (localConstraintSet Λ q) :=
  familyContent_localQueryEvent
    (P := Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
      E M ξ n)
    (hP := Mettapedia.Logic.PLNMarkovLogicInfiniteProjective.RegionExhaustion.isProjectiveMeasureFamily_stageMarginal
      E M ξ n)
    Λ q

end RegionExhaustion

end Mettapedia.Logic.PLNMarkovLogicInfiniteContent
