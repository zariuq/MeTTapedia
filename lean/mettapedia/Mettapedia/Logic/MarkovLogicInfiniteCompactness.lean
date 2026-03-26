import Mathlib.Topology.Sequences
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mettapedia.Logic.MarkovLogicInfiniteSpecification
import Mettapedia.Logic.MarkovLogicInfiniteProjective

/-!
# Infinite MLN Compactness Frontend

This module isolates the first honest compactness theorem on the infinite-MLN
side.

Each exhaustion stage `n` already yields a projective family of finite-
dimensional marginals.  Since every finite-dimensional Boolean assignment space
is finite, the corresponding probability-measure spaces are compact and
metrizable.  Therefore the whole sequence of stage marginal families lives in a
compact first-countable product space, so it admits a convergent subsequence.

The main results here are:

- `stageProbabilityFamily`: the stage `n` family as a product of probability
  measures;
- `exists_stageProbabilityFamily_tendsto_subseq`: compactness extraction of a
  convergent subsequence of those families;
- `isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily`: the limit of
  such a convergent subsequence is still projective.

This does **not** yet produce the final global infinite-MLN Gibbs measure.
Instead it identifies the compactness/extraction theorem object that the next
existence step must feed into the fixed-region DLR layer.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteCompactness

open Filter
open MeasureTheory
open scoped Topology
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteProjective
open Mettapedia.Logic.MarkovLogicInfinitePositive

namespace RegionExhaustion

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

abbrev BoolCoord (Atom : Type*) (i : Atom) :=
  Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.BoolCoord Atom i

/-- The stage-`n` finite-dimensional marginals packaged as a product of
probability measures. -/
abbrev StageProbabilityFamily (Atom : Type*) :=
  ∀ I : Finset Atom, ProbabilityMeasure (LocalAssignment Atom I)

/-- The stage-`n` marginal family as a point in the compact product of finite-
dimensional probability spaces. -/
noncomputable def stageProbabilityFamily
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (n : ℕ) : StageProbabilityFamily Atom :=
  fun I =>
    ⟨Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.stageMarginal
      E M ξ n I, inferInstance⟩

/-- For countable atom types, the stage marginal families admit a convergent
subsequence in the compact first-countable product space of finite-dimensional
probability measures. -/
theorem exists_stageProbabilityFamily_tendsto_subseq
    [Countable Atom]
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom) :
    ∃ P : StageProbabilityFamily Atom,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          Tendsto (fun n => stageProbabilityFamily E M ξ (φ n)) atTop (𝓝 P) := by
  simpa using
    (CompactSpace.tendsto_subseq (fun n => stageProbabilityFamily E M ξ n))

/-- Countable extraction restated using an explicit enumeration `e : ℕ ≃ Atom`.
This is the theorem shape used elsewhere in the infinite-MLN development. -/
theorem exists_stageProbabilityFamily_tendsto_subseq_of_equiv
    (E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom)
    (M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId)
    (ξ : BoundaryCondition Atom)
    (e : ℕ ≃ Atom) :
    ∃ P : StageProbabilityFamily Atom,
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
          Tendsto (fun n => stageProbabilityFamily E M ξ (φ n)) atTop (𝓝 P) := by
  letI : Countable Atom := (Equiv.countable_iff e).1 inferInstance
  exact exists_stageProbabilityFamily_tendsto_subseq
    (E := E) (M := M) (ξ := ξ)

/-- Any subsequential limit of the stage probability families remains
projective, because the finite-coordinate restriction maps are continuous and
the stage families are projective at every finite volume. -/
theorem isProjectiveMeasureFamily_of_tendsto_stageProbabilityFamily
    {E : Mettapedia.Logic.MarkovLogicInfiniteExhaustion.RegionExhaustion Atom}
    {M : StrictlyPositiveInfiniteGroundMLNSpec Atom ClauseId}
    {ξ : BoundaryCondition Atom}
    {P : StageProbabilityFamily Atom}
    {φ : ℕ → ℕ}
    (hφ : Tendsto (fun n => stageProbabilityFamily E M ξ (φ n)) atTop (𝓝 P)) :
    MeasureTheory.IsProjectiveMeasureFamily
      (ι := Atom) (α := BoolCoord Atom)
      (fun I => ((P I : ProbabilityMeasure (LocalAssignment Atom I)) :
        Measure (LocalAssignment Atom I))) := by
  intro I J hJI
  let r : LocalAssignment Atom I → LocalAssignment Atom J :=
    Finset.restrict₂ (π := BoolCoord Atom) hJI
  have hr_cont : Continuous r :=
    Finset.continuous_restrict₂ (A := fun _ : Atom => Bool) hJI
  have hJ :
      Tendsto (fun n => stageProbabilityFamily E M ξ (φ n) J) atTop (𝓝 (P J)) :=
    (continuous_apply J).continuousAt.tendsto.comp hφ
  have hI :
      Tendsto (fun n => stageProbabilityFamily E M ξ (φ n) I) atTop (𝓝 (P I)) :=
    (continuous_apply I).continuousAt.tendsto.comp hφ
  have hMapJ :
      Tendsto
        (fun n =>
          ProbabilityMeasure.map
            (stageProbabilityFamily E M ξ (φ n) I)
            hr_cont.measurable.aemeasurable)
        atTop
        (𝓝 (ProbabilityMeasure.map (P I) hr_cont.measurable.aemeasurable)) := by
    exact (ProbabilityMeasure.continuous_map hr_cont).continuousAt.tendsto.comp hI
  have hStageEq :
      (fun n =>
        ProbabilityMeasure.map
          (stageProbabilityFamily E M ξ (φ n) I)
          hr_cont.measurable.aemeasurable) =
      (fun n => stageProbabilityFamily E M ξ (φ n) J) := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    simpa [stageProbabilityFamily, r] using
      (Mettapedia.Logic.MarkovLogicInfiniteProjective.RegionExhaustion.isProjectiveMeasureFamily_stageMarginal
        E M ξ (φ n) (I := I) (J := J) hJI).symm
  have hMapI :
      Tendsto
        (fun n => stageProbabilityFamily E M ξ (φ n) J)
        atTop
        (𝓝 (ProbabilityMeasure.map (P I) hr_cont.measurable.aemeasurable)) := by
    simpa [hStageEq] using hMapJ
  have hEqProb :
      ProbabilityMeasure.map (P I) hr_cont.measurable.aemeasurable = P J :=
    tendsto_nhds_unique hMapI hJ
  simpa [r] using
    (congrArg (fun ν : ProbabilityMeasure (LocalAssignment Atom J) =>
      (ν : Measure (LocalAssignment Atom J))) hEqProb).symm

end RegionExhaustion

end Mettapedia.Logic.MarkovLogicInfiniteCompactness
