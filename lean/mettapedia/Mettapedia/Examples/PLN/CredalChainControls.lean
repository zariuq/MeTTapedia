import Mettapedia.ProbabilityTheory.ImpreciseProbability.BranchFrechet
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalScope
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ScreeningBand

/-!
# Bounds on a three-period diagnostic chain

The evidence, split, and query are a region's storm, its route's delay
one period later, and the route's blockage one period after that.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.CredalChainControls

open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.StochasticInference (UnitProbability)

private def delay : BranchFrechet.Marginals :=
  ⟨1 / 2, 2 / 5, 3 / 8, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

private def noDelay : BranchFrechet.Marginals :=
  ⟨1 / 2, 1 / 10, 1 / 8, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem unscreened_interval : BranchFrechet.bounds delay noDelay = some (11 / 20, 19 / 20) := by
  decide +kernel

private def weight : UnitProbability := ⟨4 / 5, by decide +kernel, by decide +kernel⟩
private def p : UnitProbability := ⟨3 / 4, by decide +kernel, by decide +kernel⟩
private def q : UnitProbability := ⟨1 / 4, by decide +kernel, by decide +kernel⟩

private def storm (world : Fin 8) : Bool := world.val.testBit 0
private def late (world : Fin 8) : Bool := world.val.testBit 1
private def blocked (world : Fin 8) : Bool := world.val.testBit 2

private def presentBand := ScreeningBand.around blocked (fun w => storm w && late w)
  p (1 / 20) (by decide +kernel)
private def absentBand := ScreeningBand.around blocked (fun w => storm w && !late w)
  q (1 / 10) (by decide +kernel)

theorem certified_deviation_interval :
    ScreeningBand.mixRows weight presentBand absentBand = (59 / 100, 71 / 100) := by decide +kernel

theorem imprecise_branch_weight :
    ScreeningBand.mixRowIntervals (ScreeningBand.around late storm weight (1 / 10) (by decide +kernel))
      presentBand absentBand = (107 / 200, 151 / 200) := by decide +kernel

theorem the_screened_point_can_have_large_error :
    IntervalError.intervalErrorRadius (11 / 20) (19 / 20) (13 / 20) = 3 / 10 := by
  norm_num [IntervalError.intervalErrorRadius]

theorem intersecting_guarantees_preserves_the_tighter_interval :
    AnytimeConditional.tighten (some (11 / 20, 19 / 20)) (some (59 / 100, 71 / 100)) =
      some (59 / 100, 71 / 100) := by decide +kernel

private def emptyBranch : BranchFrechet.Marginals :=
  ⟨1 / 2, 0, 0, le_rfl, le_rfl, by decide +kernel, by decide +kernel⟩

theorem null_branch_mass_does_not_supply_query_support :
    BranchFrechet.bounds emptyBranch emptyBranch = none := by decide +kernel

private def supported : Fin 2 → Bool := fun world => world.val == 1

private def localKnowledge : FiniteConditionalConstraints.KnowledgeBase (Fin 2) :=
  [⟨supported, fun _ => true, 3 / 4, 3 / 4, by decide +kernel, le_rfl, by decide +kernel⟩]

/-- A view computes over two local coordinates even with a large state
space in the disconnected part. -/
theorem disjoint_view_runs_over_the_local_worlds :
    (CredalScope.disjointView localKnowledge
      ([] : FiniteConditionalConstraints.KnowledgeBase (Fin (2 ^ 100)))
      supported (fun _ => true)).solve 8 = some (3 / 4, 3 / 4) := by
  decide +kernel

end Mettapedia.Examples.PLN.CredalChainControls
