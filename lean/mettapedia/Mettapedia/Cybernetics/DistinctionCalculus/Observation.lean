import Mettapedia.Cybernetics.DistinctionCalculus.Basic
import Mettapedia.Cybernetics.MultiscaleGoal
import Mettapedia.Cybernetics.StructurePreservingRepair

/-!
# Goal visibility and repair under a distinction observer

Metric coherence licenses a quotient by zero distance. Goal descent still
requires invariance on that quotient: coherence alone does not preserve every
goal. A structure-preserving repair changes the state while preserving a
selected valued report. Thus value-observer identity and full state identity
are provably different, even along a successful repair.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v w c

variable {V : Type u} {W : Type v}

def quotientObserver (a : Tolerance V) (metric : a.Metric) :
    Observer V (Quotient (a.zeroSetoid metric)) where
  observe := Quotient.mk _

theorem quotientObserver_equal_iff (a : Tolerance V) (metric : a.Metric) (x y : V) :
    (quotientObserver a metric).observe x = (quotientObserver a metric).observe y ↔
      a.Indistinguishable x y :=
  ⟨Quotient.exact, fun h => @Quotient.sound V (a.zeroSetoid metric) x y h⟩

/-- A goal can be used on the metric quotient precisely when zero distance
cannot change its answer. This uses the existing multiscale-goal construction. -/
theorem goalVisible_iff_zero_distance_invariant
    (space : MultiscaleGoal.ProblemSpace V) (a : Tolerance V) (metric : a.Metric) :
    space.GoalVisibleAt (quotientObserver a metric) ↔
      ∀ x y, a.Indistinguishable x y →
        (x ∈ space.preferredRegion ↔ y ∈ space.preferredRegion) := by
  rw [space.goalVisibleAt_iff_invariantOnFibres]
  simp only [MultiscaleGoal.ProblemSpace.GoalInvariantOnFibres, quotientObserver_equal_iff]

theorem goalVisible_iff_report_indistinguishable [DecidableEq W]
    (space : MultiscaleGoal.ProblemSpace V) (observer : Observer V W) :
    space.GoalVisibleAt observer ↔
      ∀ x y, (Tolerance.ofReport observer.observe).Indistinguishable x y →
        (x ∈ space.preferredRegion ↔ y ∈ space.preferredRegion) := by
  rw [space.goalVisibleAt_iff_invariantOnFibres]
  simp only [MultiscaleGoal.ProblemSpace.GoalInvariantOnFibres,
    Tolerance.ofReport_indistinguishable]

/-- Actual strict repair preserves the chosen value and changes the full state. -/
theorem repair_preserves_observer_not_state [DecidableEq W] {Misfit : Type w}
    {problem : StructurePreservingRepair.Problem.{u, v, w, c} V W Misfit}
    {source target : V} (repair : StructurePreservingRepair.Repair problem source target) :
    (Tolerance.ofReport problem.valuedObservation.observe).Indistinguishable source target ∧
      source ≠ target := by
  exact ⟨(Tolerance.ofReport_indistinguishable _ _ _).mpr repair.preservesValue.symm,
    repair.source_ne_target⟩

namespace ObservationExamples

open MultiscaleGoal.Canary

def visibleObserver : Tolerance FineState := Tolerance.ofReport coarseObserver.observe

theorem distinct_states_can_be_observer_identical :
    (false, false) ≠ (false, true) ∧ visibleObserver.Indistinguishable (false, false) (false, true) := by
  constructor
  · decide
  · exact (Tolerance.ofReport_indistinguishable _ _ _).mpr rfl

/-- An actually hidden goal cannot be admitted merely because the observer is metric. -/
theorem coherence_does_not_make_every_goal_visible :
    visibleObserver.Metric ∧ ¬ hiddenProblem.GoalVisibleAt coarseObserver :=
  ⟨Tolerance.ofReport_metric _, hiddenProblem_not_goalVisibleAt⟩

theorem visible_goal_is_retained : visibleProblem.GoalVisibleAt coarseObserver :=
  visibleProblem_goalVisibleAt

end ObservationExamples

end Mettapedia.Cybernetics.DistinctionCalculus
