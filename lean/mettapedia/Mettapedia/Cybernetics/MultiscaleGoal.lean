import Mettapedia.Cybernetics.ObservedVariety

/-!
# Observer-relative goals across scales

Fields and Levin describe agents at many scales as navigating problem spaces
toward preferred regions.  Before a preferred region at a fine scale may be
called a goal at a coarser scale, membership in that region must be decidable
from the coarse observation alone.  This module states that boundary exactly.

A fine goal is visible at a coarse observation precisely when it is constant
on every observation fibre.  The canonical coarse goal is the image of the
fine preferred region.  A hidden-coordinate canary proves that not every fine
goal descends to a legitimate coarse goal.

This is a prerequisite for a theory of multiscale competency, not by itself a
claim that a system is an agent or that it competently reaches its goal.

References:

- C. Fields and M. Levin, *Competency in Navigating Arbitrary Spaces as an
  Invariant for Analyzing Cognition in Diverse Embodiments* (2022).
- M. Levin, *The Multiscale Wisdom of the Body: Collective Intelligence as a
  Tractable Interface for Bioengineering* (2024).
- W. James, *The Principles of Psychology* (1890), for fixed ends reached by
  variable means as a criterion of intelligent behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.MultiscaleGoal

universe uState uView

/-- A problem space identifies the states and its selected preferred region.
No transition dynamics or agency claim is implied by this static datum. -/
structure ProblemSpace (State : Type uState) where
  preferredRegion : Set State

namespace ProblemSpace

variable {State : Type uState} {View : Type uView}

/-- A fine-scale preferred region is visible at an observation scale when a
predicate on observed views recognizes exactly the preferred fine states. -/
def GoalVisibleAt (space : ProblemSpace State)
    (observer : Observer State View) : Prop :=
  ∃ coarseGoal : Set View, ∀ state,
    state ∈ space.preferredRegion ↔
      observer.observe state ∈ coarseGoal

/-- Goal membership is invariant on observation fibres when observationally
indistinguishable states agree about membership in the preferred region. -/
def GoalInvariantOnFibres (space : ProblemSpace State)
    (observer : Observer State View) : Prop :=
  ∀ first second,
    observer.observe first = observer.observe second →
      (first ∈ space.preferredRegion ↔
        second ∈ space.preferredRegion)

/-- The canonical coarse preferred region is the observer image of the fine
preferred region. -/
def coarsePreferredRegion (space : ProblemSpace State)
    (observer : Observer State View) : Set View :=
  observer.observe '' space.preferredRegion

/-- Exact visibility criterion for a preferred region.  Unlike a generic
value-factorization theorem, the propositional codomain needs no surjectivity
or default value for unreachable coarse observations. -/
theorem goalVisibleAt_iff_invariantOnFibres
    (space : ProblemSpace State) (observer : Observer State View) :
    space.GoalVisibleAt observer ↔
      space.GoalInvariantOnFibres observer := by
  constructor
  · rintro ⟨coarseGoal, recognizes⟩ first second sameView
    constructor
    · intro firstPreferred
      apply (recognizes second).mpr
      rw [← sameView]
      exact (recognizes first).mp firstPreferred
    · intro secondPreferred
      apply (recognizes first).mpr
      rw [sameView]
      exact (recognizes second).mp secondPreferred
  · intro invariant
    refine ⟨space.coarsePreferredRegion observer, fun state => ?_⟩
    constructor
    · intro preferred
      exact ⟨state, preferred, rfl⟩
    · rintro ⟨witness, preferred, sameView⟩
      exact (invariant witness state sameView).mp preferred

/-- The canonical image region recognizes every fibre-invariant goal. -/
theorem mem_coarsePreferredRegion_iff
    (space : ProblemSpace State) (observer : Observer State View)
    (invariant : space.GoalInvariantOnFibres observer) (state : State) :
    observer.observe state ∈ space.coarsePreferredRegion observer ↔
      state ∈ space.preferredRegion := by
  constructor
  · rintro ⟨witness, preferred, sameView⟩
    exact (invariant witness state sameView).mp preferred
  · intro preferred
    exact ⟨state, preferred, rfl⟩

end ProblemSpace

/-! ## Visible and hidden goal canaries -/

namespace Canary

abbrev FineState := Bool × Bool

/-- A coarse scale that observes only the first coordinate. -/
def coarseObserver : Observer FineState Bool where
  observe := Prod.fst

/-- A preferred region stated entirely in the visible coordinate. -/
def visibleProblem : ProblemSpace FineState where
  preferredRegion := {state | state.1 = true}

/-- The visible preferred region genuinely descends to the coarse scale. -/
theorem visibleProblem_goalVisibleAt :
    visibleProblem.GoalVisibleAt coarseObserver := by
  refine ⟨{view | view = true}, ?_⟩
  intro state
  rfl

/-- A preferred region stated entirely in the coordinate erased by the
coarse observation. -/
def hiddenProblem : ProblemSpace FineState where
  preferredRegion := {state | state.2 = true}

/-- The hidden-coordinate goal cannot be represented as a goal of the coarse
state.  The two fine states share one coarse view but disagree on success. -/
theorem hiddenProblem_not_goalVisibleAt :
    ¬ hiddenProblem.GoalVisibleAt coarseObserver := by
  intro visible
  have invariant :=
    (hiddenProblem.goalVisibleAt_iff_invariantOnFibres coarseObserver).mp visible
  have contradiction := invariant (false, false) (false, true) rfl
  simp [hiddenProblem] at contradiction

end Canary

end Mettapedia.Cybernetics.MultiscaleGoal

#print axioms Mettapedia.Cybernetics.MultiscaleGoal.ProblemSpace.goalVisibleAt_iff_invariantOnFibres
#print axioms Mettapedia.Cybernetics.MultiscaleGoal.Canary.visibleProblem_goalVisibleAt
#print axioms Mettapedia.Cybernetics.MultiscaleGoal.Canary.hiddenProblem_not_goalVisibleAt
