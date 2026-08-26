import Mathlib.Tactic

/-!
# Unit-ranked transition systems

A broad refinement relation and a one-level transition relation are different
structures.  This module records the additional data needed for the latter: a
natural-number rank and a proof that each admitted step raises it by exactly
one.  The length of a path is then intrinsic, while the existence of a longer
path entails the existence of every shorter suffix length.

This construction is independent of any particular interpretation of states.
Downstream modules may prove that its steps refine an existing preorder or
semantic relation.
-/

set_option autoImplicit false

namespace Mettapedia.Order

universe uState

/-- A transition relation whose individual steps raise a natural-number rank
by exactly one. -/
structure RankedStep (State : Type uState) where
  Step : State → State → Prop
  rank : State → Nat
  step_rank : ∀ {source target}, Step source target →
    rank target = rank source + 1

namespace RankedStep

variable {State : Type uState} (system : RankedStep State)

/-- A proof-relevant path of exactly the displayed number of unit-ranked
steps. -/
inductive Path : Nat → State → State → Prop where
  | refl (state : State) : Path 0 state state
  | step {n : Nat} {source middle target : State} :
      system.Step source middle → Path n middle target →
      Path (n + 1) source target

namespace Path

/-- Concatenation adds exact path lengths. -/
theorem append {firstSteps secondSteps : Nat}
    {first middle last : State}
    (firstPath : system.Path firstSteps first middle)
    (secondPath : system.Path secondSteps middle last) :
    system.Path (firstSteps + secondSteps) first last := by
  induction firstPath with
  | refl => simpa using secondPath
  | @step steps first next middle edge rest inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Path.step edge (inductionHypothesis secondPath)

/-- The rank difference along a path is exactly its length. -/
theorem rank_target_eq_rank_source_add {steps : Nat} {source target : State}
    (path : system.Path steps source target) :
    system.rank target = system.rank source + steps := by
  induction path with
  | refl => simp
  | @step steps source middle target edge rest inductionHypothesis =>
      rw [inductionHypothesis, system.step_rank edge]
      omega

/-- Two unit-ranked paths with the same endpoints have the same length. -/
theorem length_unique {firstSteps secondSteps : Nat} {source target : State}
    (firstPath : system.Path firstSteps source target)
    (secondPath : system.Path secondSteps source target) :
    firstSteps = secondSteps := by
  have firstRank := firstPath.rank_target_eq_rank_source_add
  have secondRank := secondPath.rank_target_eq_rank_source_add
  omega

/-- Removing the first step exposes a path one level shorter. -/
theorem tail {steps : Nat} {source target : State}
    (path : system.Path (steps + 1) source target) :
    ∃ middle, system.Step source middle ∧ system.Path steps middle target := by
  cases path with
  | step edge rest => exact ⟨_, edge, rest⟩

end Path

/-- Some pair of states is connected by a path of the given length. -/
def RealizesLength (steps : Nat) : Prop :=
  ∃ source target, system.Path steps source target

/-- The realized path-length spectrum has no gaps below a successor: a
realized path of length `n + 1` contains a realized suffix of length `n`. -/
theorem realizesLength_pred {steps : Nat}
    (realized : system.RealizesLength (steps + 1)) :
    system.RealizesLength steps := by
  obtain ⟨source, target, path⟩ := realized
  obtain ⟨middle, _, tail⟩ := path.tail
  exact ⟨middle, target, tail⟩

end RankedStep

end Mettapedia.Order

#print axioms Mettapedia.Order.RankedStep.Path.rank_target_eq_rank_source_add
#print axioms Mettapedia.Order.RankedStep.Path.length_unique
#print axioms Mettapedia.Order.RankedStep.realizesLength_pred
