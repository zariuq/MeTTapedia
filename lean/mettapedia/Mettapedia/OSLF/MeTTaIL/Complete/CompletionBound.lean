import Mettapedia.OSLF.MeTTaIL.Complete.Termination

/-! Finite equation-class search is complete at every sufficiently large
work budget. This strengthens the existential completion witness to the
bound required by a runner with an arbitrary positive work quantum.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Classes

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

theorem completion_bound (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (descends : Descends plan) {carrier : List Pattern}
    (finite : ∀ pattern, Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) source pattern →
      pattern ∈ carrier) :
    ∃ cost, ∀ work, cost ≤ work → complete plan (runAt plan bound expected source work) = true := by
  obtain ⟨settled, stable⟩ := reps_settle plan bound expected source finite
  let keys := (runAt plan bound expected source settled).reps.flatMap (lanesOf plan bound expected)
  obtain ⟨extra, done⟩ := keys_eventually_complete plan bound expected descends keys (by
    intro key member
    obtain ⟨rep, _, inLanes⟩ := List.mem_flatMap.mp member
    exact ⟨rep, inLanes⟩)
  refine ⟨settled + extra, ?_⟩
  intro work enough
  apply List.all_eq_true.mpr
  intro entry member
  obtain ⟨repMember, inLanes, current⟩ := (rounds_reached plan bound expected source work).entries entry member
  have same := stable work (by omega)
  have settledMember : entry.1.rep ∈ (runAt plan bound expected source settled).reps := by
    rw [← same]
    exact repMember
  have born : entry.1.rep.born ≤ settled := by
    have early := (rounds_reached plan bound expected source settled).born _ settledMember
    rwa [runAt_round] at early
  have key : entry.1 ∈ keys := List.mem_flatMap.mpr ⟨_, settledMember, inLanes⟩
  rw [current]
  apply done entry.1 key
  have round := runAt_round plan bound expected source work
  simp only [runAt] at round
  rw [round]
  omega

#print axioms completion_bound

end Mettapedia.OSLF.MeTTaIL.Complete.Classes
