import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GSOSBehaviour
import Mettapedia.CategoryTheory.FiniteActionTreeObservations

/-!
# The set-based final observation is a strict coarsening of event multiplicity

The actual admitted GSOS profile has two distinct firings of a repeated
choice. Its set-based final observation identifies that choice with a single
leaf, while the event-fibre comparison distinguishes them. Existing GSOS
context congruence remains scoped to the set-based observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GSOSProfile

open Interface
open Mettapedia.CategoryTheory Mettapedia.OSLF.FiniteBranching

def multiplicitySystem : EventMultiplicity.System Term Nat := step.eventSystem (fun candidate => candidate.action)

def repeatedLeft : multiplicitySystem.Choice repeated :=
  ⟨leftEvent.firing, leftEvent.prepared, leftEvent.permitted⟩

def repeatedRight : multiplicitySystem.Choice repeated :=
  ⟨rightEvent.firing, rightEvent.prepared, rightEvent.permitted⟩

theorem repeated_choices_distinct : repeatedLeft ≠ repeatedRight := by
  intro same
  have paths := congrArg (fun choice : multiplicitySystem.Choice repeated => choice.val.path) same
  change [false] = [true] at paths
  cases List.cons.inj paths |>.1

theorem pure_choice_candidate_unique
    (choice : multiplicitySystem.Choice (GSOSControls.pure (0 : Nat))) : choice.val = ⟨[], 7, 1⟩ := by
  rcases choice with ⟨⟨path, action, output⟩, prepared, leaf, found, allowed⟩
  cases path with
  | nil =>
      have leafZero : leaf = 0 := (Option.some.inj found).symm
      subst leaf
      have fields : action = 7 ∧ output = 1 := by simpa [LeafAllows] using allowed
      rcases fields with ⟨rfl, rfl⟩
      rfl
  | cons _ _ => cases found

theorem pure_choice_subsingleton
    (first second : multiplicitySystem.Choice (GSOSControls.pure (0 : Nat))) : first = second :=
  Subtype.ext ((pure_choice_candidate_unique first).trans (pure_choice_candidate_unique second).symm)

theorem repeated_not_event_bisimilar :
    ¬EventMultiplicity.Bisimilar multiplicitySystem repeated
      multiplicitySystem (GSOSControls.pure (0 : Nat)) := by
  rintro ⟨_, ⟨b⟩, related⟩
  exact repeated_choices_distinct ((b.choices related).injective
    (pure_choice_subsingleton _ _))

theorem repeated_successor_sets_equal (action : Nat) :
    observedSuccessors repeated action = observedSuccessors (GSOSControls.pure (0 : Nat)) action := by
  simp [observed_successors_eq, repeated, successors_choose]

theorem repeated_final_observations_equal : observe repeated = observe (GSOSControls.pure (0 : Nat)) := by
  apply FiniteActionTree.Tree.ext (Subsingleton.elim _ _)
  intro action
  unfold observe
  rw [FinalSemantics.observe_step, FinalSemantics.observe_step]
  change FinitePowerset.map _ (observedSuccessors repeated action) =
    FinitePowerset.map _ (observedSuccessors (GSOSControls.pure (0 : Nat)) action)
  rw [repeated_successor_sets_equal]

theorem final_set_observation_is_strictly_coarser :
    observe repeated = observe (GSOSControls.pure (0 : Nat)) ∧
    ¬EventMultiplicity.Bisimilar multiplicitySystem repeated
      multiplicitySystem (GSOSControls.pure (0 : Nat)) :=
  ⟨repeated_final_observations_equal, repeated_not_event_bisimilar⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GSOSProfile
