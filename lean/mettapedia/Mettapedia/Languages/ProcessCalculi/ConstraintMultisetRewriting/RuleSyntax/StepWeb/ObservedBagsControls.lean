import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundControls

/-!
# Controls for bags asked at each member's own information

The bag of the two members that make a `1` and a `2` unless a `9` is present (`Rounds.Controls.ninePair`)
is admitted on its own at the empty state (`ninePair_admitted`). So:

* the own-guard step admits it (`ninePair_own`);
* a profile asking every member for one occurrence in the fiber of every row refuses it, since the
  empty state has none (`count_one_refuses`);
* a profile asking for none keeps it (`count_zero_admits`).

So the observed step is strictly finer than the own-guard step (`observed_strictly_finer`), and its
queries are asked against the occurrences present before the bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags.Controls

open _root_.Mettapedia.Logic.LP
open _root_.Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (regionOf)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
  (RegionQuery)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame
  (Terms frames ext embed)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
  (Tm X E c x)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds.Controls
  (unlessNine oneUnlessNine ninePair ninePair_admitted)

/-- Every member asks that the fiber of every row, over every solution, hold `number` occurrences. -/
def countAll (number : ℕ) : Profile ℕ (ext action) unlessNine :=
  fun _ => [RegionQuery.count (fun _ _ => true) number]

theorem ninePair_nonempty : (bagOf action ninePair).members ≠ [] :=
  List.cons_ne_nil _ _

/-- **The own-guard step admits the bag of the two at the empty state.** -/
theorem ninePair_own :
    (ownBagStep X ℕ (ext action) unlessNine).Admits (s := Synchronous.empty) (bagOf action ninePair) :=
  (ownBagStep_admits_iff _).mpr ⟨ninePair_nonempty, ninePair_admitted⟩

/-- **A count that fails refuses the bag**: the empty state has no occurrence in any fiber. -/
theorem count_one_refuses :
    ¬ (observedOwnStep X (countAll 1)).Admits (s := Synchronous.empty) (bagOf action ninePair) := by
  rw [observedOwnStep_admits_iff]
  rintro ⟨_, own, asks⟩
  obtain ⟨b, σ, solved⟩ := own.2.2.1
  have inside : oneUnlessNine ∈ (bagOf action ninePair).members := by simp [bagOf, ninePair]
  have holds := asks oneUnlessNine inside (RegionQuery.count (fun _ _ => true) 1)
    (by simp [countAll]) b σ (Bag.models_member X inside solved)
  simp [RegionQuery.count_holds_iff, regionOf, Synchronous.empty] at holds

/-- **A count that holds keeps the bag**: no occurrence in the fiber of every row. -/
theorem count_zero_admits :
    (observedOwnStep X (countAll 0)).Admits (s := Synchronous.empty) (bagOf action ninePair) := by
  rw [observedOwnStep_admits_iff]
  refine ⟨ninePair_nonempty, ninePair_admitted, fun m _ q member b σ _ => ?_⟩
  have same : q = RegionQuery.count (fun _ _ => true) 0 := by simpa [countAll] using member
  subst same
  simp [RegionQuery.count_holds_iff, regionOf, Synchronous.empty]

/-- **The observed step is strictly finer than the own-guard step.** -/
theorem observed_strictly_finer :
    (ownBagStep X ℕ (ext action) unlessNine).Admits (s := Synchronous.empty) (bagOf action ninePair) ∧
      ¬ (observedOwnStep X (countAll 1)).Admits (s := Synchronous.empty) (bagOf action ninePair) :=
  ⟨ninePair_own, count_one_refuses⟩

#print axioms ninePair_own
#print axioms count_one_refuses
#print axioms count_zero_admits
#print axioms observed_strictly_finer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ObservedBags.Controls
