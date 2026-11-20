import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls

/-!
# Which pairs the criterion asks about, and how many switches witness the separation

* **Restricting composition strengthens the negative half.** A translation homomorphic on every pair
  is homomorphic on the composable ones, so emptiness of uniform translations from the step with
  restricted composition gives emptiness from the step with every pair composable, into any target
  (`restricted_implies_total`); with the reflective calculus as target this is the negative half of
  `strict_separation` (`total_from_restricted`).
* **The count check and the collect pattern witness the separation as well as none queries**
  (`separation_by_count`, `separation_by_collect`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Witnesses

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation isEmpty_uniformTranslation)
open ByInstantiation (G)

/-- **Restricting composition strengthens the negative half**, into any target. -/
theorem restricted_implies_total (ω : G [] .nm) (M : ParallelCalculus) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) M) → IsEmpty (UniformTranslation (stepParallel ω) M) :=
  fun empty => ⟨fun τ => empty.false
    ⟨τ.map, fun S T _ => τ.homomorphic S T trivial, τ.preserves, τ.reflects⟩⟩

/-- With the reflective calculus as target. -/
theorem total_from_restricted {ω : G [] .nm} (closed : ByInstantiation.Closed ω) :
    IsEmpty (UniformTranslation (stepParallel ω) (rhoParallel ω)) :=
  restricted_implies_total ω _ (strict_separation_solvable closed).2

/-- The count check makes the step with restricted composition switchable. -/
theorem count_switchable (ω : G [] .nm) : (stepParallelSolvable ω).Switchable := by
  obtain ⟨_, _, composable, succeeds, blocked⟩ := count_switched ω
  exact ⟨countSystem ω, blockerSystem, composable, succeeds, blocked⟩

/-- So does the collect pattern. -/
theorem collect_switchable (ω : G [] .nm) : (stepParallelSolvable ω).Switchable := by
  obtain ⟨_, _, composable, succeeds, blocked⟩ := collect_switched ω
  exact ⟨collectSystem ω, blockerSystem, composable, succeeds, blocked⟩

/-- **The separation's negative half, witnessed by a count check.** -/
theorem separation_by_count (ω : G [] .nm) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) (rhoParallel ω)) :=
  isEmpty_uniformTranslation (count_switchable ω) (rhoParallel_persistent ω)

/-- **The separation's negative half, witnessed by a collect pattern.** -/
theorem separation_by_collect (ω : G [] .nm) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) (rhoParallel ω)) :=
  isEmpty_uniformTranslation (collect_switchable ω) (rhoParallel_persistent ω)

#print axioms restricted_implies_total
#print axioms total_from_restricted
#print axioms count_switchable
#print axioms collect_switchable
#print axioms separation_by_count
#print axioms separation_by_collect

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Witnesses
