import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Operational
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Barbed

/-!
# Observations on arbitrary clean target points

The indexed weak barbed bisimilarity is the existing source/target relation,
with every output on an observed closed channel counted as a barb. This is
not a claim of contextual congruence under arbitrary transform programs or
another convention for reading rho's barbs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open ByInstantiation (G Closed)

/-- Full abstraction extends to every pair of clean points, rather than
only literal compiler outputs. The two directions use actual bisimulations. -/
theorem indexed_barbed_iff {observed : G [] .nm → Prop} (closed : ∀ name, observed name → Closed name)
    (first second : Point) :
    Encodings.SourceBisimilar observed (readback first) (readback second) ↔
      Encodings.StepBisimilar observed first.val second.val := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨_, Encodings.step_of_source closed bisimulation,
      readback first, readback second, readback_represents first, readback_represents second, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨_, Encodings.source_of_step closed bisimulation,
      first.val, second.val, readback_represents first, readback_represents second, related⟩

/-- Infinite executions of the restricted point calculus and of the original
program agree. The clean invariant supplies every intermediate proof. -/
theorem point_divergence_iff_raw (before : Point) :
    (∃ states : Nat → Point, states 0 = before ∧ ∀ n, Move (states n) (states (n + 1))) ↔
      ∃ states : Nat → RawState, states 0 = before.val ∧ ∀ n, Encodings.Moves (states n) (states (n + 1)) := by
  constructor
  · rintro ⟨states, first, steps⟩
    exact ⟨fun n => (states n).val, congrArg Subtype.val first, steps⟩
  · rintro ⟨states, first, steps⟩
    have clean : ∀ n, Clean (states n) := by
      intro n
      induction n with
      | zero => rw [first]; exact before.property
      | succ n ih => exact clean_closed ih (steps n)
    exact ⟨fun n => ⟨states n, clean n⟩, Subtype.ext first, steps⟩

theorem point_divergence_iff_source (before : Point) :
    (∃ states : Nat → Point, states 0 = before ∧ ∀ n, Move (states n) (states (n + 1))) ↔
      ∃ processes : Nat → RhoProcess, processes 0 = readback before ∧
        ∀ n, rhoLanguageDefGSLT.Step (processes n) (processes (n + 1)) :=
  (point_divergence_iff_raw before).trans (divergence_iff before)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
